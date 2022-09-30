# Copyright © 2022 CISPA Helmholtz Center for Information Security.
# Author: Dominic Steinhöfel.
#
# This file is part of ISLa.
#
# ISLa is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# ISLa is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with ISLa.  If not, see <http://www.gnu.org/licenses/>.

import copy
import itertools
import logging
from functools import reduce
from typing import Union, Optional, Set, Dict, cast, Tuple, List, Callable

import z3
from grammar_graph import gg
from orderedset import OrderedSet

from isla import language
from isla.derivation_tree import DerivationTree
from isla.helpers import is_nonterminal, Maybe, chain_functions, is_prefix
from isla.isla_predicates import (
    STANDARD_STRUCTURAL_PREDICATES,
    STANDARD_SEMANTIC_PREDICATES,
)
from isla.language import (
    Formula,
    StructuralPredicate,
    SemanticPredicate,
    parse_isla,
    VariablesCollector,
    Constant,
    FilterVisitor,
    NumericQuantifiedFormula,
    StructuralPredicateFormula,
    SMTFormula,
    SemanticPredicateFormula,
    Variable,
    replace_formula,
    BoundVariable,
    ExistsIntFormula,
    ForallIntFormula,
    QuantifiedFormula,
    PropositionalCombinator,
    ConjunctiveFormula,
    ForallFormula,
    ExistsFormula,
    NegatedFormula,
    DisjunctiveFormula,
    BindExpression,
    split_conjunction,
    split_disjunction,
    parse_bnf,
    unparse_isla,
)
from isla.three_valued_truth import ThreeValuedTruth
from isla.trie import SubtreesTrie
from isla.type_defs import Grammar, Path
from isla.z3_helpers import (
    evaluate_z3_expression,
    DomainError,
    is_valid,
    z3_and,
    z3_or,
    z3_eq,
    replace_in_z3_expr,
    z3_subst,
)

logger = logging.getLogger("evaluator")


def propositionally_unsatisfiable(formula: Formula) -> bool:
    if formula == SMTFormula(z3.BoolVal(True)):
        return False
    if formula == SMTFormula(z3.BoolVal(False)):
        return True

    z3_formula = approximate_isla_to_smt_formula(
        formula, replace_untranslatable_with_predicate=True
    )

    return is_valid(z3_formula).is_true()


def evaluate(
    formula: Formula | str,
    reference_tree: DerivationTree,
    grammar: Grammar | str,
    structural_predicates: Set[StructuralPredicate] = STANDARD_STRUCTURAL_PREDICATES,
    semantic_predicates: Set[SemanticPredicate] = STANDARD_SEMANTIC_PREDICATES,
    assumptions: Optional[Set[Formula]] = None,
    subtrees_trie: Optional[SubtreesTrie] = None,
    graph: Optional[gg.GrammarGraph] = None,
) -> ThreeValuedTruth:
    assumptions = assumptions or set()

    if isinstance(grammar, str):
        grammar = parse_bnf(grammar)

    assert reference_tree is not None
    assert isinstance(reference_tree, DerivationTree)
    subtrees_trie = reference_tree.trie() if subtrees_trie is None else subtrees_trie
    graph = gg.GrammarGraph.from_grammar(grammar) if graph is None else graph

    formula = instantiate_top_level_constant(
        parse_isla(formula, grammar, structural_predicates, semantic_predicates)
        if isinstance(formula, str)
        else formula,
        reference_tree,
    )

    # NOTE: Deactivated, might be too strict for evaluation (though maybe
    #       necessary for solving). See comment in well_formed.
    # if assertions_activated():
    #     res, msg = well_formed(formula, grammar)
    #     assert res, msg

    if not assumptions and not FilterVisitor(
        lambda f: isinstance(f, NumericQuantifiedFormula)
    ).collect(formula):
        # The legacy evaluation performs better, but only works w/o
        # NumericQuantifiedFormulas / assumptions. # It might be possible to consider
        # assumptions, but the implemented method works and we would rather not invest
        # that work to gain some seconds of performance.
        return evaluate_legacy(
            formula, grammar, {}, reference_tree, trie=subtrees_trie, graph=graph
        )

    qfr_free: Formula = eliminate_quantifiers(
        formula,
        grammar=grammar,
        numeric_constants={
            c
            for f in (assumptions | {formula})
            for c in VariablesCollector.collect(f)
            if isinstance(c, Constant) and c.is_numeric()
        },
    )

    # Substitute assumptions

    # First, eliminate quantifiers in assumptions. We don't supply any numeric constants
    # here, as this would be unsound in assumptions: We know that the core holds for any
    # int, but not for which one.
    qfr_free_assumptions_set = eliminate_quantifiers_in_assumptions(
        assumptions, formula, grammar
    )
    assert qfr_free_assumptions_set

    # The assumptions in qfr_free_assumptions_set have to be regarded as a disjunction,
    # thus we can only return True if the formula holds for all assumptions. However,
    # we can already return False if it does not hold for any assumption.

    for qfr_free_assumptions in qfr_free_assumptions_set:
        # Replace the assumptions by True in the formula
        assumptions_instantiated = qfr_free
        for assumption in qfr_free_assumptions:
            assumptions_instantiated = replace_formula(
                assumptions_instantiated, assumption, SMTFormula(z3.BoolVal(True))
            )

        # Evaluate predicates
        without_predicates: Formula = replace_formula(
            assumptions_instantiated,
            lambda f: evaluate_predicates_action(f, reference_tree, graph),
        )

        # The remaining formula is a pure SMT formula if there were no quantifiers over
        # open trees. In the case that there *were* such quantifiers, we still convert
        # to an SMT formula, replacing all quantifiers with fresh predicates, which
        # still allows us to perform an evaluation.
        smt_formula: z3.BoolRef = approximate_isla_to_smt_formula(
            without_predicates, replace_untranslatable_with_predicate=True
        )

        smt_result = is_valid(smt_formula)

        # We return unknown / false directly if the result is unknown / false for any
        # assumption.
        if smt_result.is_unknown():
            return ThreeValuedTruth.unknown()
        elif smt_result.is_false():
            if not propositionally_unsatisfiable(
                reduce(
                    Formula.__and__, qfr_free_assumptions, SMTFormula(z3.BoolVal(True))
                )
            ):
                return ThreeValuedTruth.false()
        else:
            assert smt_result.is_true()

    # We have proven the formula true for all assumptions: Return True
    return ThreeValuedTruth.true()


def instantiate_top_level_constant(formula, reference_tree):
    top_level_constants = {
        c
        for c in VariablesCollector.collect(formula)
        if isinstance(c, Constant) and not c.is_numeric()
    }
    assert len(top_level_constants) <= 1
    formula = (
        formula.substitute_expressions(
            {next(iter(top_level_constants)): reference_tree}
        )
        if len(top_level_constants) > 0
        else formula
    )
    return formula


def evaluate_predicates_action(
    formula: Formula, reference_tree: DerivationTree, graph: gg.GrammarGraph
) -> bool | Formula:
    if isinstance(formula, StructuralPredicateFormula):
        return SMTFormula(z3.BoolVal(formula.evaluate(reference_tree)))

    if isinstance(formula, SemanticPredicateFormula):
        eval_result = formula.evaluate(graph)

        if not eval_result.ready():
            return False

        if eval_result.true():
            return SMTFormula(z3.BoolVal(True))
        elif eval_result.false():
            return SMTFormula(z3.BoolVal(False))

        substs: Dict[Variable | DerivationTree, DerivationTree] = eval_result.result
        assert isinstance(substs, dict)
        assert all(
            isinstance(key, Variable) and key.n_type == Variable.NUMERIC_NTYPE
            for key in substs
        )
        return SMTFormula(
            z3_and(
                [
                    cast(z3.BoolRef, z3_eq(const.to_smt(), str(substs[const])))
                    for const in substs
                ]
            ),
            *substs.keys(),
        )

    return False


def eliminate_quantifiers_in_assumptions(
    assumptions: Set[Formula], formula: Formula, grammar: Grammar
) -> Set[Tuple[Formula, ...]]:
    # NOTE: We could eliminate unsatisfiable preconditions already here, but that turned
    #       out to be quite expensive. Rather, we check whether the precondition was
    #       unsatisfiable before returning a negative evaluation result.
    # NOTE: We only check propositional unsatisfiability, which is an approximation;
    #       thus, it is theoretically possible that we return a negative result for an
    #       actually true formula. This, however, only happens with assumptions present,
    #       which are used in the solver when checking whether an existential quantifier
    #       can be quickly removed. Not removing the quantifier is thus not soundness
    #       critical. Also, false negative results should generally be less critical
    #       than false positive ones.
    return {
        assumptions
        for assumptions in itertools.product(
            *[
                split_disjunction(conjunct)
                for assumption in assumptions
                for conjunct in split_conjunction(
                    eliminate_quantifiers(
                        assumption, grammar=grammar, keep_existential_quantifiers=True
                    )
                )
                # By quantifier elimination, we might obtain the original formula the
                # same way it was derived before. This has to be excluded, to ensure
                # that the formula is not trivially satisfied
                if conjunct != formula
            ]
        )
        # if not propositionally_unsatisfiable(  # <- See comment above
        #     reduce(Formula.__and__, assumptions, SMTFormula(z3.BoolVal(True))))
    }


def well_formed(
    formula: Formula,
    grammar: Grammar,
    bound_vars: Optional[OrderedSet[BoundVariable]] = None,
    in_expr_vars: Optional[OrderedSet[Variable]] = None,
    bound_by_smt: Optional[OrderedSet[Variable]] = None,
) -> Tuple[bool, str]:
    # TODO Problem: The formula
    #   ```
    #   forall <?NONTERMINAL> container in start:
    #     exists <?NONTERMINAL> length_field in container:
    #       exists int decimal:
    #         (hex_to_decimal(length_field, decimal) and
    #          (= (div (str.len (str.replace_all container " " "")) 2)
    #          (str.to.int decimal)))
    #   ```
    #  is reported as ill-formed since `container`, the in-expression of the existential
    #  qfr, is reported to be bound by the SMT formula. This could be an actual problem,
    #  but not when evaluating, only when generating. With two symbols for the SMT
    #  formula, I simply received a timeout. Can we defer the Z3 call in the solver
    #  until `container` is fixed?

    bound_vars = OrderedSet([]) if bound_vars is None else bound_vars
    in_expr_vars = OrderedSet([]) if in_expr_vars is None else in_expr_vars
    bound_by_smt = OrderedSet([]) if bound_by_smt is None else bound_by_smt

    unknown_typed_variables = [
        var
        for var in formula.free_variables()
        if is_nonterminal(var.n_type) and var.n_type not in grammar
    ]
    if unknown_typed_variables:
        return False, "Unkown types of variables " + ", ".join(
            map(repr, unknown_typed_variables)
        )

    def raise_not_implemented_error(
        formula: Formula,
    ) -> Maybe[Tuple[bool, str]]:
        raise NotImplementedError(f"Unsupported formula type {type(formula).__name__}")

    def close(check_function: callable) -> callable:
        return lambda f: check_function(
            f,
            grammar,
            bound_vars,
            in_expr_vars,
            bound_by_smt,
        )

    monad = chain_functions(
        map(
            close,
            [
                wellformed_exists_int_formula,
                wellformed_quantified_formula,
                wellformed_smt_formula,
                wellformed_propositional_formula,
                wellformed_structural_predicate_formula,
                raise_not_implemented_error,
            ],
        ),
        formula,
    )

    return monad.a


def wellformed_exists_int_formula(
    formula: Formula,
    grammar: Grammar,
    bound_vars: OrderedSet[BoundVariable],
    in_expr_vars: OrderedSet[Variable],
    bound_by_smt: OrderedSet[Variable],
) -> Maybe[Tuple[bool, str]]:
    if not isinstance(formula, ExistsIntFormula):
        return Maybe.nothing()

    if formula.bound_variables().intersection(bound_vars):
        return Maybe(
            (
                False,
                f"Variables {', '.join(map(str, formula.bound_variables().intersection(bound_vars)))} "
                f"already bound in outer scope",
            )
        )

    unbound_variables = [
        free_var
        for free_var in formula.free_variables()
        if type(free_var) is BoundVariable
        if free_var not in bound_vars
    ]
    if unbound_variables:
        return Maybe(
            (
                False,
                "Unbound variables "
                + ", ".join(map(repr, unbound_variables))
                + f" in {formula}",
            )
        )

    return Maybe(
        well_formed(
            formula.inner_formula,
            grammar,
            bound_vars | formula.bound_variables(),
            in_expr_vars,
            bound_by_smt,
        )
    )


def wellformed_quantified_formula(
    formula: Formula,
    grammar: Grammar,
    bound_vars: OrderedSet[BoundVariable],
    in_expr_vars: OrderedSet[Variable],
    bound_by_smt: OrderedSet[Variable],
) -> Maybe[Tuple[bool, str]]:
    if not isinstance(formula, QuantifiedFormula):
        return Maybe.nothing()

    if formula.in_variable in bound_by_smt:
        return Maybe(
            (
                False,
                f"Variable {formula.in_variable} in {formula} bound be outer SMT formula",
            )
        )
    if formula.bound_variables().intersection(bound_vars):
        return Maybe(
            (
                False,
                f"Variables {', '.join(map(str, formula.bound_variables().intersection(bound_vars)))} "
                f"already bound in outer scope",
            )
        )
    if (
        type(formula.in_variable) is BoundVariable
        and formula.in_variable not in bound_vars
    ):
        return Maybe((False, f"Unbound variable {formula.in_variable} in {formula}"))
    unbound_variables = [
        free_var
        for free_var in formula.free_variables()
        if type(free_var) is BoundVariable
        if free_var not in bound_vars
    ]
    if unbound_variables:
        return Maybe(
            (
                False,
                "Unbound variables "
                + ", ".join(map(repr, unbound_variables))
                + f" in {formula}",
            )
        )

    unknown_typed_variables = [
        var
        for var in formula.bound_variables()
        if is_nonterminal(var.n_type) and var.n_type not in grammar
    ]
    if unknown_typed_variables:
        return Maybe(
            (
                False,
                "Unkown types of variables "
                + ", ".join(map(repr, unknown_typed_variables))
                + f" in {formula}",
            )
        )

    if formula.bind_expression is not None:
        unknown_typed_variables = [
            var
            for var in formula.bind_expression.all_bound_variables(grammar)
            if is_nonterminal(var.n_type) and var.n_type not in grammar
        ]
        if unknown_typed_variables:
            return Maybe(
                (
                    False,
                    "Unkown types of variables "
                    + ", ".join(map(repr, unknown_typed_variables))
                    + f" in match expression {formula.bind_expression}",
                )
            )

    return Maybe(
        well_formed(
            formula.inner_formula,
            grammar,
            bound_vars | formula.bound_variables(),
            in_expr_vars | OrderedSet([formula.in_variable]),
            bound_by_smt,
        )
    )


def wellformed_smt_formula(
    formula: Formula,
    _1,
    bound_vars: OrderedSet[BoundVariable],
    in_expr_vars: OrderedSet[Variable],
    _2,
) -> Maybe[Tuple[bool, str]]:
    if not isinstance(formula, SMTFormula):
        return Maybe.nothing()

    if any(free_var in in_expr_vars for free_var in formula.free_variables()):
        return Maybe(
            (
                False,
                f"Formula {formula} binding variables of 'in' expressions in an outer quantifier.",
            )
        )

    if any(
        free_var not in bound_vars
        for free_var in formula.free_variables()
        if type(free_var) is BoundVariable
    ):
        return Maybe((False, "(TODO)"))

    return Maybe((True, ""))


def wellformed_propositional_formula(
    formula: Formula,
    grammar: Grammar,
    bound_vars: OrderedSet[BoundVariable],
    in_expr_vars: OrderedSet[Variable],
    bound_by_smt: OrderedSet[Variable],
) -> Maybe[Tuple[bool, str]]:
    if not isinstance(formula, PropositionalCombinator):
        return Maybe.nothing()

    if isinstance(formula, ConjunctiveFormula):
        smt_formulas = [f for f in formula.args if type(f) is SMTFormula]
        other_formulas = [f for f in formula.args if type(f) is not SMTFormula]

        for smt_formula in smt_formulas:
            res, msg = well_formed(
                smt_formula, grammar, bound_vars, in_expr_vars, bound_by_smt
            )
            if not res:
                return Maybe((False, msg))

        for smt_formula in smt_formulas:
            bound_vars |= [
                var
                for var in smt_formula.free_variables()
                if type(var) is BoundVariable
            ]
            bound_by_smt |= smt_formula.free_variables()

        for f in other_formulas:
            res, msg = well_formed(f, grammar, bound_vars, in_expr_vars, bound_by_smt)
            if not res:
                return Maybe((False, msg))

        return Maybe((True, ""))
    else:
        for subformula in formula.args:
            res, msg = well_formed(
                subformula, grammar, bound_vars, in_expr_vars, bound_by_smt
            )
            if not res:
                return Maybe((False, msg))

        return Maybe((True, ""))


def wellformed_structural_predicate_formula(
    formula: Formula,
    _1,
    bound_vars: OrderedSet[BoundVariable],
    _2,
    _3,
) -> Maybe[Tuple[bool, str]]:
    if not isinstance(formula, StructuralPredicateFormula):
        return Maybe.nothing()

    unbound_variables = [
        free_var
        for free_var in formula.free_variables()
        if type(free_var) is BoundVariable
        if free_var not in bound_vars
    ]
    if unbound_variables:
        return Maybe(
            (
                False,
                "Unbound variables "
                + ", ".join(map(repr, unbound_variables))
                + f" in {formula}",
            )
        )

    return Maybe((True, ""))


def evaluate_legacy(
    formula: Formula,
    grammar: Grammar | str,
    assignments: Dict[Variable, Tuple[Path, DerivationTree]],
    reference_tree: DerivationTree,
    trie: Optional[SubtreesTrie] = None,
    graph: Optional[gg.GrammarGraph] = None,
) -> ThreeValuedTruth:
    """
    An evaluation method which is based on tracking assignments in a dictionary.
    This does not work with formulas containing numeric constant introductions,
    but is significantly faster than the more general method based on formula manipulations.

    :param formula: The formula to evaluate.
    :param grammar: The reference grammar.
    :param assignments: The assignments recorded so far.
    :param reference_tree: The tree to which the paths in assignments refer.
    :param trie: A prefix tree (tree) mapping tree paths from `reference_tree` (in pre-order) to subtrees.
    :param graph: The GrammarGraph for `grammar`.
    :return: A (three-valued) truth value.
    """
    assert reference_tree is not None
    assert isinstance(reference_tree, DerivationTree)

    grammar = parse_bnf(grammar) if isinstance(grammar, str) else grammar
    graph = gg.GrammarGraph.from_grammar(grammar) if graph is None else graph
    trie = reference_tree.trie() if trie is None else trie

    def raise_not_implemented_error(
        f: Formula,
    ) -> Maybe[ThreeValuedTruth]:
        raise NotImplementedError(
            f"Don't know how to evaluate the formula {unparse_isla(f)}"
        )

    def close(evaluation_function: callable) -> callable:
        return lambda f: evaluation_function(
            f,
            assignments,
            reference_tree,
            graph,
            grammar,
            trie,
        )

    monad = chain_functions(
        map(
            close,
            [
                evaluate_exists_int_formula,
                evaluate_smt_formula,
                evaluate_quantified_formula,
                evaluate_structural_predicate_formula,
                evaluate_semantic_predicate_formula,
                evaluate_negated_formula_formula,
                evaluate_conjunctive_formula_formula,
                evaluate_disjunctive_formula,
                raise_not_implemented_error,
            ],
        ),
        formula,
    )

    return monad.a


def evaluate_exists_int_formula(
    formula: Formula, _1, _2, _3, _4, _5
) -> Maybe[ThreeValuedTruth]:
    if not isinstance(formula, ExistsIntFormula):
        return Maybe.nothing()

    raise NotImplementedError(
        "This method cannot evaluate IntroduceNumericConstantFormula formulas."
    )


def evaluate_smt_formula(
    formula: Formula,
    assignments: Dict[Variable, Tuple[Path, DerivationTree]],
    _1,
    _2,
    _3,
    _4,
) -> Maybe[ThreeValuedTruth]:
    if not isinstance(formula, SMTFormula):
        return Maybe.nothing()

    if formula.free_variables().difference(assignments) or any(
        tree.is_open() for tree in formula.substitutions.values()
    ):
        return Maybe(ThreeValuedTruth.unknown())

    z3_formula = (
        z3_subst(
            formula.formula,
            {
                z3.String(var.name): z3.StringVal(str(tree))
                for var, tree in formula.substitutions.items()
            },
        )
        if formula.substitutions
        else formula.formula
    )

    try:
        translation = evaluate_z3_expression(z3_formula)

        var_map: Dict[str, Variable] = {var.name: var for var in assignments}

        args_instantiation = [assignments[var_map[arg]][1] for arg in translation[0]]

        if any(inst.is_open() for inst in args_instantiation):
            return Maybe(ThreeValuedTruth.unknown())

        string_instantiations = tuple(map(str, args_instantiation))

        try:
            return Maybe(
                ThreeValuedTruth.from_bool(
                    translation[1](string_instantiations)
                    if string_instantiations
                    else translation[1]
                )
            )
        except DomainError:
            return Maybe(ThreeValuedTruth.false())
    except NotImplementedError:
        return Maybe(
            is_valid(
                z3.substitute(
                    formula.formula,
                    *tuple(
                        {
                            z3.String(symbol.name): z3.StringVal(
                                str(symbol_assignment[1])
                            )
                            for symbol, symbol_assignment in assignments.items()
                        }.items()
                    ),
                )
            )
        )


def evaluate_quantified_formula(
    formula: Formula,
    assignments: Dict[Variable, Tuple[Path, DerivationTree]],
    reference_tree: DerivationTree,
    graph: gg.GrammarGraph,
    grammar: Grammar,
    trie: SubtreesTrie,
) -> Maybe[ThreeValuedTruth]:
    if not isinstance(formula, QuantifiedFormula):
        return Maybe.nothing()

    if isinstance(formula.in_variable, DerivationTree):
        in_path, in_inst = next(
            (path, subtree)
            for path, subtree in reference_tree.paths()
            if subtree.id == formula.in_variable.id
        )
    else:
        assert formula.in_variable in assignments
        in_path, in_inst = assignments[formula.in_variable]

    if formula.bind_expression is None:
        sub_trie = trie.get_subtrie(in_path)

        new_assignments: List[Dict[Variable, Tuple[Path, DerivationTree]]] = []
        for path_key, (path, subtree) in sub_trie.items():
            if subtree.value == formula.bound_variable.n_type:
                new_assignments.append(
                    {formula.bound_variable: (in_path + path, subtree)}
                )
    else:
        new_assignments = [
            {
                var: (in_path + path, tree)
                for var, (path, tree) in new_assignment.items()
            }
            for new_assignment in matches_for_quantified_formula(
                formula, grammar, in_inst, {}
            )
        ]

    new_assignments = [
        new_assignment | assignments for new_assignment in new_assignments
    ]

    assert all(
        reference_tree.is_valid_path(path)
        and reference_tree.find_node(tree) is not None
        and reference_tree.get_subtree(path) == tree
        for assignment in new_assignments
        for path, tree in assignment.values()
    )

    # If the reference tree contains open leaves, we have to check whether those
    # might eventually match the quantifier. In the case of a universal quantifier,
    # this results in an "unknown" verdict in any case; in the case of an existential
    # quantifier, it results in "unknown" only if no instantiation matches the
    # quantifier.

    has_potential_matches = any(
        quantified_formula_might_match(
            (
                formula
                if isinstance(formula.in_variable, DerivationTree)
                else formula.substitute_expressions({formula.in_variable: in_inst})
            ).substitute_expressions({v: t for v, (_, t) in assignments.items()}),
            path_to_nonterminal,
            reference_tree,
            grammar,
            graph.reachable,
        )
        for path_to_nonterminal, _ in reference_tree.open_leaves()
    )

    if isinstance(formula, ForallFormula):
        if has_potential_matches:
            return Maybe(ThreeValuedTruth.unknown())

        return Maybe(
            ThreeValuedTruth.all(
                evaluate_legacy(
                    formula.inner_formula,
                    grammar,
                    new_assignment,
                    reference_tree,
                    trie,
                    graph=graph,
                )
                for new_assignment in new_assignments
            )
        )
    elif isinstance(formula, ExistsFormula):
        result = ThreeValuedTruth.any(
            evaluate_legacy(
                formula.inner_formula,
                grammar,
                new_assignment,
                reference_tree,
                trie,
                graph=graph,
            )
            for new_assignment in new_assignments
        )

        return Maybe(
            ThreeValuedTruth.unknown()
            if not result.is_true() and has_potential_matches
            else result
        )


def evaluate_structural_predicate_formula(
    formula: Formula,
    assignments: Dict[Variable, Tuple[Path, DerivationTree]],
    reference_tree: DerivationTree,
    _1,
    _2,
    _3,
) -> Maybe[ThreeValuedTruth]:
    if not isinstance(formula, StructuralPredicateFormula):
        return Maybe.nothing()

    arg_insts = [
        arg
        if isinstance(arg, str)
        else next(
            path for path, subtree in reference_tree.paths() if subtree.id == arg.id
        )
        if isinstance(arg, DerivationTree)
        else assignments[arg][0]
        for arg in formula.args
    ]
    return Maybe(
        ThreeValuedTruth.from_bool(
            formula.predicate.evaluate(reference_tree, *arg_insts)
        )
    )


def evaluate_semantic_predicate_formula(
    formula: Formula,
    assignments: Dict[Variable, Tuple[Path, DerivationTree]],
    _1,
    graph: gg.GrammarGraph,
    _2,
    _3,
) -> Maybe[ThreeValuedTruth]:
    if not isinstance(formula, SemanticPredicateFormula):
        return Maybe.nothing()

    arg_insts = [
        arg
        if isinstance(arg, DerivationTree) or arg not in assignments
        else assignments[arg][1]
        for arg in formula.args
    ]
    eval_res = formula.predicate.evaluate(graph, *arg_insts)

    if eval_res.true():
        return Maybe(ThreeValuedTruth.true())
    elif eval_res.false():
        return Maybe(ThreeValuedTruth.false())

    if not eval_res.ready() or not all(
        isinstance(key, Constant) for key in eval_res.result
    ):
        # Evaluation resulted in a tree update; that is, the formula is satisfiable, but only
        # after an update of its arguments. This result happens when evaluating formulas during
        # solution search after instantiating variables with concrete trees.
        return Maybe(ThreeValuedTruth.unknown())

    assignments.update(
        {const: (tuple(), assgn) for const, assgn in eval_res.result.items()}
    )

    return Maybe(ThreeValuedTruth.true())


def evaluate_negated_formula_formula(
    formula: Formula,
    assignments: Dict[Variable, Tuple[Path, DerivationTree]],
    reference_tree: DerivationTree,
    graph: gg.GrammarGraph,
    grammar: Grammar,
    trie: SubtreesTrie,
) -> Maybe[ThreeValuedTruth]:
    if not isinstance(formula, NegatedFormula):
        return Maybe.nothing()

    return Maybe(
        ThreeValuedTruth.not_(
            evaluate_legacy(
                formula.args[0],
                grammar,
                assignments,
                reference_tree,
                trie,
                graph=graph,
            )
        )
    )


def evaluate_conjunctive_formula_formula(
    formula: Formula,
    assignments: Dict[Variable, Tuple[Path, DerivationTree]],
    reference_tree: DerivationTree,
    graph: gg.GrammarGraph,
    grammar: Grammar,
    trie: SubtreesTrie,
) -> Maybe[ThreeValuedTruth]:
    if not isinstance(formula, ConjunctiveFormula):
        return Maybe.nothing()

    return Maybe(
        ThreeValuedTruth.all(
            evaluate_legacy(
                sub_formula,
                grammar,
                assignments,
                reference_tree,
                trie,
                graph=graph,
            )
            for sub_formula in formula.args
        )
    )


def evaluate_disjunctive_formula(
    formula: Formula,
    assignments: Dict[Variable, Tuple[Path, DerivationTree]],
    reference_tree: DerivationTree,
    graph: gg.GrammarGraph,
    grammar: Grammar,
    trie: SubtreesTrie,
) -> Maybe[ThreeValuedTruth]:
    if not isinstance(formula, DisjunctiveFormula):
        return Maybe.nothing()

    return Maybe(
        ThreeValuedTruth.any(
            evaluate_legacy(
                sub_formula,
                grammar,
                assignments,
                reference_tree,
                trie,
                graph=graph,
            )
            for sub_formula in formula.args
        )
    )


def eliminate_quantifiers(
    formula: Formula,
    grammar: Grammar,
    graph: Optional[gg.GrammarGraph] = None,
    numeric_constants: Optional[Set[Constant]] = None,
    keep_existential_quantifiers=False,
) -> Formula:
    # TODO: Use pre-computed paths
    numeric_constants = (
        {
            var
            for var in VariablesCollector().collect(formula)
            if isinstance(var, Constant) and var.is_numeric()
        }
        if numeric_constants is None
        else numeric_constants
    )

    graph = gg.GrammarGraph.from_grammar(grammar) if graph is None else graph

    # We eliminate all quantified formulas over derivation tree elements
    # by replacing them by the finite set of matches in the inner trees.
    quantified_formulas = [
        f
        for f in get_toplevel_quantified_formulas(formula)
        if isinstance(f, QuantifiedFormula)
    ]

    for quantified_formula in quantified_formulas:
        formula = eliminate_quantifiers_in_quantified_formula(
            formula,
            grammar,
            graph,
            keep_existential_quantifiers,
            numeric_constants,
            quantified_formula,
        )

    numeric_quantified_formulas = [
        f
        for f in get_toplevel_quantified_formulas(formula)
        if isinstance(f, NumericQuantifiedFormula)
    ]

    for quantified_formula in numeric_quantified_formulas:
        formula = eliminate_quantifiers_in_numeric_quantified_formula(
            formula,
            grammar,
            graph,
            keep_existential_quantifiers,
            numeric_constants,
            quantified_formula,
        )

    return formula


def eliminate_quantifiers_in_numeric_quantified_formula(
    context_formula: Formula,
    grammar: Grammar,
    graph: gg.GrammarGraph,
    keep_existential_quantifiers: bool,
    numeric_constants: Set[Constant],
    quantified_formula: NumericQuantifiedFormula,
) -> Formula:
    if isinstance(quantified_formula, ExistsIntFormula):
        # There might be a constant for which this formula is satisfied
        context_formula = replace_formula(
            context_formula,
            quantified_formula,
            ExistsIntFormula(
                quantified_formula.bound_variable,
                eliminate_quantifiers(
                    quantified_formula.inner_formula,
                    grammar,
                    graph=graph,
                    numeric_constants=numeric_constants,
                    keep_existential_quantifiers=keep_existential_quantifiers,
                ),
            ),
        )

        context_formula = context_formula | reduce(
            Formula.__or__,
            [
                eliminate_quantifiers(
                    quantified_formula.inner_formula.substitute_variables(
                        {quantified_formula.bound_variable: constant}
                    ),
                    grammar,
                    graph=graph,
                    numeric_constants=numeric_constants,
                )
                for constant in numeric_constants
            ],
            SMTFormula(z3.BoolVal(False)),
        )
    elif isinstance(quantified_formula, ForallIntFormula):
        context_formula = replace_formula(
            context_formula,
            quantified_formula,
            ForallIntFormula(
                quantified_formula.bound_variable,
                eliminate_quantifiers(
                    quantified_formula.inner_formula,
                    grammar,
                    graph=graph,
                    numeric_constants=numeric_constants,
                    keep_existential_quantifiers=keep_existential_quantifiers,
                ),
            ),
        )

    return context_formula


def eliminate_quantifiers_in_quantified_formula(
    context_formula: Formula,
    grammar: Grammar,
    graph: gg.GrammarGraph,
    keep_existential_quantifiers: bool,
    numeric_constants: Set[Constant],
    quantified_formula: QuantifiedFormula,
) -> Formula:
    assert isinstance(quantified_formula.in_variable, DerivationTree)
    # We can only eliminate this quantifier if in the in_expr, there is no open tree
    # from which the nonterminal of the bound variale can be reached. In that case,
    # we don't know whether the formula holds. We can still instantiate all matches,
    # but have to keep the original formula.
    keep_orig_formula = keep_existential_quantifiers or any(
        graph.reachable(leaf.value, quantified_formula.bound_variable.n_type)
        for _, leaf in quantified_formula.in_variable.open_leaves()
    )
    matches = [
        {var: tree for var, (_, tree) in match.items()}
        for match in matches_for_quantified_formula(
            quantified_formula, grammar, quantified_formula.in_variable
        )
    ]
    instantiations = [
        eliminate_quantifiers(
            quantified_formula.inner_formula.substitute_expressions(match),
            grammar,
            graph=graph,
            numeric_constants=numeric_constants,
            keep_existential_quantifiers=keep_existential_quantifiers,
        )
        for match in matches
    ]
    reduce_op = (
        Formula.__and__
        if isinstance(quantified_formula, ForallFormula)
        else Formula.__or__
    )

    if instantiations:
        replacement = reduce(reduce_op, instantiations)
        if keep_orig_formula:
            replacement = reduce_op(quantified_formula, replacement)

        return replace_formula(context_formula, quantified_formula, replacement)

    if not keep_orig_formula:
        return replace_formula(
            context_formula,
            quantified_formula,
            SMTFormula(z3.BoolVal(isinstance(quantified_formula, ForallFormula))),
        )

    return context_formula


def matches_for_quantified_formula(
    formula: QuantifiedFormula,
    grammar: Grammar,
    in_tree: Optional[DerivationTree] = None,
    initial_assignments: Optional[Dict[Variable, Tuple[Path, DerivationTree]]] = None,
) -> List[Dict[Variable, Tuple[Path, DerivationTree]]]:
    assert in_tree is None or isinstance(in_tree, DerivationTree)
    if in_tree is None:
        in_tree = formula.in_variable
        assert isinstance(in_tree, DerivationTree)

    qfd_var: BoundVariable = formula.bound_variable
    bind_expr: Optional[BindExpression] = formula.bind_expression
    new_assignments: List[Dict[Variable, Tuple[Path, DerivationTree]]] = []
    if initial_assignments is None:
        initial_assignments = {}

    def search_action(path: Path, tree: DerivationTree) -> None:
        nonlocal new_assignments

        node, children = tree
        if node == qfd_var.n_type:
            if bind_expr is not None:
                maybe_match: Optional[
                    Tuple[Tuple[BoundVariable, Tuple[Path, DerivationTree]]], ...
                ]
                maybe_match = bind_expr.match(tree, grammar)

                if maybe_match is not None:
                    maybe_match = dict(maybe_match)
                    new_assignment = copy.copy(initial_assignments)
                    new_assignment[qfd_var] = path, tree
                    new_assignment.update(
                        {v: (path + p[0], p[1]) for v, p in maybe_match.items()}
                    )

                    # The assignment is correct if there is not any non-matched leaf
                    if all(
                        any(
                            match_path == leaf_path[: len(match_path)]
                            for match_path, _ in maybe_match.values()
                        )
                        for leaf_path, _ in tree.leaves()
                    ):
                        new_assignments.append(new_assignment)
            else:
                new_assignment = copy.copy(initial_assignments)
                new_assignment[qfd_var] = path, tree
                new_assignments.append(new_assignment)

    in_tree.traverse(search_action)

    return new_assignments


def get_toplevel_quantified_formulas(
    formula: Formula,
) -> List[Union[QuantifiedFormula, NumericQuantifiedFormula]]:
    if isinstance(formula, QuantifiedFormula) or isinstance(
        formula, NumericQuantifiedFormula
    ):
        return [formula]
    elif isinstance(formula, PropositionalCombinator):
        return [
            f for arg in formula.args for f in get_toplevel_quantified_formulas(arg)
        ]
    else:
        return []


def approximate_isla_to_smt_formula(
    formula: Formula,
    replace_untranslatable_with_predicate=False,
    predicate_mapping: Optional[Dict[Formula, z3.BoolRef]] = None,
) -> z3.BoolRef:
    assert not predicate_mapping or replace_untranslatable_with_predicate
    predicate_mapping = {} if predicate_mapping is None else predicate_mapping

    if isinstance(formula, SMTFormula):
        return formula.formula

    if isinstance(formula, ConjunctiveFormula):
        return z3_and(
            [
                approximate_isla_to_smt_formula(
                    child, replace_untranslatable_with_predicate, predicate_mapping
                )
                for child in formula.args
            ]
        )

    if isinstance(formula, DisjunctiveFormula):
        return z3_or(
            [
                approximate_isla_to_smt_formula(
                    child, replace_untranslatable_with_predicate, predicate_mapping
                )
                for child in formula.args
            ]
        )

    if isinstance(formula, NegatedFormula):
        return z3.Not(
            approximate_isla_to_smt_formula(
                formula.args[0],
                replace_untranslatable_with_predicate,
                predicate_mapping,
            )
        )

    if isinstance(formula, ForallIntFormula):
        return z3.ForAll(
            [formula.bound_variable.to_smt()],
            approximate_isla_to_smt_formula(
                formula.inner_formula,
                replace_untranslatable_with_predicate,
                predicate_mapping,
            ),
        )

    if isinstance(formula, ExistsIntFormula):
        return z3.Exists(
            [formula.bound_variable.to_smt()],
            approximate_isla_to_smt_formula(
                formula.inner_formula,
                replace_untranslatable_with_predicate,
                predicate_mapping,
            ),
        )

    if not replace_untranslatable_with_predicate:
        raise NotImplementedError(
            f"Don't know how to translate formula {formula} to SMT"
        )

    if formula not in predicate_mapping:
        name_idx = 1
        replacement = z3.Bool(f"P_{name_idx}")
        while replacement in predicate_mapping.values():
            replacement = z3.Bool(f"P_{name_idx}")
            name_idx += 1

        assert replacement not in predicate_mapping.values()
        predicate_mapping[formula] = replacement

    return predicate_mapping[formula]


z3_type_predicate = z3.Function("type", z3.StringSort(), z3.StringSort(), z3.BoolSort())


def fix_str_to_int(formula: z3.BoolRef) -> z3.BoolRef:
    """
    The `str.to.int` / `str.to_int` function in Z3 / SMT-LIB is not behaving as
    one would expect. Notably, it does not work for negative numbers: It always
    outputs "-1" (default for values out of range) when called for them. This
    function replaces all `str.to.int` expressions with a sign-aware version.

    Notably, `(str.to.int x)` is replaced by
    `(ite (= (str.at x 0) "-") (* -1 (str.to.int (str.substr x 1 (- (str.len x) 1)))) (str.to.int x))`.

    When working with this formula, you should still make sure that `x` is constrained
    to strings representing valid integers.

    :param formula: Formula in which to replace `str.to.int` with optimized version.
    :return: The "fixed" formula.
    """

    def replacement(
        expr: z3.ExprRef | z3.QuantifierRef,
    ) -> Optional[z3.ExprRef | z3.QuantifierRef]:
        if expr.decl().kind() == z3.Z3_OP_STR_TO_INT:
            var = expr.children()[0]
            return z3.If(
                z3_eq(var.at(0), "-"),
                z3.IntVal(-1) * z3.StrToInt(z3.SubString(var, 1, z3.Length(var) - 1)),
                z3.StrToInt(var),
            )

        return None

    return replace_in_z3_expr(formula, replacement)


def quantified_formula_might_match(
    qfd_formula: QuantifiedFormula,
    path_to_nonterminal: Path,
    tree: DerivationTree,
    grammar: Grammar,
    reachable: Optional[Callable[[str, str], bool]] = None,
) -> bool:
    """
    This function returns `True` if in order to match the `qfd_formula`, the given path
    has to be expanded. It will return `False` if expanding that path makes no difference,
    either because there is a match already or because the expansion will not contribute
    to a future match. The purpose is to check, e.g., if a nonterminal shall be expanded
     or "freely" instantiated; or to check if a quantifier can be removed, because it won't
      match any expansion (in addition of not already matchine!).

    :param qfd_formula: The quantified formula for which to check if the given tree path might become a match.
    :param path_to_nonterminal: The path in the tree to check.
    :param tree: The context tree.
    :param grammar: The reference grammar.
    :param reachable: A reachability function in the grammar.
    :return: `True` iff some expansion of this path matches the formula, and the formula does not already match.
    """
    if reachable is None:
        reachable = gg.GrammarGraph.from_grammar(grammar).reachable

    node = tree.get_subtree(path_to_nonterminal)
    assert not node.children, "quantified_formula_might_match only works for leaf nodes"

    if qfd_formula.in_variable.find_node(node) is None:
        return False

    if qfd_formula.is_already_matched(node):
        # This formula won't match node IFF there is no subtree in node that matches.
        return any(
            quantified_formula_might_match(qfd_formula, path, node, grammar, reachable)
            for path, _ in node.paths()
            if path
        )

    qfd_nonterminal = qfd_formula.bound_variable.n_type

    if qfd_nonterminal == node.value:
        return qfd_formula.bind_expression is not None

    if qfd_nonterminal != node.value and (
        node.value == qfd_nonterminal or reachable(node.value, qfd_nonterminal)
    ):
        return True

    if qfd_formula.bind_expression is None:
        # The formula matches a (parent) element or not, but it's no future match.
        return False

    # This leaf won't reach the "root node" of the match tree for `qfd_formula`.
    assert qfd_nonterminal != node.value and not (
        node.value == qfd_nonterminal or reachable(node.value, qfd_nonterminal)
    )

    return can_extend_leaf_to_make_quantifier_match_parent(
        qfd_formula, path_to_nonterminal, tree, grammar, reachable
    )


def can_extend_leaf_to_make_quantifier_match_parent(
    qfd_formula: QuantifiedFormula,
    path_to_nonterminal: Path,
    tree: DerivationTree,
    grammar: Grammar,
    reachable: Callable[[str, str], bool],
) -> bool:
    """
    This function returns `True` if expanding at the given path makes `qfd_formula` match some parent.

    :param qfd_formula: The quantified formula for which to check if the given tree path might become a match.
    :param path_to_nonterminal: The path in the tree to check.
    :param tree: The context tree.
    :param grammar: The reference grammar.
    :param reachable: A reachability function in the grammar.
    :return: `True` iff expanding the given path makes `qfd_formula` match higher up in the tree.
    """
    # Return true if extending this leaf makes the quantifier match some parent.

    node = tree.get_subtree(path_to_nonterminal)

    maybe_prefix_tree: DerivationTree
    for maybe_prefix_tree, var_map in qfd_formula.bind_expression.to_tree_prefix(
        qfd_formula.bound_variable.n_type, grammar
    ):
        reverse_var_map = {path: var for var, path in var_map.items()}

        for idx in reversed(range(len(path_to_nonterminal))):
            subtree = tree.get_subtree(path_to_nonterminal[:idx])
            if not maybe_prefix_tree.is_potential_prefix(
                subtree
            ) or qfd_formula.is_already_matched(subtree):
                continue

            # If the current nonterminal does not need to be further expanded to match
            # the prefix tree, we need to return false; otherwise, we would needlessly
            # expand nonterminals that could actually be freely instantiated.

            path_to_node_in_prefix_tree = path_to_nonterminal[idx:]

            while not maybe_prefix_tree.is_valid_path(path_to_node_in_prefix_tree):
                path_to_node_in_prefix_tree = path_to_node_in_prefix_tree[:-1]

            # If this path in the prefix tree is sub-path of a path associated with a
            # *nonterminal* dummy variable, we do not report a possible match; such an
            # element can be freely instantiated. For a terminal dummy variable, a
            # possible match is reported if the leaf can be expanded to match that
            # variable.
            mapping_paths = [
                path
                for path in reverse_var_map
                if is_prefix(path_to_node_in_prefix_tree, path)
            ]
            assert mapping_paths

            if all(
                isinstance(reverse_var_map[mapping_path], language.DummyVariable)
                and is_nonterminal(reverse_var_map[mapping_path].n_type)
                for mapping_path in mapping_paths
            ):
                continue

            node_in_prefix_tree = maybe_prefix_tree.get_subtree(
                path_to_node_in_prefix_tree
            )

            if (
                node.value == node_in_prefix_tree.value and node_in_prefix_tree.children
            ) or reachable(node.value, node_in_prefix_tree.value):
                return True

    return False
