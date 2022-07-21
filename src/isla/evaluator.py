import copy
import itertools
import logging
from functools import reduce
from typing import Union, Optional, Set, Dict, cast, Tuple, List

import datrie
import z3
from grammar_graph import gg
from orderedset import OrderedSet

from isla.helpers import is_nonterminal, transitive_closure, path_to_trie_key, get_subtrie
from isla.isla_predicates import STANDARD_STRUCTURAL_PREDICATES, STANDARD_SEMANTIC_PREDICATES
from isla.language import Formula, StructuralPredicate, SemanticPredicate, parse_isla, \
    VariablesCollector, Constant, FilterVisitor, NumericQuantifiedFormula, StructuralPredicateFormula, SMTFormula, \
    SemanticPredicateFormula, Variable, replace_formula, \
    BoundVariable, ExistsIntFormula, ForallIntFormula, QuantifiedFormula, PropositionalCombinator, \
    ConjunctiveFormula, ForallFormula, ExistsFormula, NegatedFormula, \
    DisjunctiveFormula, BindExpression, split_conjunction, split_disjunction, DummyVariable
from isla.derivation_tree import DerivationTree
from isla.three_valued_truth import ThreeValuedTruth
from isla.type_defs import Grammar, Path, CanonicalGrammar
from isla.z3_helpers import evaluate_z3_expression, DomainError, is_valid, z3_and, z3_or, z3_eq, replace_in_z3_expr

logger = logging.getLogger("evaluator")


def propositionally_unsatisfiable(formula: Formula) -> bool:
    if formula == SMTFormula(z3.BoolVal(True)):
        return False
    if formula == SMTFormula(z3.BoolVal(False)):
        return True

    z3_formula = approximate_isla_to_smt_formula(formula, replace_untranslatable_with_predicate=True)

    return is_valid(z3_formula).is_true()


def evaluate(
        formula: Union[Formula, str],
        reference_tree: DerivationTree,
        grammar: Grammar,
        structural_predicates: Set[StructuralPredicate] = STANDARD_STRUCTURAL_PREDICATES,
        semantic_predicates: Set[SemanticPredicate] = STANDARD_SEMANTIC_PREDICATES,
        assumptions: Optional[Set[Formula]] = None,
        subtrees_trie: Optional[datrie.Trie] = None,
        graph: Optional[gg.GrammarGraph] = None) -> ThreeValuedTruth:
    assumptions = assumptions or set()

    assert reference_tree is not None
    assert isinstance(reference_tree, DerivationTree)
    if subtrees_trie is None:
        subtrees_trie = reference_tree.trie()
    if graph is None:
        graph = gg.GrammarGraph.from_grammar(grammar)

    if isinstance(formula, str):
        formula = parse_isla(formula, grammar, structural_predicates, semantic_predicates)

    top_level_constants = {
        c for c in VariablesCollector.collect(formula)
        if isinstance(c, Constant) and not c.is_numeric()}
    assert len(top_level_constants) <= 1
    if len(top_level_constants) > 0:
        formula = formula.substitute_expressions({next(iter(top_level_constants)): reference_tree})

    # NOTE: Deactivated, might be too strict for evaluation (though maybe
    #       necessary for solving). See comment in well_formed.
    # if assertions_activated():
    #     res, msg = well_formed(formula, grammar)
    #     assert res, msg

    if not assumptions and not FilterVisitor(lambda f: isinstance(f, NumericQuantifiedFormula)).collect(formula):
        # The legacy evaluation performs better, but only works w/o NumericQuantifiedFormulas / assumptions.
        # It might be possible to consider assumptions, but the implemented method works and we would
        # rather not invest that work to gain some seconds of performance.
        return evaluate_legacy(formula, grammar, {}, reference_tree, trie=subtrees_trie, graph=graph)

    qfr_free: Formula = eliminate_quantifiers(
        formula,
        grammar=grammar,
        numeric_constants={
            c for f in (assumptions | {formula}) for c in VariablesCollector.collect(f)
            if isinstance(c, Constant) and c.is_numeric()
        }
    )

    # Substitute assumptions

    # First, eliminate quantifiers in assumptions. We don't supply any numeric constants
    # here, as this would be unsound in assumptions: We know that the core holds for any
    # int, but not for which one.
    # NOTE: We could eliminate unsatisfiable preconditions already here, but that turned
    #       out to be quite expensive. Rather, we check whether the precondition was
    #       unsatisfiable before returning a negative evaluation result.
    # NOTE: We only check propositional unsatisfiability, which is an approximation; thus,
    #       it is theoretically possible that we return a negative result for an actually
    #       true formula. This, however, only happens with assumptions present, which are
    #       used in the solver when checking whether an existential quantifier can be quickly
    #       removed. Not removing the quantifier is thus not soundness critical. Also,
    #       false negative results should generally be less critical than false positive ones.
    qfr_free_assumptions_set: Set[Tuple[Formula, ...]] = {
        assumptions for assumptions in itertools.product(*[
            split_disjunction(conjunct)
            for assumption in assumptions
            for conjunct in split_conjunction(eliminate_quantifiers(
                assumption, grammar=grammar, keep_existential_quantifiers=True))
            # By quantifier elimination, we might obtain the original formula the same way
            # it was derived before. This has to be excluded, to ensure that the formula
            # is not trivially satisfied
            if conjunct != formula
        ])
        # if not propositionally_unsatisfiable(
        #     reduce(Formula.__and__, assumptions, SMTFormula(z3.BoolVal(True))))  # <- See comment above
    }

    assert qfr_free_assumptions_set

    # The assumptions in qfr_free_assumptions_set have to be regarded as a disjunction,
    # thus we can only return True if the formula holds for all assumptions. However,
    # we can already return False if it does not hold for any assumption.

    for qfr_free_assumptions in qfr_free_assumptions_set:
        # Replace the assumptions by True in the formula
        assumptions_instantiated = qfr_free
        for assumption in qfr_free_assumptions:
            assumptions_instantiated = replace_formula(
                assumptions_instantiated, assumption, SMTFormula(z3.BoolVal(True)))

        # Evaluate predicates
        def evaluate_predicates_action(formula: Formula) -> bool | Formula:
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
                assert all(isinstance(key, Variable) and key.n_type == Variable.NUMERIC_NTYPE for key in substs)
                return SMTFormula(z3_and([
                    cast(z3.BoolRef, z3_eq(const.to_smt(), str(substs[const])))
                    for const in substs]), *substs.keys())

            return False

        without_predicates: Formula = replace_formula(assumptions_instantiated, evaluate_predicates_action)

        # The remaining formula is a pure SMT formula if there were no quantifiers over open trees.
        # In the case that there *were* such quantifiers, we still convert to an SMT formula, replacing
        # all quantifiers with fresh predicates, which still allows us to perform an evaluation.
        smt_formula: z3.BoolRef = approximate_isla_to_smt_formula(without_predicates,
                                                                  replace_untranslatable_with_predicate=True)

        smt_result = is_valid(smt_formula)

        # We return unknown / false directly if the result is unknown / false for any assumption.
        if smt_result.is_unknown():
            return ThreeValuedTruth.unknown()
        elif smt_result.is_false():
            if not propositionally_unsatisfiable(
                    reduce(Formula.__and__, qfr_free_assumptions, SMTFormula(z3.BoolVal(True)))):
                return ThreeValuedTruth.false()
        else:
            assert smt_result.is_true()

    # We have proven the formula true for all assumptions: Return True
    return ThreeValuedTruth.true()


def well_formed(formula: Formula,
                grammar: Grammar,
                bound_vars: Optional[OrderedSet[BoundVariable]] = None,
                in_expr_vars: Optional[OrderedSet[Variable]] = None,
                bound_by_smt: Optional[OrderedSet[Variable]] = None) -> Tuple[bool, str]:
    # TODO Problem: The formula
    #   ```
    #   forall <?NONTERMINAL> container in start:
    #     exists <?NONTERMINAL> length_field in container:
    #       exists int decimal:
    #         (hex_to_decimal(length_field, decimal) and
    #          (= (div (str.len (str.replace_all container " " "")) 2) (str.to.int decimal)))
    #   ```
    #  is reported as ill-formed since `container`, the in-expression of the existential qfr,
    #  is reported to be bound by the SMT formula. This could be an actual problem, but not when
    #  evaluating, only when generating. With two symbols for the SMT formula, I simply received
    #  a timeout. Can we defer the Z3 call in the solver until `container` is fixed?

    if bound_vars is None:
        bound_vars = OrderedSet([])
    if in_expr_vars is None:
        in_expr_vars = OrderedSet([])
    if bound_by_smt is None:
        bound_by_smt = OrderedSet([])

    unknown_typed_variables = [
        var for var in formula.free_variables()
        if is_nonterminal(var.n_type) and var.n_type not in grammar]
    if unknown_typed_variables:
        return False, "Unkown types of variables " + ", ".join(map(repr, unknown_typed_variables))

    if isinstance(formula, ExistsIntFormula) or isinstance(formula, ForallIntFormula):
        if formula.bound_variables().intersection(bound_vars):
            return False, f"Variables {', '.join(map(str, formula.bound_variables().intersection(bound_vars)))} " \
                          f"already bound in outer scope"

        unbound_variables = [
            free_var for free_var in formula.free_variables()
            if type(free_var) is BoundVariable
            if free_var not in bound_vars]
        if unbound_variables:
            return False, f"Unbound variables " + ", ".join(map(repr, unbound_variables)) + f" in {formula}"

        return well_formed(
            formula.inner_formula,
            grammar,
            bound_vars | formula.bound_variables(),
            in_expr_vars,
            bound_by_smt
        )
    elif isinstance(formula, QuantifiedFormula):
        if formula.in_variable in bound_by_smt:
            return False, f"Variable {formula.in_variable} in {formula} bound be outer SMT formula"
        if formula.bound_variables().intersection(bound_vars):
            return False, f"Variables {', '.join(map(str, formula.bound_variables().intersection(bound_vars)))} " \
                          f"already bound in outer scope"
        if type(formula.in_variable) is BoundVariable and formula.in_variable not in bound_vars:
            return False, f"Unbound variable {formula.in_variable} in {formula}"
        unbound_variables = [
            free_var for free_var in formula.free_variables()
            if type(free_var) is BoundVariable
            if free_var not in bound_vars]
        if unbound_variables:
            return False, f"Unbound variables " + ", ".join(map(repr, unbound_variables)) + f" in {formula}"

        unknown_typed_variables = [
            var for var in formula.bound_variables()
            if is_nonterminal(var.n_type) and var.n_type not in grammar]
        if unknown_typed_variables:
            return False, "Unkown types of variables " + ", ".join(map(repr, unknown_typed_variables)) + \
                   f" in {formula}"

        if formula.bind_expression is not None:
            unknown_typed_variables = [
                var for var in formula.bind_expression.all_bound_variables(grammar)
                if is_nonterminal(var.n_type) and var.n_type not in grammar]
            if unknown_typed_variables:
                return False, "Unkown types of variables " + ", ".join(map(repr, unknown_typed_variables)) + \
                       f" in match expression {formula.bind_expression}"

        return well_formed(
            formula.inner_formula,
            grammar,
            bound_vars | formula.bound_variables(),
            in_expr_vars | OrderedSet([formula.in_variable]),
            bound_by_smt
        )
    elif isinstance(formula, SMTFormula):
        if any(free_var in in_expr_vars for free_var in formula.free_variables()):
            return False, f"Formula {formula} binding variables of 'in' expressions in an outer quantifier."

        if any(free_var not in bound_vars
               for free_var in formula.free_variables()
               if type(free_var) is BoundVariable):
            return False, "(TODO)"

        return True, ""
    elif isinstance(formula, PropositionalCombinator):
        if isinstance(formula, ConjunctiveFormula):
            smt_formulas = [f for f in formula.args if type(f) is SMTFormula]
            other_formulas = [f for f in formula.args if type(f) is not SMTFormula]

            for smt_formula in smt_formulas:
                res, msg = well_formed(smt_formula, grammar, bound_vars, in_expr_vars, bound_by_smt)
                if not res:
                    return False, msg

            for smt_formula in smt_formulas:
                bound_vars |= [var for var in smt_formula.free_variables() if type(var) is BoundVariable]
                bound_by_smt |= smt_formula.free_variables()

            for f in other_formulas:
                res, msg = well_formed(f, grammar, bound_vars, in_expr_vars, bound_by_smt)
                if not res:
                    return False, msg

            return True, ""
        else:
            for subformula in formula.args:
                res, msg = well_formed(subformula, grammar, bound_vars, in_expr_vars, bound_by_smt)
                if not res:
                    return False, msg

            return True, ""
    elif isinstance(formula, StructuralPredicateFormula) or isinstance(formula, SemanticPredicateFormula):
        unbound_variables = [
            free_var for free_var in formula.free_variables()
            if type(free_var) is BoundVariable
            if free_var not in bound_vars]
        if unbound_variables:
            return False, f"Unbound variables " + ", ".join(map(repr, unbound_variables)) + f" in {formula}"
        return True, ""
    else:
        raise NotImplementedError(f"Unsupported formula type {type(formula).__name__}")


def evaluate_legacy(
        formula: Formula,
        grammar: Grammar,
        assignments: Dict[Variable, Tuple[Path, DerivationTree]],
        reference_tree: DerivationTree,
        vacuously_satisfied: Optional[Set[Formula]] = None,
        trie: Optional[datrie.Trie] = None,
        graph: Optional[gg.GrammarGraph] = None) -> ThreeValuedTruth:
    """
    An evaluation method which is based on tracking assignments in a dictionary.
    This does not work with formulas containing numeric constant introductions,
    but is significantly faster than the more general method based on formula manipulations.

    :param formula: The formula to evaluate.
    :param grammar: The reference grammar.
    :param assignments: The assignments recorded so far.
    :param reference_tree: The tree to which the paths in assignments refer.
    :param vacuously_satisfied: A set into which universal formulas will be added when they're vacuously satisfied.
    :param trie: A prefix tree (tree) mapping tree paths from `reference_tree` (in pre-order) to subtrees.
    :param graph: The GrammarGraph for `grammar`.
    :return: A (three-valued) truth value.
    """
    assert reference_tree is not None
    assert isinstance(reference_tree, DerivationTree)

    if graph is None:
        graph = gg.GrammarGraph.from_grammar(grammar)

    if trie is None:
        trie = reference_tree.trie()

    if vacuously_satisfied is None:
        vacuously_satisfied = set()

    if isinstance(formula, ExistsIntFormula):
        raise NotImplementedError("This method cannot evaluate IntroduceNumericConstantFormula formulas.")
    elif isinstance(formula, SMTFormula):
        try:
            translation = evaluate_z3_expression(formula.formula)

            try:
                var_map: Dict[str, Variable] = {
                    var.name: var
                    for var in assignments
                }

                args_instantiation = tuple([
                    str(assignments[var_map[arg]][1])
                    for arg in translation[0]])

                return ThreeValuedTruth.from_bool(
                    translation[1](args_instantiation) if args_instantiation
                    else translation[1])
            except DomainError:
                return ThreeValuedTruth.false()
        except NotImplementedError:
            return is_valid(z3.substitute(
                formula.formula,
                *tuple({z3.String(symbol.name): z3.StringVal(str(symbol_assignment[1]))
                        for symbol, symbol_assignment
                        in assignments.items()}.items())))
    elif isinstance(formula, QuantifiedFormula):
        if isinstance(formula.in_variable, DerivationTree):
            in_path, in_inst = next(
                (path, subtree)
                for path, subtree in reference_tree.paths()
                if subtree.id == formula.in_variable.id)
        else:
            assert formula.in_variable in assignments
            in_path, in_inst = assignments[formula.in_variable]

        if formula.bind_expression is None:
            sub_trie = get_subtrie(trie, in_path)

            new_assignments: List[Dict[Variable, Tuple[Path, DerivationTree]]] = []
            for path_key, (path, subtree) in sub_trie.items():
                if subtree.value == formula.bound_variable.n_type:
                    new_assignments.append({formula.bound_variable: (in_path + path, subtree)})
        else:
            new_assignments = [
                {var: (in_path + path, tree) for var, (path, tree) in new_assignment.items()}
                for new_assignment in matches_for_quantified_formula(
                    formula, grammar, in_inst, {}, trie=get_subtrie(trie, in_path))]

        new_assignments = [
            new_assignment | assignments
            for new_assignment in new_assignments]

        assert all(
            reference_tree.is_valid_path(path) and
            reference_tree.find_node(tree) is not None and
            reference_tree.get_subtree(path) == tree
            for assignment in new_assignments
            for path, tree in assignment.values())

        if isinstance(formula, ForallFormula):
            if not new_assignments:
                vacuously_satisfied.add(formula)

            return ThreeValuedTruth.all(evaluate_legacy(
                formula.inner_formula, grammar, new_assignment, reference_tree, vacuously_satisfied, trie, graph=graph)
                                        for new_assignment in new_assignments)
        elif isinstance(formula, ExistsFormula):
            return ThreeValuedTruth.any(evaluate_legacy(
                formula.inner_formula, grammar, new_assignment, reference_tree, vacuously_satisfied, trie, graph=graph)
                                        for new_assignment in new_assignments)
    elif isinstance(formula, StructuralPredicateFormula):
        arg_insts = [
            arg if isinstance(arg, str)
            else next(path for path, subtree in reference_tree.paths() if subtree.id == arg.id)
            if isinstance(arg, DerivationTree)
            else assignments[arg][0]
            for arg in formula.args]
        return ThreeValuedTruth.from_bool(formula.predicate.evaluate(reference_tree, *arg_insts))
    elif isinstance(formula, SemanticPredicateFormula):
        arg_insts = [arg if isinstance(arg, DerivationTree) or arg not in assignments
                     else assignments[arg][1]
                     for arg in formula.args]
        eval_res = formula.predicate.evaluate(graph, *arg_insts)

        if eval_res.true():
            return ThreeValuedTruth.true()
        elif eval_res.false():
            return ThreeValuedTruth.false()

        if not eval_res.ready() or not all(isinstance(key, Constant) for key in eval_res.result):
            # Evaluation resulted in a tree update; that is, the formula is satisfiable, but only
            # after an update of its arguments. This result happens when evaluating formulas during
            # solution search after instantiating variables with concrete trees.
            return ThreeValuedTruth.unknown()

        assignments.update({const: (tuple(), assgn) for const, assgn in eval_res.result.items()})
        return ThreeValuedTruth.true()
    elif isinstance(formula, NegatedFormula):
        return ThreeValuedTruth.not_(evaluate_legacy(
            formula.args[0], grammar, assignments, reference_tree, vacuously_satisfied, trie, graph=graph))
    elif isinstance(formula, ConjunctiveFormula):
        return ThreeValuedTruth.all(
            evaluate_legacy(sub_formula, grammar, assignments, reference_tree, vacuously_satisfied, trie, graph=graph)
            for sub_formula in formula.args)
    elif isinstance(formula, DisjunctiveFormula):
        return ThreeValuedTruth.any(
            evaluate_legacy(sub_formula, grammar, assignments, reference_tree, vacuously_satisfied, trie, graph=graph)
            for sub_formula in formula.args)
    else:
        raise NotImplementedError()


def eliminate_quantifiers(
        formula: Formula,
        grammar: Grammar,
        graph: Optional[gg.GrammarGraph] = None,
        numeric_constants: Optional[Set[Constant]] = None,
        keep_existential_quantifiers=False) -> Formula:
    # TODO: Use pre-computed paths
    if numeric_constants is None:
        numeric_constants = {
            var for var in VariablesCollector().collect(formula)
            if isinstance(var, Constant) and var.is_numeric()}
    if graph is None:
        graph = gg.GrammarGraph.from_grammar(grammar)

    # We eliminate all quantified formulas over derivation tree elements
    # by replacing them by the finite set of matches in the inner trees.
    quantified_formulas = [f for f in get_toplevel_quantified_formulas(formula)
                           if isinstance(f, QuantifiedFormula)]

    if quantified_formulas:
        for quantified_formula in quantified_formulas:
            assert isinstance(quantified_formula.in_variable, DerivationTree)

            # We can only eliminate this quantifier if in the in_expr, there is no open tree
            # from which the nonterminal of the bound variale can be reached. In that case,
            # we don't know whether the formula holds. We can still instantiate all matches,
            # but have to keep the original formula.

            keep_orig_formula = keep_existential_quantifiers or any(
                graph.reachable(leaf.value, quantified_formula.bound_variable.n_type)
                for _, leaf in quantified_formula.in_variable.open_leaves())

            matches = [
                {var: tree for var, (_, tree) in match.items()}
                for match in matches_for_quantified_formula(
                    quantified_formula, grammar, quantified_formula.in_variable)]
            instantiations = [
                eliminate_quantifiers(
                    quantified_formula.inner_formula.substitute_expressions(match),
                    grammar,
                    graph=graph,
                    numeric_constants=numeric_constants,
                    keep_existential_quantifiers=keep_existential_quantifiers)
                for match in matches]

            reduce_op = Formula.__and__ if isinstance(quantified_formula, ForallFormula) else Formula.__or__

            if instantiations:
                replacement = reduce(reduce_op, instantiations)
                if keep_orig_formula:
                    replacement = reduce_op(quantified_formula, replacement)

                formula = replace_formula(formula, quantified_formula, replacement)
            else:
                if not keep_orig_formula:
                    formula = replace_formula(
                        formula,
                        quantified_formula,
                        SMTFormula(z3.BoolVal(isinstance(quantified_formula, ForallFormula))))

    numeric_quantified_formulas = [f for f in get_toplevel_quantified_formulas(formula)
                                   if isinstance(f, NumericQuantifiedFormula)]

    if numeric_quantified_formulas:
        for quantified_formula in numeric_quantified_formulas:
            if isinstance(quantified_formula, ExistsIntFormula):
                # There might be a constant for which this formula is satisfied
                formula = replace_formula(
                    formula,
                    quantified_formula,
                    ExistsIntFormula(
                        quantified_formula.bound_variable,
                        eliminate_quantifiers(
                            quantified_formula.inner_formula,
                            grammar,
                            graph=graph,
                            numeric_constants=numeric_constants,
                            keep_existential_quantifiers=keep_existential_quantifiers)))

                formula = formula | reduce(Formula.__or__, [
                    eliminate_quantifiers(
                        quantified_formula.inner_formula.substitute_variables({
                            quantified_formula.bound_variable: constant}),
                        grammar,
                        graph=graph, numeric_constants=numeric_constants)
                    for constant in numeric_constants
                ], SMTFormula(z3.BoolVal(False)))
            elif isinstance(quantified_formula, ForallIntFormula):
                formula = replace_formula(
                    formula,
                    quantified_formula,
                    ForallIntFormula(
                        quantified_formula.bound_variable,
                        eliminate_quantifiers(
                            quantified_formula.inner_formula,
                            grammar,
                            graph=graph,
                            numeric_constants=numeric_constants,
                            keep_existential_quantifiers=keep_existential_quantifiers)))

    return formula


def matches_for_quantified_formula(
        formula: QuantifiedFormula,
        grammar: Grammar,
        in_tree: Optional[DerivationTree] = None,
        initial_assignments: Optional[Dict[Variable, Tuple[Path, DerivationTree]]] = None,
        trie: Optional[datrie.Trie] = None) -> \
        List[Dict[Variable, Tuple[Path, DerivationTree]]]:
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

        subtrees_trie = None
        if trie is not None:
            subtrees_trie = get_subtrie(trie, path)

        node, children = tree
        if node == qfd_var.n_type:
            if bind_expr is not None:
                maybe_match: Optional[Tuple[Tuple[BoundVariable, Tuple[Path, DerivationTree]]], ...]
                maybe_match = bind_expr.match(tree, grammar, subtrees_trie=subtrees_trie)

                if maybe_match is not None:
                    maybe_match = dict(maybe_match)
                    new_assignment = copy.copy(initial_assignments)
                    new_assignment[qfd_var] = path, tree
                    new_assignment.update({v: (path + p[0], p[1]) for v, p in maybe_match.items()})

                    # The assignment is correct if there is not any non-matched leaf
                    if all(any(match_path == leaf_path[:len(match_path)]
                               for match_path, _ in maybe_match.values())
                           for leaf_path, _ in tree.leaves()):
                        new_assignments.append(new_assignment)
            else:
                new_assignment = copy.copy(initial_assignments)
                new_assignment[qfd_var] = path, tree
                new_assignments.append(new_assignment)

    in_tree.traverse(search_action)

    return new_assignments


def get_toplevel_quantified_formulas(formula: Formula) -> \
        List[Union[QuantifiedFormula, NumericQuantifiedFormula]]:
    if isinstance(formula, QuantifiedFormula) or isinstance(formula, NumericQuantifiedFormula):
        return [formula]
    elif isinstance(formula, PropositionalCombinator):
        return [f for arg in formula.args for f in get_toplevel_quantified_formulas(arg)]
    else:
        return []


def approximate_isla_to_smt_formula(
        formula: Formula,
        replace_untranslatable_with_predicate=False,
        predicate_mapping: Optional[Dict[Formula, z3.BoolRef]] = None) -> z3.BoolRef:
    assert not predicate_mapping or replace_untranslatable_with_predicate
    if predicate_mapping is None:
        predicate_mapping = {}

    if isinstance(formula, SMTFormula):
        return formula.formula

    if isinstance(formula, ConjunctiveFormula):
        return z3_and([approximate_isla_to_smt_formula(child, replace_untranslatable_with_predicate, predicate_mapping)
                       for child in formula.args])

    if isinstance(formula, DisjunctiveFormula):
        return z3_or([approximate_isla_to_smt_formula(child, replace_untranslatable_with_predicate, predicate_mapping)
                      for child in formula.args])

    if isinstance(formula, NegatedFormula):
        return z3.Not(
            approximate_isla_to_smt_formula(formula.args[0], replace_untranslatable_with_predicate, predicate_mapping))

    if isinstance(formula, ForallIntFormula):
        return z3.ForAll(
            [formula.bound_variable.to_smt()],
            approximate_isla_to_smt_formula(formula.inner_formula, replace_untranslatable_with_predicate,
                                            predicate_mapping))

    if isinstance(formula, ExistsIntFormula):
        return z3.Exists(
            [formula.bound_variable.to_smt()],
            approximate_isla_to_smt_formula(formula.inner_formula, replace_untranslatable_with_predicate,
                                            predicate_mapping))

    if not replace_untranslatable_with_predicate:
        raise NotImplementedError(f"Don't know how to translate formula {formula} to SMT")

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

    def replacement(expr: z3.ExprRef | z3.QuantifierRef) -> Optional[z3.ExprRef | z3.QuantifierRef]:
        if expr.decl().kind() == z3.Z3_OP_STR_TO_INT:
            var = expr.children()[0]
            return z3.If(
                z3_eq(var.at(0), "-"),
                z3.IntVal(-1) * z3.StrToInt(z3.SubString(var, 1, z3.Length(var) - 1)),
                z3.StrToInt(var)
            )

        return None

    return replace_in_z3_expr(formula, replacement)


def isla_to_smt_formula(formula: Formula, do_fix_str_to_int: bool = True) -> z3.BoolRef:
    if isinstance(formula, SMTFormula):
        if do_fix_str_to_int:
            return fix_str_to_int(formula.formula)

        return formula.formula

    if isinstance(formula, ConjunctiveFormula):
        return z3_and([isla_to_smt_formula(child) for child in formula.args])

    if isinstance(formula, DisjunctiveFormula):
        return z3_or([isla_to_smt_formula(child) for child in formula.args])

    if isinstance(formula, NegatedFormula):
        return z3.Not(isla_to_smt_formula(formula.args[0]))

    if isinstance(formula, QuantifiedFormula):
        assert isinstance(formula.in_variable, Variable)
        premises = [
            z3_type_predicate(formula.bound_variable.to_smt(), z3.StringVal(formula.bound_variable.n_type)),
            z3.Contains(formula.in_variable.to_smt(), formula.bound_variable.to_smt())
        ]
        bound_vars = []

        if formula.bind_expression:
            # NOTE: Stipulating the precise shape of the match expression as a
            #       concatenation of match expression elements can lead to
            #       non-termination of Z3 despite a set timeout. Removed that.
            for bound_element in formula.bind_expression.bound_elements:
                assert not isinstance(bound_element, list), "Conversion of optionals not yet implemented"
                if not isinstance(bound_element, DummyVariable):
                    premises.append(z3.Contains(formula.bound_variable.to_smt(), bound_element.to_smt()))
                    bound_vars.append(bound_element.to_smt())
                    continue

        if isinstance(formula, ForallFormula):
            return z3.ForAll(
                [formula.bound_variable.to_smt()] + bound_vars,
                z3.Implies(z3.And(*premises), isla_to_smt_formula(formula.inner_formula)))
        else:
            return z3.Exists(
                [formula.bound_variable.to_smt()] + bound_vars,
                z3.And(z3.And(*premises), isla_to_smt_formula(formula.inner_formula)))

    if isinstance(formula, ForallIntFormula):
        return z3.ForAll(
            [formula.bound_variable.to_smt()],
            isla_to_smt_formula(formula.inner_formula))

    if isinstance(formula, ExistsIntFormula):
        return z3.Exists(
            [formula.bound_variable.to_smt()],
            isla_to_smt_formula(formula.inner_formula))

    if isinstance(formula, StructuralPredicateFormula) or isinstance(formula, SemanticPredicateFormula):
        arg_types = [z3.IntSort() if isinstance(arg, int) else z3.StringSort() for arg in formula.args]
        args = [arg.to_smt() if isinstance(arg, Variable) else arg for arg in formula.args]
        predicate = z3.Function(formula.predicate.name, *(arg_types + [z3.BoolSort()]))
        return predicate(*args)

    raise NotImplementedError(f"Translation of formula {formula} (type {type(formula).__name__}) not implemented")


def equivalent(
        formula_1: Formula,
        formula_2: Formula,
        grammar: Optional[CanonicalGrammar] = None,
        do_fix_str_to_int: bool = True) -> Optional[bool]:
    dir_1 = implies(formula_1, formula_2, grammar, do_fix_str_to_int)
    dir_2 = implies(formula_2, formula_1, grammar, do_fix_str_to_int)

    if dir_1 is None or dir_2 is None:
        return None

    return dir_1 and dir_2


def implies(
        formula_1: Formula,
        formula_2: Formula,
        grammar: Optional[CanonicalGrammar] = None,
        do_fix_str_to_int: bool = True) -> Optional[bool]:
    sublang_relation = {}
    if grammar:
        sublang_relation = transitive_closure({
            (nonterminal_1, nonterminal_2)
            for nonterminal_1 in grammar
            for nonterminal_2 in grammar
            if (nonterminal_1 == nonterminal_2
                or any(derivation == [nonterminal_1] for derivation in grammar[nonterminal_2])
                or grammar[nonterminal_1] == [[nonterminal_2]])
        })

    f_1 = isla_to_smt_formula(formula_1, do_fix_str_to_int=do_fix_str_to_int)
    f_2 = isla_to_smt_formula(formula_2, do_fix_str_to_int=do_fix_str_to_int)

    premises = []

    x = z3.String("x")
    for nonterminal_1, nonterminal_2 in sublang_relation:
        premises.append(z3.ForAll([x], z3.Implies(z3_type_predicate(x, z3.StringVal(nonterminal_2)),
                                                  z3_type_predicate(x, z3.StringVal(nonterminal_1)))))

    # TODO: Consider adding special axioms for frequently used predicates like `before`

    for i in range(4):
        s = z3.Solver()
        s.set("timeout", (i + 1) * 30)
        for premise in premises:
            s.append(premise)
        s.append(z3.Not(z3.Implies(f_1, f_2)))
        result = s.check()

        if result != z3.unknown:
            return result == z3.unsat

    return None
