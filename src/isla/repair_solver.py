import itertools
import logging
import random
from typing import FrozenSet, Tuple, cast, Dict, Iterator, Mapping, Optional

import grammar_graph.gg as gg
import z3
from frozendict import frozendict
from orderedset import FrozenOrderedSet
from returns.curry import partial
from returns.maybe import Maybe, Nothing, Some
from returns.pipeline import flow
from returns.pipeline import is_successful

from isla.derivation_tree import DerivationTree
from isla.evaluator import matches_for_quantified_formula, evaluate
from isla.existential_helpers import insert_tree
from isla.fuzzer import GrammarCoverageFuzzer
from isla.helpers import frozen_canonical, is_nonterminal, grammar_to_frozen
from isla.isla_predicates import STANDARD_STRUCTURAL_PREDICATES
from isla.isla_shortcuts import disjunction, conjunction
from isla.language import (
    set_smt_auto_eval,
    Formula,
    QuantifiedFormula,
    PropositionalCombinator,
    ForallFormula,
    replace_formula,
    ExistsFormula,
    FilterVisitor,
    Variable,
    StructuralPredicateFormula,
    SMTFormula,
    true,
    DisjunctiveFormula,
    split_disjunction,
    split_conjunction,
    BoundVariable,
    convert_to_dnf,
    convert_to_nnf,
    VariablesCollector,
    Constant,
    parse_isla,
    ensure_unique_bound_variables,
)
from isla.solver import ISLaSolver
from isla.type_defs import FrozenGrammar, Path, Grammar
from isla_formalizations.xml_lang import (
    XML_NAMESPACE_CONSTRAINT,
    XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
)

random.seed(0)

LOGGER = logging.getLogger(__name__)


def extract_top_level_quantified_formulas(
    formula: Formula,
) -> FrozenOrderedSet[QuantifiedFormula]:
    """
    Returns all top-level quantified formulas in the given formula.

    :param formula: The formula to search in.
    :return: A tuple of all top-level quantified formulas.
    """

    if isinstance(formula, QuantifiedFormula):
        return FrozenOrderedSet({formula})

    if isinstance(formula, PropositionalCombinator):
        return FrozenOrderedSet(
            {
                f
                for arg in formula.args
                for f in extract_top_level_quantified_formulas(arg)
            }
        )

    return FrozenOrderedSet()


def set_auto_subst_and_eval(formula: Formula, value: bool) -> Formula:
    set_smt_auto_eval(formula, value)
    set_smt_auto_eval(formula, value)
    return formula


def evaluate_structural_predicates(
    constraint: Formula, context_tree: DerivationTree
) -> Formula:
    predicate_formula: StructuralPredicateFormula
    for predicate_formula in FilterVisitor(
        lambda f: (
            isinstance(f, StructuralPredicateFormula)
            and all(not isinstance(arg, Variable) for arg in f.args)
        )
    ).collect(constraint):
        instantiation = SMTFormula(z3.BoolVal(predicate_formula.evaluate(context_tree)))
        constraint = replace_formula(constraint, predicate_formula, instantiation)

    return constraint


class RepairSolver:
    def __init__(
        self,
        grammar: FrozenGrammar | Grammar,
        maybe_constraint: Optional[Formula] = None,
        structural_predicates=frozenset(STANDARD_STRUCTURAL_PREDICATES),
    ):
        self.max_tries_existential_insertion: int = 2

        self.grammar = grammar_to_frozen(grammar)
        self.canonical_grammar = frozen_canonical(self.grammar)
        self.graph = gg.GrammarGraph.from_grammar(self.grammar)
        self.solve_iterator = self.make_solve_iterator()
        self.fuzzer = GrammarCoverageFuzzer(self.grammar)

        self.constraint = (
            Maybe.from_optional(maybe_constraint)
            .map(
                lambda c: parse_isla(c, grammar, structural_predicates)
                if isinstance(c, str)
                else c
            )
            .map(ensure_unique_bound_variables)
            .value_or(true())
        )

        top_constants = {
            c
            for c in VariablesCollector.collect(self.constraint)
            if isinstance(c, Constant) and not c.is_numeric()
        }

        assert len(top_constants) <= 1, (
            "ISLa only accepts up to one constant (free variable), "
            + f'found {len(top_constants)}: {", ".join(map(str, top_constants))}'
        )

        self.top_constant = Maybe.from_optional(next(iter(top_constants), None))

    def solve(self) -> DerivationTree:
        return next(self.solve_iterator)

    def make_solve_iterator(self) -> Iterator[DerivationTree]:
        while True:
            tree = self.fuzzer.fuzz_tree()

            LOGGER.debug("Trying to repair tree %s", tree)

            maybe_repaired = self.repair_tree(
                self.instantiate_top_constant(tree),
                tree,
            )

            if is_successful(maybe_repaired):
                yield maybe_repaired.unwrap()

    def instantiate_top_constant(self, tree: DerivationTree) -> Formula:
        return self.top_constant.map(
            lambda c: self.constraint.substitute_expressions({c: tree})
        ).value_or(self.constraint)

    def repair_tree(
        self,
        constraint: Formula,
        tree: DerivationTree,
    ) -> Maybe[DerivationTree]:
        LOGGER.debug("Repairing tree '%s' with constraint '%s'", tree, constraint)

        # 1. Instantiate all quantifiers.
        instantiated = self.instantiate_quantifiers(constraint)

        # 2. Evaluate all structural predicates.
        no_structural_predicates = evaluate_structural_predicates(instantiated, tree)

        # 3. Replace all valid SMT expressions with `true` (considering the negation scope).
        no_true_semantic_formulas = convert_to_dnf(
            convert_to_nnf(
                self.eliminate_true_semantic_formulas(no_structural_predicates, tree)
            ),
            deep=False,
        )

        # 4a. If the formula is a disjunction, recursively try to satisfy each disjunct.
        #     Return the first successfully repaired tree, or Nothing.
        if isinstance(no_true_semantic_formulas, DisjunctiveFormula):
            return flow(
                no_true_semantic_formulas,
                split_disjunction,
                partial(
                    map,
                    lambda disjunct: self.repair_tree(
                        disjunct,
                        tree,
                    ),
                ),
                lambda maybe_repaired_trees: next(
                    (
                        maybe_repaired_tree
                        for maybe_repaired_tree in maybe_repaired_trees
                        if is_successful(maybe_repaired_tree)
                    ),
                    Nothing,
                ),
            )

        conjuncts = split_conjunction(no_true_semantic_formulas)

        # 4b. If the formula is an existentially quantified formula or a conjunction containing
        #     such a formula, recursively try to satisfy those quantified formulas for different
        #     insertions. Return the first successfully repaired tree, or Nothing.
        maybe_first_existential_formula_and_index = next(
            (
                Some((idx, conjunct))
                for idx, conjunct in enumerate(conjuncts)
                if isinstance(conjunct, ExistsFormula)
            ),
            Nothing,
        )

        if is_successful(maybe_first_existential_formula_and_index):
            (
                idx,
                existential_formula,
            ) = maybe_first_existential_formula_and_index.unwrap()

            for (
                instantiated_formula,
                tree_substitutions,
            ) in self.eliminate_existential_formula(existential_formula, tree):
                new_constraint = (
                    conjunction(
                        *conjuncts[:idx],
                        *conjuncts[idx + 1 :],
                    ).substitute_expressions(tree_substitutions)
                    & instantiated_formula
                )

                repaired_tree = self.repair_tree(
                    new_constraint,
                    tree.substitute(tree_substitutions),
                )

                if is_successful(repaired_tree):
                    return repaired_tree

            return Nothing

        # 4c. If the formula is a single semantic formula or a conjunction of semantic formulas,
        #     repair all semantic formulas by making all constrained tree elements abstract and
        #     asking for a solution. If a solution exists, return the repaired tree. Otherwise,
        #     return Nothing.
        assert all(
            isinstance(conjunct, SMTFormula) or isinstance(conjunct, ForallFormula)
            for conjunct in conjuncts
        )

        smt_conjuncts = tuple(
            conjunct for conjunct in conjuncts if isinstance(conjunct, SMTFormula)
        )

        if not smt_conjuncts:
            return Some(tree)

        participating_paths = {
            tree.find_node(arg)
            for conjunct in smt_conjuncts
            for arg in conjunct.tree_arguments()
        }

        pruning_substitutions = {
            tree.get_subtree(path): DerivationTree(
                tree.get_subtree(path).value, None, id=tree.id
            )
            for path in participating_paths
            if is_nonterminal(tree.get_subtree(path).value)
            and not tree.get_subtree(path).children is None
        }

        # TODO: Inline `eliminate_all_semantic_formulas` or make it a library
        #       function; the repair solver should not depend on the original solver.
        solver = ISLaSolver(
            self.grammar,
            conjunction(*smt_conjuncts).substitute_expressions(pruning_substitutions),
            initial_tree=Some(tree.substitute(pruning_substitutions)),
            max_number_smt_instantiations=1,
            max_number_free_instantiations=1,
        )

        return (
            solver.eliminate_all_semantic_formulas(solver.queue[0][1]).bind(
                lambda states: Some(states[0].tree) if states else Nothing
            )
            # .bind(
            #     lambda tree: (
            #         finished_tree := next(finish_unconstrained_tree(tree)),
            #         repair_tree(
            #             conjunction(*[c for c in conjuncts if c not in smt_conjuncts]),
            #             finished_tree,
            #             grammar,
            #             max_tries_existential_insertion,
            #             Some(canonical_grammar),
            #             Some(graph),
            #         ),
            #     )[-1]
            # )
            .bind(
                lambda tree: next(
                    (
                        Some(closed_tree)
                        for closed_tree in itertools.islice(
                            self.finish_unconstrained_tree(tree), 50
                        )
                        if evaluate(
                            conjunction(
                                *[c for c in conjuncts if not isinstance(c, SMTFormula)]
                            ).substitute_expressions(
                                {
                                    tree.get_subtree(path): subtree
                                    for path, subtree in closed_tree.paths()
                                }
                            ),
                            closed_tree,
                            self.grammar,
                        ).is_true()
                    ),
                    Nothing,
                )
            )
        )

    def instantiate_quantifiers(
        self,
        formula: Formula,
        ignore: FrozenSet[Formula] = frozenset(),
    ) -> Formula:
        # We disable the automatic evaluation and substitution of SMT expressions
        # because we want to use the # SMT expressions as-is in the formula (to
        # repair the invalid ones).
        formula = set_auto_subst_and_eval(formula, False)

        top_level_qfd_formulas = extract_top_level_quantified_formulas(
            formula
        ).difference(ignore)

        if not top_level_qfd_formulas:
            return set_auto_subst_and_eval(formula, True)

        for qfd_formula in top_level_qfd_formulas:
            matches = tuple(
                frozendict({var: tree for var, (_, tree) in match.items()})
                for match in matches_for_quantified_formula(
                    qfd_formula, self.grammar, in_tree=qfd_formula.in_variable
                )
                if not qfd_formula.is_already_matched(
                    match[qfd_formula.bound_variable][1]
                )
            )

            qfd_formula = qfd_formula.add_already_matched(
                [match[qfd_formula.bound_variable] for match in matches]
            )
            ignore = ignore | {qfd_formula}

            if isinstance(qfd_formula, ForallFormula):
                instantiations = conjunction(
                    *map(qfd_formula.inner_formula.substitute_expressions, matches),
                )

                formula = (
                    replace_formula(formula, qfd_formula, instantiations) & qfd_formula
                )
            elif isinstance(qfd_formula, ExistsFormula):
                instantiations = disjunction(
                    *map(qfd_formula.inner_formula.substitute_expressions, matches),
                )

                formula = replace_formula(
                    formula,
                    qfd_formula,
                    instantiations | qfd_formula,
                )

        return self.instantiate_quantifiers(formula, ignore)

    def finish_unconstrained_tree(
        self,
        tree: DerivationTree,
    ) -> Iterator[DerivationTree]:
        while True:
            result = tree
            for path, leaf in tree.open_leaves():
                leaf_inst = self.fuzzer.expand_tree(DerivationTree(leaf.value, None))
                result = result.replace_path(path, leaf_inst)

            yield result

    def eliminate_true_semantic_formulas(
        self,
        constraint: Formula,
        context_tree: DerivationTree,
    ) -> Formula:
        for semantic_formula in FilterVisitor(
            lambda f: (
                isinstance(f, SMTFormula)
                and not f.free_variables()
                and evaluate(f, context_tree, self.grammar).is_true()
            )
        ).collect(constraint):
            constraint = replace_formula(constraint, semantic_formula, true())

        return constraint

    def eliminate_existential_formula(
        self,
        existential_formula: ExistsFormula,
        context_tree: DerivationTree,
    ) -> Iterator[Tuple[Formula, Mapping[DerivationTree, DerivationTree]]]:
        inserted_trees_and_bind_paths: Tuple[
            Tuple[DerivationTree, Dict[BoundVariable, Path]], ...
        ] = tuple(
            Maybe.from_optional(existential_formula.bind_expression)
            .map(
                lambda bind_expr: bind_expr.to_tree_prefix(
                    existential_formula.bound_variable.n_type, self.grammar
                )
            )
            .value_or(
                [(DerivationTree(existential_formula.bound_variable.n_type, None), {})]
            )
        )

        inserted_tree: DerivationTree
        bind_expr_paths: Dict[BoundVariable, Path]
        for inserted_tree, bind_expr_paths in inserted_trees_and_bind_paths:
            insertion_results = insert_tree(
                self.canonical_grammar,
                inserted_tree,
                existential_formula.in_variable,
                graph=self.graph,
                max_num_solutions=self.max_tries_existential_insertion,  # TODO: Convert to stream!
            )

            for tree_after_insertion in insertion_results:
                yield from self.process_insertion_result(
                    bind_expr_paths,
                    context_tree,
                    existential_formula,
                    inserted_tree,
                    tree_after_insertion,
                )

    def process_insertion_result(
        self,
        bind_expr_paths: Dict[BoundVariable, Path],
        context_tree: DerivationTree,
        existential_formula: ExistsFormula,
        inserted_tree: DerivationTree,
        tree_after_insertion: DerivationTree,
    ):
        replaced_path = context_tree.find_node(existential_formula.in_variable)
        resulting_tree = context_tree.replace_path(replaced_path, tree_after_insertion)

        tree_substitutions = cast(
            frozendict[DerivationTree, DerivationTree], frozendict()
        )

        for idx in range(len(replaced_path) + 1):
            original_path = replaced_path[: idx - 1]
            original_tree = context_tree.get_subtree(original_path)

            if not resulting_tree.is_valid_path(original_path):
                continue

            if original_tree.value != resulting_tree.get_subtree(original_path).value:
                continue

            if resulting_tree.get_subtree(original_path) == original_tree:
                continue

            tree_substitutions = tree_substitutions.set(
                original_tree, resulting_tree.get_subtree(original_path)
            )

        assert tree_after_insertion.find_node(inserted_tree) is not None

        variable_substitutions = frozendict(
            {existential_formula.bound_variable: inserted_tree}
            | (
                {
                    var: inserted_tree.get_subtree(path)
                    for var, path in bind_expr_paths.items()
                    if var in existential_formula.bind_expression.bound_variables()
                }
                if bind_expr_paths
                else {}
            )
        )

        instantiated_formula = existential_formula.inner_formula.substitute_expressions(
            variable_substitutions
        ).substitute_expressions(tree_substitutions)

        yield instantiated_formula, tree_substitutions


# logging.basicConfig(level=logging.DEBUG)
# print(repair_tree(formula, inp_tree, grammar))

# iterator = solve(def_use_constraint, grammar)
# for _ in range(100):
#     print(next(iterator))

solver = RepairSolver(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES, XML_NAMESPACE_CONSTRAINT)
for _ in range(100):
    print(solver.solve())
