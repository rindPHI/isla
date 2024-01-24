import itertools
import logging
import random
import sys
from functools import reduce, lru_cache
from typing import (
    FrozenSet,
    Tuple,
    cast,
    Dict,
    Iterator,
    Mapping,
    Optional,
    Sequence,
    List,
    Set,
    Iterable,
    Callable,
)

import grammar_graph.gg as gg
import z3
from frozendict import frozendict
from grammar_to_regex.cfg2regex import RegexConverter
from grammar_to_regex.regex import regex_to_z3
from orderedset import FrozenOrderedSet
from returns.converters import result_to_maybe
from returns.curry import partial
from returns.functions import tap
from returns.maybe import Maybe, Nothing, Some
from returns.pipeline import flow
from returns.pipeline import is_successful
from returns.pointfree import map_
from returns.result import safe
from typeguard import typechecked

from isla.derivation_tree import DerivationTree
from isla.evaluator import matches_for_quantified_formula, evaluate
from isla.fuzzer import GrammarCoverageFuzzer, GrammarFuzzer
from isla.helpers import deep_str, depth_indent, star, lazystr
from isla.helpers import (
    frozen_canonical,
    is_nonterminal,
    grammar_to_frozen,
    lazyjoin,
    cluster_by_common_elements,
    get_elem_by_equivalence,
    merge_dict_of_sets,
    split_str_with_nonterminals,
    get_expansions,
    compute_nullable_nonterminals,
    delete_unreachable,
    grammar_to_unfrozen,
)
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
    set_smt_auto_subst,
    FormulaVisitor,
    fresh_constant,
    false,
    parse_bnf,
    validate_structural_predicate_arguments,
)
from isla.parser import EarleyParser
from isla.tree_insertion import insert_tree
from isla.type_defs import FrozenGrammar, Path, Grammar, FrozenCanonicalGrammar
from isla.z3_helpers import (
    z3_subst,
    visit_z3_expr,
    numeric_intervals_from_regex,
    z3_or,
    z3_solve,
    parent_relationships_in_z3_expr,
    smt_string_val_to_string,
    is_z3_var,
)

LOGGER = logging.getLogger(__name__)

ExtractModelValueFallbackType = Callable[
    [
        Variable,
        z3.ModelRef,
        Mapping[Variable, z3.ExprRef],
        Set[Variable],
        Set[Variable],
    ],
    Maybe[DerivationTree],
]


@typechecked
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


@typechecked
def set_auto_subst_and_eval(formula: Formula, value: bool) -> Formula:
    set_smt_auto_eval(formula, value)
    set_smt_auto_subst(formula, value)
    return formula


@typechecked
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
    @typechecked
    def __init__(
        self,
        grammar: FrozenGrammar | Grammar | str,
        maybe_constraint: Optional[Formula | str] = None,
        structural_predicates=frozenset(STANDARD_STRUCTURAL_PREDICATES),
        max_tries_existential_insertion: int = 4,
    ):
        # TODO: Make configurable.
        self.enable_optimized_z3_queries: bool = True
        self.max_tries_existential_insertion: int = max_tries_existential_insertion
        self.grammar_unwinding_threshold: int = 4

        self.grammar = grammar_to_frozen(
            parse_bnf(grammar) if isinstance(grammar, str) else grammar
        )
        self.canonical_grammar = frozen_canonical(self.grammar)
        self.graph = gg.GrammarGraph.from_grammar(self.grammar)
        self.solve_iterator = self.make_solve_iterator()
        self.fuzzer = GrammarCoverageFuzzer(self.grammar)

        self.constraint = (
            Maybe.from_optional(maybe_constraint)
            .map(
                lambda c: parse_isla(c, self.grammar, structural_predicates)
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

    @safe
    @typechecked
    def parse(
        self,
        inp: str,
        nonterminal: str = "<start>",
        silent: bool = False,
    ) -> DerivationTree:
        """
        Parses the given input `inp`. Raises a `SyntaxError` if the input does not
        satisfy the grammar, and returns the parsed `DerivationTree` otherwise.

        :param inp: The input to parse.
        :param nonterminal: The nonterminal to start parsing with, if a string
          corresponding to a sub-grammar shall be parsed. We don't check semantic
          correctness in that case.
        :param silent: If True, no error is sent to the log stream in case of a
            failed parse.
        :return: A parsed `DerivationTree`.
        """

        grammar = self.grammar
        if nonterminal != "<start>":
            grammar = grammar.set("<start>", (nonterminal,))
            grammar = grammar_to_frozen(
                delete_unreachable(grammar)
            )  # TODO: Directly frozen

        parser = EarleyParser(grammar)
        try:
            parse_tree = next(parser.parse(inp))
            if nonterminal != "<start>":
                parse_tree = parse_tree[1][0]
            tree = DerivationTree.from_parse_tree(parse_tree)
        except SyntaxError as err:
            if not silent:
                LOGGER.error(f'Error parsing "{inp}" starting with "{nonterminal}"')
            raise err

        return tree

    @typechecked
    def solve(self) -> DerivationTree:
        return next(self.solve_iterator)

    @typechecked
    def make_solve_iterator(self) -> Iterator[DerivationTree]:
        while True:
            tree = self.fuzzer.fuzz_tree()

            # TODO test code
            # tree = self.parse('<b:a x:b="XXX"></c:x>').unwrap()

            # assert tree.structurally_equal(tree_)

            maybe_repaired = self.repair_tree(
                self.instantiate_top_constant(tree),
                tree,
            )

            if is_successful(maybe_repaired):
                yield maybe_repaired.unwrap()

    @typechecked
    def instantiate_top_constant(self, tree: DerivationTree) -> Formula:
        return self.top_constant.map(
            lambda c: self.constraint.substitute_expressions({c: tree})
        ).value_or(self.constraint)

    @typechecked
    def repair_tree(
        self,
        constraint: Formula | Iterable[Formula],
        tree: DerivationTree,
    ) -> Maybe[DerivationTree]:
        if not isinstance(constraint, Formula):
            constraint = conjunction(*constraint)

        LOGGER.debug(
            "%sRepairing tree '%s' with constraint '%s'",
            depth_indent(),
            tree,
            constraint,
        )
        constraint = set_auto_subst_and_eval(constraint, False)

        # 1. Instantiate all quantifiers.
        instantiated = self.instantiate_quantifiers(constraint)
        assert auto_subst_and_eval_is_false(instantiated)

        # 2. Evaluate all structural predicates.
        no_structural_predicates = evaluate_structural_predicates(instantiated, tree)
        if no_structural_predicates == false():
            # This can happen for unsatisfied structural predicates in a conjunction;
            # backtrack or fail.
            return Nothing

        # 3. Replace all valid SMT expressions with `true` (considering the
        #    negation scope).
        no_true_semantic_formulas = convert_to_dnf(
            self.eliminate_true_semantic_formulas(
                convert_to_nnf(no_structural_predicates), tree
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
                map_(tap(lambda t: isinstance(t, DerivationTree))),
            )

        conjuncts = tuple(split_conjunction(no_true_semantic_formulas))

        if not any(isinstance(c, ExistsFormula) for c in conjuncts):
            # 4c. If the formula is a single semantic formula or a conjunction of
            #     semantic formulas, repair all semantic formulas by making all
            #     constrained tree elements abstract and asking for a solution.
            #     If a solution exists, return the repaired tree. Otherwise,
            #     return Nothing.
            assert all(
                isinstance(conjunct, SMTFormula) or isinstance(conjunct, ForallFormula)
                for conjunct in conjuncts
            )

            smt_conjuncts = tuple(
                conjunct for conjunct in conjuncts if isinstance(conjunct, SMTFormula)
            )

            if not smt_conjuncts:
                # No SMT formulas => We can finish the tree by grammar fuzzing.
                # However, we must evaluate whether the such closed trees satisfy
                # the constraints.
                return self.try_to_finish(tree, conjunction(*conjuncts))

            pruning_substitutions = compute_pruning_substitutions(smt_conjuncts, tree)
            pruned_smt_conjuncts = tuple(
                conjunct.substitute_expressions(pruning_substitutions)
                for conjunct in smt_conjuncts
            )
            pruned_tree = tree.substitute(pruning_substitutions)

            def apply_smt_substitutions(
                substs: Mapping[DerivationTree, DerivationTree]
            ) -> Maybe[DerivationTree]:
                non_smt_formula = conjunction(
                    *(c for c in conjuncts if not isinstance(c, SMTFormula))
                )

                if substs:
                    return self.repair_tree(
                        non_smt_formula.substitute_expressions(substs),
                        tree.substitute(substs),
                    )

                # No substitutions => We can finish the tree by grammar fuzzing.
                # However, we must evaluate whether the such closed trees satisfy
                # the constraints.
                return self.try_to_finish(tree, non_smt_formula)

            return (
                self.eliminate_all_semantic_formulas(pruned_smt_conjuncts, pruned_tree)
                .map(
                    lambda s: (
                        LOGGER.debug(
                            "SMT solution found: %s", lazystr(lambda: deep_str(s))
                        ),
                        s,
                    )[-1]
                )
                .lash(lambda _: (LOGGER.debug("No SMT solution found"), Nothing)[-1])
                .bind(apply_smt_substitutions)
                .map(tap(lambda t: DerivationTree.__instancecheck__))
            )

        return flow(
            self.eliminate_first_existential_formula(conjuncts, tree),
            partial(map, star(self.repair_tree)),
            partial(filter, is_successful),
            lambda maybe_repaired_trees: next(maybe_repaired_trees, Nothing),
        )

    def eliminate_first_existential_formula(
        self, conjuncts: Tuple[Formula, ...], tree: DerivationTree
    ) -> Iterator[Tuple[Tuple[Formula, ...], DerivationTree]]:
        r"""
        TODO

        >>> import string
        >>> grammar = frozendict({
        ...     "<start>": ("<stmt>",),
        ...     "<stmt>": ("<assgn> ; <stmt>", "<assgn>"),
        ...     "<assgn>": ("<var> := <rhs>",),
        ...     "<rhs>": ("<var>", "<digit>"),
        ...     "<var>": tuple(string.ascii_lowercase),
        ...     "<digit>": tuple(string.digits)
        ... })

        >>> solver = RepairSolver(grammar, max_tries_existential_insertion=3)
        >>> tree = solver.parse("a := 1 ; b := 2 ; c := 3").unwrap()

        >>> constraint_1 = parse_isla('exists <var> in start: <var> = "x"', grammar)
        >>> constraint_1 = constraint_1.substitute_expressions({constraint_1.in_variable: tree})

        >>> constraint_2 = parse_isla('exists <digit> in start: <digit> = "1"', grammar)
        >>> constraint_2 = constraint_2.substitute_expressions({constraint_2.in_variable: tree})

        >>> print(
        ...     "\n".join(
        ...         [
        ...             f"{new_conjuncts} |- {new_tree}"
        ...             for new_conjuncts, new_tree, substs in itertools.islice(
        ...                 solver.eliminate_first_existential_formula(
        ...                     (constraint_1, constraint_2), tree
        ...                 ),
        ...                 10,
        ...             )
        ...         ]
        ...     )
        ... )
        (var == "x", digit == "1") |- <var> := <rhs> ; <var> := <digit> ; a := 1 ; b := 2 ; c := 3
        (var == "x", digit == "1") |- <var> := <var> ; <var> := <digit> ; a := 1 ; b := 2 ; c := 3
        (var == "x", digit == "1") |- <var> := <digit> ; <var> := <rhs> ; a := 1 ; b := 2 ; c := 3
        (var == "x", digit == "1") |- <var> := <rhs> ; a := 1 ; <var> := <digit> ; b := 2 ; c := 3
        (var == "x", digit == "1") |- <var> := <var> ; a := 1 ; <var> := <digit> ; b := 2 ; c := 3
        (var == "x", digit == "1") |- a := 1 ; <var> := <rhs> ; <var> := <digit> ; b := 2 ; c := 3
        (var == "x", digit == "1") |- <var> := <rhs> ; a := 1 ; b := 2 ; <var> := <digit> ; c := 3
        (var == "x", digit == "1") |- <var> := <var> ; a := 1 ; b := 2 ; <var> := <digit> ; c := 3
        (var == "x", digit == "1") |- a := 1 ; <var> := <rhs> ; b := 2 ; <var> := <digit> ; c := 3

        :param conjuncts:
        :param tree:
        :return:
        """

        validate_structural_predicate_arguments(conjuncts, tree)

        idx, first_existential_formula = Maybe.from_optional(
            next(
                filter(
                    star(lambda idx, f: isinstance(f, ExistsFormula)),
                    enumerate(conjuncts),
                ),
                None,
            )
        ).value_or((-1, None))

        if not first_existential_formula:
            yield conjuncts, tree, frozendict({})
            return

        other_conjuncts = conjuncts[:idx] + conjuncts[idx + 1 :]

        assert (
            not first_existential_formula.in_variable.value == "<start>"
            or first_existential_formula.in_variable == tree
        )

        for (
            instantiated_formula,
            tree_substitutions,
        ) in self.eliminate_existential_formula(
            first_existential_formula,
            tree,
        ):
            updated_conjuncts = tuple(
                c.substitute_expressions(tree_substitutions) for c in other_conjuncts
            )
            updated_tree = tree.substitute(tree_substitutions)

            validate_structural_predicate_arguments(instantiated_formula, updated_tree)
            validate_structural_predicate_arguments(updated_conjuncts, updated_tree)

            yield (instantiated_formula,) + updated_conjuncts, updated_tree

    def try_to_finish(
        self, tree: DerivationTree, validity_constraint: Formula, max_tries: int = 50
    ) -> Maybe[DerivationTree]:
        """
        TODO: Document & add test cases.

        :param tree:
        :param validity_constraint:
        :param max_tries:
        :return:
        """

        return next(
            (
                Some(closed_tree)
                for closed_tree, closing_substs in itertools.islice(
                    self.finish_unconstrained_tree(tree), max_tries
                )
                if evaluate(
                    validity_constraint.substitute_expressions(closing_substs),
                    closed_tree,
                    self.grammar,
                ).is_true()
            ),
            Nothing,
        )

    @typechecked
    def instantiate_quantifiers(
        self,
        formula: Formula,
        ignore: FrozenSet[Formula] = frozenset(),
    ) -> Formula:
        r"""
        TODO: Document.

        >>> grammar = {
        ...     "<start>": ["<digits>"],
        ...     "<digits>": ["<digit><digits>", "<digit>"],
        ...     "<digit>": ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"],
        ... }
        >>> constraint = '''
        ...     forall <digit> digit_1 in start: (
        ...         digit_1 = "0" or
        ...             exists <digit> digit_2 in start: (
        ...                 before(digit_2, digit_1) and digit_2 = "0"
        ...             )
        ...     )'''
        >>> solver = RepairSolver(grammar, constraint)
        >>> tree = solver.parse("012").unwrap()
        >>> print(
        ...     "\n".join(
        ...         map(
        ...             str,
        ...             split_conjunction(
        ...                 solver.instantiate_quantifiers(
        ...                     solver.instantiate_top_constant(tree)
        ...                 )
        ...             ),
        ...         )
        ...     )
        ... )
        ((digit_1 == "0", {'digit_1': '0'}) ∨ ((((before(0, 0) ∧ (digit_2 == "0", {'digit_2': '0'})) ∨ (before(1, 0) ∧ (digit_2 == "0", {'digit_2': '1'}))) ∨ (before(2, 0) ∧ (digit_2 == "0", {'digit_2': '2'}))) ∨ ∃ digit_2 ∈ 012: ((before(digit_2, 0) ∧ digit_2 == "0"))))
        ((digit_1 == "0", {'digit_1': '1'}) ∨ ((((before(0, 1) ∧ (digit_2 == "0", {'digit_2': '0'})) ∨ (before(1, 1) ∧ (digit_2 == "0", {'digit_2': '1'}))) ∨ (before(2, 1) ∧ (digit_2 == "0", {'digit_2': '2'}))) ∨ ∃ digit_2 ∈ 012: ((before(digit_2, 1) ∧ digit_2 == "0"))))
        ((digit_1 == "0", {'digit_1': '2'}) ∨ ((((before(0, 2) ∧ (digit_2 == "0", {'digit_2': '0'})) ∨ (before(1, 2) ∧ (digit_2 == "0", {'digit_2': '1'}))) ∨ (before(2, 2) ∧ (digit_2 == "0", {'digit_2': '2'}))) ∨ ∃ digit_2 ∈ 012: ((before(digit_2, 2) ∧ digit_2 == "0"))))
        ∀ digit_1 ∈ 012: ((digit_1 == "0" ∨ ∃ digit_2 ∈ 012: ((before(digit_2, digit_1) ∧ digit_2 == "0"))))

        :param formula:
        :param ignore:
        :return:
        """

        # We disable the automatic evaluation and substitution of SMT expressions
        # because we want to use the # SMT expressions as-is in the formula (to
        # repair the invalid ones).
        formula = set_auto_subst_and_eval(formula, False)

        top_level_qfd_formulas = extract_top_level_quantified_formulas(
            formula
        ).difference(ignore)

        if not top_level_qfd_formulas:
            return formula

        for qfd_formula in top_level_qfd_formulas:
            matches = tuple(
                frozendict({var: tree for var, (_, tree) in match.items()})
                for match in matches_for_quantified_formula(
                    qfd_formula, self.grammar, in_tree=qfd_formula.in_variable
                )
                # if not qfd_formula.is_already_matched(
                #     match[qfd_formula.bound_variable][1]
                # )
                if hash(
                    (
                        match[qfd_formula.bound_variable][1].id,
                        match[qfd_formula.bound_variable][1].structural_hash(),
                    )
                )
                not in qfd_formula.already_matched
            )

            qfd_formula = add_already_matched(
                qfd_formula, [match[qfd_formula.bound_variable] for match in matches]
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

    @typechecked
    def finish_unconstrained_tree(
        self,
        tree: DerivationTree,
    ) -> Iterator[Tuple[DerivationTree, frozendict[DerivationTree, DerivationTree]]]:
        while True:
            result_tree = tree
            result_substs: frozendict[DerivationTree, DerivationTree] = frozendict({})
            for path, leaf in tree.open_leaves():
                leaf_inst = self.fuzzer.expand_tree(DerivationTree(leaf.value, None))
                result_tree = result_tree.replace_path(path, leaf_inst)
                result_substs = result_substs.set(leaf, leaf_inst)

            yield result_tree, result_substs

    @typechecked
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

    @typechecked
    def eliminate_existential_formula(
        self,
        existential_formula: ExistsFormula,
        context_tree: DerivationTree,
    ) -> Iterator[Tuple[Formula, Mapping[DerivationTree, DerivationTree]]]:
        assert (
            not existential_formula.in_variable.value == "<start>"
            or existential_formula.in_variable == context_tree
        )

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
                existential_formula.in_variable,
                inserted_tree,
                self.graph,
                Some(self.canonical_grammar),
            )

            for insertion_result in insertion_results:
                assert len(insertion_result) == 2
                assert isinstance(insertion_result[0], DerivationTree)
                assert isinstance(insertion_result[1], tuple)
                yield self.process_insertion_result(
                    bind_expr_paths,
                    context_tree,
                    existential_formula,
                    inserted_tree,
                    *insertion_result,
                )
            else:
                LOGGER.debug(
                    "Could not insert tree '%s' (%s) into '%s' (%s)",
                    inserted_tree,
                    inserted_tree.value,
                    existential_formula.in_variable,
                    existential_formula.in_variable.value,
                )

    @typechecked
    def process_insertion_result(
        self,
        bind_expr_paths: Dict[BoundVariable, Path],
        context_tree: DerivationTree,
        existential_formula: ExistsFormula,
        inserted_tree: DerivationTree,
        tree_after_insertion: DerivationTree,
        path_to_inserted_tree: Path,
    ) -> Tuple[Formula, Mapping[DerivationTree, DerivationTree]]:
        # assert {s.id for _, s in context_tree.paths()}.issubset(
        #     {s.id for _, s in tree_after_insertion.paths()}
        # )

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

        # TODO: Check if these assertions make sense. They failed, but I'm noe
        #       sure whether they might be too strict.
        # assert (
        #     tree_after_insertion.get_subtree(path_to_inserted_tree).value
        #     == inserted_tree.value
        # )
        # assert all(
        #     c in tree_after_insertion.get_subtree(path_to_inserted_tree).children
        #     for c in inserted_tree.children
        # )

        # TODO: Is it robust to use the bind_expr_paths in the new tree?
        inserted_tree_in_tree_after_insertion = tree_after_insertion.get_subtree(
            tree_after_insertion.find_node(inserted_tree)
        )

        variable_substitutions = frozendict(
            {existential_formula.bound_variable: inserted_tree_in_tree_after_insertion}
            | (
                {
                    var: inserted_tree_in_tree_after_insertion.get_subtree(path)
                    for var, path in bind_expr_paths.items()
                    if var in existential_formula.bind_expression.bound_variables()
                }
                if bind_expr_paths
                else {}
            )
        )

        # variable_substitutions = frozendict(
        #     {existential_formula.bound_variable: inserted_tree}
        #     | (
        #         {
        #             var: inserted_tree.get_subtree(path)
        #             for var, path in bind_expr_paths.items()
        #             if var in existential_formula.bind_expression.bound_variables()
        #         }
        #         if bind_expr_paths
        #         else {}
        #     )
        # )

        instantiated_formula = existential_formula.inner_formula.substitute_expressions(
            variable_substitutions
        ).substitute_expressions(tree_substitutions)

        return instantiated_formula, tree_substitutions

    # TODO: Polish the functions below, which were copied from ISLaSolver
    @typechecked
    def eliminate_all_semantic_formulas(
        self, smt_formulas: Sequence[SMTFormula], tree: DerivationTree
    ) -> Maybe[Mapping[DerivationTree, DerivationTree]]:
        """
        Eliminates all SMT-LIB formulas that appear in `state`'s constraint as conjunctive elements.
        If, e.g., an SMT-LIB formula occurs as a disjunction, no solution is computed.

        >>> solver = RepairSolver({"<start>": ["<a>"], "<a>": ["a"]})
        >>> solver.eliminate_all_semantic_formulas([true()], DerivationTree("<start>", None))
        <Some: frozendict.frozendict({})>

        >>> solver.eliminate_all_semantic_formulas([false()], DerivationTree("<start>", None))
        <Nothing>

        :param state: The state in which to solve all SMT-LIB formulas.
        :param max_instantiations: The number of solutions the SMT solver should be asked for.
        :return: The discovered solutions.
        """

        if not smt_formulas:
            return Some(tree)

        LOGGER.debug("Eliminating semantic formulas [%s]", lazyjoin(", ", smt_formulas))

        # NOTE: We need to cluster SMT formulas by tree substitutions. If there are two
        # formulas with a variable $var which is instantiated to different trees, we
        # need two separate solutions. If, however, $var is instantiated with the
        # *same* tree, we need one solution to both formulas together.
        smt_formulas = rename_instantiated_variables_in_smt_formulas(smt_formulas)

        # Now, we also cluster formulas by common variables (and instantiated subtrees:
        # One formula might yield an instantiation of a subtree of the instantiation of
        # another formula. They need to appear in the same cluster). The solver can
        # better handle smaller constraints, and those which do not have variables in
        # common can be handled independently.

        @typechecked
        def cluster_keys(smt_formula: SMTFormula):
            return (
                smt_formula.free_variables()
                | smt_formula.instantiated_variables
                | set(
                    [
                        subtree
                        for tree in smt_formula.substitutions.values()
                        for _, subtree in tree.paths()
                    ]
                )
            )

        formula_clusters: Tuple[Tuple[SMTFormula, ...], ...] = tuple(
            map(
                tuple, cluster_by_common_elements(smt_formulas, cluster_keys)
            )  # TODO: Return tuple directly
        )

        assert all(
            not cluster_keys(smt_formula)
            or any(smt_formula in cluster for cluster in formula_clusters)
            for smt_formula in smt_formulas
        )

        formula_clusters = tuple(cluster for cluster in formula_clusters if cluster)
        remaining_clusters = tuple(
            smt_formula for smt_formula in smt_formulas if not cluster_keys(smt_formula)
        )

        if remaining_clusters:
            formula_clusters += (remaining_clusters,)

        # These solutions are all independent, such that we can combine each solution
        # with all others.
        maybe_solution: Maybe[frozendict[DerivationTree, DerivationTree]] = reduce(
            lambda maybe_combined_solution, maybe_cluster_solution: (
                maybe_combined_solution.bind(
                    lambda combined_solution: maybe_cluster_solution.map(
                        lambda cluster_solution: frozendict(
                            combined_solution | cluster_solution
                        )
                    )
                )
            ),
            map(self.solve_quantifier_free_formula, map(tuple, formula_clusters)),
            Some(frozendict()),
        )

        # We also have to instantiate all subtrees of the substituted element.
        return maybe_solution.map(subtree_solutions)

    @typechecked
    def solve_quantifier_free_formula(
        self,
        smt_formulas: Tuple[SMTFormula, ...],
    ) -> Maybe[frozendict[DerivationTree, DerivationTree]]:
        """
        Attempts to solve the given SMT-LIB formulas by calling Z3.

        Note that this function does not unify variables pointing to the same derivation
        trees. E.g., a solution may be returned for the formula `var_1 = "a" and
        var_2 = "b"`, though `var_1` and `var_2` point to the same `<var>` tree as
        defined by their substitutions maps. Unification is performed in
        `eliminate_all_semantic_formulas`.

        :param smt_formulas: The SMT-LIB formulas to solve.
        :return: A (possibly empty) list of solutions.
        """

        # If any SMT formula refers to *sub*trees in the instantiations of other SMT
        # formulas, we have to instantiate those first.
        priority_formulas = smt_formulas_referring_to_subtrees(smt_formulas)

        if priority_formulas:
            smt_formulas = priority_formulas
            assert not smt_formulas_referring_to_subtrees(smt_formulas)

        tree_substitutions = reduce(
            lambda d1, d2: cast(
                frozendict[Variable, DerivationTree], frozendict(d1 | d2)
            ),
            [smt_formula.substitutions for smt_formula in smt_formulas],
            frozendict({}),
        )

        variables_in_smt_formulas = reduce(
            lambda d1, d2: d1 | d2,
            [
                smt_formula.free_variables() | smt_formula.instantiated_variables
                for smt_formula in smt_formulas
            ],
            set(),
        )

        (
            solver_result,
            maybe_model,
        ) = self.solve_smt_formulas_with_language_constraints(
            variables_in_smt_formulas,
            tuple([smt_formula.formula for smt_formula in smt_formulas]),
            tree_substitutions,
        )

        if solver_result != z3.sat:
            return Nothing

        assert maybe_model is not None

        result: Maybe[frozendict[DerivationTree, DerivationTree]] = reduce(
            lambda maybe_solution, constant: maybe_solution.bind(
                lambda solution: maybe_model.map(
                    lambda model: (
                        solution
                        + (
                            (
                                tree_substitutions.get(constant, constant),
                                model[constant],
                            ),
                        )
                    )
                )
            ),
            variables_in_smt_formulas,
            Some(()),
        ).map(frozendict)

        assert result.map(
            lambda r: isinstance(r, frozendict)
            and all(
                isinstance(k, DerivationTree) and isinstance(v, DerivationTree)
                for k, v in r.items()
            )
        ).value_or(False)

        return result

    @typechecked
    def solve_smt_formulas_with_language_constraints(
        self,
        variables: Set[Variable],
        smt_formulas: Tuple[z3.BoolRef, ...],
        tree_substitutions: frozendict[Variable, DerivationTree],
    ) -> Tuple[z3.CheckSatResult, Maybe[frozendict[Variable, DerivationTree]]]:
        """
        TODO Document, test.

        :param variables:
        :param smt_formulas:
        :param tree_substitutions:
        :return:
        """

        # if all(is_valid(z3.simplify(f)).is_true() for f in smt_formulas):
        #     return z3.sat, Some(frozendict())

        length_vars: frozenset[Variable] = frozenset()
        int_vars: frozenset[Variable] = frozenset()
        fresh_var_map: frozendict[Variable, z3.ExprRef] = frozendict({})

        # We disable optimized Z3 queries if the SMT formulas contain "too concrete"
        # substitutions, that is, substitutions with a tree that is not merely an
        # open leaf. Example: we have a constraint `str.len(<chars>) < 10` and a
        # tree `<char><char>`; only the concrete length "2" is possible then.
        optimized_solution_enabled = self.enable_optimized_z3_queries and not any(
            substitution.children for substitution in tree_substitutions.values()
        )

        if optimized_solution_enabled:
            # # We first check whether `smt_formulas` are a system of equations.
            # # If so, we can assume that all participating variables must attain
            # # the same value, since this method is only called with dependent
            # # clusters of variables. We will then find the most specific
            # # nonterminal from the types of the participating variables and choose
            # # a random instantiation.
            if all(
                formula.decl().kind() == z3.Z3_OP_EQ
                and all(is_z3_var(c) for c in formula.children())
                for formula in smt_formulas
            ):
                most_specific_ntype: str = compute_most_specific_type(
                    [
                        tree_substitutions[var].value
                        if var in tree_substitutions
                        else var.n_type
                        for var in variables
                    ],
                    self.graph,
                )[0]

                # TODO: It seems to be a problem if an ID with a namespace is used. Z3
                #       seems to be lazy and generally go for the IDs without prefix,
                #       thus the problem does not surface; but it still exists!
                #       This should be solved, regardless of whether we use optimized
                #       equation solving or not.
                # grammar = delete_unreachable(
                #     self.grammar.set("<id>", ("<id-no-prefix>",)), frozen=True
                # )

                value = GrammarFuzzer(self.grammar).expand_tree(
                    DerivationTree(most_specific_ntype, None)
                )

                equation_solving_result = Some(
                    frozendict(
                        {
                            var: (
                                t := value.ensure_unique_ids(),
                                DerivationTree(
                                    t.value,
                                    t.children,
                                    id=tree_substitutions[var].id,
                                ),
                            )[-1]
                            for var in variables
                        }
                    )
                )

                # return z3.sat, equation_solving_result

                LOGGER.debug(
                    "Equation solving would return %s",
                    equation_solving_result,
                )

                return z3.sat, Some(
                    frozendict(
                        {
                            var: (
                                t := value.ensure_unique_ids(),
                                DerivationTree(
                                    t.value, t.children, id=tree_substitutions[var].id
                                ),
                            )[-1]
                            for var in variables
                        }
                    )
                )

            vars_in_context = infer_variable_contexts(variables, smt_formulas)
            length_vars = vars_in_context["length"]
            int_vars = vars_in_context["int"]
            flexible_vars = vars_in_context["flexible"]

            # Add language constraints for "flexible" variables
            flex_language_constraints: Tuple[
                z3.BoolRef, ...
            ] = self.generate_language_constraints(flexible_vars, tree_substitutions)

            # Create fresh variables for `str.len` and `str.to.int` variables.
            all_variables = set(variables)
            for var in length_vars | int_vars:
                fresh = fresh_constant(
                    all_variables,
                    Constant(var.name, "NOT-NEEDED"),
                )
                fresh_var_map = fresh_var_map.set(var, z3.Int(fresh.name))

            # In `smt_formulas`, we replace all `length(...)` terms for "length
            # variables" with the corresponding fresh variable.
            replacement_map: Dict[z3.ExprRef, z3.ExprRef] = {
                expr: fresh_var_map[
                    get_elem_by_equivalence(
                        expr.children()[0],
                        length_vars | int_vars,
                        lambda e1, e2: e1 == e2.to_smt(),
                    )
                ]
                for formula in smt_formulas
                for expr in visit_z3_expr(formula)
                if expr.decl().kind() in {z3.Z3_OP_SEQ_LENGTH, z3.Z3_OP_STR_TO_INT}
                and expr.children()[0]
                in {var.to_smt() for var in length_vars | int_vars}
            }

            # Perform substitution, add formulas
            smt_formulas_no_seq_and_strtoint: Tuple[z3.BoolRef, ...] = tuple(
                cast(z3.BoolRef, z3_subst(formula, replacement_map))
                for formula in smt_formulas
            )

            # Lengths must be positive
            length_constraints: Tuple[z3.BoolRef, ...] = tuple(
                cast(
                    z3.BoolRef,
                    replacement_map[z3.Length(length_var.to_smt())] >= z3.IntVal(0),
                )
                for length_var in length_vars
            )

            # Add custom intervals for int variables
            interval_constraints: Tuple[z3.BoolRef, ...] = ()
            for int_var in int_vars:
                regex = self.extract_regular_expression(int_var.n_type)
                maybe_intervals = numeric_intervals_from_regex(regex)
                repl_var = replacement_map[z3.StrToInt(int_var.to_smt())]
                interval_constraints += maybe_intervals.map(
                    lambda intervals: (
                        z3_or(
                            [
                                z3.And(
                                    repl_var >= z3.IntVal(interval[0])
                                    if interval[0] > -sys.maxsize
                                    else z3.BoolVal(True),
                                    repl_var <= z3.IntVal(interval[1])
                                    if interval[1] < sys.maxsize
                                    else z3.BoolVal(True),
                                )
                                for interval in intervals
                            ]
                        ),
                    )
                ).value_or(())

            sat_result, maybe_model = z3_solve(
                flex_language_constraints
                + length_constraints
                + interval_constraints
                + smt_formulas_no_seq_and_strtoint
            )
        else:
            sat_result, maybe_model = z3_solve(
                self.generate_language_constraints(variables, tree_substitutions)
                + smt_formulas
            )

        if sat_result != z3.sat:
            return sat_result, Nothing

        if optimized_solution_enabled and all(
            formula.decl().kind() == z3.Z3_OP_EQ
            and all(is_z3_var(c) for c in formula.children())
            for formula in smt_formulas
        ):
            LOGGER.debug(
                "Solver actually returned %s",
                self.extract_model_values(
                    variables, maybe_model, fresh_var_map, length_vars, int_vars
                ),
            )

        assert maybe_model is not None
        return sat_result, self.extract_model_values(
            variables, maybe_model, fresh_var_map, length_vars, int_vars
        )

    def extract_model_values(
        self, variables, maybe_model, fresh_var_map, length_vars, int_vars
    ):
        """
        TODO: Test, Document.

        :param variables:
        :param maybe_model:
        :param fresh_var_map:
        :param length_vars:
        :param int_vars:
        :return:
        """
        model_values: Maybe[frozendict[Variable, DerivationTree]] = reduce(
            lambda maybe_solution, var: maybe_solution.bind(
                lambda solution: self.extract_model_value(
                    var, maybe_model, fresh_var_map, length_vars, int_vars
                ).map(lambda model_value: solution + ((var, model_value),))
            ),
            variables,
            Some(()),
        ).map(frozendict)

        assert model_values.map(
            lambda r: isinstance(r, frozendict)
            and all(
                isinstance(k, Variable) and isinstance(v, DerivationTree)
                for k, v in r.items()
            )
        ).value_or(False)

        return model_values

    @typechecked
    def generate_language_constraints(
        self,
        variables_in_smt_formulas: Iterable[Variable],
        tree_substitutions: Mapping[Variable, DerivationTree],
    ) -> Tuple[z3.BoolRef, ...]:
        formulas: Tuple[z3.BoolRef, ...] = ()
        for constant in variables_in_smt_formulas:
            if constant in tree_substitutions:
                # We have a more concrete shape of the desired instantiation available
                regexes = [
                    self.extract_regular_expression(t)
                    if is_nonterminal(t)
                    else z3.Re(t)
                    for t in split_str_with_nonterminals(
                        str(tree_substitutions[constant])
                    )
                ]
                assert regexes
                regex = z3.Concat(*regexes) if len(regexes) > 1 else regexes[0]
            else:
                regex = self.extract_regular_expression(constant.n_type)

            formulas += (z3.InRe(z3.String(constant.name), regex),)

        return formulas

    @lru_cache(maxsize=128)
    @typechecked
    def extract_regular_expression(self, nonterminal: str) -> z3.ReRef:
        # For definitions like `<a> ::= <b>`, we only compute the regular expression
        # for `<b>`. That way, we might save some calls if `<b>` is used multiple times
        # (e.g., as in `<byte>`).
        canonical_expansions = self.canonical_grammar[nonterminal]

        if (
            len(canonical_expansions) == 1
            and len(canonical_expansions[0]) == 1
            and is_nonterminal(canonical_expansions[0][0])
        ):
            sub_nonterminal = canonical_expansions[0][0]
            assert (
                nonterminal != sub_nonterminal
            ), f"Expansion {nonterminal} => {sub_nonterminal}: Infinite recursion!"
            return self.extract_regular_expression(sub_nonterminal)

        # Similarly, for definitions like `<a> ::= <b> " x " <c>`, where `<b>` and `<c>`
        # don't reach `<a>`, we only compute the regular expressions for `<b>` and `<c>`
        # and return a concatenation. This also saves us expensive conversions (e.g.,
        # for `<seq> ::= <byte> <byte>`).
        if (
            len(canonical_expansions) == 1
            and any(is_nonterminal(elem) for elem in canonical_expansions[0])
            and all(
                not is_nonterminal(elem)
                or elem != nonterminal
                and not self.graph.reachable(elem, nonterminal)
                for elem in canonical_expansions[0]
            )
        ):
            result_elements: List[z3.ReRef] = [
                z3.Re(elem)
                if not is_nonterminal(elem)
                else self.extract_regular_expression(elem)
                for elem in canonical_expansions[0]
            ]
            return z3.Concat(*result_elements)

        regex_conv = RegexConverter(
            grammar_to_unfrozen(
                self.grammar
            ),  # TODO: Make RegexConverter work with immutable grammars
            compress_unions=True,
            max_num_expansions=self.grammar_unwinding_threshold,
        )

        regex = regex_conv.to_regex(nonterminal, convert_to_z3=False)

        LOGGER.debug(
            f"Computed regular expression for nonterminal {nonterminal}:\n{regex}"
        )

        return regex_to_z3(regex)

    @typechecked
    def extract_model_value(
        self,
        var: Variable,
        model: z3.ModelRef,
        fresh_var_map: Mapping[Variable, z3.ExprRef],
        length_vars: Set[Variable],
        int_vars: Set[Variable],
    ) -> Maybe[DerivationTree]:
        r"""
        Extracts a value for :code:`var` from :code:`model`. Considers the following
        special cases:

        Numeric Variables
            Returns a closed derivation tree of one node with a string representation
            of the numeric solution.

        "Length" Variables
            Returns a string of the length corresponding to the model and
            :code:`fresh_var_map`, see also
            :meth:`~isla.repair_solver.safe_create_fixed_length_tree()`.

        "Int" Variables
            Tries to parse the numeric solution from the model (obtained via
            :code:`fresh_var_map`) into the type of :code:`var` and returns the
            corresponding derivation tree.

        >>> grammar = {
        ...     "<start>": ["<A>"],
        ...     "<A>": ["<X><Y>"],
        ...     "<X>": ["x", "x<X>"],
        ...     "<Y>": ["<digit>", "<digit><Y>"],
        ...     "<digit>": ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"],
        ... }
        >>> solver = RepairSolver(grammar)

        **"Length" Variables:**

        >>> from isla.z3_helpers import z3_eq
        >>> x = Variable("x", "<X>")
        >>> x_0 = z3.Int("x_0")
        >>> f = z3_eq(x_0, z3.IntVal(3))
        >>> z3_solver = z3.Solver()
        >>> z3_solver.add(f)
        >>> z3_solver.check()
        sat
        >>> model = z3_solver.model()
        >>> result = solver.extract_model_value(x, model, {x: x_0}, {x}, set()).unwrap()
        >>> result.value
        '<X>'
        >>> str(result)
        'xxx'

        **"Int" Variables:**

        >>> y = Variable("y", "<Y>")
        >>> y_0 = z3.Int("y_0")
        >>> f = z3_eq(y_0, z3.IntVal(5))
        >>> z3_solver = z3.Solver()
        >>> z3_solver.add(f)
        >>> z3_solver.check()
        sat
        >>> model = z3_solver.model()
        >>> DerivationTree.next_id = 1
        >>> solver.extract_model_value(y, model, {y: y_0}, set(), {y}).unwrap()
        DerivationTree('<Y>', (DerivationTree('<digit>', (DerivationTree('5', (), id=1),), id=2),), id=3)

        **"Flexible" Variables:**

        >>> f = z3_eq(x.to_smt(), z3.StringVal("xxxxx"))
        >>> z3_solver = z3.Solver()
        >>> z3_solver.add(f)
        >>> z3_solver.check()
        sat
        >>> model = z3_solver.model()
        >>> result = solver.extract_model_value(x, model, {}, set(), set()).unwrap()
        >>> result.value
        '<X>'
        >>> str(result)
        'xxxxx'

        **Special Number Formats**

        It may happen that the solver returns, e.g., "1" as a solution for an int
        variable, but the grammar only recognizes "+001". We support this case, i.e.,
        an optional "+" and optional 0 padding; an optional 0 padding for negative
        numbers is also supported.

        >>> grammar = {
        ...     "<start>": ["<int>"],
        ...     "<int>": ["<sign>00<leaddigit><digits>"],
        ...     "<sign>": ["-", "+"],
        ...     "<digits>": ["", "<digit><digits>"],
        ...     "<digit>": list("0123456789"),
        ...     "<leaddigit>": list("123456789"),
        ... }
        >>> solver = RepairSolver(grammar)

        >>> i = Variable("i", "<int>")
        >>> i_0 = z3.Int("i_0")
        >>> f = z3_eq(i_0, z3.IntVal(5))

        >>> z3_solver = z3.Solver()
        >>> z3_solver.add(f)
        >>> z3_solver.check()
        sat

        The following test works when run from the IDE, but unfortunately not when
        started from CI/the `test_doctests.py` script. Thus, we only show it as code
        block (we added a unit test as a replacement)::

            model = z3_solver.model()
            print(solver.extract_model_value(i, model, {i: i_0}, set(), {i}))
            # Prints: +005

        :param var: The variable for which to extract a solution from the model.
        :param model: The model containing the solution.
        :param fresh_var_map: A map from variables to fresh symbols for "length" and
                              "int" variables.
        :param length_vars: The set of "length" variables.
        :param int_vars: The set of "int" variables.
        :return: A :class:`~isla.derivation_tree.DerivationTree` object corresponding
                 to the solution in :code:`model`.
        """

        f_flex_vars = self.extract_model_value_flexible_var
        f_int_vars = partial(self.extract_model_value_int_var, f_flex_vars)
        f_length_vars = partial(self.extract_model_value_length_var, f_int_vars)

        return f_length_vars(var, model, fresh_var_map, length_vars, int_vars)

    @typechecked
    def extract_model_value_length_var(
        self,
        fallback: ExtractModelValueFallbackType,
        var: Variable,
        model: z3.ModelRef,
        fresh_var_map: Mapping[Variable, z3.ExprRef],
        length_vars: Set[Variable],
        int_vars: Set[Variable],
    ) -> Maybe[DerivationTree]:
        """
        Addresses the case of length variables from
        :meth:`~isla.repair_solver.RepairSolver.extract_model_value`.

        :param fallback: The function to call if this function is not responsible.
        :param var: See :meth:`~isla.repair_solver.RepairSolver.extract_model_value`.
        :param model: See :meth:`~isla.repair_solver.RepairSolver.extract_model_value`.
        :param fresh_var_map: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :param length_vars: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :param int_vars: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :return: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        """
        if var not in length_vars:
            return fallback(var, model, fresh_var_map, length_vars, int_vars)

        return create_fixed_length_tree(
            start=var.n_type,
            canonical_grammar=self.canonical_grammar,
            target_length=model[fresh_var_map[var]].as_long(),
        )

    @typechecked
    def extract_model_value_int_var(
        self,
        fallback: ExtractModelValueFallbackType,
        var: Variable,
        model: z3.ModelRef,
        fresh_var_map: Mapping[Variable, z3.ExprRef],
        length_vars: Set[Variable],
        int_vars: Set[Variable],
    ) -> Maybe[DerivationTree]:
        """
        Addresses the case of int variables from
        :meth:`~isla.solver.RepairSolver.extract_model_value`.

        :param fallback: The function to call if this function is not responsible.
        :param var: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :param model: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :param fresh_var_map: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :param length_vars: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :param int_vars: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :return: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        """
        if var not in int_vars:
            return fallback(var, model, fresh_var_map, length_vars, int_vars)

        str_model_value = model[fresh_var_map[var]].as_string()

        try:
            int_model_value = int(str_model_value)
        except ValueError:
            raise RuntimeError(f"Value {str_model_value} for {var} is not a number")

        var_type = var.n_type

        try:
            return result_to_maybe(
                self.parse(
                    str(int_model_value),
                    var_type,
                    silent=True,
                )
            )
        except SyntaxError:
            # This may happen, e.g, with padded values: Only "01" is a valid
            # solution, but not "1". Similarly, a grammar may expect "+1", but
            # "1" is returned by the solver. We support the number format
            # `[+-]0*<digits>`. Whenever the grammar recognizes at least this
            # set for the nonterminal in question, we return a derivation tree.
            # Otherwise, a RuntimeError is raised.

            z3_solver = z3.Solver()
            z3_solver.set("timeout", 300)

            maybe_plus_re = z3.Option(z3.Re("+"))
            zeroes_padding_re = z3.Star(z3.Re("0"))

            # TODO: Ensure symbols are fresh
            maybe_plus_var = z3.String("__plus")
            zeroes_padding_var = z3.String("__padding")

            z3_solver.add(z3.InRe(maybe_plus_var, maybe_plus_re))
            z3_solver.add(z3.InRe(zeroes_padding_var, zeroes_padding_re))

            z3_solver.add(
                z3.InRe(
                    z3.Concat(
                        maybe_plus_var if int_model_value >= 0 else z3.StringVal("-"),
                        zeroes_padding_var,
                        z3.StringVal(
                            str_model_value
                            if int_model_value >= 0
                            else str(-int_model_value)
                        ),
                    ),
                    self.extract_regular_expression(var.n_type),
                )
            )

            if z3_solver.check() != z3.sat:
                LOGGER.warning(
                    RuntimeError(
                        "Could not parse a numeric solution "
                        + f"({str_model_value}) for variable "
                        + f"{var} of type '{var.n_type}'; try "
                        + "running the solver without optimized Z3 queries or make "
                        + "sure that ranges are restricted to syntactically valid "
                        + "ones (according to the grammar).",
                    )
                )

            return result_to_maybe(
                self.parse(
                    (
                        z3_solver.model()[maybe_plus_var].as_string()
                        if int_model_value >= 0
                        else "-"
                    )
                    + z3_solver.model()[zeroes_padding_var].as_string()
                    + (
                        str_model_value
                        if int_model_value >= 0
                        else str(-int_model_value)
                    ),
                    var.n_type,
                )
            )

    @typechecked
    def extract_model_value_flexible_var(
        self,
        var: Variable,
        model: z3.ModelRef,
        _fresh_var_map,
        _length_vars,
        _int_vars,
    ) -> Maybe[DerivationTree]:
        """
        Addresses the case of "flexible" variables from
        :meth:`~isla.solver.RepairSolver.extract_model_value`.

        :param var: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :param model: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :param _fresh_var_map: Not needed.
        :param _length_vars: Not needed.
        :param _int_vars: Not needed.
        :return: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        """

        return result_to_maybe(
            self.parse(
                smt_string_val_to_string(model[z3.String(var.name)]),
                var.n_type,
            )
        )


def compute_most_specific_type(
    types: Iterable[str],
    graph: gg.GrammarGraph,
) -> Tuple[str, ...]:
    """
    TODO: Document, test.
    :param types:
    :param graph:
    :return:
    """

    return tuple(
        sorted(
            types,
            key=lambda t: len(
                tuple(
                    other_type
                    for other_type in types
                    if other_type != t and graph.reachable(t, other_type)
                )
            ),
        )
    )


def compute_pruning_substitutions(
    smt_conjuncts: Sequence[SMTFormula], tree: DerivationTree
) -> frozendict[DerivationTree, DerivationTree]:
    """
    TODO: Document, test.

    :param smt_conjuncts:
    :param tree:
    :return:
    """

    participating_paths = {
        tree.find_node(arg)
        for conjunct in smt_conjuncts
        for arg in conjunct.tree_arguments()
    }

    return frozendict(
        (
            cast(
                Tuple[DerivationTree, DerivationTree],
                (
                    subtree := tree.get_subtree(path),
                    subtree,
                    DerivationTree(subtree.value, None, id=subtree.id),
                )[1:],
            )
            for path in participating_paths
            if is_nonterminal(tree.get_subtree(path).value)
            and not tree.get_subtree(path).children is None
        )
    )


def add_already_matched(
    f: QuantifiedFormula, trees: DerivationTree | Iterable[DerivationTree]
) -> QuantifiedFormula:
    # TODO this is a hack
    return type(f)(
        f.bound_variable,
        f.in_variable,
        f.inner_formula,
        f.bind_expression,
        (
            f.already_matched
            | (
                FrozenOrderedSet([trees.structural_hash()])
                if isinstance(trees, DerivationTree)
                else FrozenOrderedSet(
                    [hash((tree.id, tree.structural_hash())) for tree in trees]
                )
            )
        ),
    )


@typechecked
def rename_instantiated_variables_in_smt_formulas(
    smt_formulas: Sequence[SMTFormula],
) -> Tuple[SMTFormula, ...]:
    """
    TODO: Document, polish.

    :param self:
    :param smt_formulas:
    :return:
    """

    old_smt_formulas = smt_formulas
    smt_formulas = ()
    for subformula in old_smt_formulas:
        subst_var: Variable
        subst_tree: DerivationTree

        new_smt_formula: z3.BoolRef = subformula.formula
        new_substitutions = subformula.substitutions
        new_instantiated_variables = subformula.instantiated_variables

        for subst_var, subst_tree in subformula.substitutions.items():
            new_name = f"{subst_tree.value}_{subst_tree.id}"
            new_var = BoundVariable(new_name, subst_var.n_type)

            new_smt_formula = cast(
                z3.BoolRef,
                z3_subst(new_smt_formula, {subst_var.to_smt(): new_var.to_smt()}),
            )
            new_substitutions = {
                new_var if k == subst_var else k: v
                for k, v in new_substitutions.items()
            }
            new_instantiated_variables = {
                new_var if v == subst_var else v for v in new_instantiated_variables
            }

        smt_formulas += (
            SMTFormula(
                new_smt_formula,
                *subformula.free_variables_,
                instantiated_variables=new_instantiated_variables,
                substitutions=new_substitutions,
            ),
        )

    return smt_formulas


@typechecked
def infer_variable_contexts(
    variables: Set[Variable], smt_formulas: Sequence[z3.BoolRef]
) -> frozendict[str, FrozenSet[Variable]]:
    """
    Divides the given variables into

    1. those that occur only in :code:`length(...)` contexts,
    2. those that occur only in :code:`str.to.int(...)` contexts, and
    3. "flexible" constants occurring in other/various contexts.

    >>> x = Variable("x", "<X>")
    >>> y = Variable("y", "<Y>")

    Two variables in an arbitrary context.

    >>> from isla.z3_helpers import z3_eq
    >>> f = z3_eq(x.to_smt(), y.to_smt())
    >>> contexts = infer_variable_contexts({x, y}, (f,))
    >>> contexts["length"]
    frozenset()
    >>> contexts["int"]
    frozenset()
    >>> contexts["flexible"] == {Variable("x", "<X>"), Variable("y", "<Y>")}
    True

    Variable x occurs in a length context, variable y in an arbitrary one.

    >>> f = z3.And(
    ...     z3.Length(x.to_smt()) > z3.IntVal(10),
    ...     z3_eq(y.to_smt(), z3.StringVal("y")))
    >>> print(deep_str(infer_variable_contexts({x, y}, (f,))))
    {length: {x}, int: {}, flexible: {y}}

    Variable x occurs in a length context, y does not occur.

    >>> f = z3.Length(x.to_smt()) > z3.IntVal(10)
    >>> print(deep_str(infer_variable_contexts({x, y}, (f,))))
    {length: {x}, int: {}, flexible: {y}}

    Variables x and y both occur in a length context.

    >>> f = z3.Length(x.to_smt()) > z3.Length(y.to_smt())
    >>> contexts = infer_variable_contexts({x, y}, (f,))
    >>> contexts["length"] == {Variable("x", "<X>"), Variable("y", "<Y>")}
    True
    >>> contexts["int"]
    frozenset()
    >>> contexts["flexible"]
    frozenset()

    Variable x occurs in a :code:`str.to.int` context.

    >>> f = z3.StrToInt(x.to_smt()) > z3.IntVal(17)
    >>> print(deep_str(infer_variable_contexts({x}, (f,))))
    {length: {}, int: {x}, flexible: {}}

    Now, x also occurs in a different context; it's "flexible" now.

    >>> f = z3.And(
    ...     z3.StrToInt(x.to_smt()) > z3.IntVal(17),
    ...     z3_eq(x.to_smt(), z3.StringVal("17")))
    >>> print(deep_str(infer_variable_contexts({x}, (f,))))
    {length: {}, int: {}, flexible: {x}}

    :param variables: The constants to divide/filter from.
    :param smt_formulas: The SMT formulas to consider in the filtering.
    :return: A pair of constants occurring in `str.len` contexts, and the
    remaining ones. The union of both sets equals `variables`, and both sets
    are disjoint.
    """

    parent_relationships = reduce(
        merge_dict_of_sets,
        [parent_relationships_in_z3_expr(formula) for formula in smt_formulas],
        {},
    )

    contexts: frozendict[Variable, FrozenSet[int]] = frozendict(
        {
            var: frozenset(
                {
                    expr.decl().kind()
                    for expr in parent_relationships.get(var.to_smt(), set())
                }
            )
            or {-1}
            for var in variables
        }
    )

    # The set `length_vars` consists of all variables that only occur in
    # `str.len(...)` context.
    length_vars: FrozenSet[Variable] = frozenset(
        {
            var
            for var in variables
            if all(context == z3.Z3_OP_SEQ_LENGTH for context in contexts[var])
        }
    )

    # The set `int_vars` consists of all variables that only occur in
    # `str.to.int(...)` context.
    int_vars: FrozenSet[Variable] = frozenset(
        {
            var
            for var in variables
            if all(context == z3.Z3_OP_STR_TO_INT for context in contexts[var])
        }
    )

    # "Flexible" variables are the remaining ones.
    flexible_vars = frozenset(variables.difference(length_vars).difference(int_vars))

    return frozendict(
        {"length": length_vars, "int": int_vars, "flexible": flexible_vars}
    )


@typechecked
def create_fixed_length_tree(
    start: DerivationTree | str,
    canonical_grammar: FrozenCanonicalGrammar,
    target_length: int,
) -> Maybe[DerivationTree]:
    """
    TODO: Document, polish.

    >>> grammar = {
    ...     "<start>": ["<X>"],
    ...     "<X>": ["x", "x<X>"],
    ... }
    >>> tree = create_fixed_length_tree("<X>", frozen_canonical(grammar), 5)
    >>> tree
    <Some: xxxxx>
    >>> tree.map(lambda t: t.value)
    <Some: <X>>

    :param start:
    :param canonical_grammar:
    :param target_length:
    :return:
    """

    nullable = compute_nullable_nonterminals(canonical_grammar)
    start = DerivationTree(start) if isinstance(start, str) else start
    stack: List[Tuple[DerivationTree, int, Tuple[Tuple[Path, DerivationTree], ...]]] = [
        (start, int(start.value not in nullable), (((), start),)),
    ]

    while stack:
        tree, curr_len, open_leaves = stack.pop()

        if not open_leaves:
            if curr_len == target_length:
                return Some(tree)
            else:
                continue

        if curr_len > target_length:
            continue

        idx: int
        path: Path
        leaf: DerivationTree
        for idx, (path, leaf) in reversed(list(enumerate(open_leaves))):
            terminal_expansions, expansions = get_expansions(
                leaf.value, canonical_grammar
            )

            if terminal_expansions:
                expansions.append(random.choice(terminal_expansions))

            # Only choose one random terminal expansion; keep all nonterminal expansions
            expansions = sorted(
                expansions,
                key=lambda expansion: len(
                    [elem for elem in expansion if is_nonterminal(elem)]
                ),
            )

            for expansion in reversed(expansions):
                new_children = tuple(
                    [
                        DerivationTree(elem, None if is_nonterminal(elem) else ())
                        for elem in expansion
                    ]
                )

                expanded_tree = tree.replace_path(
                    path,
                    DerivationTree(
                        leaf.value,
                        new_children,
                    ),
                )

                stack.append(
                    (
                        expanded_tree,
                        curr_len
                        + sum(
                            [
                                len(child.value)
                                if child.children == ()
                                else (1 if child.value not in nullable else 0)
                                for child in new_children
                            ]
                        )
                        - int(leaf.value not in nullable),
                        open_leaves[:idx]
                        + tuple(
                            [
                                (path + (child_idx,), new_child)
                                for child_idx, new_child in enumerate(new_children)
                                if is_nonterminal(new_child.value)
                            ]
                        )
                        + open_leaves[idx + 1 :],
                    )
                )

    LOGGER.warning(
        "Could not create a tree of length %d with start nonterminal/tree %s",
        target_length,
        start,
    )
    return Nothing


@typechecked
def subtree_solutions(
    solution: Mapping[DerivationTree, DerivationTree]
) -> frozendict[DerivationTree, DerivationTree]:
    """
    TODO: Polish, document.

    :param solution:
    :return:
    """

    solution_with_subtrees: frozendict[DerivationTree, DerivationTree] = frozendict({})

    for orig, subst in solution.items():
        assert isinstance(
            orig, DerivationTree
        ), f"Expected a DerivationTree, given: {type(orig).__name__}"

        # Note: It can happen that a path in the original tree is not valid in the
        #       substitution, e.g., if we happen to replace a larger with a smaller
        #       tree.
        for path, tree in [
            (p, t)
            for p, t in orig.paths()
            if t not in solution_with_subtrees and subst.is_valid_path(p)
        ]:
            solution_with_subtrees = solution_with_subtrees.set(
                tree, subst.get_subtree(path)
            )

    return solution_with_subtrees


@typechecked
def smt_formulas_referring_to_subtrees(
    smt_formulas: Sequence[SMTFormula],
) -> Tuple[SMTFormula, ...]:
    """
    Returns a list of SMT formulas whose solutions address subtrees of other SMT
    formulas, but whose own substitution subtrees are in turn *not* referred by
    top-level substitution trees of other formulas. Those must be solved first to avoid
    inconsistencies.

    # TODO: Document better, polish.

    :param smt_formulas: The formulas to search for references to subtrees.
    :return: The list of conflicting formulas that must be solved first.
    """

    @typechecked
    def subtree_ids(formula: SMTFormula) -> Set[int]:
        return {
            subtree.id
            for tree in formula.substitutions.values()
            for _, subtree in tree.paths()
            if subtree.id != tree.id
        }

    @typechecked
    def tree_ids(formula: SMTFormula) -> Set[int]:
        return {tree.id for tree in formula.substitutions.values()}

    subtree_ids_for_formula: Dict[SMTFormula, Set[int]] = {
        formula: subtree_ids(formula) for formula in smt_formulas
    }

    tree_ids_for_formula: Dict[SMTFormula, Set[int]] = {
        formula: tree_ids(formula) for formula in smt_formulas
    }

    @typechecked
    def independent_from_solutions_of_other_formula(
        idx: int, formula: SMTFormula
    ) -> bool:
        return all(
            not tree_ids_for_formula[other_formula].intersection(
                subtree_ids_for_formula[formula]
            )
            for other_idx, other_formula in enumerate(smt_formulas)
            if other_idx != idx
        )

    @typechecked
    def refers_to_subtree_of_other_formula(idx: int, formula: SMTFormula) -> bool:
        return any(
            tree_ids_for_formula[formula].intersection(
                subtree_ids_for_formula[other_formula]
            )
            for other_idx, other_formula in enumerate(smt_formulas)
            if other_idx != idx
        )

    return tuple(
        formula
        for idx, formula in enumerate(smt_formulas)
        if refers_to_subtree_of_other_formula(idx, formula)
        and independent_from_solutions_of_other_formula(idx, formula)
    )


@typechecked
def auto_subst_and_eval_is_false(formula: Formula) -> bool:
    class AutoSubstEvalVisitor(FormulaVisitor):
        @typechecked
        def __init__(self):
            super().__init__()
            self.problems: Tuple[SMTFormula, ...] = ()

        @typechecked
        def visit_smt_formula(self, formula: SMTFormula):
            if formula.auto_eval or formula.auto_subst:
                self.problems += (formula,)

    visitor = AutoSubstEvalVisitor()
    formula.accept(visitor)

    if visitor.problems:
        LOGGER.warning(
            "Found formulas with auto_eval or auto_subst set to True:\n%s",
            "\n".join(map(str, visitor.problems)),
        )

    return not len(visitor.problems)
