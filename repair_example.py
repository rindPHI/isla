import itertools
import string
import sys
from typing import FrozenSet, Tuple, cast, Dict, Iterator, Mapping

import grammar_graph.gg as gg
import z3
from frozendict import frozendict
from orderedset import FrozenOrderedSet
from returns.maybe import Maybe, Nothing, Some
from returns.pipeline import is_successful

from isla.derivation_tree import DerivationTree
from isla.evaluator import matches_for_quantified_formula, evaluate
from isla.existential_helpers import insert_tree
from isla.fuzzer import GrammarCoverageFuzzer
from isla.helpers import frozen_canonical, is_nonterminal
from isla.isla_shortcuts import disjunction, conjunction
from isla.language import (
    set_smt_auto_eval,
    set_smt_auto_subst,
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
    convert_to_nnf, NoopFormulaTransformer,
)
from isla.solver import ISLaSolver
from isla.type_defs import FrozenGrammar, Path, FrozenCanonicalGrammar

# Our example is the assignment language with the following grammar:

grammar = frozendict(
    {
        "<start>": ("<stmt>",),
        "<stmt>": ("<assgn> ; <stmt>", "<assgn>"),
        "<assgn>": ("<var> := <rhs>",),
        "<rhs>": ("<var>", "<digit>"),
        "<var>": tuple(string.ascii_lowercase),
        "<digit>": tuple(string.digits),
    }
)

# We want to repair programs that violate the def-use constraint:

def_use_constraint = """
forall <assgn> assgn_1="<var> := {<var> rhs}" in start:
  exists <assgn> assgn_2="{<var> lhs} := <rhs>" in start:
    (before(assgn_2, assgn_1) and (= lhs rhs))
"""

# Consider the simple program `x := y ; y := 1`. This program violates the
# def-use constraint because the variable `y` is used before it is defined.

inp_str = "x := y ; y := 1 ; a := z"
# inp_str = "x := y ; y := 1"
# inp_str = "x := 1 ; y := x"

# We parse that program.
solver = ISLaSolver(grammar, def_use_constraint)
inp_tree = solver.parse(inp_str, skip_check=True)

# We substitute the start constant of the def-use constraint with the parsed
# derivation tree:
formula = solver.top_constant.map(
    lambda c: solver.formula.substitute_expressions({c: inp_tree})
).unwrap()

# Now, we define our quantifier instantiation routing. Note that this only
# works for closed trees; otherwise, eliminating particularly universal
# quantifiers is not as easy.


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


def instantiate_quantifiers(
    formula: Formula, ignore: FrozenSet[Formula] = frozenset()
) -> Formula:
    # We disable the automatic evaluation and substitution of SMT expressions
    # because we want to use the # SMT expressions as-is in the formula (to
    # repair the invalid ones).
    formula = set_auto_subst_and_eval(formula, False)

    top_level_qfd_formulas = extract_top_level_quantified_formulas(formula).difference(
        ignore
    )
    if not top_level_qfd_formulas:
        return set_auto_subst_and_eval(formula, True)

    for qfd_formula in top_level_qfd_formulas:
        matches = tuple(
            frozendict({var: tree for var, (_, tree) in match.items()})
            for match in matches_for_quantified_formula(
                qfd_formula, grammar, in_tree=qfd_formula.in_variable
            )
        )

        if isinstance(qfd_formula, ForallFormula):
            instantiations = conjunction(
                *map(qfd_formula.inner_formula.substitute_expressions, matches),
            )

            formula = replace_formula(formula, qfd_formula, instantiations)
        elif isinstance(qfd_formula, ExistsFormula):
            instantiations = disjunction(
                *map(qfd_formula.inner_formula.substitute_expressions, matches),
            )

            formula = replace_formula(
                formula,
                qfd_formula,
                instantiations | qfd_formula,
            )
            ignore = ignore | {qfd_formula}

    return instantiate_quantifiers(formula, ignore)


def repair_tree(
    orig_constraint: Formula,
    tree: DerivationTree,
    grammar: FrozenGrammar,
    max_tries_existential_insertion: int = 10,
    maybe_specialized_constraint: Maybe[Formula] = Nothing,
    maybe_canonical_grammar: Maybe[FrozenCanonicalGrammar] = Nothing,
    maybe_graph: Maybe[gg.GrammarGraph] = Nothing,
) -> Maybe[DerivationTree]:
    canonical_grammar = maybe_canonical_grammar.value_or(frozen_canonical(grammar))
    graph = maybe_graph.value_or(gg.GrammarGraph.from_grammar(grammar))
    specialized_constraint = maybe_specialized_constraint.value_or(orig_constraint)

    print(specialized_constraint, file=sys.stderr)

    # 1. Instantiate all quantifiers.
    instantiated = instantiate_quantifiers(specialized_constraint)

    # 2. Evaluate all structural predicates.
    no_structural_predicates = evaluate_structural_predicates(instantiated, tree)

    # 3. Replace all valid SMT expressions with `true` (considering the negation scope).
    no_true_semantic_formulas = convert_to_dnf(
        convert_to_nnf(
            eliminate_true_semantic_formulas(no_structural_predicates, tree, grammar)
        ),
        deep=False,
    )

    # 4a. If the formula is a disjunction, recursively try to satisfy each disjunct.
    #     Return the first successfully repaired tree, or Nothing.
    if isinstance(no_true_semantic_formulas, DisjunctiveFormula):
        return next(
            (
                Some(disjunct)
                for disjunct in split_disjunction(no_true_semantic_formulas)
                if is_successful(
                    repair_tree(
                        orig_constraint,
                        tree,
                        grammar,
                        max_tries_existential_insertion,
                        Some(disjunct),
                        Some(canonical_grammar),
                        Some(graph),
                    )
                )
            ),
            Nothing,
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
        idx, existential_formula = maybe_first_existential_formula_and_index.unwrap()
        for (
            instantiated_formula,
            tree_substitutions,
        ) in eliminate_existential_formula(
            existential_formula,
            tree,
            grammar,
            canonical_grammar,
            graph,
            max_tries_existential_insertion,
        ):
            new_constraint = (
                conjunction(
                    *conjuncts[:idx],
                    *conjuncts[idx + 1 :],
                ).substitute_expressions(tree_substitutions)
                & instantiated_formula
            )

            repaired_tree = repair_tree(
                orig_constraint,
                tree.substitute(tree_substitutions),
                grammar,
                max_tries_existential_insertion,
                Some(new_constraint),
                Some(canonical_grammar),
                Some(graph),
            )

            if is_successful(repaired_tree):
                return repaired_tree

        return Nothing

    # 4c. If the formula is a single semantic formula or a conjunction of semantic formulas,
    #     repair all semantic formulas by making all constrained tree elements abstract and
    #     asking for a solution. If a solution exists, return the repaired tree. Otherwise,
    #     return Nothing.
    assert all(isinstance(conjunct, SMTFormula) for conjunct in conjuncts)

    participating_paths = {
        tree.find_node(arg)
        for conjunct in conjuncts
        for arg in conjunct.tree_arguments()
    }

    pruning_substitutions = {
        tree.get_subtree(path): DerivationTree(tree.get_subtree(path).value, None)
        for path in participating_paths
        if is_nonterminal(tree.get_subtree(path).value)
        and not tree.get_subtree(path).children is None
    }

    solver = ISLaSolver(
        grammar,
        conjunction(*conjuncts).substitute_expressions(pruning_substitutions),
        initial_tree=Some(tree.substitute(pruning_substitutions)),
        max_number_smt_instantiations=1,
        max_number_free_instantiations=1,
    )

    return (
        solver.eliminate_all_semantic_formulas(solver.queue[0][1])
        .bind(lambda states: Some(states[0].tree) if states else Nothing)
        .map(
            lambda tree: next(
                closed_tree
                for closed_tree in itertools.islice(finish_unconstrained_tree(tree), 10)
                if evaluate(orig_constraint, closed_tree, grammar).is_true()
            )
        )
    )


def finish_unconstrained_tree(
    tree: DerivationTree,
) -> Iterator[DerivationTree]:
    fuzzer = GrammarCoverageFuzzer(grammar)

    while True:
        result = tree
        for path, leaf in tree.open_leaves():
            leaf_inst = fuzzer.expand_tree(DerivationTree(leaf.value, None))
            result = result.replace_path(path, leaf_inst)

        yield result


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


def eliminate_true_semantic_formulas(
    constraint: Formula, context_tree: DerivationTree, grammar: FrozenGrammar
) -> Formula:
    for semantic_formula in FilterVisitor(
        lambda f: (
            isinstance(f, SMTFormula)
            and not f.free_variables()
            and evaluate(f, context_tree, grammar).is_true()
        )
    ).collect(constraint):
        constraint = replace_formula(constraint, semantic_formula, true())

    return constraint


def eliminate_existential_formula(
    existential_formula: ExistsFormula,
    context_tree: DerivationTree,
    grammar: FrozenGrammar,
    canonical_grammar: FrozenCanonicalGrammar,
    graph: gg.GrammarGraph,
    max_tries_existential_insertion: int = 10,
) -> Iterator[Tuple[Formula, Mapping[DerivationTree, DerivationTree]]]:
    inserted_trees_and_bind_paths: Tuple[
        Tuple[DerivationTree, Dict[BoundVariable, Path]], ...
    ] = tuple(
        Maybe.from_optional(existential_formula.bind_expression)
        .map(
            lambda bind_expr: bind_expr.to_tree_prefix(
                existential_formula.bound_variable.n_type, grammar
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
            canonical_grammar,
            inserted_tree,
            existential_formula.in_variable,
            graph=graph,
            max_num_solutions=max_tries_existential_insertion,  # TODO: Convert to stream!
        )

        for insertion_result in insertion_results:
            replaced_path = context_tree.find_node(existential_formula.in_variable)
            resulting_tree = context_tree.replace_path(replaced_path, insertion_result)

            tree_substitutions = cast(
                frozendict[DerivationTree, DerivationTree], frozendict()
            )
            for idx in range(len(replaced_path) + 1):
                original_path = replaced_path[: idx - 1]
                original_tree = context_tree.get_subtree(original_path)

                if not resulting_tree.is_valid_path(original_path):
                    continue

                if (
                    original_tree.value
                    != resulting_tree.get_subtree(original_path).value
                ):
                    continue

                if resulting_tree.get_subtree(original_path) == original_tree:
                    continue

                tree_substitutions = tree_substitutions.set(
                    original_tree, resulting_tree.get_subtree(original_path)
                )

            assert insertion_result.find_node(inserted_tree) is not None
            variable_substitutions = {existential_formula.bound_variable: inserted_tree}

            if bind_expr_paths:
                variable_substitutions.update(
                    {
                        var: inserted_tree.get_subtree(path)
                        for var, path in bind_expr_paths.items()
                        if var in existential_formula.bind_expression.bound_variables()
                    }
                )

            instantiated_formula = (
                existential_formula.inner_formula.substitute_expressions(
                    variable_substitutions
                ).substitute_expressions(tree_substitutions)
            )

            yield instantiated_formula, tree_substitutions


# logging.basicConfig(level=logging.DEBUG)
print(repair_tree(formula, inp_tree, grammar))
