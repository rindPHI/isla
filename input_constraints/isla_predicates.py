from typing import Union, Optional

from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import canonical
from grammar_graph.gg import GrammarGraph

from input_constraints.existential_helpers import insert_tree
from input_constraints.helpers import is_before
from input_constraints.isla import DerivationTree, Constant, SemPredEvalResult, StructuralPredicate, SemanticPredicate
from input_constraints.type_defs import Grammar

BEFORE_PREDICATE = StructuralPredicate("before", 2, is_before)


def count(grammar: Optional[Grammar],
          in_tree: DerivationTree,
          needle: DerivationTree,
          num: Union[Constant, DerivationTree]) -> SemPredEvalResult:
    assert needle.children is None  # Maybe relax later
    assert is_nonterminal(needle.value)

    num_needle_occurrences = len(in_tree.filter(lambda t: needle.is_prefix(t)))

    if grammar is not None:
        graph = GrammarGraph.from_grammar(grammar)
        leaf_nonterminals = [node.value for _, node in in_tree.open_leaves()]

        more_needles_possible = any(graph.get_node(leaf_nonterminal).reachable(graph.get_node(needle.value))
                                    for leaf_nonterminal in leaf_nonterminals)
    else:
        assert in_tree.is_complete(), "Pass a grammar to the count predicate to evaluate open trees."
        more_needles_possible = False

    if isinstance(num, Constant):
        # Return the number of needle occurrences in in_tree, or "not ready" if in_tree is not
        # closed and more needle occurrences can yet occur in in_tree
        if more_needles_possible:
            return SemPredEvalResult(None)

        return SemPredEvalResult({num: DerivationTree(str(num_needle_occurrences), None)})

    assert num.children is None
    assert num.value.isnumeric()
    target_num_needle_occurrences = int(num.value)

    if num_needle_occurrences > target_num_needle_occurrences:
        return SemPredEvalResult(False)

    if not more_needles_possible:
        # TODO: We could also try to insert needle into already closed parts of the tree,
        #       similar to treatment of existential quantifiers...
        if num_needle_occurrences == target_num_needle_occurrences:
            return SemPredEvalResult(True)
        else:
            return SemPredEvalResult(False)

    if more_needles_possible and num_needle_occurrences == target_num_needle_occurrences:
        return SemPredEvalResult(None)

    assert num_needle_occurrences < target_num_needle_occurrences

    # Try to add more needles to in_tree, such that no more needles can be obtained
    # in the resulting tree from expanding leaf nonterminals.

    # NOTE: We insert a new tree for needle (with a new ID), since otherwise, the needle ends up in
    #       the solver's current solution tree and might get substituted by expansions.

    canonical_grammar = canonical(grammar)
    candidates = insert_tree(canonical_grammar, DerivationTree(needle.value, needle.children), in_tree)
    while candidates:
        candidate = candidates.pop(0)
        candidate_needle_occurrences = len(candidate.filter(lambda t: needle.is_prefix(t)))
        if candidate_needle_occurrences > target_num_needle_occurrences:
            continue

        candidate_more_needles_possible = \
            any(graph.get_node(leaf_nonterminal).reachable(graph.get_node(needle.value))
                for leaf_nonterminal in [node.value for _, node in candidate.open_leaves()])

        if not candidate_more_needles_possible and candidate_needle_occurrences == target_num_needle_occurrences:
            return SemPredEvalResult({in_tree: candidate})

        if candidate_more_needles_possible and candidate_needle_occurrences < target_num_needle_occurrences:
            candidates.extend(insert_tree(canonical_grammar, DerivationTree(needle.value, needle.children), candidate))

    # TODO: Check if None would not be more appropriate. Could we have missed a better insertion opportunity?
    return SemPredEvalResult(False)


COUNT_PREDICATE = SemanticPredicate(
    "count", 3, count,
    custom_args_equality=(
        lambda t1, t2:
        t1[0] == t2[0]
        and t1[1].structurally_equal(t2[1])
        and (not isinstance(t1[2], Constant) or isinstance(t2[2], Constant))
        and (not isinstance(t2[2], Constant) or isinstance(t1[2], Constant))
        and (not isinstance(t1[2], Constant) or t1[2] == t2[2])
        and (isinstance(t1[2], Constant) or t1[2].structurally_equal(t2[2]))
    )
)
