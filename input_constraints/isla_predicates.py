from typing import Union

from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import canonical
from grammar_graph.gg import GrammarGraph

from input_constraints.existential_helpers import insert_tree
from input_constraints.helpers import is_before
from input_constraints.isla import DerivationTree, Constant, SemPredEvalResult, StructuralPredicate
from input_constraints.type_defs import Grammar

BEFORE_PREDICATE = StructuralPredicate("before", 2, is_before)


def count(grammar: Grammar,
          in_tree: DerivationTree,
          needle: DerivationTree,
          num: Union[Constant, DerivationTree]) -> SemPredEvalResult:
    assert needle.children is None  # Maybe relax later
    assert is_nonterminal(needle.value)

    num_needle_occurrences = len(in_tree.filter(lambda t: needle.is_prefix(t)))

    graph = GrammarGraph.from_grammar(grammar)
    leaf_nonterminals = [node.value for _, node in in_tree.open_leaves()]

    more_needles_possible = any(graph.get_node(leaf_nonterminal).reachable(graph.get_node(needle.value))
                                for leaf_nonterminal in leaf_nonterminals)

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
        if num_needle_occurrences == target_num_needle_occurrences:
            return SemPredEvalResult(True)
        else:
            return SemPredEvalResult(False)

    if more_needles_possible and num_needle_occurrences == target_num_needle_occurrences:
        return SemPredEvalResult(None)

    assert num_needle_occurrences < target_num_needle_occurrences

    # Try to add more needles to in_tree, such that no more needles can be obtained
    # in the resulting tree from expanding leaf nonterminals.

    canonical_grammar = canonical(grammar)
    candidates = insert_tree(canonical_grammar, needle, in_tree)
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
            candidates.extend(insert_tree(canonical_grammar, needle, candidate))

    # TODO: Check if None would not be more appropriate. Could we have missed a better insertion opportunity?
    return SemPredEvalResult(False)
