import random
from typing import Optional, List, Tuple, Dict, cast

from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import non_canonical
from grammar_graph.gg import GrammarGraph, NonterminalNode

from input_constraints.helpers import get_subtree, prev_path_complete, replace_tree_path, \
    reverse_tree_iterator, get_path_of_subtree, geometric_sequence
from input_constraints.type_defs import ParseTree, Path, CanonicalGrammar, CanonicalExpansionAlternative


def match_expansions(graph: GrammarGraph,
                     l_1: CanonicalExpansionAlternative,
                     l_2: CanonicalExpansionAlternative,
                     index_1: int = 0,
                     index_2: int = 0) -> List[Dict[int, int]]:
    if not l_1:
        return [{}]

    if not l_2:
        return []

    if not is_nonterminal(l_1[0]):
        return match_expansions(graph, l_1[1:], l_2, index_1 + 1, index_2)

    if not is_nonterminal(l_2[0]):
        return match_expansions(graph, l_1, l_2[1:], index_1, index_2 + 1)

    assert is_nonterminal(l_1[0])
    assert is_nonterminal(l_2[0])

    result = []
    if l_1[0] == l_2[0] or graph.get_node(l_2[0]).reachable(graph.get_node(l_1[0])):
        # We take that match, but also continue looking for alternatives
        further_matches: List[Dict[int, int]] = [r for r in match_expansions(graph, l_1[1:], l_2[1:],
                                                                             index_1 + 1,
                                                                             index_2 + 2)]

        for further_match in further_matches:
            result.append(dict([(index_1, index_2)] + cast(List[Tuple[int, int]], list(further_match.items()))))

    result.extend(match_expansions(graph, l_1, l_2[1:], index_1, index_2 + 1))

    return result


def insert_before(grammar: CanonicalGrammar,
                  tree: ParseTree,
                  in_tree: ParseTree,
                  before_path: Path,
                  graph: Optional[GrammarGraph] = None,
                  current_path: Optional[Path] = None) -> Optional[ParseTree]:
    if current_path is None:
        current_path = before_path

    if graph is None:
        graph = GrammarGraph.from_grammar(non_canonical(grammar))

    to_insert_node, to_insert_children = tree

    # We first check whether there are holes in the (incomplete) tree which we can exploit.
    # If so, we do this.
    perfect_matches: List[Path] = []
    embeddable_matches: List[Tuple[Path, ParseTree]] = []
    for path_before, tree_before in reverse_tree_iterator(before_path, in_tree):
        node, children = tree_before
        if children is not None:
            continue

        if node == to_insert_node:
            perfect_matches.append(path_before)
        elif graph.get_node(node).reachable(graph.get_node(to_insert_node)):
            embeddable_matches.append((path_before, tree_before))

    match_path_perfect: Optional[Path] = None
    match_path_embeddable: Optional[Path] = None
    match_tree: Optional[ParseTree] = None

    if perfect_matches:
        match_path_perfect = random.choices(perfect_matches, geometric_sequence(len(perfect_matches)).reverse())[0]
    if embeddable_matches:
        match_path_embeddable, match_tree = random.choices(embeddable_matches,
                                                           geometric_sequence(len(embeddable_matches)).reverse())[0]

    if perfect_matches and embeddable_matches:
        if random.random() < .9:
            return replace_tree_path(in_tree, match_path_perfect, tree)
        else:
            t = wrap_in_tree_starting_in(match_tree[0], tree, grammar, graph)
            return replace_tree_path(in_tree, match_path_embeddable, t)
    elif perfect_matches:
        return replace_tree_path(in_tree, match_path_perfect, tree)
    elif embeddable_matches:
        t = wrap_in_tree_starting_in(match_tree[0], tree, grammar, graph)
        return replace_tree_path(in_tree, match_path_embeddable, t)

    # Next, we check whether we can take another alternative at the parent node.

    curr_tree = get_subtree(current_path, in_tree)
    curr_node, curr_children = curr_tree

    if is_nonterminal(curr_node):
        # TODO: The below code fragment does not seem to be needed for the current examples,
        #       which would simplify matters quite a bit. Check for other examples!
        # parent_tree = get_subtree(current_path[:-1], in_tree)
        # parent_node, parent_children = parent_tree
        # chosen_expansion = [child[0] for child in parent_children]
        # alternative_expansions = [alternative
        #                           for alternative in grammar[parent_node]
        #                           if alternative != chosen_expansion]
        #
        # for alternative in alternative_expansions:
        #     matches = match_expansions(graph, chosen_expansion, alternative)
        #
        #     for match in matches:
        #         # Now find a place where to insert `tree`. This must be a position not in `match`'s keys,
        #         # and, if `current_path` is a prefix of `before_path`, before the insertion point of `curr_node`.
        #         possibilities = [pos for pos in range(len(alternative))
        #                          if pos not in match.values() and
        #                          (not is_prefix(current_path, before_path) or pos < match[current_path[-1]]) and
        #                          is_nonterminal(alternative[pos]) and
        #                          (curr_node == alternative[pos] or
        #                           graph.get_node(alternative[pos]).reachable(graph.get_node(curr_node)))]
        #
        #         # Could also return multiple solutions, but we only choose one (for now)
        #         if possibilities:
        #             instantiations: Dict[int, ParseTree] = {v: parent_children[k] for k, v in match.items()}
        #             instantiations[possibilities[0]] = tree
        #
        #             new_children: List[ParseTree] = []
        #             for alternative_elem_idx, alternative_elem in enumerate(alternative):
        #                 if alternative_elem_idx in instantiations:
        #                     to_insert: ParseTree = instantiations[alternative_elem_idx]
        #                     result = wrap_in_tree_starting_in(alternative_elem, to_insert, grammar, graph)
        #                     new_children.append(result)
        #                 else:
        #                     new_children.append((alternative_elem, None))
        #
        #             return replace_tree_path(in_tree, current_path[:-1], (parent_node, new_children))

        # Finally, we try a self-embedding: embed the current node into a tree starting
        # with the same nonterminal, such that `tree` can be added somewhere before
        # the place where `current_tree` is added.

        current_graph_node: NonterminalNode = graph.get_node(curr_node)
        if current_graph_node.reachable(current_graph_node):
            shortest_derivation_path: Optional[List[str]] = None
            new_tree_for_parent: Optional[ParseTree] = None
            for alternative in grammar[curr_node]:
                for alternative_nonterminal in [e for e in alternative if is_nonterminal(e)]:
                    alternative_node = graph.get_node(alternative_nonterminal)
                    if alternative_node.reachable(current_graph_node):
                        path = [n.symbol for n in graph.shortest_non_trivial_path(alternative_node, current_graph_node)]
                        assert len(path) > 1
                        assert path[0] == alternative_nonterminal
                        assert path[-1] == curr_node

                        t = wrap_in_tree_starting_in(curr_node, curr_tree, grammar, graph)

                        # check if `t` contains a `(tree[0], None)` subtree before the parent node -> insertion point
                        # TODO maybe too strong? Sufficient is some `(symbol, None)` s.t. the parent node
                        #      can be reached from symbol
                        contains_insertion_point = False
                        for path_before, tree_before in reverse_tree_iterator(get_path_of_subtree(t, curr_tree), t):
                            if tree_before == (to_insert_node, None):
                                t = replace_tree_path(t, path_before, tree)
                                contains_insertion_point = True
                                break

                        if contains_insertion_point and (shortest_derivation_path is None or
                                                         len(path) < len(shortest_derivation_path)):
                            shortest_derivation_path = path
                            new_tree_for_parent = t

            if new_tree_for_parent is not None:
                return replace_tree_path(in_tree, current_path, new_tree_for_parent)

    next_path = prev_path_complete(current_path, in_tree)
    if next_path is None:
        return None
    else:
        return insert_before(grammar, tree, in_tree, before_path, graph, next_path)


def wrap_in_tree_starting_in(start_nonterminal: str,
                             tree: ParseTree,
                             grammar: CanonicalGrammar, graph: GrammarGraph) -> ParseTree:
    start_node = graph.get_node(start_nonterminal)
    end_node = graph.get_node(tree[0])
    assert start_node.reachable(end_node)

    derivation_path = [n.symbol for n in graph.shortest_non_trivial_path(start_node, end_node)]

    result: ParseTree = (start_nonterminal, [])
    curr_tree: ParseTree = result
    for path_idx in range(len(derivation_path) - 1):
        path_nonterminal = derivation_path[path_idx]
        next_nonterminal = derivation_path[path_idx + 1]
        alternatives_for_path_nonterminal = [a for a in grammar[path_nonterminal]
                                             if next_nonterminal in a]
        shortest_alt_for_path_nonterminal = \
            [a for a in alternatives_for_path_nonterminal
             if not any(a_ for a_ in alternatives_for_path_nonterminal
                        if len(a_) < len(a))][0]
        idx_of_next_nonterminal = shortest_alt_for_path_nonterminal.index(next_nonterminal)
        for alt_idx, alt_symbol in enumerate(shortest_alt_for_path_nonterminal):
            if alt_idx == idx_of_next_nonterminal:
                if path_idx == len(derivation_path) - 2:
                    curr_tree[1].append(tree)
                else:
                    curr_tree[1].append((alt_symbol, []))
            else:
                curr_tree[1].append((alt_symbol, None if is_nonterminal(alt_symbol) else []))

        curr_tree = curr_tree[1][idx_of_next_nonterminal]

    return result
