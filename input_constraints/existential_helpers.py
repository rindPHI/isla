import random
from typing import Optional, List, Tuple, Dict, cast, Union, Set, Generator, Iterable

from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import non_canonical
from grammar_graph.gg import GrammarGraph, NonterminalNode, Node, ChoiceNode
from orderedset import OrderedSet

from input_constraints import isla
from input_constraints.helpers import get_subtree, prev_path_complete, replace_tree_path, \
    reverse_tree_iterator, get_path_of_subtree, geometric_sequence, last_path, open_leaves, path_iterator
from input_constraints.isla import abstract_tree_to_string
from input_constraints.type_defs import ParseTree, Path, CanonicalGrammar, CanonicalExpansionAlternative, AbstractTree


# TODO: Probably not needed, maybe remove
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


def insert_tree(grammar: CanonicalGrammar,
                tree: AbstractTree,
                in_tree: AbstractTree,
                before_path: Optional[Path] = None,
                graph: Optional[GrammarGraph] = None,
                current_path: Optional[Path] = None) -> List[AbstractTree]:
    # TODO: The updated implementation does not necessarily maintain the insertion-before criterion;
    #       we might actually consider abolishing it and check syntactic predicates by filtering,
    #       which should be cheap enough and yield a simpler implementation.

    if before_path is None:
        before_path = last_path(in_tree)

    if current_path is None:
        current_path = before_path

    if graph is None:
        graph = GrammarGraph.from_grammar(non_canonical(grammar))

    to_insert_node, to_insert_children = tree
    to_insert_nonterminal = to_insert_node if isinstance(to_insert_node, str) else to_insert_node.n_type

    # We first check whether there are holes in the (incomplete) tree which we can exploit.
    # If so, we do this.
    perfect_matches: List[Path] = []
    embeddable_matches: List[Tuple[Path, ParseTree]] = []
    for path_before, tree_before in reverse_tree_iterator(before_path, in_tree):
        node, children = tree_before
        if children is not None:
            continue

        if node == to_insert_nonterminal:
            perfect_matches.append(path_before)
        elif graph.get_node(node).reachable(graph.get_node(to_insert_nonterminal)):
            embeddable_matches.append((path_before, tree_before))

    result: List[AbstractTree] = []

    def add_to_result(new_tree: Union[AbstractTree, List[AbstractTree]]) -> List[AbstractTree]:
        if type(new_tree) is list:
            for t in new_tree:
                add_to_result(t)
            return result

        if new_tree not in result:
            result.append(new_tree)
        return result

    for match_path_perfect in perfect_matches:
        add_to_result(replace_tree_path(in_tree, match_path_perfect, tree))

    for match_path_embeddable, match_tree in embeddable_matches:
        t = wrap_in_tree_starting_in(match_tree[0], tree, grammar, graph)
        add_to_result(replace_tree_path(in_tree, match_path_embeddable, t))

    # Next, we check whether we can take another alternative at the parent node.

    curr_tree = get_subtree(current_path, in_tree)
    curr_node, curr_children = curr_tree

    if is_nonterminal(curr_node):
        # Finally, we try a self-embedding: embed the current node into a tree starting
        # with the same nonterminal, such that `tree` can be added somewhere before
        # the place where `current_tree` is added.

        current_graph_node: NonterminalNode = graph.get_node(curr_node)
        if current_graph_node.reachable(current_graph_node):
            for self_embedding_path in paths_between(graph, curr_node, curr_node):
                for self_embedding_tree in path_to_tree(grammar, self_embedding_path):
                    leaves = list(open_leaves(self_embedding_tree))
                    curr_node_occs = len([leaf for leaf in leaves if leaf[1][0] == curr_node])
                    for leaf_path, (leaf_nonterm, _) in open_leaves(self_embedding_tree):
                        to_insert_graph_node = graph.get_node(to_insert_nonterminal)
                        if leaf_nonterm == curr_node and curr_node_occs < 2:
                            continue

                        if leaf_nonterm == to_insert_nonterminal:
                            new_tree_for_parent = replace_tree_path(self_embedding_tree, leaf_path, tree)
                            add_to_result(replace_tree_path(in_tree, current_path, new_tree_for_parent))
                            continue

                        if graph.get_node(leaf_nonterm).reachable(to_insert_graph_node):
                            for connecting_path in paths_between(graph, leaf_nonterm, to_insert_nonterminal):
                                for connecting_tree in path_to_tree(grammar, connecting_path):
                                    for insert_leaf_path, (insert_leaf_nonterm, _) in open_leaves(connecting_tree):
                                        if insert_leaf_nonterm == to_insert_nonterminal:
                                            instantiated_connecting_tree = \
                                                replace_tree_path(connecting_tree, insert_leaf_path, tree)
                                            instantiated_connecting_tree = shrink_tree(instantiated_connecting_tree)
                                            new_tree_for_parent = replace_tree_path(self_embedding_tree,
                                                                                    leaf_path,
                                                                                    instantiated_connecting_tree)
                                            add_to_result(replace_tree_path(in_tree, current_path, new_tree_for_parent))

            # new_tree_for_parent: Optional[ParseTree] = None
            #
            # shortest_derivation_path: Optional[List[str]] = None
            # for alternative in grammar[curr_node]:
            #    for alternative_nonterminal in [e for e in alternative if is_nonterminal(e)]:
            #        alternative_node = graph.get_node(alternative_nonterminal)
            #        if alternative_node.reachable(current_graph_node):
            #            path = [n.symbol for n in graph.shortest_non_trivial_path(alternative_node, current_graph_node)]
            #            assert len(path) > 1
            #            assert path[0] == alternative_nonterminal
            #            assert path[-1] == curr_node

            #            t = wrap_in_tree_starting_in(curr_node, curr_tree, grammar, graph)

            #            # check if `t` contains a `(tree[0], None)` subtree before the parent node -> insertion point
            #            # TODO maybe too strong? Sufficient is some `(symbol, None)` s.t. the parent node
            #            #      can be reached from symbol
            #            contains_insertion_point = False
            #            for path_before, tree_before in reverse_tree_iterator(get_path_of_subtree(t, curr_tree), t):
            #                if tree_before == (to_insert_nonterminal, None):
            #                    t = replace_tree_path(t, path_before, tree)
            #                    contains_insertion_point = True
            #                    break

            #            if contains_insertion_point and (shortest_derivation_path is None or
            #                                             len(path) < len(shortest_derivation_path)):
            #                shortest_derivation_path = path
            #                new_tree_for_parent = t

            # if new_tree_for_parent is not None:
            #     add_to_result(replace_tree_path(in_tree, current_path, new_tree_for_parent))

    next_path = prev_path_complete(current_path, in_tree)
    if next_path is None:
        return result
    else:
        return add_to_result(insert_tree(grammar, tree, in_tree, before_path, graph, next_path))


def shrink_tree(tree: AbstractTree) -> AbstractTree:
    node, children = tree

    if type(node) is str and not is_nonterminal(node):
        return tree

    contains_constant = False
    for _, subtree in path_iterator(tree):
        if isinstance(subtree[0], isla.Constant):
            contains_constant = True
            break

    if contains_constant:
        return node, None if children is None else [shrink_tree(child) for child in children]
    else:
        return node, None


def wrap_in_tree_starting_in(start_nonterminal: str,
                             tree: AbstractTree,
                             grammar: CanonicalGrammar, graph: GrammarGraph) -> ParseTree:
    start_node = graph.get_node(start_nonterminal)
    tree_root_nonterminal = tree[0] if type(tree[0]) is str else tree[0].n_type
    end_node = graph.get_node(tree_root_nonterminal)
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


def path_to_tree(grammar: CanonicalGrammar, path: Union[Tuple[str], List[str]]) -> List[ParseTree]:
    assert len(path) > 1
    result: List[ParseTree] = []
    candidates: List[ParseTree] = [(path[0], None)]
    path = path[1:]

    while path:
        next_nonterminal = path[0]
        for _ in range(len(candidates)):
            candidate = candidates.pop(0)
            leaf_path, (leaf_node, _) = next(open_leaves(candidate))
            matching_expansions = [expansion for expansion in grammar[leaf_node]
                                   if next_nonterminal in expansion]
            if not matching_expansions:
                continue
            for matching_expansion in matching_expansions:
                nonterminal_positions = [i for i, x in enumerate(matching_expansion)
                                         if x == next_nonterminal]
                for nonterminal_position in nonterminal_positions:
                    next_children = [(nonterm, [])
                                     if idx != nonterminal_position
                                     else (nonterm, None)
                                     for idx, nonterm in enumerate(matching_expansion)]

                    new_candidate = replace_tree_path(candidate, leaf_path, (leaf_node, next_children))
                    if len(path) == 1:
                        result.append(new_candidate)
                    else:
                        candidates.append(new_candidate)

        path = path[1:]

    return make_leaves_open(result)


def make_leaves_open(result: List[ParseTree]) -> List[ParseTree]:
    for tree in result:
        node, children = tree
        if children is not None and not children:
            result.remove(tree)
            result.append((node, None))
            break

        queue = [tree]
        while queue:
            next_node = queue.pop()
            for idx, child in enumerate(next_node[1]):
                if not is_nonterminal(child[0]):
                    next_node[1][idx] = (child[0], [])
                    continue

                if child[1] is None:
                    continue

                if not child[1]:
                    next_node[1][idx] = (child[0], None)
                    continue

                queue.append(child)

    return result


def paths_between(graph: GrammarGraph, start: str, dest: str) -> Generator[Tuple[str, ...], None, None]:
    start_node = graph.get_node(start)
    dest_node = graph.get_node(dest)

    assert isinstance(start_node, NonterminalNode)

    prefixes: List[Tuple[Set[Node], List[Node]]] = [(set()
                                                     if start_node == dest_node and start_node.reachable(start_node)
                                                     else {start_node}, [start_node])]
    result: OrderedSet[Tuple[str, ...]] = OrderedSet([])

    while prefixes:
        visited, prefix = prefixes.pop()
        assert isinstance(prefix[-1], NonterminalNode)
        for child in cast(NonterminalNode, prefix[-1]).children:
            if child not in visited:
                new_path = prefix + [child]
                if child == dest_node:
                    s_path = tuple([n.symbol for n in new_path if type(n) is not ChoiceNode])
                    if s_path not in result:
                        result.add(s_path)
                        yield s_path
                elif isinstance(child, NonterminalNode):
                    prefixes.append((visited | {child}, new_path))