from functools import lru_cache
from typing import Optional, List, Tuple, cast, Union, Set, Generator

import z3
from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import non_canonical
from grammar_graph.gg import GrammarGraph, NonterminalNode, Node, ChoiceNode
from orderedset import OrderedSet

from input_constraints import isla
from input_constraints.helpers import is_prefix, path_iterator
from input_constraints.isla import DerivationTree
from input_constraints.type_defs import Path, CanonicalGrammar, ParseTree


def insert_tree(grammar: CanonicalGrammar,
                tree: DerivationTree,
                in_tree: DerivationTree,
                graph: Optional[GrammarGraph] = None,
                current_path: Optional[Path] = None,
                max_num_solutions: Optional[int] = 50) -> List[DerivationTree]:
    if current_path is None:
        current_path = tuple()

    if graph is None:
        graph = GrammarGraph.from_grammar(non_canonical(grammar))

    to_insert_node, to_insert_children = tree
    to_insert_nonterminal = to_insert_node if isinstance(to_insert_node, str) else to_insert_node.n_type

    # We first check whether there are holes in the (incomplete) tree which we can exploit.
    # If so, we do this.
    result: List[DerivationTree] = []
    result_hashes: Set[int] = set()

    def add_to_result(
            new_tree: Union[DerivationTree, List[DerivationTree]]) -> bool:
        if type(new_tree) is list:
            for t in new_tree:
                if not add_to_result(t):
                    return False
            return True

        # The following alternative avoids prefixes, but is quite expensive if there are many results.
        # if (new_tree.structural_hash() not in result_hashes
        #         and not any(existing.is_prefix(new_tree) for existing in result)):

        if new_tree.structural_hash() not in result_hashes:
            result.append(new_tree)
            result_hashes.add(new_tree.structural_hash())

        return not max_num_solutions or len(result) < max_num_solutions

    # NOTE: Removed using "embeddable" matches since this can yield problematic results. E.g., if a containing
    #       tree into which tree is embedded occurs in a syntactic predicate, then the it happened
    perfect_matches: List[Path] = []
    embeddable_matches: List[Tuple[Path, DerivationTree]] = []
    for subtree_path, subtree in in_tree.paths():
        node, children = subtree
        if not isinstance(node, str):
            continue

        if children is not None:
            continue

        #  if node == to_insert_nonterminal:
        #      perfect_matches.append(subtree_path)

        if graph.reachable(graph.get_node(node), graph.get_node(to_insert_nonterminal)):
            embeddable_matches.append((subtree_path, subtree))

    for match_path_embeddable, match_tree in embeddable_matches:
        t = wrap_in_tree_starting_in(match_tree.root_nonterminal(), tree, grammar, graph)
        orig_node = in_tree.get_subtree(match_path_embeddable)
        assert t.value == orig_node.value
        if not add_to_result(in_tree.replace_path(
                match_path_embeddable,
                DerivationTree(t.value, t.children, orig_node.id),
                graph,
                retain_id=True)):
            return result

    # NOTE: Removed the attempt to use existing "holes" for now. There is some kind of problem with
    #       the "declared before used" example if we use it. It works if we set tree.id = orig_node.id
    #       (with side effect!) instead of creating a new DerivationTree object with that same ID,
    #       for whatever reason, but this has undesired effects for other examples. E.g., in the CSV
    #       with same field size example, we only get rows like "a;x;x;x" since the last three fields
    #       have the same ID. Also, DerivationTrees should be immutable. If we find out what breaks the
    #       def-use example, we can reactivate this code.
    #
    # for match_path_perfect in perfect_matches:
    #     orig_node = in_tree.get_subtree(match_path_perfect)
    #     assert tree.value == orig_node.value
    #     add_to_result(in_tree.replace_path(
    #         match_path_perfect,
    #         DerivationTree(tree.value, tree.children, orig_node.id),
    #         retain_id=True
    #     ))

    # Next, we check whether we can take another alternative at the parent node.

    curr_tree = in_tree.get_subtree(current_path)
    curr_node, curr_children = curr_tree

    if isinstance(curr_node, str) and is_nonterminal(curr_node):
        # Finally, we try a self-embedding: embed the current node into a tree starting
        # with the same nonterminal, such that `tree` can be added somewhere before
        # the place where `current_tree` is added.

        current_graph_node: NonterminalNode = graph.get_node(curr_node)
        if graph.reachable(current_graph_node, current_graph_node):
            for self_embedding_path in paths_between(graph, curr_node, curr_node):
                for self_embedding_tree in path_to_tree(grammar, graph, self_embedding_path):
                    # For each the curr_tree and the tree to insert, have to find one leaf s.t. either
                    # (1) we can replace the leaf with that tree, or
                    # (2) we can add that tree somewhere below that leaf.

                    def insert(trees_to_insert: List[DerivationTree],
                               into_tree: DerivationTree,
                               insert_paths: Optional[List[Path]] = None) -> List[DerivationTree]:
                        if not trees_to_insert:
                            assert insert_paths is not None
                            return [into_tree]

                        if not insert_paths:
                            insert_paths = []

                        result: List[DerivationTree] = []

                        leaves = list(into_tree.open_leaves())

                        for leaf_idx, (leaf_path, (leaf_nonterm, _)) in enumerate(leaves):
                            if any(is_prefix(insert_path, leaf_path) for insert_path in insert_paths):
                                continue

                            for insert_tree_idx, tree_to_insert in enumerate(trees_to_insert):
                                nonterm_to_insert = tree_to_insert.root_nonterminal()
                                if leaf_nonterm == nonterm_to_insert:
                                    result += insert(trees_to_insert[:insert_tree_idx] +
                                                     trees_to_insert[insert_tree_idx + 1:],
                                                     into_tree.replace_path(leaf_path, tree_to_insert, graph),
                                                     insert_paths + [leaf_path])
                                elif (tree_to_insert.children is not None
                                      and tree_to_insert.num_children() == 1
                                      and tree_to_insert.children[0].value == leaf_nonterm):
                                    result += insert(
                                        trees_to_insert[:insert_tree_idx] +
                                        trees_to_insert[insert_tree_idx + 1:],
                                        into_tree.replace_path(leaf_path, tree_to_insert.children[0], graph),
                                        insert_paths + [leaf_path])
                                else:
                                    leaf_nonterm_node = graph.get_node(leaf_nonterm)
                                    to_insert_nonterm_node = graph.get_node(nonterm_to_insert)
                                    if not graph.reachable(leaf_nonterm_node, to_insert_nonterm_node):
                                        continue

                                    for connecting_path in paths_between(graph, leaf_nonterm, nonterm_to_insert):
                                        for connecting_tree in path_to_tree(grammar, graph, connecting_path):
                                            for insert_leaf_path, (insert_leaf_nonterm, _) in \
                                                    connecting_tree.open_leaves():
                                                if insert_leaf_nonterm != nonterm_to_insert:
                                                    continue

                                                instantiated_connecting_tree = connecting_tree.replace_path(
                                                    insert_leaf_path, tree_to_insert, graph)
                                                result += insert(
                                                    trees_to_insert[:insert_tree_idx] +
                                                    trees_to_insert[insert_tree_idx + 1:],
                                                    into_tree.replace_path(
                                                        leaf_path, instantiated_connecting_tree, graph),
                                                    insert_paths + [leaf_path + insert_leaf_path])

                        return result

                    results = insert([curr_tree, tree], self_embedding_tree)
                    for instantiated_tree in results:
                        orig_node = in_tree.get_subtree(current_path)
                        assert instantiated_tree.value == orig_node.value
                        instantiated_tree.id = orig_node.id

                        new_tree = in_tree.replace_path(current_path, instantiated_tree, graph)
                        if not add_to_result(new_tree):
                            return result

    np = in_tree.next_path(current_path)
    if np is None:
        return result
    else:
        add_to_result(insert_tree(grammar, tree, in_tree, graph, np, max_num_solutions=max_num_solutions))
        return result


def shrink_tree(tree: DerivationTree) -> DerivationTree:
    node, children = tree

    if type(node) is str and not is_nonterminal(node):
        return tree

    contains_constant = False
    for _, subtree in tree.paths():
        if isinstance(subtree.value, isla.Constant):
            contains_constant = True
            break

    if contains_constant:
        return DerivationTree(node, None if children is None else [shrink_tree(child) for child in children])
    else:
        return DerivationTree(node, None)


def wrap_in_tree_starting_in(start_nonterminal: str,
                             tree: DerivationTree,
                             grammar: CanonicalGrammar, graph: GrammarGraph) -> DerivationTree:
    start_node = graph.get_node(start_nonterminal)
    end_node = graph.get_node(tree.root_nonterminal())
    parse_tree = tree.to_parse_tree()
    assert graph.reachable(start_node, end_node)

    derivation_path = [n.symbol for n in graph.shortest_non_trivial_path(start_node, end_node)]

    # We work with raw parse trees here since DerivationTree objects are immutable
    result_pt: ParseTree = (start_nonterminal, [])
    curr_tree: ParseTree = result_pt
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
                    curr_tree[1].append(parse_tree)
                else:
                    curr_tree[1].append((alt_symbol, []))
            else:
                curr_tree[1].append((alt_symbol, None if is_nonterminal(alt_symbol) else []))

        curr_tree = curr_tree[1][idx_of_next_nonterminal]

    result = DerivationTree.from_parse_tree(result_pt)

    # Ensure ID is corect
    for path, t in path_iterator(result_pt):
        if t is parse_tree:
            result = result.replace_path(path, tree, graph)
            break

    return result


def path_to_tree(
        grammar: CanonicalGrammar, graph: GrammarGraph, path: Union[Tuple[str], List[str]]) -> List[DerivationTree]:
    assert len(path) > 1
    result: List[DerivationTree] = []
    candidates: List[DerivationTree] = [DerivationTree(path[0], None)]
    path = path[1:]

    while path:
        next_nonterminal = path[0]
        for _ in range(len(candidates)):
            candidate = candidates.pop(0)
            leaf_path, (leaf_node, _) = next(candidate.open_leaves())
            matching_expansions = [expansion for expansion in grammar[leaf_node]
                                   if next_nonterminal in expansion]
            if not matching_expansions:
                continue
            for matching_expansion in matching_expansions:
                nonterminal_positions = [i for i, x in enumerate(matching_expansion)
                                         if x == next_nonterminal]
                for nonterminal_position in nonterminal_positions:
                    next_children = [DerivationTree(nonterm, [])
                                     if idx != nonterminal_position
                                     else DerivationTree(nonterm, None)
                                     for idx, nonterm in enumerate(matching_expansion)]

                    new_candidate = candidate.replace_path(leaf_path, DerivationTree(leaf_node, next_children), graph)
                    if len(path) == 1:
                        result.append(new_candidate)
                    else:
                        candidates.append(new_candidate)

        path = path[1:]

    return [make_leaves_open(tree) for tree in result]


def make_leaves_open(tree: DerivationTree) -> DerivationTree:
    if tree.children is None:
        return tree

    if not tree.children:
        if is_nonterminal(tree.value):
            return DerivationTree(tree.value, None, tree.id)
        else:
            return tree

    return DerivationTree(tree.value, [make_leaves_open(child) for child in tree.children], tree.id)


@lru_cache(maxsize=None)
def paths_between(graph: GrammarGraph, start: str, dest: str) -> OrderedSet[Tuple[str, ...]]:
    start_node = graph.get_node(start)
    dest_node = graph.get_node(dest)

    assert isinstance(start_node, NonterminalNode)

    prefixes: List[Tuple[Set[Node], List[Node]]] = [
        (set()
         if start_node == dest_node and graph.reachable(start_node, start_node)
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
                        # yield s_path
                elif isinstance(child, NonterminalNode):
                    prefixes.append((visited | {child}, new_path))

    return result
