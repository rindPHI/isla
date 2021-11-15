import sys
from functools import lru_cache
from typing import Optional, List, Tuple, cast, Union, Set

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
                max_num_solutions: Optional[int] = 50) -> List[DerivationTree]:
    result: List[DerivationTree] = []
    result_hashes: Set[int] = set()

    def add_to_result(new_tree: Union[DerivationTree, List[DerivationTree]]):
        if type(new_tree) is list:
            for t in new_tree:
                add_to_result(t)
            return

        # The following alternative avoids prefixes, but is quite expensive if there are many results.
        # if (new_tree.structural_hash() not in result_hashes
        #         and not any(existing.is_prefix(new_tree) for existing in result)):

        if (new_tree.find_node(tree) is not None  # In rare cases things fail (see simple-tar case study)
                and new_tree.structural_hash() not in result_hashes):
            result.append(new_tree)
            result_hashes.add(new_tree.structural_hash())

    graph = graph or GrammarGraph.from_grammar(non_canonical(grammar))
    current_path = ()

    while current_path is not None:
        # Note: This can produce max_num_solutions * (number of insertion strategies) many solutions,
        # but, we do not divide the solution "slots" since different solutions are interesting for
        # different problems.
        num_solutions = None if max_num_solutions is None else max(0, max_num_solutions - len(result))
        if num_solutions is not None and num_solutions <= 0:
            break

        add_to_result(compute_direct_embeddings(tree, in_tree, grammar, graph, num_solutions))
        add_to_result(compute_self_embeddings(current_path, tree, in_tree, grammar, graph, num_solutions))
        add_to_result(compute_context_additions(current_path, tree, in_tree, grammar, graph, num_solutions))

        current_path = in_tree.next_path(current_path)

    return result


def compute_context_additions(
        current_path: Path,
        tree: DerivationTree,
        in_tree: DerivationTree,
        grammar: CanonicalGrammar,
        graph: GrammarGraph,
        max_num_solutions: Optional[int]) -> List[DerivationTree]:
    curr_tree = in_tree.get_subtree(current_path)

    if curr_tree.value == tree.value:
        # TODO: Could also go for reachable instead direct match
        return insert_trees(
            [curr_tree],
            in_tree.replace_path(current_path, tree),
            grammar, graph, max_num_solutions)

    return []


def compute_self_embeddings(
        current_path: Path,
        tree: DerivationTree,
        in_tree: DerivationTree,
        grammar: CanonicalGrammar,
        graph: GrammarGraph,
        max_num_solutions: Optional[int]) -> List[DerivationTree]:
    # We try a self-embedding: embed the current node into a tree starting
    # with the same nonterminal, such that `tree` can be added somewhere before
    # the place where `current_tree` is added.
    curr_tree = in_tree.get_subtree(current_path)
    curr_node = curr_tree.value

    if (not isinstance(curr_node, str) or
            not is_nonterminal(curr_node) or
            not graph.reachable(graph.get_node(curr_node), graph.get_node(curr_node))):
        return []

    results: List[DerivationTree] = []

    self_embedding_trees = [
        self_embedding_tree
        for self_embedding_path in paths_between(graph, curr_node, curr_node)
        for self_embedding_tree in path_to_tree(grammar, self_embedding_path)]

    instantiated_self_embedding_trees: List[DerivationTree] = [
        insert_result
        for self_embedding_tree in self_embedding_trees
        for insert_result in insert_trees([curr_tree, tree], self_embedding_tree, grammar, graph, max_num_solutions)]

    for instantiated_tree in instantiated_self_embedding_trees:
        if len(results) >= (max_num_solutions or sys.maxsize):
            break

        assert instantiated_tree.has_unique_ids()

        orig_node = in_tree.get_subtree(current_path)
        assert instantiated_tree.value == orig_node.value
        # instantiated_tree.id = orig_node.id
        assert instantiated_tree.has_unique_ids()

        new_tree = in_tree.replace_path(current_path, instantiated_tree)
        new_tree = DerivationTree(new_tree.value, new_tree.children)
        assert new_tree.has_unique_ids()
        results.append(new_tree)

    return results


def compute_direct_embeddings(
        tree: DerivationTree,
        in_tree: DerivationTree,
        grammar: CanonicalGrammar,
        graph: GrammarGraph,
        max_num_solutions: Optional[int]) -> List[DerivationTree]:
    # perfect_matches: List[Path] = []
    embeddable_matches: List[Tuple[Path, DerivationTree]] = []

    for subtree_path, subtree in in_tree.paths():
        node, children = subtree
        if not isinstance(node, str):
            continue

        if children is not None:
            continue

        #  if node == to_insert_nonterminal:
        #      perfect_matches.append(subtree_path)

        if graph.reachable(graph.get_node(node), graph.get_node(tree.value)):
            embeddable_matches.append((subtree_path, subtree))

    results: List[DerivationTree] = []
    for match_path_embeddable, match_tree in embeddable_matches:
        if len(results) >= (max_num_solutions or sys.maxsize):
            break

        t = wrap_in_tree_starting_in(match_tree.root_nonterminal(), tree, grammar, graph)
        orig_node = in_tree.get_subtree(match_path_embeddable)
        assert t.value == orig_node.value
        results.append(in_tree.replace_path(
            match_path_embeddable,
            DerivationTree(t.value, t.children, orig_node.id),
            retain_id=True))

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

    return results


def insert_trees(
        trees_to_insert: List[DerivationTree],
        into_tree: DerivationTree,
        grammar: CanonicalGrammar,
        graph: GrammarGraph,
        max_num_solutions: Optional[int],
        insert_paths: Optional[List[Path]] = None) -> List[DerivationTree]:
    assert all(t.id not in [t.id for _, t in into_tree.paths()] for t in trees_to_insert)

    if not trees_to_insert:
        assert insert_paths is not None
        return [into_tree]

    if not insert_paths:
        insert_paths = []

    result: List[DerivationTree] = []

    leaves_and_insert_trees = [
        (leaf_path, leaf_nonterm, insert_tree_idx, tree_to_insert)
        for insert_tree_idx, tree_to_insert in enumerate(trees_to_insert)
        for leaf_path, (leaf_nonterm, _) in into_tree.open_leaves()
        if not any(is_prefix(insert_path, leaf_path) for insert_path in insert_paths)]

    for leaf_path, leaf_nonterm, insert_tree_idx, tree_to_insert in leaves_and_insert_trees:
        if len(result) >= (max_num_solutions or sys.maxsize):
            break

        nonterm_to_insert = tree_to_insert.root_nonterminal()
        if leaf_nonterm == nonterm_to_insert:
            result += insert_trees(
                trees_to_insert[:insert_tree_idx] +
                trees_to_insert[insert_tree_idx + 1:],
                into_tree.replace_path(leaf_path, tree_to_insert),
                grammar, graph, max_num_solutions,
                insert_paths + [leaf_path])
            continue

        if (tree_to_insert.children is not None
                and tree_to_insert.num_children() == 1
                and tree_to_insert.children[0].value == leaf_nonterm):
            result += insert_trees(
                trees_to_insert[:insert_tree_idx] +
                trees_to_insert[insert_tree_idx + 1:],
                into_tree.replace_path(leaf_path, tree_to_insert.children[0]),
                grammar, graph, max_num_solutions,
                insert_paths + [leaf_path])
            continue

        leaf_nonterm_node = graph.get_node(leaf_nonterm)
        to_insert_nonterm_node = graph.get_node(nonterm_to_insert)
        if not graph.reachable(leaf_nonterm_node, to_insert_nonterm_node):
            continue

        connecting_trees_and_leaves = [
            (connecting_tree, insert_leaf_path, insert_leaf_nonterm)
            for connecting_path in paths_between(graph, leaf_nonterm, nonterm_to_insert)
            for connecting_tree in path_to_tree(grammar, connecting_path)
            for insert_leaf_path, (insert_leaf_nonterm, _) in connecting_tree.open_leaves()
            if insert_leaf_nonterm == nonterm_to_insert
        ]

        for connecting_tree, insert_leaf_path, insert_leaf_nonterm in connecting_trees_and_leaves:
            if len(result) >= (max_num_solutions or sys.maxsize):
                break

            instantiated_connecting_tree = connecting_tree.replace_path(insert_leaf_path, tree_to_insert)

            result += insert_trees(
                trees_to_insert[:insert_tree_idx] +
                trees_to_insert[insert_tree_idx + 1:],
                into_tree.replace_path(leaf_path, instantiated_connecting_tree),
                grammar, graph, max_num_solutions,
                insert_paths + [leaf_path + insert_leaf_path])

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

    # Ensure ID is correct
    for path, t in path_iterator(result_pt):
        if t is parse_tree:
            result = result.replace_path(path, tree)
            break

    return result


def path_to_tree(
        grammar: CanonicalGrammar, path: Union[Tuple[str], List[str]]) -> List[DerivationTree]:
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

                    new_candidate = candidate.replace_path(leaf_path, DerivationTree(leaf_node, next_children))
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
