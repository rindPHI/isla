# Copyright © 2022 CISPA Helmholtz Center for Information Security.
# Author: Dominic Steinhöfel.
#
# This file is part of ISLa.
#
# ISLa is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# ISLa is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with ISLa.  If not, see <http://www.gnu.org/licenses/>.

import sys
from functools import lru_cache
from typing import Optional, List, Tuple, cast, Union, Set, Dict

from grammar_graph.gg import GrammarGraph, NonterminalNode, Node, ChoiceNode
from orderedset import OrderedSet

from isla import language
from isla.helpers import (
    is_prefix,
    path_iterator,
    dict_of_lists_to_list_of_dicts,
    assertions_activated,
    is_nonterminal,
)
from isla.derivation_tree import DerivationTree
from isla.parser import non_canonical
from isla.type_defs import Path, CanonicalGrammar, ParseTree

DIRECT_EMBEDDING = 0b001
SELF_EMBEDDING = 0b010
CONTEXT_ADDITION = 0b100


def insert_tree(
    grammar: CanonicalGrammar,
    tree: DerivationTree,
    in_tree: DerivationTree,
    graph: Optional[GrammarGraph] = None,
    max_num_solutions: Optional[int] = 50,
    methods: int = DIRECT_EMBEDDING + SELF_EMBEDDING + CONTEXT_ADDITION,
) -> List[DerivationTree]:
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

        assert graph.tree_is_valid(new_tree)
        assert all(
            new_tree.find_node(node.id) is not None for _, node in in_tree.paths()
        )

        if (
            new_tree.find_node(tree)
            is not None  # In rare cases things fail (see simple-tar case study)
            and new_tree.structural_hash() not in result_hashes
        ):
            result.append(new_tree)
            result_hashes.add(new_tree.structural_hash())

    graph = graph or GrammarGraph.from_grammar(non_canonical(grammar))
    current_path = ()

    while current_path is not None:
        # Note: This can produce max_num_solutions * (number of insertion strategies) many solutions,
        # but, we do not divide the solution "slots" since different solutions are interesting for
        # different problems.
        num_solutions = (
            None
            if max_num_solutions is None
            else max(0, max_num_solutions - len(result))
        )
        if num_solutions is not None and num_solutions <= 0:
            break

        if methods & DIRECT_EMBEDDING:
            add_to_result(
                compute_direct_embeddings(tree, in_tree, grammar, graph, num_solutions)
            )
        if methods & SELF_EMBEDDING:
            add_to_result(
                compute_self_embeddings(
                    current_path, tree, in_tree, grammar, graph, num_solutions
                )
            )

        # NOTE: "Context addition" has been deactivated, since it leads to a loss of subtrees:
        #       a compatible subtree is replaced, and the lost trees shall be re-inserted into
        #       the arising tree. This re-insertion failed (see, e.g., test case test_insert_lang_3),
        #       i.e., it produced an output not containing the root of the tree that should be
        #       re-inserted. We could try to fix this behavior, or simply remove the context addition
        #       part. Insertion by embedding is, in any case, non-destructive.
        # NOTE: Context addition is needed for XML and possibly other "nested" languages.
        if methods & CONTEXT_ADDITION:
            add_to_result(
                compute_context_additions(
                    current_path, tree, in_tree, grammar, graph, num_solutions
                )
            )

        current_path = in_tree.next_path(current_path)

    return result


def compute_context_additions(
    current_path: Path,
    tree: DerivationTree,
    in_tree: DerivationTree,
    grammar: CanonicalGrammar,
    graph: GrammarGraph,
    max_num_solutions: Optional[int],
) -> List[DerivationTree]:
    curr_tree = in_tree.get_subtree(current_path)

    if curr_tree.value != tree.value:
        return []

    into_tree = in_tree.replace_path(current_path, tree)

    # We have to make sure that all building blocks of in_tree occur in the result.
    # Thus, we collect all sibling trees of curr_tree, such that all leaves are retained.
    all_in_tree_subtrees: Dict[Path, DerivationTree] = {current_path: curr_tree}
    for path, tree in in_tree.paths():
        if (
            path
            and not any(
                p == path or is_prefix(p, path) or is_prefix(path, p)
                for p in all_in_tree_subtrees
            )
            and tree.id not in [t.id for _, t in into_tree.paths()]
        ):
            all_in_tree_subtrees[path] = tree

    # TODO: Could also go for reachable instead direct match
    result = insert_trees(
        list(all_in_tree_subtrees.values()),
        into_tree,
        grammar,
        graph,
        max_num_solutions,
    )

    # TODO: Rather than applying the filtering below, we should fix the `insert_trees`
    #       method to *really* insert all trees. The re-insertion failed (see, e.g.,
    #       test case test_insert_lang_3), i.e., it produced an output not containing
    #       the root of the tree that should be re-inserted. Yet, for time reasons I
    #       resorted to this hacky solution. (DS)
    return [
        tree
        for tree in result
        if (
            all(
                tree.find_node(inserted_tree) is not None
                for inserted_tree in all_in_tree_subtrees.values()
            )
            and tree.find_node(into_tree) is not None
        )
        and all(tree.find_node(node.id) is not None for _, node in in_tree.paths())
    ]


def compute_self_embeddings(
    current_path: Path,
    tree: DerivationTree,
    in_tree: DerivationTree,
    grammar: CanonicalGrammar,
    graph: GrammarGraph,
    max_num_solutions: Optional[int],
) -> List[DerivationTree]:
    # We try a self-embedding: embed the current node into a tree starting
    # with the same nonterminal, such that `tree` can be added somewhere before
    # the place where `current_tree` is added.
    curr_tree = in_tree.get_subtree(current_path)
    curr_node = curr_tree.value

    if (
        not isinstance(curr_node, str)
        or not is_nonterminal(curr_node)
        or not graph.reachable(graph.get_node(curr_node), graph.get_node(curr_node))
    ):
        return []

    results: Dict[int, DerivationTree] = {}

    self_embedding_trees = [
        self_embedding_tree
        for self_embedding_path in paths_between(graph, curr_node, curr_node)
        for self_embedding_tree in path_to_tree(grammar, self_embedding_path)
    ]

    assert all(t.has_unique_ids() for t in self_embedding_trees)
    assert curr_tree.has_unique_ids()
    assert tree.has_unique_ids()

    instantiated_self_embedding_trees: List[DerivationTree] = [
        insert_result
        for self_embedding_tree in self_embedding_trees
        for insert_result in insert_trees(
            [curr_tree, tree], self_embedding_tree, grammar, graph, max_num_solutions
        )
    ]

    for instantiated_tree in instantiated_self_embedding_trees:
        assert graph.tree_is_valid(instantiated_tree)

        if len(results) >= (max_num_solutions or sys.maxsize):
            break

        assert instantiated_tree.has_unique_ids()

        orig_node = in_tree.get_subtree(current_path)
        assert instantiated_tree.value == orig_node.value
        # instantiated_tree.id = orig_node.id
        assert instantiated_tree.has_unique_ids()

        new_tree = in_tree.replace_path(current_path, instantiated_tree)
        assert graph.tree_is_valid(new_tree)

        # new_tree = DerivationTree(new_tree.value, new_tree.children)
        # assert graph.tree_is_valid(new_tree.to_parse_tree())
        assert new_tree.has_unique_ids()

        assert all(
            new_tree.find_node(node.id) is not None for _, node in in_tree.paths()
        )

        results[new_tree.structural_hash()] = new_tree

    return list(results.values())


def compute_direct_embeddings(
    tree: DerivationTree,
    in_tree: DerivationTree,
    grammar: CanonicalGrammar,
    graph: GrammarGraph,
    max_num_solutions: Optional[int],
) -> List[DerivationTree]:
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

    results: Dict[int, DerivationTree] = {}
    for match_path_embeddable, match_tree in embeddable_matches:
        if len(results) >= (max_num_solutions or sys.maxsize):
            break

        t = wrap_in_tree_starting_in(
            match_tree.root_nonterminal(), tree, grammar, graph
        )
        orig_node = in_tree.get_subtree(match_path_embeddable)
        assert t.value == orig_node.value
        new_tree = in_tree.replace_path(
            match_path_embeddable,
            DerivationTree(t.value, t.children, orig_node.id),
            retain_id=True,
        )
        assert all(
            new_tree.find_node(node.id) is not None for _, node in in_tree.paths()
        )
        results[new_tree.structural_hash()] = new_tree

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

    return list(results.values())


def children_with_at_most_one_parent(tree: DerivationTree) -> List[DerivationTree]:
    result: List[DerivationTree] = [tree]

    curr_tree = tree
    while curr_tree.children and len(curr_tree.children) < 2:
        curr_tree = curr_tree.children[0]
        result.append(curr_tree)

    return result


def insert_trees(
    trees_to_insert: List[DerivationTree],
    into_tree: DerivationTree,
    grammar: CanonicalGrammar,
    graph: GrammarGraph,
    max_num_solutions: Optional[int],
) -> List[DerivationTree]:
    assert into_tree.has_unique_ids()
    assert all(tree.has_unique_ids() for tree in trees_to_insert)
    if assertions_activated():
        ids_in_tree_to_insert = {
            t.id for tree in trees_to_insert for _, t in tree.filter(lambda _: True)
        }
        ids_in_into_tree = {t.id for _, t in into_tree.filter(lambda _: True)}
        assert ids_in_tree_to_insert.isdisjoint(ids_in_into_tree)

    possible_insertion_points: Dict[DerivationTree, List[Path]] = {
        tree: [
            path
            for path, subtree in into_tree.leaves()
            if any(
                subtree.value == insert_tree_subtree.value
                or (
                    is_nonterminal(subtree.value)
                    and is_nonterminal(insert_tree_subtree.value)
                    and graph.reachable(subtree.value, insert_tree_subtree.value)
                )
                for insert_tree_subtree in children_with_at_most_one_parent(tree)
            )
        ]
        for tree in trees_to_insert
    }
    possible_insertion_points = {
        t: l for t, l in possible_insertion_points.items() if l
    }

    all_combinations: List[Dict[DerivationTree, Path]] = dict_of_lists_to_list_of_dicts(
        possible_insertion_points
    )

    possible_combinations: List[Dict[DerivationTree, Path]] = [
        combination
        for combination in all_combinations
        if combination
        and all(
            idx_1 == idx_2
            or (
                path_1 != path_2
                and not is_prefix(path_1, path_2)
                and not is_prefix(path_2, path_1)
            )
            for idx_1, path_1 in enumerate(combination.values())
            for idx_2, path_2 in enumerate(combination.values())
        )
    ]

    result: List[DerivationTree] = []
    for combination in possible_combinations:
        if len(result) >= (max_num_solutions or sys.maxsize):
            return result

        result_trees = [into_tree]

        tree: DerivationTree
        insertion_path: Path
        for tree, insertion_path in combination.items():
            new_result_trees = []
            while result_trees:
                result_tree = result_trees.pop()

                insertion_point_tree = result_tree.get_subtree(insertion_path)
                if insertion_point_tree.value == tree.value:
                    new_tree = result_tree.replace_path(insertion_path, tree)
                    assert graph.tree_is_valid(new_tree)
                    assert new_tree.has_unique_ids()
                    assert all(
                        new_tree.find_node(node.id) is not None
                        for _, node in tree.paths()
                    )

                    new_result_trees.append(new_tree)
                    continue

                single_parent_tree_children = [
                    t
                    for t in children_with_at_most_one_parent(tree)
                    if is_nonterminal(t.value)
                ]

                # for subtree in [t for t in single_parent_tree_children if t.value == insertion_point_tree.value]:
                #     # NOTE: Here, IDs from `tree` might get lost, since we extract subtrees
                #     #       and place them in insert_tree!
                #     new_tree = result_tree.replace_path(insertion_path, subtree)
                #     assert new_tree.has_unique_ids()
                #     assert graph.tree_is_valid(new_tree.to_parse_tree())
                #     assert all(new_tree.find_node(node.id) is not None for _, node in tree.paths())
                #     new_result_trees.append(new_tree)

                insertion_points: Dict[Path, DerivationTree] = {
                    insertion_path: insertion_point_tree
                }

                insertion_points.update(
                    find_higher_up_insertion_points(
                        result_tree,
                        insertion_path,
                        single_parent_tree_children,
                        graph,
                    )
                )

                # (DS): To consider: Should we consider all such subtrees? Seems to work with one, though...
                subtree = next(
                    t for t in single_parent_tree_children if is_nonterminal(t.value)
                )
                new_result_trees.extend(
                    connect_trees(
                        subtree, result_tree, insertion_points, grammar, graph
                    )
                )

            result_trees.extend(new_result_trees)

        result.extend(result_trees)

    return result


def find_higher_up_insertion_points(
    tree: DerivationTree,
    insertion_path: Path,
    single_parent_tree_children: List[DerivationTree],
    graph: GrammarGraph,
) -> Dict[Path, DerivationTree]:
    result: Dict[Path, DerivationTree] = {}

    for subtree in single_parent_tree_children:
        # We might have to insert subtree some steps higher up in the hierarchy.
        # Example Scriptsize-C: If we insert a <declaration> at a <statement> node,
        # we need a complex connection, but if there is a <block_statement> node
        # above the <statement>, we can directly insert the <declaration> below.
        p = insertion_path
        while p:
            p = p[:-1]

            if len(tree.get_subtree(p).children or []) > 1:
                return result

            if tree.get_subtree(p).value == subtree.value:
                continue

            if graph.reachable(tree.get_subtree(p).value, subtree.value):
                result[p] = tree.get_subtree(p)

    return result


def connect_trees(
    tree_to_add: DerivationTree,
    parent_tree: DerivationTree,
    insertion_points: Dict[Path, DerivationTree],
    canonical_grammar: CanonicalGrammar,
    graph: GrammarGraph,
) -> List[DerivationTree]:
    result: List[DerivationTree] = []
    for connecting_tree, insert_leaf_path, insertion_path in (
        (connecting_tree, insert_leaf_path, insertion_path)
        for insertion_path, insertion_point_tree in insertion_points.items()
        if is_nonterminal(insertion_point_tree.value)
        for connecting_path in paths_between(
            graph, insertion_point_tree.value, tree_to_add.value
        )
        for connecting_tree in path_to_tree(canonical_grammar, connecting_path)
        for insert_leaf_path, (
            insert_leaf_nonterm,
            _,
        ) in connecting_tree.open_leaves()
        if insert_leaf_nonterm == tree_to_add.value
    ):
        # We have to preserve the ID of the original node at that path.
        connecting_tree_with_orig_leaf_id = DerivationTree(
            connecting_tree.value,
            connecting_tree.children,
            parent_tree.get_subtree(insertion_path).id,
        )
        assert connecting_tree_with_orig_leaf_id.has_unique_ids()

        instantiated_connecting_tree = connecting_tree_with_orig_leaf_id.replace_path(
            insert_leaf_path, tree_to_add
        )
        assert instantiated_connecting_tree.has_unique_ids()

        new_tree = parent_tree.replace_path(
            insertion_path, instantiated_connecting_tree
        )
        assert new_tree.has_unique_ids()
        assert graph.tree_is_valid(new_tree)
        result.append(new_tree)
        continue
    else:
        # Inserting bigger subtrees is better (retains more identifiers that might
        # be referred in formulas), so we stop after the first successfully inserted subtree.
        return result


def shrink_tree(tree: DerivationTree) -> DerivationTree:
    node, children = tree

    if type(node) is str and not is_nonterminal(node):
        return tree

    contains_constant = False
    for _, subtree in tree.paths():
        if isinstance(subtree.value, language.Constant):
            contains_constant = True
            break

    if contains_constant:
        return DerivationTree(
            node,
            None if children is None else [shrink_tree(child) for child in children],
        )
    else:
        return DerivationTree(node, None)


def wrap_in_tree_starting_in(
    start_nonterminal: str,
    tree: DerivationTree,
    grammar: CanonicalGrammar,
    graph: GrammarGraph,
) -> DerivationTree:
    start_node = graph.get_node(start_nonterminal)
    end_node = graph.get_node(tree.root_nonterminal())
    parse_tree = tree.to_parse_tree()
    assert graph.reachable(start_node, end_node)

    derivation_path = [
        n.symbol for n in graph.shortest_non_trivial_path(start_node, end_node)
    ]

    # We work with raw parse trees here since DerivationTree objects are immutable
    result_pt: ParseTree = (start_nonterminal, [])
    curr_tree: ParseTree = result_pt
    for path_idx in range(len(derivation_path) - 1):
        path_nonterminal = derivation_path[path_idx]
        next_nonterminal = derivation_path[path_idx + 1]
        alternatives_for_path_nonterminal = [
            a for a in grammar[path_nonterminal] if next_nonterminal in a
        ]
        shortest_alt_for_path_nonterminal = [
            a
            for a in alternatives_for_path_nonterminal
            if not any(
                a_ for a_ in alternatives_for_path_nonterminal if len(a_) < len(a)
            )
        ][0]
        idx_of_next_nonterminal = shortest_alt_for_path_nonterminal.index(
            next_nonterminal
        )

        for alt_idx, alt_symbol in enumerate(shortest_alt_for_path_nonterminal):
            if alt_idx == idx_of_next_nonterminal:
                if path_idx == len(derivation_path) - 2:
                    curr_tree[1].append(parse_tree)
                else:
                    curr_tree[1].append((alt_symbol, []))
            else:
                curr_tree[1].append(
                    (alt_symbol, None if is_nonterminal(alt_symbol) else [])
                )

        curr_tree = curr_tree[1][idx_of_next_nonterminal]

    result = DerivationTree.from_parse_tree(result_pt)

    # Ensure ID is correct
    for path, t in path_iterator(result_pt):
        if t is parse_tree:
            result = result.replace_path(path, tree)
            break

    return result


def path_to_tree(
    grammar: CanonicalGrammar, path: Union[Tuple[str], List[str]]
) -> List[DerivationTree]:
    assert len(path) > 1
    result: List[DerivationTree] = []
    candidates: List[DerivationTree] = [DerivationTree(path[0], None)]
    path = path[1:]

    while path:
        next_nonterminal = path[0]
        for _ in range(len(candidates)):
            candidate = candidates.pop(0)
            leaf_path, (leaf_node, _) = next(candidate.open_leaves())
            matching_expansions = [
                expansion
                for expansion in grammar[leaf_node]
                if next_nonterminal in expansion
            ]
            if not matching_expansions:
                continue
            for matching_expansion in matching_expansions:
                nonterminal_positions = [
                    i for i, x in enumerate(matching_expansion) if x == next_nonterminal
                ]
                for nonterminal_position in nonterminal_positions:
                    next_children = [
                        DerivationTree(nonterm, [])
                        if idx != nonterminal_position
                        else DerivationTree(nonterm, None)
                        for idx, nonterm in enumerate(matching_expansion)
                    ]

                    new_candidate = candidate.replace_path(
                        leaf_path, DerivationTree(leaf_node, next_children)
                    )

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

    return DerivationTree(
        tree.value, [make_leaves_open(child) for child in tree.children], tree.id
    )


@lru_cache(maxsize=None)
def paths_between(
    graph: GrammarGraph, start: str, dest: str
) -> OrderedSet[Tuple[str, ...]]:
    start_node = graph.get_node(start)
    dest_node = graph.get_node(dest)

    assert isinstance(start_node, NonterminalNode)

    prefixes: List[Tuple[Set[Node], List[Node]]] = [
        (
            set()
            if start_node == dest_node and graph.reachable(start_node, start_node)
            else {start_node},
            [start_node],
        )
    ]
    result: OrderedSet[Tuple[str, ...]] = OrderedSet([])

    while prefixes:
        visited, prefix = prefixes.pop()
        assert isinstance(prefix[-1], NonterminalNode)
        for child in cast(NonterminalNode, prefix[-1]).children:
            if child not in visited:
                new_path = prefix + [child]
                if child == dest_node:
                    s_path = tuple(
                        [n.symbol for n in new_path if type(n) is not ChoiceNode]
                    )
                    if s_path not in result:
                        result.add(s_path)
                        # yield s_path
                elif isinstance(child, NonterminalNode):
                    prefixes.append((visited | {child}, new_path))

    return result
