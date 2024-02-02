from typing import Iterator, Tuple, Iterable

import more_itertools
from frozendict import frozendict
from grammar_graph.gg import GrammarGraph, Node, ChoiceNode, NonterminalNode
from returns.maybe import Nothing, Maybe, Some

from isla.derivation_tree import DerivationTree
from isla.helpers import (
    is_nonterminal,
    canonical,
    frozen_canonical,
    assertions_activated,
    deep_str,
)
from isla.type_defs import Path, FrozenCanonicalGrammar


def validate_insertion_result(
    graph: GrammarGraph,
    original_tree: DerivationTree,
    inserted_tree: DerivationTree,
    result_tree: DerivationTree,
    paths_to_ignore_in_inserted_tree: Iterable[Path] = (),
) -> None:
    """
    This function validates a tree insertion result. In particular, it asserts that

    - all identifiers in :code:`original_tree` are retained;
    - all identifiers in :code:`inserted tree`, except those in :code:`paths_to_ignore_in_inserted_tree`;
    - the constructed tree is valid.

    :param graph: The grammar graph.
    :param original_tree: The original tree.
    :param inserted_tree: The tree to insert.
    :param result_tree: The resulting tree.
    :param paths_to_ignore_in_inserted_tree: Paths in the inserted tree that should
        be ignored when checking whether all identifiers are retained.
    :return: Nothing (but yields an AssertionError if assertions are activated and
        an assumption is not met).
    """

    if not assertions_activated():
        return

    result_ids = {node.id for _, node in result_tree.paths()}
    orig_ids = {node.id for _, node in original_tree.paths()}
    inserted_tree_ids = {
        node.id
        for path, node in inserted_tree.paths()
        if path not in paths_to_ignore_in_inserted_tree
    }

    node_diff = tuple(
        (
            original_tree.get_subtree(original_tree.find_node(tid)).value,
            tid,
        )
        for tid in orig_ids.difference(result_ids)
    )
    assert orig_ids.issubset(result_ids), (
        f"The node(s) {node_diff} from the "
        f"original tree are not contained in the identifier set from "
        f"the resulting tree."
    )

    node_diff = tuple(
        (
            inserted_tree.get_subtree(inserted_tree.find_node(tid)).value,
            tid,
        )
        for tid in inserted_tree_ids.difference(result_ids)
    )
    assert inserted_tree_ids.issubset(result_ids), (
        f"The node(s) {node_diff} from the "
        f"inserted tree are not contained in the identifier set from "
        f"the resulting tree."
    )

    assert graph.tree_is_valid(result_tree)


def graph_path_to_tree(
    graph_path: Tuple[Node, ...],
    graph: GrammarGraph,
    maybe_canonical_grammar: Maybe[FrozenCanonicalGrammar] = Nothing,
) -> Tuple[DerivationTree, Path]:
    """
    Returns a tuple of a derivation tree and a path, where the path corresponds to
    the given grammar graph path.

    Example
    -------

    >>> import string
    >>> grammar = frozendict({
    ...     "<start>": ("<stmt>",),
    ...     "<stmt>": ("<assgn> ; <stmt>", "<assgn>"),
    ...     "<assgn>": ("<var> := <rhs>",),
    ...     "<rhs>": ("<var>", "<digit>"),
    ...     "<var>": tuple(string.ascii_lowercase),
    ...     "<digit>": tuple(string.digits),
    ... })
    >>> graph = GrammarGraph.from_grammar(grammar)

    >>> resulting_tree, path_to_end = connect_nonterminals("<stmt>", "<var>", graph)

    >>> graph_path: Tuple[Node, ...] = tuple(
    ...     graph.shortest_path(
    ...         graph.get_node("<stmt>"),
    ...         graph.get_node("<var>"),
    ...         nodes_filter=None,
    ...     )
    ... )

    >>> resulting_tree, path_to_end = graph_path_to_tree(graph_path, graph)

    >>> graph.tree_is_valid(resulting_tree)
    True

    >>> print(resulting_tree)
    <var> := <rhs> ; <stmt>

    >>> print(resulting_tree.value)
    <stmt>

    >>> print(resulting_tree.get_subtree(path_to_end))
    <var>

    Let us have a look at the path connecting a :code:`<assgn>` node with a
    :code:`<var>` node on the right-hand side:

    >>> graph_path: Tuple[Node, ...] = tuple(
    ...     tuple(
    ...         graph.all_paths(
    ...             graph.get_node("<assgn>"),
    ...             {graph.get_node("<var>")}
    ...         )
    ...     )[1]
    ... )

    >>> resulting_tree, path_to_end = graph_path_to_tree(graph_path, graph)

    >>> graph.tree_is_valid(resulting_tree)
    True

    >>> print(resulting_tree)
    <var> := <var>

    >>> print(resulting_tree.value)
    <assgn>

    >>> print(path_to_end)
    (2, 0)

    >>> print(resulting_tree.get_subtree(path_to_end))
    <var>

    :param graph_path: The path in the grammar graph to turn into a tree.
    :param graph: The grammar graph.
    :param maybe_canonical_grammar: The canonical version of the grammar represented
        by :code:`graph`. If :code:`Nothing`, the canonical grammar is computed
        from :code:`graph` (with the according potential overhead).
    :return: A pair of a derivation tree and a path in that tree, such that the path
        corresponds to the given grammar graph path.
    """

    canonical_grammar = maybe_canonical_grammar.value_or(canonical(graph.grammar))
    start = graph_path[0].symbol
    end = graph_path[-1].symbol

    resulting_tree: DerivationTree = DerivationTree(start)
    path_to_end: Path = ()
    current_node: DerivationTree = resulting_tree

    for idx_of_symbolic_node_in_graph_path, (symbolic_node, choice_node) in enumerate(
        more_itertools.grouper(graph_path, n=2, incomplete="fill", fillvalue=None)
    ):
        symbolic_node: NonterminalNode | NonterminalNode
        choice_node: ChoiceNode

        # The index is incremented once for each *pair,* so we must multiply by two
        # to obtain the actual index of the symbolic node.
        idx_of_symbolic_node_in_graph_path *= 2

        assert graph_path[idx_of_symbolic_node_in_graph_path] == symbolic_node
        assert resulting_tree.get_subtree(path_to_end).value == symbolic_node.symbol
        assert current_node.value == symbolic_node.symbol
        assert (
            choice_node is not None
            or resulting_tree.get_subtree(path_to_end).value == end
        )

        if not choice_node:
            break

        # NOTE: We build upon the convention that choice node symbols are of the form
        #       <symbol>-<expansion_idx>, where <expansion_idx> is the index of the
        #       expansion in the grammar. This structure should be made explicit by
        #       a numeric index in ChoiceNode objects.
        expansion_idx = int(choice_node.symbol[choice_node.symbol.rfind("-") + 1 :]) - 1
        expansion = canonical_grammar[symbolic_node.symbol][expansion_idx]

        new_children = tuple(
            DerivationTree(symbol, None if is_nonterminal(symbol) else ())
            for symbol in expansion
        )

        resulting_tree = resulting_tree.replace_path(
            path_to_end, DerivationTree(current_node.value, new_children)
        )
        assert graph.tree_is_valid(resulting_tree)

        # To determine the next path element, we must choose the index of the next
        # node in the graph path in the children of the current choice node.
        # TODO: This can fail since the grammar graph library currently does not
        #       distinguish several occurrences of the same nonterminal node, as
        #       does the original algorithm by Havrikov. Thus, if a nonterminal
        #       occurs more than once in an expansion, we might pick the wrong
        #       index unless we implement some backtracking or lookahead.
        #       We should fix the grammar graph library eventually.
        assert len(graph_path) > idx_of_symbolic_node_in_graph_path + 2
        index_in_expansion = choice_node.children.index(
            graph_path[idx_of_symbolic_node_in_graph_path + 2]
        )
        current_node = new_children[index_in_expansion]

        path_to_end += (index_in_expansion,)

    assert resulting_tree.value == start
    assert resulting_tree.get_subtree(path_to_end).value == end
    assert (
        not is_nonterminal(end)
        or resulting_tree.get_subtree(path_to_end).children is None
    )

    return resulting_tree, path_to_end


def connect_nonterminals(
    start: str,
    end: str,
    graph: GrammarGraph,
    maybe_canonical_grammar: Maybe[FrozenCanonicalGrammar] = Nothing,
) -> Tuple[DerivationTree, Path]:
    """
    Returns a tuple of a derivation tree and a path, such that the root of the tree
    has the value of the symbol :code:`start` and the leaf of the tree at the path
    has the value of the symbol :code:`end`. The tree path between those two nodes
    is a shortest path between the symbols. If :code:`start` and :code:`end` are
    the same symbol, the tree is a single node.

    Example
    -------

    >>> import string
    >>> grammar = frozendict({
    ...     "<start>": ("<stmt>",),
    ...     "<stmt>": ("<assgn> ; <stmt>", "<assgn>"),
    ...     "<assgn>": ("<var> := <rhs>",),
    ...     "<rhs>": ("<var>", "<digit>"),
    ...     "<var>": tuple(string.ascii_lowercase),
    ...     "<digit>": tuple(string.digits),
    ... })
    >>> graph = GrammarGraph.from_grammar(grammar)

    >>> resulting_tree, path_to_end = connect_nonterminals("<stmt>", "<var>", graph)

    >>> print(resulting_tree)
    <var> := <rhs> ; <stmt>

    >>> print(resulting_tree.value)
    <stmt>

    >>> print(resulting_tree.get_subtree(path_to_end))
    <var>

    We obtain a single node if the start and end symbols are the same:

    >>> resulting_tree, path_to_end = connect_nonterminals("<stmt>", "<stmt>", graph)
    >>> print(resulting_tree)
    <stmt>

    :param start: The start symbol.
    :param end: The end symbol.
    :param graph: The grammar graph.
    :param maybe_canonical_grammar: The canonical version of the grammar represented
        by :code:`graph`. If :code:`Nothing`, the canonical grammar is computed
        from :code:`graph` (with the according potential overhead).
    :return: A pair of a derivation tree starting at :code:`start` and a path to a
        node in that tree labeled with :code:`end`.
    """

    assert start == end or graph.reachable(
        start, end
    ), f"{end} is not reachable from {start}"

    start_node = graph.get_node(start)
    end_node = graph.get_node(end)

    shortest_graph_path: Tuple[Node, ...] = (
        tuple(graph.shortest_path(start_node, end_node, nodes_filter=None))
        if start != end
        else ()
    )

    if not shortest_graph_path:
        # Start and end symbols are the same, so we return a trivial connecting tree.
        return DerivationTree(start, None), ()

    return graph_path_to_tree(shortest_graph_path, graph, maybe_canonical_grammar)


def insert_tree_into_hole(
    original_tree: DerivationTree,
    tree_to_insert: DerivationTree,
    graph: GrammarGraph,
    maybe_canonical_grammar: Maybe[FrozenCanonicalGrammar] = Nothing,
) -> Iterator[Tuple[DerivationTree, Path]]:
    """
    This tree insertion method inserts :code:`tree_to_insert` into :code:`original_tree`
    by using an existing "hole" in :code:`original_tree`, i.e., an open leaf node.
    If possible, we append the children of :code:`tree_to_insert` to :code:`original_tree`;
    otherwise, we generate a suitable connecting tree.

    Example
    -------

    >>> import string
    >>> grammar = frozendict({
    ...     "<start>": ("<stmt>",),
    ...     "<stmt>": ("<assgn> ; <stmt>", "<assgn>"),
    ...     "<assgn>": ("<var> := <rhs>",),
    ...     "<rhs>": ("<var>", "<digit>"),
    ...     "<var>": tuple(string.ascii_lowercase),
    ...     "<digit>": tuple(string.digits),
    ... })
    >>> graph = GrammarGraph.from_grammar(grammar)

    >>> pre_original_inp = 'a := 1 ; b := x ; c := 3'

    >>> from isla.parser import EarleyParser
    >>> pre_original_tree = DerivationTree.from_parse_tree(
    ...     next(EarleyParser(grammar).parse(pre_original_inp))
    ... )
    >>> original_tree = pre_original_tree.replace_path((0, 0), DerivationTree("<assgn>", None))
    >>> print(original_tree)
    <assgn> ; b := x ; c := 3

    >>> declaration = DerivationTree.from_parse_tree(
    ...     ("<assgn>", [
    ...         ("<var>", [("x", [])]),
    ...         (" := ", []),
    ...         ("<rhs>", None),
    ...     ])
    ... )

    >>> print(deep_str(list(insert_tree_into_hole(
    ...     original_tree, declaration, graph
    ... ))))
    [(x := <rhs> ; b := x ; c := 3, (0, 0))]

    In the following case, we need a connecting tree:

    >>> original_tree = pre_original_tree.replace_path((0, 2, 2), DerivationTree("<stmt>", None))
    >>> print(original_tree)
    a := 1 ; b := x ; <stmt>

    >>> declaration = DerivationTree.from_parse_tree(
    ...     ("<assgn>", [
    ...         ("<var>", [("x", [])]),
    ...         (" := ", []),
    ...         ("<rhs>", None),
    ...     ])
    ... )

    If we considered the shortest path only, we would exclusively obtain
    the first one of the results displayed below, which is not minimal.

    >>> for result in insert_tree_into_hole(
    ...     original_tree, declaration, graph
    ... ):
    ...     print(deep_str(result))
    (a := 1 ; b := x ; x := <rhs> ; <stmt>, (0, 2, 2, 0))
    (a := 1 ; b := x ; x := <rhs>, (0, 2, 2, 0))

    :param original_tree: The original tree into which to insert :code:`tree_to_insert`.
    :param tree_to_insert: The tree to insert.
    :param graph: The graph of the underlying reference grammar.
    :param maybe_canonical_grammar: The canonical version of the grammar represented
        by :code:`graph`. If :code:`Nothing`, the canonical grammar is computed
        from :code:`graph` (with the according potential overhead).
    :return: Pairs of derivation trees resulting from the insertion and paths pointing
        to the position of the inserted tree in those resulting trees.
    """

    for path_to_hole, hole in original_tree.open_leaves():
        if hole.value == tree_to_insert.value:
            result = original_tree.replace_path(
                path_to_hole,
                DerivationTree(tree_to_insert.value, tree_to_insert.children, hole.id),
            )

            # The root of the inserted tree is "lost" in the result, so we set
            # `paths_to_ignore_in_inserted_tree` correspondingly.
            validate_insertion_result(
                graph, original_tree, tree_to_insert, result, ((),)
            )
            yield result, path_to_hole

        if graph.reachable(hole.value, tree_to_insert.value):
            # We consider all paths and not just the shortest one, since we want to
            # find all possible insertions. This is necessary since the shortest path
            # might not be the one that we want to use for the insertion (see the
            # example in the docstring).
            for graph_path in graph.all_paths(
                graph.get_node(hole.value), {graph.get_node(tree_to_insert.value)}
            ):
                (
                    connecting_tree,
                    path_in_connecting_tree_to_tree_to_insert,
                ) = graph_path_to_tree(
                    tuple(graph_path), graph, maybe_canonical_grammar
                )

                connecting_tree = DerivationTree(
                    hole.value,
                    connecting_tree.children,
                    hole.id,
                )

                connecting_tree = connecting_tree.replace_path(
                    path_in_connecting_tree_to_tree_to_insert, tree_to_insert
                )

                result = original_tree.replace_path(path_to_hole, connecting_tree)
                path_to_tree_to_insert = (
                    path_to_hole + path_in_connecting_tree_to_tree_to_insert
                )

                validate_insertion_result(graph, original_tree, tree_to_insert, result)
                yield result, path_to_tree_to_insert


def insert_tree_by_self_embedding(
    original_tree: DerivationTree,
    tree_to_insert: DerivationTree,
    graph: GrammarGraph,
    maybe_canonical_grammar: Maybe[FrozenCanonicalGrammar] = Nothing,
) -> Iterator[Tuple[DerivationTree, Path]]:
    """
    The self embedding method embeds :code:`tree_to_insert` into :code:`original_tree`
    by finding a node in :code:`original_tree` whose label can reach itself in the
    grammar graph in such a way that :code:`tree_to_insert` can be embedded in the
    such expanded tree.

    More precisely, we aim to find a node :code:`node` in :code:`original_tree` such
    that there is a connection `|*` enabling the following outcome::

                <start>
               /   |   \
                 node'
             /    |*    \
                node  tree_to_insert

    where :code:`node'` is a new node with the same label as :code:`node`.

    All identifiers from the passed trees are preserved in the results.

    Example
    -------

    >>> import string
    >>> grammar = frozendict({
    ...     "<start>": ("<stmt>",),
    ...     "<stmt>": ("<assgn> ; <stmt>", "<assgn>"),
    ...     "<assgn>": ("<var> := <rhs>",),
    ...     "<rhs>": ("<var>", "<digit>"),
    ...     "<var>": tuple(string.ascii_lowercase),
    ...     "<digit>": tuple(string.digits),
    ... })
    >>> graph = GrammarGraph.from_grammar(grammar)

    >>> original_inp = 'a := 1 ; b := x ; c := 3'

    >>> from isla.parser import EarleyParser
    >>> original_tree = DerivationTree.from_parse_tree(
    ...     next(EarleyParser(grammar).parse(original_inp))
    ... )

    >>> declaration = DerivationTree.from_parse_tree(
    ...     ("<assgn>", [
    ...         ("<var>", [("x", [])]),
    ...         (" := ", []),
    ...         ("<rhs>", None),
    ...     ])
    ... )

    >>> for result in insert_tree_by_self_embedding(
    ...     original_tree, declaration, graph
    ... ):
    ...    print(deep_str(result))
    (x := <rhs> ; a := 1 ; b := x ; c := 3, (0, 0))
    (a := 1 ; x := <rhs> ; b := x ; c := 3, (0, 2, 0))
    (a := 1 ; b := x ; x := <rhs> ; c := 3, (0, 2, 2, 0))

    >>> new_variable_node = DerivationTree("<var>")
    >>> for result in insert_tree_by_self_embedding(
    ...     original_tree, new_variable_node, graph
    ... ):
    ...    print(deep_str(result))
    (<var> := <rhs> ; a := 1 ; b := x ; c := 3, (0, 0, 0))
    (<var> := <var> ; a := 1 ; b := x ; c := 3, (0, 0, 2, 0))
    (a := 1 ; <var> := <rhs> ; b := x ; c := 3, (0, 2, 0, 0))
    (a := 1 ; <var> := <var> ; b := x ; c := 3, (0, 2, 0, 2, 0))
    (a := 1 ; b := x ; <var> := <rhs> ; c := 3, (0, 2, 2, 0, 0))
    (a := 1 ; b := x ; <var> := <var> ; c := 3, (0, 2, 2, 0, 2, 0))

    :param original_tree: The original tree into which to insert :code:`tree_to_insert`
        using the self embedding method.
    :param tree_to_insert: The tree to insert.
    :param graph: The graph of the underlying reference grammar.
    :param maybe_canonical_grammar: The canonical version of the grammar represented
        by :code:`graph`. If :code:`Nothing`, the canonical grammar is computed
        from :code:`graph` (with the according potential overhead).
    :return: Pairs of derivation trees resulting from the insertion and paths pointing
        to the position of the inserted tree in those resulting trees.
    """

    for node_path, node in original_tree.paths():
        if not is_nonterminal(node.value):
            continue

        graph_node = graph.get_node(node.value)
        for graph_path in graph.all_paths(graph_node, {graph_node}):
            tree_from_path, path_to_final_node = graph_path_to_tree(
                tuple(graph_path), graph, maybe_canonical_grammar
            )

            for (
                path_in_tree_from_path,
                tree_from_path_leaf,
            ) in tree_from_path.open_leaves():
                if path_in_tree_from_path == path_to_final_node:
                    continue

                if tree_from_path_leaf.value == tree_to_insert.value:
                    # We can use this tree to insert `tree_to_insert`.
                    new_subtree = tree_from_path.replace_path(
                        path_in_tree_from_path, tree_to_insert
                    ).replace_path(path_to_final_node, node)

                    result_tree = original_tree.replace_path(node_path, new_subtree)
                    path_to_inserted_tree_in_result = node_path + path_in_tree_from_path

                    validate_insertion_result(
                        graph, original_tree, tree_to_insert, result_tree
                    )
                    yield result_tree, path_to_inserted_tree_in_result

                elif graph.reachable(tree_from_path_leaf.value, tree_to_insert.value):
                    # We must use a connecting tree to insert `tree_to_insert`.
                    for connecting_graph_path in graph.all_paths(
                        graph.get_node(tree_from_path_leaf.value),
                        {graph.get_node(tree_to_insert.value)},
                    ):
                        (
                            connecting_tree_from_path,
                            path_to_final_node_in_connecting_tree,
                        ) = graph_path_to_tree(
                            tuple(connecting_graph_path), graph, maybe_canonical_grammar
                        )

                        instantiated_connecting_tree = (
                            connecting_tree_from_path.replace_path(
                                path_to_final_node_in_connecting_tree, tree_to_insert
                            )
                        )

                        new_subtree = tree_from_path.replace_path(
                            path_in_tree_from_path, instantiated_connecting_tree
                        ).replace_path(path_to_final_node, node)

                        result_tree = original_tree.replace_path(node_path, new_subtree)
                        path_to_inserted_tree_in_result = (
                            node_path
                            + path_in_tree_from_path
                            + path_to_final_node_in_connecting_tree
                        )

                        validate_insertion_result(
                            graph, original_tree, tree_to_insert, result_tree
                        )

                        yield result_tree, path_to_inserted_tree_in_result


def insert_tree_by_reverse_embedding(
    original_tree: DerivationTree,
    tree_to_insert: DerivationTree,
    graph: GrammarGraph,
    maybe_canonical_grammar: Maybe[FrozenCanonicalGrammar] = Nothing,
) -> Iterator[Tuple[DerivationTree, Path]]:
    """
    The reverse embedding method attempts to

    1. Find the first node in :code:`original_tree` that fits into a hole in
       :code:`tree_to_insert`. The tree above that node must be linear, i.e.,
       each node most have exactly one child.
    2. Adds the subtree of that node in :code:`original_tree` as a subtree of
       the hole in :code:`tree_to_insert`.
    3. Adds the resulting tree to the part of :code:`original_tree` that is above
       the node that was found in step 1.

    If there are any collisions in step 3, e.g., because both trees start with the
    :code:`<start>` nonterminal, the nodes from :code:`original_tree` are
    preferred.

    More precisely, we aim to find nodes matching the following setup::

           original_tree:        tree_to_insert:

              <start>               tti_root
                 |                 /   |   \
              parent                 hole
         orig_tree_subtree

    such that the following tree is grammatically valid (for a suitable
    instantiation of the new connecting parts `|*` between (1) parent and tti_root and
    (2) hole and orig_tree_subtree)::

             <start>
                |
             parent
                |*
            tti_root
            /   |  \
              hole
                |*
         orig_tree_subtree

    All nodes of the original tree must be preserved. If necessary, the
    root node of tree_to_insert is removed and replace by an existing
    node with the same label from the original tree.

    Example
    -------

    >>> from frozendict import frozendict
    >>> grammar = frozendict(
    ...     {
    ...         "<start>": ("<xml-tree>",),
    ...         "<xml-tree>": ("", "<xml-open-tag><xml-tree><xml-close-tag>"),
    ...         "<xml-open-tag>": ("<langle><id><attrs>>",),
    ...         "<xml-close-tag>": ("<langle>/<id>>",),
    ...         "<attrs>": ("", " <attr><attrs>"),
    ...         "<attr>": ('<id>="XXX"',),
    ...         "<id>": ("<letter>:<letter>",),
    ...         "<letter>": ("a", "b", "c", "x"),
    ...         "<langle>": ("<",),
    ...     }
    ... )


    This is our original input:

    >>> original_inp = '<b:c b:c="XXX" x:b="XXX"></b:x>'

    >>> from isla.parser import EarleyParser
    >>> original_tree = DerivationTree.from_parse_tree(
    ...     next(EarleyParser(grammar).parse(original_inp))
    ... )

    The context node to insert is :code:`<<id> <attr>><xml-tree></<id>>`:

    >>> tree_to_insert = DerivationTree.from_parse_tree(
    ...     (
    ...         "<xml-tree>",
    ...         [
    ...             (
    ...                 "<xml-open-tag>",
    ...                 [
    ...                     ("<langle>", [("<", [])]),
    ...                     ("<id>", None),
    ...                     ("<attrs>", [(" ", []), ("<attr>", None), ("<attrs>", [])]),
    ...                     (">", []),
    ...                 ],
    ...             ),
    ...             ("<xml-tree>", None),
    ...             (
    ...                 "<xml-close-tag>",
    ...                 [
    ...                     ("<langle>", [("<", [])]),
    ...                     ("/", []),
    ...                     ("<id>", None),
    ...                     (">", []),
    ...                 ],
    ...             ),
    ...         ],
    ...     )
    ... )

    There is one possible result of the insertion:

    >>> graph = GrammarGraph.from_grammar(grammar)
    >>> deep_str(list(insert_tree_by_reverse_embedding(
    ...     original_tree, tree_to_insert, graph))
    ... )
    '[(<<id> <attr>><b:c b:c="XXX" x:b="XXX"></b:x></<id>>, (0,))]'

    :param original_tree: The original tree into which to insert :code:`tree_to_insert`
        using the reverse embedding method.
    :param tree_to_insert: The tree to insert.
    :param graph: The graph of the underlying reference grammar.
    :param maybe_canonical_grammar: The canonical version of the grammar represented
        by :code:`graph`. If :code:`Nothing`, the canonical grammar is computed
        from :code:`graph` (with the according potential overhead).
    :return: Pairs of derivation trees resulting from the insertion and paths pointing
        to the position of the inserted tree in those resulting trees.
    """

    assert original_tree.value == tree_to_insert.value or graph.reachable(
        original_tree.value, tree_to_insert.value
    )

    tree_to_insert_holes: frozendict[Path, DerivationTree] = frozendict(
        tree_to_insert.open_leaves()
    )

    for orig_tree_path, orig_tree_subtree in original_tree.paths():
        parent_path: Path = () if not orig_tree_path else orig_tree_path[:-1]
        parent_node: DerivationTree = original_tree.get_subtree(parent_path)

        if (
            not is_nonterminal(orig_tree_subtree.value)
            or parent_node.value != tree_to_insert.value
            and not graph.reachable(parent_node.value, tree_to_insert.value)
        ):
            continue

        matching_holes = (
            (path, hole)
            for path, hole in tree_to_insert_holes.items()
            if (
                hole.value == orig_tree_subtree.value
                or graph.reachable(hole.value, orig_tree_subtree.value)
            )
        )

        for path_to_hole, hole in matching_holes:
            # Tree from `parent` to `tti_root`.
            (
                connecting_tree_1,
                path_in_connecting_tree_1_to_tti_root,
            ) = connect_nonterminals(
                parent_node.value, tree_to_insert.value, graph, maybe_canonical_grammar
            )

            # Retain the original identifier of `parent`.
            connecting_tree_1 = DerivationTree(
                parent_node.value,
                connecting_tree_1.children,
                parent_node.id,
            )

            # Tree from `hole` to `orig_tree_subtree`.
            (
                connecting_tree_2,
                path_in_connecting_tree_2_to_orig_tree_subtree,
            ) = connect_nonterminals(
                hole.value, orig_tree_subtree.value, graph, maybe_canonical_grammar
            )

            # Retain the original identifier of `hole`.
            connecting_tree_2 = DerivationTree(
                connecting_tree_2.value,
                connecting_tree_2.children,
                hole.id,
            )

            #       <start>
            #          |
            #       parent
            #  orig_tree_subtree
            result = original_tree

            #          <start>
            #             |
            #          parent
            #             |*
            #         tti_root*
            result = result.replace_path(parent_path, connecting_tree_1)

            #          <start>
            #             |
            #          parent
            #             |*
            #         tti_root
            #         /   |  \
            #           hole
            result = result.replace_path(
                parent_path + path_in_connecting_tree_1_to_tti_root, tree_to_insert
            )

            #          <start>
            #             |
            #          parent
            #             |*
            #         tti_root
            #         /   |  \
            #           hole
            #             |*
            #      orig_tree_subtree*
            result = result.replace_path(
                parent_path + path_in_connecting_tree_1_to_tti_root + path_to_hole,
                connecting_tree_2,
            )

            #          <start>
            #             |
            #          parent
            #             |*
            #         tti_root
            #         /   |  \
            #           hole
            #             |*
            #      orig_tree_subtree
            result = result.replace_path(
                parent_path
                + path_in_connecting_tree_1_to_tti_root
                + path_to_hole
                + path_in_connecting_tree_2_to_orig_tree_subtree,
                orig_tree_subtree,
            )

            path_to_inserted_tree = parent_path + path_in_connecting_tree_1_to_tti_root

            # In the validation, we permit the path to the hole in the inserted
            # tree to not appear in the result if the second connecting tree is
            # trivial. In that case, the hole is replaced by `orig_tree_subtree`.
            validate_insertion_result(
                graph,
                original_tree,
                tree_to_insert,
                result,
                (path_to_hole,) if len(connecting_tree_2) == 1 else (),
            )
            yield result, path_to_inserted_tree

        if len(orig_tree_subtree.children or []) > 1:
            break


def insert_tree(
    original_tree: DerivationTree,
    tree_to_insert: DerivationTree,
    graph: GrammarGraph,
    maybe_canonical_grammar: Maybe[FrozenCanonicalGrammar] = Nothing,
) -> Iterator[Tuple[DerivationTree, Path]]:
    """
    This function inserts :code:`tree_to_insert` into :code:`original_tree` in three
    possible ways using the following functions:

    1. :func:`~isla.tree_insertion.insert_tree_into_hole`
    2. :func:`~isla.tree_insertion.insert_tree_by_self_embedding`
    3. :func:`~isla.tree_insertion.insert_tree_by_reverse_embedding`

    Example
    -------

    Consider the following, simplified XML grammar:

    >>> from frozendict import frozendict
    >>> grammar = frozendict(
    ...     {
    ...         "<start>": ("<xml-tree>",),
    ...         "<xml-tree>": ("", "<xml-open-tag><xml-tree><xml-close-tag>"),
    ...         "<xml-open-tag>": ("<langle><id><attrs>>",),
    ...         "<xml-close-tag>": ("<langle>/<id>>",),
    ...         "<attrs>": ("", " <attr><attrs>"),
    ...         "<attr>": ('<id>="XXX"',),
    ...         "<id>": ("<letter>:<letter>",),
    ...         "<letter>": ("a", "b", "c", "x"),
    ...         "<langle>": ("<",),
    ...     }
    ... )

    We want to embed the following input into an additional context:

    >>> original_inp = '<b:c b:c="XXX" x:b="XXX"></b:x>'

    >>> from isla.parser import EarleyParser
    >>> original_tree = DerivationTree.from_parse_tree(
    ...     next(EarleyParser(grammar).parse(original_inp))
    ... )

    The context to insert is the abstract input :code:`<<id> <attr>><xml-tree></<id>>`:

    >>> tree_to_insert = DerivationTree.from_parse_tree(
    ...     (
    ...         "<xml-tree>",
    ...         [
    ...             (
    ...                 "<xml-open-tag>",
    ...                 [
    ...                     ("<langle>", [("<", [])]),
    ...                     ("<id>", None),
    ...                     ("<attrs>", [(" ", []), ("<attr>", None), ("<attrs>", [])]),
    ...                     (">", []),
    ...                 ],
    ...             ),
    ...             ("<xml-tree>", None),
    ...             (
    ...                 "<xml-close-tag>",
    ...                 [
    ...                     ("<langle>", [("<", [])]),
    ...                     ("/", []),
    ...                     ("<id>", None),
    ...                     (">", []),
    ...                 ],
    ...             ),
    ...         ],
    ...     )
    ... )

    In this case, the function :func:`~isla.tree_insertion.insert_tree_by_reverse_embedding`
    is the only one that can be used to insert the tree:

    >>> graph = GrammarGraph.from_grammar(grammar)
    >>> deep_str(list(insert_tree(original_tree, tree_to_insert, graph)))
    '[(<<id> <attr>><b:c b:c="XXX" x:b="XXX"></b:x></<id>>, (0,))]'

    :param original_tree: The original tree into which to insert :code:`tree_to_insert`.
    :param tree_to_insert: The tree to insert.
    :param graph: The graph of the underlying reference grammar.
    :param maybe_canonical_grammar: The canonical version of the grammar represented
        by :code:`graph`. If :code:`Nothing`, the canonical grammar is computed
        from :code:`graph` (with the according potential overhead).
    :return: Pairs of derivation trees resulting from the insertion and paths pointing
        to the position of the inserted tree in those resulting trees.
    """

    maybe_canonical_grammar = maybe_canonical_grammar.lash(
        lambda _: Some(frozen_canonical(graph.grammar))
    )

    iterators = (
        insert_tree_into_hole(
            original_tree, tree_to_insert, graph, maybe_canonical_grammar
        ),
        insert_tree_by_self_embedding(
            original_tree, tree_to_insert, graph, maybe_canonical_grammar
        ),
        insert_tree_by_reverse_embedding(
            original_tree, tree_to_insert, graph, maybe_canonical_grammar
        ),
    )

    idx = 0
    while iterators:
        try:
            yield next(iterators[idx])
        except StopIteration:
            iterators = iterators[:idx] + iterators[idx + 1 :]

        if iterators:
            idx = (idx + 1) % len(iterators)
