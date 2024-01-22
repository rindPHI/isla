from typing import Iterator, Tuple

import more_itertools
from frozendict import frozendict
from grammar_graph.gg import GrammarGraph, Node
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

    :param start: The start symbol.
    :param end: The end symbol.
    :param graph: The grammar graph.
    :param maybe_canonical_grammar: The canonical version of the grammar represented
        by :code:`graph`. If :code:`Nothing`, the canonical grammar is computed
        from :code:`graph` (with the according potential overhead).
    :return: A pair of a derivation tree starting at :code:`start` and a path to a
        node in that tree labeled with :code:`end`.
    """

    canonical_grammar = maybe_canonical_grammar.value_or(canonical(graph.grammar))

    start_node = graph.get_node(start)
    end_node = graph.get_node(end)

    assert start == end or graph.reachable(
        start, end
    ), f"{end} is not reachable from {start}"

    shortest_graph_path: Tuple[Node, ...] = (
        tuple(graph.shortest_path(start_node, end_node, nodes_filter=None))
        if start != end
        else ()
    )

    resulting_tree: DerivationTree = DerivationTree(start)
    path_to_end: Path = ()
    current_node: DerivationTree = resulting_tree

    for symbolic_node, choice_node in more_itertools.grouper(
        shortest_graph_path, n=2, incomplete="fill", fillvalue=None
    ):
        assert resulting_tree.get_subtree(path_to_end).value == symbolic_node.symbol
        assert (
            not path_to_end
            or current_node.children[path_to_end[-1]].value == symbolic_node.symbol
        )
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

        current_node = DerivationTree(current_node.value, new_children)
        resulting_tree = resulting_tree.replace_path(path_to_end, current_node)
        path_to_end += (expansion_idx,)

    assert resulting_tree.value == start
    assert resulting_tree.get_subtree(path_to_end).value == end
    assert (
        not is_nonterminal(end)
        or resulting_tree.get_subtree(path_to_end).children is None
    )

    return resulting_tree, path_to_end


def insert_tree_into_hole(
    original_tree: DerivationTree,
    tree_to_insert: DerivationTree,
    graph: GrammarGraph,
    maybe_canonical_grammar: Maybe[FrozenCanonicalGrammar] = Nothing,
) -> Iterator[Tuple[DerivationTree, Path, Path]]:
    """
    TODO: Document, test.

    :param original_tree:
    :param tree_to_insert:
    :param graph:
    :param maybe_canonical_grammar: The canonical version of the grammar represented
        by :code:`graph`. If :code:`Nothing`, the canonical grammar is computed
        from :code:`graph` (with the according potential overhead).
    :return:
    """

    yield from iter(())


def insert_tree_by_self_embedding(
    original_tree: DerivationTree,
    tree_to_insert: DerivationTree,
    graph: GrammarGraph,
    maybe_canonical_grammar: Maybe[FrozenCanonicalGrammar] = Nothing,
) -> Iterator[Tuple[DerivationTree, Path, Path]]:
    """
    TODO: Document, test.

    :param original_tree:
    :param tree_to_insert:
    :param graph:
    :param maybe_canonical_grammar: The canonical version of the grammar represented
        by :code:`graph`. If :code:`Nothing`, the canonical grammar is computed
        from :code:`graph` (with the according potential overhead).
    :return:
    """

    yield from iter(())


def insert_tree_by_reverse_embedding(
    original_tree: DerivationTree,
    tree_to_insert: DerivationTree,
    graph: GrammarGraph,
    maybe_canonical_grammar: Maybe[FrozenCanonicalGrammar] = Nothing,
) -> Iterator[Tuple[DerivationTree, Path, Path]]:
    """
    TODO: Document, test.

    The reverse embedding method attempts to

    1. Find a the first node in :code:`original_tree` that fits into a hole in
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
    '[<<id> <attr>><b:c b:c="XXX" x:b="XXX"></b:x></<id>>]'

    :param original_tree:
    :param tree_to_insert:
    :param graph:
    :param maybe_canonical_grammar: The canonical version of the grammar represented
        by :code:`graph`. If :code:`Nothing`, the canonical grammar is computed
        from :code:`graph` (with the according potential overhead).
    :return:
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
                orig_tree_subtree.value,
                connecting_tree_2.children,
                orig_tree_subtree.id,
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

            if assertions_activated():
                result_ids = {node.id for _, node in result.paths()}
                orig_ids = {node.id for _, node in original_tree.paths()}
                node_diff = tuple(
                    (original_tree.get_subtree(original_tree.find_node(tid)).value, tid)
                    for tid in orig_ids.difference(result_ids)
                )
                assert orig_ids.issubset(result_ids), (
                    f"The node(s) {node_diff} from the "
                    f"original tree are not contained in the identifier set from "
                    f"the resulting tree."
                )
                assert graph.tree_is_valid(result)

            yield result

        if len(orig_tree_subtree.children or []) > 1:
            break


def insert_tree(
    original_tree: DerivationTree,
    tree_to_insert: DerivationTree,
    graph: GrammarGraph,
    maybe_canonical_grammar: Maybe[FrozenCanonicalGrammar] = Nothing,
) -> Iterator[Tuple[DerivationTree, Path, Path]]:
    """
    TODO: Document, test.

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

    >>> from isla.parser import EarleyParser
    >>> original_inp = '<b:c b:c="XXX" x:b="XXX"></b:x>'
    >>> original_tree = DerivationTree.from_parse_tree(
    ...     next(EarleyParser(grammar).parse(original_inp))
    ... )

    :code:`<<id> <attr>><xml-tree></<id>>`

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

    >>> graph = GrammarGraph.from_grammar(grammar)
    >>> deep_str(list(insert_tree(original_tree, tree_to_insert, graph)))
    '[<<id> <attr>><b:c b:c="XXX" x:b="XXX"></b:x></<id>>]'

    :param original_tree:
    :param tree_to_insert:
    :param graph:
    :param maybe_canonical_grammar: The canonical version of the grammar represented
        by :code:`graph`. If :code:`Nothing`, the canonical grammar is computed
        from :code:`graph` (with the according potential overhead).
    :return:
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
        else:
            idx = (idx + 1) % len(iterators)
