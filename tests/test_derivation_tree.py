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

import pickle
import random
import unittest
from typing import List

from isla.derivation_tree import DerivationTree
from isla.fuzzer import GrammarFuzzer
from isla.helpers import parent_or_child, canonical
from isla_formalizations.xml_lang import XML_GRAMMAR
from test_data import LANG_GRAMMAR
from test_helpers import parse


class TestDerivationTree(unittest.TestCase):
    def test_nextpath(self):
        tree = DerivationTree.from_parse_tree(
            ("1", [("2", [("4", [])]), ("3", [("5", [("7", [])]), ("6", [])])])
        )

        path = (0, 0)
        self.assertEqual(("4", []), tree.get_subtree(path).to_parse_tree())

        path = tree.next_path(path)
        self.assertEqual((1,), path)
        self.assertEqual(
            ("3", [("5", [("7", [])]), ("6", [])]),
            tree.get_subtree(path).to_parse_tree(),
        )

        self.assertEqual((1, 0), tree.next_path(path))

        path = (1, 0)
        self.assertEqual(("5", [("7", [])]), tree.get_subtree(path).to_parse_tree())

        path = tree.next_path(path)
        path = tree.next_path(path)
        self.assertEqual((1, 1), path)
        self.assertEqual(("6", []), tree.get_subtree(path).to_parse_tree())

    def test_traverse(self):
        tree = DerivationTree.from_parse_tree(
            ("1", [("2", [("4", [])]), ("3", [("5", [("7", [])]), ("6", [])])])
        )

        visited_nodes: List[int] = []

        def action(path, node):
            visited_nodes.append(int(node.value))

        visited_nodes.clear()
        tree.bfs(action)
        self.assertEqual([1, 2, 3, 4, 5, 6, 7], visited_nodes)

        visited_nodes.clear()
        tree.traverse(action, kind=DerivationTree.TRAVERSE_POSTORDER, reverse=True)
        self.assertEqual([6, 7, 5, 3, 4, 2, 1], visited_nodes)

        visited_nodes.clear()
        tree.traverse(action, kind=DerivationTree.TRAVERSE_PREORDER, reverse=False)
        self.assertEqual([1, 2, 4, 3, 5, 7, 6], visited_nodes)

        visited_nodes.clear()
        tree.traverse(action, kind=DerivationTree.TRAVERSE_POSTORDER, reverse=False)
        self.assertEqual([4, 2, 7, 5, 6, 3, 1], visited_nodes)

        visited_nodes.clear()
        tree.traverse(action, kind=DerivationTree.TRAVERSE_PREORDER, reverse=True)
        self.assertEqual([1, 3, 6, 5, 7, 2, 4], visited_nodes)

        def check_path(path, node):
            self.assertEqual(node, tree.get_subtree(path))

        tree.traverse(check_path, kind=DerivationTree.TRAVERSE_PREORDER, reverse=True)
        tree.traverse(check_path, kind=DerivationTree.TRAVERSE_PREORDER, reverse=False)
        tree.traverse(action, kind=DerivationTree.TRAVERSE_POSTORDER, reverse=True)
        tree.traverse(action, kind=DerivationTree.TRAVERSE_POSTORDER, reverse=False)

    def test_hashes_different(self):
        tree_one = DerivationTree.from_parse_tree(("<start>", [("<stmt>", None)]))
        tree_two = DerivationTree.from_parse_tree(
            ("<start>", [("<stmt>", [("<assgn>", None)])])
        )
        self.assertNotEqual(
            tree_one.compute_hash_iteratively(True),
            tree_two.compute_hash_iteratively(True),
        )
        self.assertNotEqual(tree_one.structural_hash(), tree_two.structural_hash())

    def test_hash_caching(self):
        tree = DerivationTree.from_parse_tree(
            ("1", [("2", [("4", [])]), ("3", [("5", [("7", [])]), ("6", [])])])
        )

        for path, subtree in tree.paths():
            self.assertFalse(subtree._DerivationTree__structural_hash)

        orig_hash = tree.structural_hash()

        for path, subtree in tree.paths():
            self.assertTrue(subtree._DerivationTree__structural_hash)

        new_tree = tree.replace_path(
            (0, 0), DerivationTree.from_parse_tree(("8", [("9", [])]))
        )

        self.assertFalse(new_tree._DerivationTree__structural_hash)

        for path, subtree in new_tree.paths():
            has_cache = subtree._DerivationTree__structural_hash is not None
            parent_or_child_of_inserted = parent_or_child(path, (0, 0))
            self.assertTrue(
                has_cache
                and not parent_or_child_of_inserted
                or not has_cache
                and parent_or_child_of_inserted
            )

        self.assertNotEqual(orig_hash, new_tree.structural_hash())

    def test_next_path(self):
        tree = DerivationTree.from_parse_tree(
            ("1", [("2", [("4", [])]), ("3", [("5", [("7", [])]), ("6", [])])])
        )

        subtrees = []
        nxt = tree.next_path((0, 0))
        while nxt is not None:
            subtrees.append(tree.get_subtree(nxt).to_parse_tree())
            nxt = tree.next_path(nxt)

        self.assertEqual(
            [
                ("3", [("5", [("7", [])]), ("6", [])]),
                ("5", [("7", [])]),
                ("7", []),
                ("6", []),
            ],
            subtrees,
        )

        paths = []
        nxt = tree.next_path(tuple())
        while nxt is not None:
            paths.append(nxt)
            nxt = tree.next_path(nxt)

        all_paths = [path for path, _ in tree.paths()]

        self.assertEqual(all_paths, [tuple()] + paths)

    def test_next_path_complete_2(self):
        inp = "x := 1 ; y := z"
        tree = DerivationTree.from_parse_tree(parse(inp, LANG_GRAMMAR))
        paths = []
        nxt = tree.next_path(tuple())
        while nxt is not None:
            paths.append(nxt)
            nxt = tree.next_path(nxt)

        all_paths = [path for path, _ in tree.paths()]

        self.assertEqual(all_paths, [tuple()] + paths)

    def test_substitute(self):
        tree = DerivationTree.from_parse_tree(
            ("1", [("2", [("4", [])]), ("3", [("5", [("7", [])]), ("6", [])])])
        )

        result = tree.substitute(
            {
                tree.get_subtree((0, 0)): DerivationTree.from_parse_tree(
                    ("8", [("9", [])])
                ),
                tree.get_subtree((1, 1)): DerivationTree.from_parse_tree(("10", [])),
            }
        )

        self.assertEqual(
            (
                "1",
                [("2", [("8", [("9", [])])]), ("3", [("5", [("7", [])]), ("10", [])])],
            ),
            result.to_parse_tree(),
        )

    def test_potential_prefix(self):
        potential_prefix_tree = DerivationTree.from_parse_tree(
            (
                "<xml-tree>",
                [
                    ("<xml-open-tag>", [("<", []), ("<id>", None), (">", [])]),
                    ("<xml-tree>", None),
                    ("<xml-close-tag>", [("</", []), ("<id>", None), (">", [])]),
                ],
            )
        )
        other_tree = DerivationTree.from_parse_tree(
            (
                "<xml-tree>",
                [
                    ("<xml-open-tag>", None),
                    ("<xml-tree>", None),
                    ("<xml-close-tag>", None),
                ],
            )
        )

        self.assertTrue(potential_prefix_tree.is_potential_prefix(other_tree))
        self.assertFalse(potential_prefix_tree.is_prefix(other_tree))

        self.assertTrue(other_tree.is_prefix(potential_prefix_tree))
        self.assertTrue(other_tree.is_potential_prefix(potential_prefix_tree))

    def test_find_start(self):
        tree = DerivationTree("<start>", id=1)
        self.assertEqual((), tree.find_node(1))

    def test_from_parse_tree(self):
        for _ in range(20):
            fuzzer = GrammarFuzzer(
                XML_GRAMMAR, max_nonterminals=50, min_nonterminals=10
            )
            tree = ("<start>", None)
            for _ in range(random.randint(1, 50)):
                try:
                    tree = fuzzer.expand_tree_once(
                        DerivationTree.from_parse_tree(tree)
                    ).to_parse_tree()
                except ValueError:
                    # Tree already closed
                    break

            dtree = DerivationTree.from_parse_tree(tree)
            self.assertEqual(tree, dtree.to_parse_tree())

            tree = fuzzer.expand_tree(
                DerivationTree.from_parse_tree(tree)
            ).to_parse_tree()
            dtree = DerivationTree.from_parse_tree(tree)
            self.assertEqual(tree, dtree.to_parse_tree())

    def test_serialization_1(self):
        tree = DerivationTree.from_parse_tree(
            ("1", [("2", [("4", [])]), ("3", [("5", [("7", [])]), ("6", [])])])
        )

        self.assertEqual(str(tree), str(pickle.loads(pickle.dumps(tree))))

    def test_serialization_2(self):
        fuzzer = GrammarFuzzer(XML_GRAMMAR, max_nonterminals=50, min_nonterminals=10)

        for _ in range(20):
            tree = fuzzer.fuzz_tree()
            self.assertEqual(str(tree), str(pickle.loads(pickle.dumps(tree))))

    def test_json(self):
        tree = DerivationTree.from_parse_tree(
            ("1", [("2", [("4", [])]), ("3", [("5", [("7", [])]), ("6", [])])])
        )

        self.assertEqual(tree, DerivationTree.from_json(tree.to_json()))

    def test_zero_id(self):
        DerivationTree.next_id = 42
        tree = DerivationTree("<start>", id=0)
        self.assertEqual(0, tree.id)

    def test_nonterminals(self):
        # x := x ; z := x
        tree = DerivationTree(
            "<start>",
            (
                DerivationTree(
                    "<stmt>",
                    (
                        DerivationTree(
                            "<assgn>",
                            (
                                DerivationTree(
                                    "<var>",
                                    (
                                        DerivationTree(
                                            "x",
                                            (),
                                        ),
                                    ),
                                ),
                                DerivationTree(
                                    " := ",
                                    (),
                                ),
                                DerivationTree(
                                    "<rhs>",
                                    (
                                        DerivationTree(
                                            "<var>",
                                            (
                                                DerivationTree(
                                                    "x",
                                                    (),
                                                ),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                        DerivationTree(
                            " ; ",
                            (),
                        ),
                        DerivationTree(
                            "<stmt>",
                            (
                                DerivationTree(
                                    "<assgn>",
                                    (
                                        DerivationTree(
                                            "<var>",
                                            (
                                                DerivationTree(
                                                    "z",
                                                    (),
                                                ),
                                            ),
                                        ),
                                        DerivationTree(
                                            " := ",
                                            (),
                                        ),
                                        DerivationTree(
                                            "<rhs>",
                                            (
                                                DerivationTree(
                                                    "<var>",
                                                    (
                                                        DerivationTree(
                                                            "x",
                                                            (),
                                                        ),
                                                    ),
                                                ),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )

    def test_depth(self):
        # x := x ; z := x
        tree = DerivationTree(
            "<start>",
            (
                DerivationTree(
                    "<stmt>",
                    (
                        DerivationTree(
                            "<assgn>",
                            (
                                DerivationTree(
                                    "<var>",
                                    (
                                        DerivationTree(
                                            "x",
                                            (),
                                        ),
                                    ),
                                ),
                                DerivationTree(
                                    " := ",
                                    (),
                                ),
                                DerivationTree(
                                    "<rhs>",
                                    (
                                        DerivationTree(
                                            "<var>",
                                            (
                                                DerivationTree(
                                                    "x",
                                                    (),
                                                ),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                        DerivationTree(
                            " ; ",
                            (),
                        ),
                        DerivationTree("<stmt>", None),
                    ),
                ),
            ),
        )

        self.assertEqual(6, tree.depth())

    def test_parse_tree_compatibility(self):
        parse_tree = (
            "<xml-tree>",
            [
                ("<xml-open-tag>", [("<", []), ("<id>", None), (">", [])]),
                ("<xml-tree>", None),
                ("<xml-close-tag>", [("</", []), ("<id>", None), (">", [])]),
            ],
        )
        dtree = DerivationTree.from_parse_tree(parse_tree)

        self.assertEqual(parse_tree[0], dtree[0])
        self.assertTrue(
            all(
                parse_tree[1][idx][0] == dtree[1][idx][0]
                for idx in range(len(parse_tree[1]))
            )
        )

        node_1, _ = parse_tree
        node_2, _ = dtree
        self.assertEqual(node_1, node_2)

        node_1, _ = parse_tree[1][0]
        node_2, _ = dtree[1][0]
        self.assertEqual(node_1, node_2)

    def test_to_dot(self):
        DerivationTree.next_id = 0
        parse_tree = (
            "<xml-tree>",
            [
                ("<xml-open-tag>", [("<", []), ("<id>", None), (">", [])]),
                ("<xml-tree>", None),
                ("<xml-close-tag>", [("</", []), ("<id>", None), (">", [])]),
            ],
        )
        dtree = DerivationTree.from_parse_tree(parse_tree)

        expected = r"""// Derivation Tree
digraph {
    node [shape=plain]
    9 [label=<&lt;xml-tree&gt; <FONT COLOR="gray">(9)</FONT>>]
    9 -> 8
    9 -> 4
    9 -> 3
    8 [label=<&lt;xml-open-tag&gt; <FONT COLOR="gray">(8)</FONT>>]
    8 -> 7
    8 -> 6
    8 -> 5
    7 [label=<&lt; <FONT COLOR="gray">(7)</FONT>>]
    6 [label=<&lt;id&gt; <FONT COLOR="gray">(6)</FONT>>]
    5 [label=<&gt; <FONT COLOR="gray">(5)</FONT>>]
    4 [label=<&lt;xml-tree&gt; <FONT COLOR="gray">(4)</FONT>>]
    3 [label=<&lt;xml-close-tag&gt; <FONT COLOR="gray">(3)</FONT>>]
    3 -> 2
    3 -> 1
    3 -> 0
    2 [label=<&lt;/ <FONT COLOR="gray">(2)</FONT>>]
    1 [label=<&lt;id&gt; <FONT COLOR="gray">(1)</FONT>>]
    0 [label=<&gt; <FONT COLOR="gray">(0)</FONT>>]
    {
        rank=same
        8 -> 4 [style=invis]
        4 -> 3 [style=invis]
    }
    {
        rank=same
        7 -> 6 [style=invis]
        6 -> 5 [style=invis]
        5 -> 2 [style=invis]
        2 -> 1 [style=invis]
        1 -> 0 [style=invis]
    }
}
""".replace(
            "    ", "\t"
        )

        self.assertEqual(expected, str(dtree.to_dot()))

    def test_expand_one_step(self):
        grammar = canonical(
            {"<start>": ["<A>"], "<A>": ["<B><A>", "a<A>", "a"], "<B>": ["b"]}
        )

        tree = DerivationTree("<start>", (DerivationTree("<A>", None),))
        result = tree.expand_one_step(grammar)
        self.assertEqual(3, len(result))
        self.assertEqual(["<B><A>", "a<A>", "a"], list(map(str, result)))

        tree = DerivationTree(
            "<start>", (DerivationTree("<A>", (DerivationTree("a", ()),)),)
        )
        result = tree.expand_one_step(grammar)
        self.assertFalse(len(result))


if __name__ == "__main__":
    unittest.main()
