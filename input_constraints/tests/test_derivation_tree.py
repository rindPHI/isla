import random
import unittest
from typing import List

from fuzzingbook.GrammarFuzzer import GrammarFuzzer

from input_constraints.helpers import parent_or_child
from input_constraints.isla import DerivationTree
from input_constraints.tests.subject_languages.xml_lang import XML_GRAMMAR
from input_constraints.tests.test_data import LANG_GRAMMAR
from input_constraints.tests.test_helpers import parse


class TestDerivationTree(unittest.TestCase):
    def test_nextpath(self):
        tree = DerivationTree.from_parse_tree(("1", [
            ("2", [("4", [])]),
            ("3", [
                ("5", [("7", [])]),
                ("6", [])
            ])
        ]))

        path = (0, 0)
        self.assertEqual(('4', []), tree.get_subtree(path).to_parse_tree())

        path = tree.next_path(path)
        self.assertEqual((1,), path)
        self.assertEqual(("3", [
            ("5", [("7", [])]),
            ("6", [])
        ]), tree.get_subtree(path).to_parse_tree())

        self.assertEqual((1, 0), tree.next_path(path))

        path = (1, 0)
        self.assertEqual(("5", [("7", [])]), tree.get_subtree(path).to_parse_tree())

        path = tree.next_path(path)
        path = tree.next_path(path)
        self.assertEqual((1, 1), path)
        self.assertEqual(("6", []), tree.get_subtree(path).to_parse_tree())

    def test_traverse(self):
        tree = DerivationTree.from_parse_tree(
            ("1", [
                ("2", [("4", [])]),
                ("3", [
                    ("5", [("7", [])]),
                    ("6", [])
                ])
            ]))

        visited_nodes: List[int] = []

        def action(path, node):
            visited_nodes.append(int(node.value))

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
        tree_one = DerivationTree.from_parse_tree(('<start>', [('<stmt>', None)]))
        tree_two = DerivationTree.from_parse_tree(('<start>', [('<stmt>', [('<assgn>', None)])]))
        self.assertNotEqual(tree_one.compute_hash_iteratively(True), tree_two.compute_hash_iteratively(True))
        self.assertNotEqual(tree_one.structural_hash(), tree_two.structural_hash())

    def test_hash_caching(self):
        tree = DerivationTree.from_parse_tree(
            ("1", [
                ("2", [("4", [])]),
                ("3", [
                    ("5", [("7", [])]),
                    ("6", [])
                ])
            ]))

        for path, subtree in tree.paths():
            self.assertFalse(subtree._DerivationTree__structural_hash)

        orig_hash = tree.structural_hash()

        for path, subtree in tree.paths():
            self.assertTrue(subtree._DerivationTree__structural_hash)

        new_tree = tree.replace_path((0, 0), DerivationTree.from_parse_tree(("8", [("9", [])])))

        self.assertFalse(new_tree._DerivationTree__structural_hash)

        for path, subtree in new_tree.paths():
            has_cache = subtree._DerivationTree__structural_hash is not None
            parent_or_child_of_inserted = parent_or_child(path, (0, 0))
            self.assertTrue(
                has_cache and not parent_or_child_of_inserted or not has_cache and parent_or_child_of_inserted)

        self.assertNotEqual(orig_hash, new_tree.structural_hash())

    def test_next_path(self):
        tree = DerivationTree.from_parse_tree(("1", [
            ("2", [("4", [])]),
            ("3", [
                ("5", [("7", [])]),
                ("6", [])
            ])
        ]))

        subtrees = []
        nxt = tree.next_path((0, 0))
        while nxt is not None:
            subtrees.append(tree.get_subtree(nxt).to_parse_tree())
            nxt = tree.next_path(nxt)

        self.assertEqual([('3', [('5', [('7', [])]), ('6', [])]),
                          ('5', [('7', [])]),
                          ('7', []),
                          ('6', [])], subtrees)

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
        tree = DerivationTree.from_parse_tree(("1", [
            ("2", [("4", [])]),
            ("3", [
                ("5", [("7", [])]),
                ("6", [])
            ])
        ]))

        result = tree.substitute({
            tree.get_subtree((0, 0)): DerivationTree.from_parse_tree(("8", [("9", [])])),
            tree.get_subtree((1, 1)): DerivationTree.from_parse_tree(("10", []))
        })

        self.assertEqual(("1", [
            ("2", [("8", [("9", [])])]),
            ("3", [
                ("5", [("7", [])]),
                ("10", [])
            ])
        ]), result.to_parse_tree())

    def test_potential_prefix(self):
        potential_prefix_tree = DerivationTree.from_parse_tree(
            ('<xml-tree>', [
                ('<xml-open-tag>', [('<', []), ('<id>', None), ('>', [])]),
                ('<xml-tree>', None),
                ('<xml-close-tag>', [('</', []), ('<id>', None), ('>', [])])]))
        other_tree = DerivationTree.from_parse_tree(
            ('<xml-tree>', [
                ('<xml-open-tag>', None),
                ('<xml-tree>', None),
                ('<xml-close-tag>', None)]))

        self.assertTrue(potential_prefix_tree.is_potential_prefix(other_tree))
        self.assertFalse(potential_prefix_tree.is_prefix(other_tree))

        self.assertTrue(other_tree.is_prefix(potential_prefix_tree))
        self.assertTrue(other_tree.is_potential_prefix(potential_prefix_tree))

    def test_from_parse_tree(self):
        for _ in range(20):
            fuzzer = GrammarFuzzer(XML_GRAMMAR, max_nonterminals=50, min_nonterminals=10)
            tree = ("<start>", None)
            for _ in range(random.randint(1, 50)):
                try:
                    tree = fuzzer.expand_tree_once(tree)
                except ValueError:
                    # Tree already closed
                    break

            dtree = DerivationTree.from_parse_tree(tree)
            self.assertEqual(tree, dtree.to_parse_tree())

            tree = fuzzer.expand_tree(tree)
            dtree = DerivationTree.from_parse_tree(tree)
            self.assertEqual(tree, dtree.to_parse_tree())


if __name__ == '__main__':
    unittest.main()
