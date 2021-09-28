import unittest
from typing import List

from input_constraints.isla import DerivationTree
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

    def test_iterative_reverse_postorder_traversal(self):
        tree = DerivationTree.from_parse_tree(("1", [
            ("2", [("4", [])]),
            ("3", [
                ("5", [("7", [])]),
                ("6", [])
            ])
        ]))

        visited_nodes: List[int] = []

        def action(path, node):
            visited_nodes.append(int(node.value))

        tree.traverse_reverse_postorder_iteratively(action)
        self.assertEqual([6, 7, 5, 3, 4, 2, 1], visited_nodes)

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

        all_paths = [path for path, _ in tree.path_iterator()]

        self.assertEqual(all_paths, [tuple()] + paths)

    def test_next_path_complete_2(self):
        inp = "x := 1 ; y := z"
        tree = DerivationTree.from_parse_tree(parse(inp, LANG_GRAMMAR))
        paths = []
        nxt = tree.next_path(tuple())
        while nxt is not None:
            paths.append(nxt)
            nxt = tree.next_path(nxt)

        all_paths = [path for path, _ in tree.path_iterator()]

        self.assertEqual(all_paths, [tuple()] + paths)


if __name__ == '__main__':
    unittest.main()
