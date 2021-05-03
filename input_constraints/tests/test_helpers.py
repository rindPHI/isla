import unittest

from input_constraints.helpers import get_subtree, next_path, get_path_of_subtree, is_before


class TestHelpers(unittest.TestCase):
    def test_nextpath(self):
        tree = ("1", [
            ("2", [("4", [])]),
            ("3", [
                ("5", [("7", [])]),
                ("6", [])
            ])
        ])

        path = (0, 0)
        self.assertEqual(('4', []), get_subtree(path, tree))

        path = next_path(path, tree)
        self.assertEqual((1,), path)
        self.assertEqual(("3", [
            ("5", [("7", [])]),
            ("6", [])
        ]), get_subtree(path, tree))

        self.assertFalse(next_path(path, tree))

        path = (1,0)
        self.assertEqual(("5", [("7", [])]), get_subtree(path, tree))

        path = next_path(path, tree)
        self.assertEqual((1,1), path)
        self.assertEqual(("6", []), get_subtree(path, tree))

    def test_get_path_of_subtree(self):
        subtree = ("1", [])
        tree = ("2", [subtree, ("1", [])])
        self.assertEqual((0,), get_path_of_subtree(tree, subtree))
        tree = ("2", [("1", []), subtree])
        self.assertEqual((1,), get_path_of_subtree(tree, subtree))

    def test_is_before(self):
        self.assertFalse(is_before(tuple(), tuple()))
        self.assertFalse(is_before((1,), (1,0)))
        self.assertTrue(is_before((1,0), (1,1)))
        self.assertTrue(is_before((1,1,0), (1,2)))
        self.assertFalse(is_before((1,2,0), (1,2)))
        self.assertTrue(is_before((1,2,0), (1,3,0,0,9)))


if __name__ == '__main__':
    unittest.main()
