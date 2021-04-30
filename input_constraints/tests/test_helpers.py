import unittest

from input_constraints.helpers import get_subtree, next_path


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


if __name__ == '__main__':
    unittest.main()
