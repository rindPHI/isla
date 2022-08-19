import itertools
import unittest

from isla.derivation_tree import DerivationTree
from isla.parser import EarleyParser
from isla.trie import SubtreesTrie, path_to_trie_key, trie_key_to_path
from test_data import LANG_GRAMMAR


class TestPathIndexedTrie(unittest.TestCase):
    def test_trie_creation(self):
        parser = EarleyParser(LANG_GRAMMAR)
        tree = DerivationTree.from_parse_tree(next(parser.parse("x := 1 ; y := x ; y := 2 ; z := y ; x := z")))
        trie = SubtreesTrie(dict(tree.paths()))

        self.assertEqual(trie.keys(), [path for path, _ in tree.paths()])

    def test_get_keys_of_sub_trie(self):
        parser = EarleyParser(LANG_GRAMMAR)
        tree = DerivationTree.from_parse_tree(next(parser.parse("x := 1 ; y := x")))
        trie = SubtreesTrie(dict(tree.paths()))

        self.assertEqual(
            [path for path, _ in tree.get_subtree((0, 0)).paths()],
            trie.get_subtrie((0, 0)).keys())

    def test_get_values_of_sub_trie(self):
        parser = EarleyParser(LANG_GRAMMAR)
        tree = DerivationTree.from_parse_tree(next(parser.parse("x := 1 ; y := x")))
        trie = SubtreesTrie(dict(tree.paths()))

        self.assertEqual([st for _, st in tree.get_subtree((0, 0)).paths()], trie.get_subtrie((0, 0)).values())

    def test_get_items_of_sub_trie(self):
        parser = EarleyParser(LANG_GRAMMAR)
        tree = DerivationTree.from_parse_tree(next(parser.parse("x := 1 ; y := x")))
        trie = SubtreesTrie(dict(tree.paths()))

        self.assertEqual(
            [(path, str(st)) for path, st in tree.get_subtree((0, 0)).paths()],
            [(path, str(st)) for path, st in trie.get_subtrie((0, 0)).items()])

    def test_get_sub_trie(self):
        parser = EarleyParser(LANG_GRAMMAR)
        tree = DerivationTree.from_parse_tree(next(parser.parse("x := 1 ; y := x ; y := 2 ; z := y ; x := z")))
        trie = SubtreesTrie(dict(tree.paths()))

        for path, _ in tree.paths():
            subtree_paths = [(p, t) for p, t in trie.get_subtrie(path).items()]
            self.assertEqual([(p[len(path):], t) for p, t in tree.paths() if p[:len(path)] == path], subtree_paths)

    def test_get_subtrie_artificial(self):
        paths = []
        for l in range(6):
            paths += list(itertools.product(*[[i for i in range(5)] for _ in range(l)]))

        trie = SubtreesTrie()
        for path in paths:
            trie[path] = path, None

        for path in paths:
            expected = {(p[len(path):], None) for p in paths if p[:len(path)] == path}
            result = {(p, t) for p, t in trie.get_subtrie(path).values()}

            self.assertEqual(
                expected, result,
                f"Sub-trie differs from sub-tree at path {path}"
            )

    def test_path_to_trie_key(self):
        for l in range(6):
            paths = list(itertools.product(*[[i for i in range(5)] for _ in range(l)]))
            for path in paths:
                self.assertEqual(path, trie_key_to_path(path_to_trie_key(path)))

    def test_trie_key_to_path(self):
        self.assertEqual("\x01\x02", path_to_trie_key(trie_key_to_path("\x01\x02")))
        try:
            trie_key_to_path("\x02")
            self.fail("Exception expected for trie key '\\x02'")
        except RuntimeError:
            pass


if __name__ == '__main__':
    unittest.main()
