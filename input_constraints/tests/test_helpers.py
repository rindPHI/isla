import copy
import unittest
from typing import Optional

from fuzzingbook.Parser import EarleyParser, canonical
from grammar_graph.gg import GrammarGraph

from input_constraints.existential_helpers import path_to_tree, paths_between
from input_constraints.helpers import get_subtree, next_path, get_path_of_subtree, is_before, is_prefix, is_after, \
    prev_path_complete, path_iterator, next_path_complete, delete_unreachable
from input_constraints.tests.test_data import LANG_GRAMMAR
from input_constraints.type_defs import Grammar, ParseTree


class TestHelpers(unittest.TestCase):
    def test_path_iterator(self):
        prog = "x := 1 ; y := x"
        parser = EarleyParser(LANG_GRAMMAR)
        tree = next(parser.parse(prog))

        paths = [path for path, subtree in list(path_iterator(tree))]
        self.assertEqual([
            (), (0,), (0, 0), (0, 0, 0), (0, 0, 0, 0), (0, 0, 1), (0, 0, 2), (0, 0, 2, 0), (0, 0, 2, 0, 0),
            (0, 1), (0, 2), (0, 2, 0), (0, 2, 0, 0), (0, 2, 0, 0, 0), (0, 2, 0, 1), (0, 2, 0, 2),
            (0, 2, 0, 2, 0), (0, 2, 0, 2, 0, 0)],
            paths)

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

        path = (1, 0)
        self.assertEqual(("5", [("7", [])]), get_subtree(path, tree))

        path = next_path(path, tree)
        self.assertEqual((1, 1), path)
        self.assertEqual(("6", []), get_subtree(path, tree))

    def test_prevpath_complete(self):
        tree = ("1", [
            ("2", [("4", [])]),
            ("3", [
                ("5", [("7", [])]),
                ("6", [])
            ])
        ])

        subtrees = []
        prev = prev_path_complete((1, 1), tree)
        while prev is not None:
            subtrees.append(get_subtree(prev, tree))
            prev = prev_path_complete(prev, tree)

        self.assertEqual([
            ('7', []),
            ('5', [('7', [])]),
            ('3', [('5', [('7', [])]), ('6', [])]),
            ('4', []),
            ('2', [('4', [])]),
            ('1', [('2', [('4', [])]), ('3', [('5', [('7', [])]), ('6', [])])])],
            subtrees)

    def test_next_path_complete(self):
        tree = ("1", [
            ("2", [("4", [])]),
            ("3", [
                ("5", [("7", [])]),
                ("6", [])
            ])
        ])

        subtrees = []
        nxt = next_path_complete((0, 0), tree)
        while nxt is not None:
            subtrees.append(get_subtree(nxt, tree))
            nxt = next_path_complete(nxt, tree)

        self.assertEqual([('3', [('5', [('7', [])]), ('6', [])]),
                          ('5', [('7', [])]),
                          ('7', []),
                          ('6', [])], subtrees)

        paths = []
        nxt = next_path_complete(tuple(), tree)
        while nxt is not None:
            paths.append(nxt)
            nxt = next_path_complete(nxt, tree)

        all_paths = [path for path, _ in path_iterator(tree)]

        self.assertEqual(all_paths, [tuple()] + paths)

    def test_next_path_complete_2(self):
        inp = "x := 1 ; y := z"
        tree = parse(inp, LANG_GRAMMAR)
        paths = []
        nxt = next_path_complete(tuple(), tree)
        while nxt is not None:
            paths.append(nxt)
            nxt = next_path_complete(nxt, tree)

        all_paths = [path for path, _ in path_iterator(tree)]

        self.assertEqual(all_paths, [tuple()] + paths)

    def test_get_path_of_subtree(self):
        subtree = ("1", [])
        tree = ("2", [subtree, ("1", [])])
        self.assertEqual((0,), get_path_of_subtree(tree, subtree))
        tree = ("2", [("1", []), subtree])
        self.assertEqual((1,), get_path_of_subtree(tree, subtree))

    def test_is_before(self):
        self.assertFalse(is_before(tuple(), tuple()))
        self.assertFalse(is_before((1,), (1, 0)))
        self.assertTrue(is_before((1, 0), (1, 1)))
        self.assertTrue(is_before((1, 1, 0), (1, 2)))
        self.assertFalse(is_before((1, 2, 0), (1, 2)))
        self.assertTrue(is_before((1, 2, 0), (1, 3, 0, 0, 9)))

    def test_is_prefix(self):
        self.assertTrue(is_prefix((1, 0, 1), (1, 0, 1)))
        self.assertTrue(is_prefix((1, 0, 1), (1, 0, 1, 0)))
        self.assertTrue(is_prefix(tuple(), (1, 0, 1)))
        self.assertTrue(is_prefix(tuple(), tuple()))
        self.assertFalse(is_prefix((1,), tuple()))
        self.assertFalse(is_prefix((1,), (2,)))

    def test_is_after(self):
        self.assertFalse(is_after(tuple(), tuple()))
        self.assertFalse(is_after((1, 0), (1,)))
        self.assertTrue(is_after((1, 1), (1, 0)))
        self.assertTrue(is_after((1, 2), (1, 1, 0)))
        self.assertFalse(is_after((1, 2), (1, 2, 0)))
        self.assertTrue(is_after((1, 3, 0, 0, 9), (1, 2, 0)))

    def test_path_to_tree(self):
        self.assertEqual([('<stmt>', [('<assgn>', None)]),
                          ('<stmt>', [('<assgn>', None), (' ; ', []), ('<stmt>', None)])],
                         path_to_tree(canonical(LANG_GRAMMAR), ["<stmt>", "<assgn>"]))

        self.assertEqual([('<stmt>', [('<assgn>', None), (' ; ', []), ('<stmt>', None)])],
                         path_to_tree(canonical(LANG_GRAMMAR), ["<stmt>", "<stmt>"]))

        self.assertEqual([('<stmt>', [('<assgn>', [('<var>', None), (' := ', []), ('<rhs>', [('<digit>', None)])])]),
                          ('<stmt>', [('<assgn>', [('<var>', None), (' := ', []), ('<rhs>', [('<digit>', None)])]),
                                      (' ; ', []), ('<stmt>', None)])],
                         path_to_tree(canonical(LANG_GRAMMAR), ["<stmt>", "<assgn>", "<rhs>", "<digit>"]))

    def test_find_all_paths(self):
        graph = GrammarGraph.from_grammar(LANG_GRAMMAR)
        self.assertEqual([('<stmt>', '<assgn>', '<var>'),
                          ('<stmt>', '<assgn>', '<rhs>', '<var>')],
                         list(paths_between(graph, "<stmt>", "<var>")))

        self.assertEqual([('<stmt>', '<stmt>')], list(paths_between(graph, "<stmt>", "<stmt>")))

        self.assertFalse(list(paths_between(graph, "<assgn>", "<stmt>")))

        self.assertFalse(list(paths_between(graph, "<assgn>", "<assgn>")))


if __name__ == '__main__':
    unittest.main()


def parse(inp: str, grammar: Grammar, start_symbol: Optional[str] = None) -> ParseTree:
    if start_symbol is None:
        return next(EarleyParser(grammar).parse(inp))
    else:
        grammar = copy.deepcopy(grammar)
        grammar["<start>"] = [start_symbol]
        delete_unreachable(grammar)
        return next(EarleyParser(grammar).parse(inp))[1][0]