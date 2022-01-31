import copy
import unittest
from typing import Optional

from fuzzingbook.Parser import EarleyParser, canonical
from grammar_graph.gg import GrammarGraph

from src.isla.existential_helpers import path_to_tree, paths_between
from src.isla.helpers import is_prefix, path_iterator, delete_unreachable, \
    dict_of_lists_to_list_of_dicts, weighted_geometric_mean
from src.isla.isla_predicates import is_before
from src.isla.type_defs import Grammar, ParseTree
from tests.test_data import LANG_GRAMMAR


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

    def test_is_before(self):
        self.assertFalse(is_before(None, tuple(), tuple()))
        self.assertFalse(is_before(None, (1,), (1, 0)))
        self.assertTrue(is_before(None, (1, 0), (1, 1)))
        self.assertTrue(is_before(None, (1, 1, 0), (1, 2)))
        self.assertFalse(is_before(None, (1, 2, 0), (1, 2)))
        self.assertTrue(is_before(None, (1, 2, 0), (1, 3, 0, 0, 9)))

    def test_is_prefix(self):
        self.assertTrue(is_prefix((1, 0, 1), (1, 0, 1)))
        self.assertTrue(is_prefix((1, 0, 1), (1, 0, 1, 0)))
        self.assertTrue(is_prefix(tuple(), (1, 0, 1)))
        self.assertTrue(is_prefix(tuple(), tuple()))
        self.assertFalse(is_prefix((1,), tuple()))
        self.assertFalse(is_prefix((1,), (2,)))

    def test_path_to_tree(self):
        self.assertEqual([('<stmt>', [('<assgn>', None)]),
                          ('<stmt>', [('<assgn>', None), (' ; ', []), ('<stmt>', None)])],
                         [tree.to_parse_tree()
                          for tree in path_to_tree(canonical(LANG_GRAMMAR), ["<stmt>", "<assgn>"])])

        self.assertEqual([('<stmt>', [('<assgn>', None), (' ; ', []), ('<stmt>', None)])],
                         [tree.to_parse_tree()
                          for tree in path_to_tree(canonical(LANG_GRAMMAR), ["<stmt>", "<stmt>"])])

        self.assertEqual([('<stmt>', [('<assgn>', [('<var>', None), (' := ', []), ('<rhs>', [('<digit>', None)])])]),
                          ('<stmt>', [('<assgn>', [('<var>', None), (' := ', []), ('<rhs>', [('<digit>', None)])]),
                                      (' ; ', []), ('<stmt>', None)])],
                         [tree.to_parse_tree()
                          for tree in path_to_tree(
                             canonical(LANG_GRAMMAR), ["<stmt>", "<assgn>", "<rhs>", "<digit>"])])

    def test_find_all_paths(self):
        graph = GrammarGraph.from_grammar(LANG_GRAMMAR)
        self.assertEqual([('<stmt>', '<assgn>', '<var>'),
                          ('<stmt>', '<assgn>', '<rhs>', '<var>')],
                         list(paths_between(graph, "<stmt>", "<var>")))

        self.assertEqual([('<stmt>', '<stmt>')], list(paths_between(graph, "<stmt>", "<stmt>")))

        self.assertFalse(list(paths_between(graph, "<assgn>", "<stmt>")))

        self.assertFalse(list(paths_between(graph, "<assgn>", "<assgn>")))

    def test_dict_of_lists_to_list_of_dicts(self):
        self.assertEqual(
            [{1: 3, 2: 5}, {1: 3, 2: 6}],
            dict_of_lists_to_list_of_dicts({1: [3], 2: [5, 6]})
        )

        self.assertEqual(
            [{1: 3, 2: 5}, {1: 4, 2: 5}],
            dict_of_lists_to_list_of_dicts({1: [3, 4], 2: [5]})
        )

        self.assertEqual(
            [{1: 3, 2: 5}, {1: 3, 2: 6}, {1: 4, 2: 5}, {1: 4, 2: 6}],
            dict_of_lists_to_list_of_dicts({1: [3, 4], 2: [5, 6]})
        )

        self.assertEqual(
            [{1: 3, 2: 5, 7: 8},
             {1: 3, 2: 5, 7: 9},
             {1: 3, 2: 5, 7: 10},
             {1: 3, 2: 6, 7: 8},
             {1: 3, 2: 6, 7: 9},
             {1: 3, 2: 6, 7: 10},
             {1: 4, 2: 5, 7: 8},
             {1: 4, 2: 5, 7: 9},
             {1: 4, 2: 5, 7: 10},
             {1: 4, 2: 6, 7: 8},
             {1: 4, 2: 6, 7: 9},
             {1: 4, 2: 6, 7: 10}],
            dict_of_lists_to_list_of_dicts({1: [3, 4], 2: [5, 6], 7: [8, 9, 10]}))

    def test_weighted_geometric_mean(self):
        for i in range(1, 30):
            self.assertAlmostEqual(i, weighted_geometric_mean([i, i, i], [1, 1, 1]), 10)
            self.assertAlmostEqual(i, weighted_geometric_mean([i, i, i], [0, 0, 1]), 10)

        self.assertAlmostEqual(1.449, weighted_geometric_mean([0, 1, 2], [0, 1, 1]), 3)
        self.assertAlmostEqual(0.817, weighted_geometric_mean([0, 1, 2], [1, 1, 1]), 3)


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
