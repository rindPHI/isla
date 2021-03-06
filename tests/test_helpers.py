import copy
import itertools
import unittest
from typing import Optional

import z3
from grammar_graph.gg import GrammarGraph

from isla.derivation_tree import DerivationTree
from isla.existential_helpers import path_to_tree, paths_between
from isla.helpers import is_prefix, path_iterator, delete_unreachable, \
    dict_of_lists_to_list_of_dicts, weighted_geometric_mean, canonical, trie_key_to_path, get_subtrie, path_to_trie_key, \
    mk_subtree_trie
from isla.isla_predicates import is_before
from isla.parser import EarleyParser
from isla.type_defs import Grammar, ParseTree
from isla.z3_helpers import evaluate_z3_expression, z3_eq, smt_expr_to_str
from test_data import LANG_GRAMMAR


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
        self.assertEqual([
            ('<stmt>', [('<assgn>', None), (' ; ', []), ('<stmt>', None)]),
            ('<stmt>', [('<assgn>', None)])],
            [tree.to_parse_tree()
             for tree in path_to_tree(canonical(LANG_GRAMMAR), ["<stmt>", "<assgn>"])])

        self.assertEqual([('<stmt>', [('<assgn>', None), (' ; ', []), ('<stmt>', None)])],
                         [tree.to_parse_tree()
                          for tree in path_to_tree(canonical(LANG_GRAMMAR), ["<stmt>", "<stmt>"])])

        self.assertEqual([
            ('<stmt>', [('<assgn>', [('<var>', None), (' := ', []), ('<rhs>', [('<digit>', None)])]),
                        (' ; ', []), ('<stmt>', None)]),
            ('<stmt>', [('<assgn>', [('<var>', None), (' := ', []), ('<rhs>', [('<digit>', None)])])])],
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

    def test_strtoint_translation(self):
        f = z3_eq(z3.StrToInt(z3.StringVal("42")), z3.IntVal(42))
        self.assertEqual(z3.parse_smt2_string(f"(assert {smt_expr_to_str(f)})")[0], f)

    def test_evaluate_z3_regexp(self):
        formula = """
(str.in_re 
  "<DATE>" 
  (re.++ 
    (re.++ 
      (re.++ 
        (re.++ 
          ((_ re.loop 4 4) (re.range "0" "9")) 
          (str.to_re "-")) 
        ((_ re.loop 2 2) (re.range "0" "9")))
      (str.to_re "-")) 
    ((_ re.loop 2 2) (re.range "0" "9"))))"""

        parsed_formula = z3.parse_smt2_string(f"(assert {formula.replace('<DATE>', '2022-02-24')})")[0]
        self.assertFalse(evaluate_z3_expression(parsed_formula)[0])
        self.assertTrue(evaluate_z3_expression(parsed_formula)[1])

    def test_evaluate_z3_regexp_with_var(self):
        formula = """
(str.in_re 
  var
  (re.++ 
    (re.++ 
      (re.++ 
        (re.++ 
          ((_ re.loop 4 4) (re.range "0" "9")) 
          (str.to_re "-")) 
        ((_ re.loop 2 2) (re.range "0" "9")))
      (str.to_re "-")) 
    ((_ re.loop 2 2) (re.range "0" "9"))))"""

        var = z3.String("var")
        parsed_formula = z3.parse_smt2_string(f"(assert {formula})", decls={"var": var})[0]
        eval_result = evaluate_z3_expression(parsed_formula)

        self.assertEqual(("var",), eval_result[0])
        self.assertTrue(callable(eval_result[1]))
        self.assertTrue(eval_result[1](("2022-02-24",)))
        self.assertFalse(eval_result[1](("24-02-2022",)))

    def test_evaluate_z3_multivar_expr(self):
        formula = "(or (= a b) (= a c))"

        a, b, c = z3.Strings("a b c")
        parsed_formula = z3.parse_smt2_string(f"(assert {formula})", decls={str(var): var for var in [a, b, c]})[0]

        eval_result = evaluate_z3_expression(parsed_formula)

        vars = eval_result[0]
        self.assertEqual(3, len(vars))
        self.assertEqual({"a", "b", "c"}, set(vars))

        self.assertTrue(callable(eval_result[1]))
        assgn = {"a": "a", "b": "a", "c": "c"}
        self.assertTrue(eval_result[1](tuple([assgn[var] for var in vars])))
        assgn = {"a": "a", "b": "b", "c": "a"}
        self.assertTrue(eval_result[1](tuple([assgn[var] for var in vars])))
        assgn = {"a": "a", "b": "a", "c": "a"}
        self.assertTrue(eval_result[1](tuple([assgn[var] for var in vars])))
        assgn = {"a": "a", "b": "b", "c": "c"}
        self.assertFalse(eval_result[1](tuple([assgn[var] for var in vars])))

    def test_get_subtrie(self):
        parser = EarleyParser(LANG_GRAMMAR)
        tree = DerivationTree.from_parse_tree(next(parser.parse("x := 1 ; y := x ; y := 2 ; z := y ; x := z")))

        for path, _ in tree.paths():
            subtree_paths = [(p, t) for p, t in get_subtrie(tree.trie(), path).values()]
            self.assertEqual([(p[len(path):], t) for p, t in tree.paths() if p[:len(path)] == path], subtree_paths)

    def test_get_subtrie_artificial(self):
        paths = []
        for l in range(6):
            paths += list(itertools.product(*[[i for i in range(5)] for _ in range(l)]))

        trie = mk_subtree_trie()
        for path in paths:
            trie[path_to_trie_key(path)] = path, None

        for path in paths:
            subtree_paths = [(p, t) for p, t in get_subtrie(trie, path).values()]
            sub_trie_paths = {(p[len(path):], None) for p in paths if p[:len(path)] == path}
            self.assertEqual(
                sub_trie_paths, set(subtree_paths),
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


def parse(inp: str, grammar: Grammar, start_symbol: Optional[str] = None) -> ParseTree:
    if start_symbol is None:
        return next(EarleyParser(grammar).parse(inp))
    else:
        grammar = copy.deepcopy(grammar)
        grammar["<start>"] = [start_symbol]
        delete_unreachable(grammar)
        return next(EarleyParser(grammar).parse(inp))[1][0]
