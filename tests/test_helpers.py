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

import copy
import itertools
import unittest
from typing import Optional

import z3
from grammar_graph.gg import GrammarGraph

from isla.existential_helpers import path_to_tree, paths_between
from isla.helpers import (
    is_prefix,
    path_iterator,
    delete_unreachable,
    dict_of_lists_to_list_of_dicts,
    weighted_geometric_mean,
    canonical,
    Exceptional,
    Success,
    eliminate_suffixes,
    to_id,
    is_path,
    pop,
    replace_line_breaks,
    parent_reflexive,
    parent_or_child,
    Failure,
)
from isla.isla_predicates import is_before
from isla.parser import EarleyParser
from isla.type_defs import Grammar, ParseTree
from isla.z3_helpers import evaluate_z3_expression, z3_eq, smt_expr_to_str, DomainError
from test_data import LANG_GRAMMAR


class TestHelpers(unittest.TestCase):
    def test_path_iterator(self):
        prog = "x := 1 ; y := x"
        parser = EarleyParser(LANG_GRAMMAR)
        tree = next(parser.parse(prog))

        paths = [path for path, subtree in list(path_iterator(tree))]
        self.assertEqual(
            [
                (),
                (0,),
                (0, 0),
                (0, 0, 0),
                (0, 0, 0, 0),
                (0, 0, 1),
                (0, 0, 2),
                (0, 0, 2, 0),
                (0, 0, 2, 0, 0),
                (0, 1),
                (0, 2),
                (0, 2, 0),
                (0, 2, 0, 0),
                (0, 2, 0, 0, 0),
                (0, 2, 0, 1),
                (0, 2, 0, 2),
                (0, 2, 0, 2, 0),
                (0, 2, 0, 2, 0, 0),
            ],
            paths,
        )

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
        self.assertEqual(
            [
                ("<stmt>", [("<assgn>", None), (" ; ", []), ("<stmt>", None)]),
                ("<stmt>", [("<assgn>", None)]),
            ],
            [
                tree.to_parse_tree()
                for tree in path_to_tree(canonical(LANG_GRAMMAR), ["<stmt>", "<assgn>"])
            ],
        )

        self.assertEqual(
            [("<stmt>", [("<assgn>", None), (" ; ", []), ("<stmt>", None)])],
            [
                tree.to_parse_tree()
                for tree in path_to_tree(canonical(LANG_GRAMMAR), ["<stmt>", "<stmt>"])
            ],
        )

        self.assertEqual(
            [
                (
                    "<stmt>",
                    [
                        (
                            "<assgn>",
                            [
                                ("<var>", None),
                                (" := ", []),
                                ("<rhs>", [("<digit>", None)]),
                            ],
                        ),
                        (" ; ", []),
                        ("<stmt>", None),
                    ],
                ),
                (
                    "<stmt>",
                    [
                        (
                            "<assgn>",
                            [
                                ("<var>", None),
                                (" := ", []),
                                ("<rhs>", [("<digit>", None)]),
                            ],
                        )
                    ],
                ),
            ],
            [
                tree.to_parse_tree()
                for tree in path_to_tree(
                    canonical(LANG_GRAMMAR), ["<stmt>", "<assgn>", "<rhs>", "<digit>"]
                )
            ],
        )

    def test_find_all_paths(self):
        graph = GrammarGraph.from_grammar(LANG_GRAMMAR)
        self.assertEqual(
            [("<stmt>", "<assgn>", "<var>"), ("<stmt>", "<assgn>", "<rhs>", "<var>")],
            list(paths_between(graph, "<stmt>", "<var>")),
        )

        self.assertEqual(
            [("<stmt>", "<stmt>")], list(paths_between(graph, "<stmt>", "<stmt>"))
        )

        self.assertFalse(list(paths_between(graph, "<assgn>", "<stmt>")))

        self.assertFalse(list(paths_between(graph, "<assgn>", "<assgn>")))

    def test_dict_of_lists_to_list_of_dicts(self):
        self.assertEqual(
            [{1: 3, 2: 5}, {1: 3, 2: 6}],
            dict_of_lists_to_list_of_dicts({1: [3], 2: [5, 6]}),
        )

        self.assertEqual(
            [{1: 3, 2: 5}, {1: 4, 2: 5}],
            dict_of_lists_to_list_of_dicts({1: [3, 4], 2: [5]}),
        )

        self.assertEqual(
            [{1: 3, 2: 5}, {1: 3, 2: 6}, {1: 4, 2: 5}, {1: 4, 2: 6}],
            dict_of_lists_to_list_of_dicts({1: [3, 4], 2: [5, 6]}),
        )

        self.assertEqual(
            [
                {1: 3, 2: 5, 7: 8},
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
                {1: 4, 2: 6, 7: 10},
            ],
            dict_of_lists_to_list_of_dicts({1: [3, 4], 2: [5, 6], 7: [8, 9, 10]}),
        )

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

        parsed_formula = z3.parse_smt2_string(
            f"(assert {formula.replace('<DATE>', '2022-02-24')})"
        )[0]
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
        parsed_formula = z3.parse_smt2_string(
            f"(assert {formula})", decls={"var": var}
        )[0]
        eval_result = evaluate_z3_expression(parsed_formula)

        self.assertEqual(("var",), eval_result[0])
        self.assertTrue(callable(eval_result[1]))
        self.assertTrue(eval_result[1](("2022-02-24",)))
        self.assertFalse(eval_result[1](("24-02-2022",)))

    def test_evaluate_z3_multivar_expr(self):
        formula = "(or (= a b) (= a c))"

        a, b, c = z3.Strings("a b c")
        parsed_formula = z3.parse_smt2_string(
            f"(assert {formula})", decls={str(var): var for var in [a, b, c]}
        )[0]

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

    def test_exception_monad(self):
        self.assertEqual(
            -1,
            Exceptional.of(lambda: 1 // 0).recover(lambda _: -1, ZeroDivisionError).a,
        )

        self.assertEqual(
            6,
            Exceptional.of(lambda: 4 // 2)
            .bind(lambda v: Exceptional.of(lambda: 3 * v))
            .recover(lambda _: -1, ZeroDivisionError)
            .a,
        )

        self.assertEqual(
            6,
            Exceptional.of(lambda: 4 // 2)
            .map(lambda v: 3 * v)
            .recover(lambda _: -1, ZeroDivisionError)
            .a,
        )

        self.assertEqual(
            -1,
            Exceptional.of(lambda: 4 // 2)
            .map(lambda v: v // 0)
            .recover(lambda _: -1, ZeroDivisionError)
            .a,
        )

        self.assertEqual(
            -1,
            Exceptional.of(lambda: 4 // 0)
            .bind(lambda v: Success(lambda: 3 * v))
            .recover(lambda _: -1, ZeroDivisionError)
            .a,
        )

    def test_eliminate_suffixes(self):
        self.assertEqual([(0,), (0,)], eliminate_suffixes([(0,), (0,)]))

        self.assertEqual(
            [(0, 2, 0, 2), (0, 0, 0)], eliminate_suffixes([(0, 2, 0, 2), (0, 0, 0)])
        )

        for permutation in itertools.permutations(
            [
                (0, 2),
                (0, 2, 0, 2),
                (1, 0),
            ],
            3,
        ):
            self.assertEqual(
                {
                    (0, 2),
                    (1, 0),
                },
                set(eliminate_suffixes(permutation)),
            )

    def test_to_id(self):
        x = 17

        def f(inp):
            nonlocal x
            x = inp

        self.assertEqual(-12, to_id(f)(-12))
        self.assertEqual(-12, x)

    def test_is_path(self):
        self.assertTrue(is_path((1, 2, 3)))
        self.assertFalse(is_path((1, 2, "a")))
        self.assertFalse(is_path([1, 2]))

    def test_pop(self):
        l = [1, 2, 3]
        self.assertEqual(1, pop(l))
        self.assertEqual([2, 3], l)
        self.assertEqual(3, pop(l, index=1))
        self.assertEqual([2], l)
        self.assertEqual(42, pop([], 42))
        self.assertEqual(None, pop([]))

    def test_replace_line_breaks(self):
        self.assertEqual(rf"a\nb", replace_line_breaks("a\nb"))

    def test_parent_reflexive(self):
        self.assertTrue(parent_reflexive((1, 2), (1, 2)))
        self.assertTrue(parent_reflexive((1, 2), (1, 2, 3)))
        self.assertFalse(parent_reflexive((1, 2, 3), (1, 2)))

    def test_parent_or_child(self):
        self.assertTrue(parent_or_child((1, 2), (1, 2, 3)))
        self.assertTrue(parent_or_child((1, 2, 3), (1, 2)))
        self.assertFalse(parent_or_child((1, 3, 2), (1, 2)))
        self.assertFalse(
            parent_or_child(
                (1, 2),
                (1, 3, 2),
            )
        )

    def test_delete_unreachable(self):
        grammar = {"<start>": ["<b>"], "<a>": ["a"], "<b>": ["b"]}
        expected = {"<start>": ["<b>"], "<b>": ["b"]}
        grammar = delete_unreachable(grammar)
        self.assertEqual(expected, grammar)

        grammar = {"<start>": ["<a><b>"], "<a>": ["a"], "<b>": ["b"]}
        expected = {"<start>": ["<a><b>"], "<a>": ["a"], "<b>": ["b"]}
        grammar = delete_unreachable(grammar)
        self.assertEqual(expected, grammar)

    def test_exceptional_reraise(self):
        try:
            Exceptional.of(lambda: 1 // 0).reraise()
            self.fail()
        except ZeroDivisionError:
            pass

        Exceptional.of(lambda: 2 // 1).reraise()

    def test_recover(self):
        self.assertEqual(
            Success(True), Exceptional.of(lambda: 1 // 0).recover(lambda _: True)
        )

        self.assertEqual(
            Success(True),
            Exceptional.of(lambda: 1 // 0).recover(lambda _: True, ZeroDivisionError),
        )

        self.assertIsInstance(
            Exceptional.of(lambda: 1 // 0).recover(lambda _: True, SyntaxError), Failure
        )

    def test_evaluate_empty_str_to_int(self):
        f = z3.StrToInt(z3.StringVal(""))

        try:
            evaluate_z3_expression(f)
            self.fail("Expected exception")
        except DomainError as err:
            self.assertIn("Empty string cannot be converted to int", str(err))


def parse(inp: str, grammar: Grammar, start_symbol: Optional[str] = None) -> ParseTree:
    if start_symbol is None:
        try:
            return next(EarleyParser(grammar).parse(inp))
        except SyntaxError as err:
            print(f"Syntax error; input: '{inp}', grammar:\n{grammar}")
            raise err
    else:
        grammar = copy.deepcopy(grammar) | {"<start>": [start_symbol]}
        grammar = delete_unreachable(grammar)
        return next(EarleyParser(grammar).parse(inp))[1][0]


if __name__ == "__main__":
    unittest.main()
