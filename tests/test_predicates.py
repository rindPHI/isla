import copy
import random
import unittest

import pytest
from grammar_graph import gg

from isla import language
from isla.derivation_tree import DerivationTree
from isla.evaluator import evaluate
from isla.fuzzer import GrammarCoverageFuzzer
from isla.helpers import delete_unreachable, is_nonterminal
from isla.isla_predicates import (
    embed_tree,
    mk_parser,
    level_check,
    is_nth,
    NTH_PREDICATE,
    DIRECT_CHILD_PREDICATE,
    octal_to_dec,
)
from isla.language import parse_isla, SemPredEvalResult
from isla.parser import EarleyParser
from isla.solver import ISLaSolver
from isla.type_defs import Path
from isla_formalizations import tar, rest, scriptsizec
from isla_formalizations.csv import CSV_GRAMMAR
from isla_formalizations.tar import octal_conv_grammar
from isla_formalizations.xml_lang import XML_GRAMMAR
from test_data import LANG_GRAMMAR


class TestPredicates(unittest.TestCase):
    def test_embed_tree_1(self):
        orig_tree = DerivationTree.from_parse_tree(
            (
                "<file_mode>",
                [
                    (
                        "<padded_octal_digits>",
                        [
                            (
                                "<maybe_zeroes>",
                                [
                                    (
                                        "<zeroes>",
                                        [
                                            ("<ZERO>", [("0", [])]),
                                            ("<zeroes>", [("<ZERO>", [("0", [])])]),
                                        ],
                                    )
                                ],
                            ),
                            (
                                "<maybe_octal_digits>",
                                [("<octal_digits>", [("<octal_digit>", [("7", [])])])],
                            ),
                        ],
                    ),
                    ("<SPACE>", [(" ", [])]),
                    ("<NUL>", [("\x00", [])]),
                ],
            )
        )

        padded_tree = DerivationTree.from_parse_tree(
            (
                "<file_mode>",
                [
                    (
                        "<padded_octal_digits>",
                        [
                            (
                                "<maybe_zeroes>",
                                [
                                    (
                                        "<zeroes>",
                                        [
                                            ("<ZERO>", [("0", [])]),
                                            (
                                                "<zeroes>",
                                                [
                                                    ("<ZERO>", [("0", [])]),
                                                    (
                                                        "<zeroes>",
                                                        [("<ZERO>", [("0", [])])],
                                                    ),
                                                ],
                                            ),
                                        ],
                                    )
                                ],
                            ),
                            (
                                "<maybe_octal_digits>",
                                [("<octal_digits>", [("<octal_digit>", [("7", [])])])],
                            ),
                        ],
                    ),
                    ("<SPACE>", [(" ", [])]),
                    ("<NUL>", [("\x00", [])]),
                ],
            )
        )

        one_expected_match = {
            (0, 1): (0, 1),
            (0, 0, 0, 1): (0, 0, 0),
            (1,): (1,),
            (2,): (2,),
        }

        result = embed_tree(orig_tree, padded_tree)

        self.assertIn(one_expected_match, result)

        self.assertTrue(
            all(
                all(
                    any(
                        len(assgn_path) <= len(leaf_path)
                        and leaf_path[: len(assgn_path)] == assgn_path
                        for _, assgn_path in assignment.items()
                    )
                    for leaf_path, _ in orig_tree.leaves()
                )
                for assignment in result
            )
        )

    def test_embed_tree_2(self):
        grammar = dict(tar.TAR_GRAMMAR)
        grammar["<start>"] = ["<file_size>"]
        delete_unreachable(grammar)
        parser = EarleyParser(grammar)

        orig_tree = DerivationTree.from_parse_tree(next(parser.parse("032251413 ")))
        padded_tree = DerivationTree.from_parse_tree(next(parser.parse("0032251413 ")))

        one_expected_match = {(0, 0, 1): (0, 0), (0, 1): (0, 1)}

        result = embed_tree(orig_tree, padded_tree)

        self.assertIn(one_expected_match, result)

        self.assertTrue(
            all(
                all(
                    any(
                        len(assgn_path) <= len(leaf_path)
                        and leaf_path[: len(assgn_path)] == assgn_path
                        for _, assgn_path in assignment.items()
                    )
                    for leaf_path, _ in orig_tree.leaves()
                )
                for assignment in result
            )
        )

    def test_embed_tree_3(self):
        grammar = dict(tar.TAR_GRAMMAR)
        grammar["<start>"] = ["<file_size>"]
        delete_unreachable(grammar)
        parser = EarleyParser(grammar)

        orig_tree = DerivationTree.from_parse_tree(next(parser.parse("0111111 ")))
        padded_tree = DerivationTree.from_parse_tree(next(parser.parse("00111111 ")))

        one_expected_match = {(0, 0, 1): (0, 0), (0, 1): (0, 1)}

        result = list(embed_tree(orig_tree, padded_tree))
        print(len(result))

        self.assertIn(one_expected_match, result)

        self.assertTrue(
            all(
                all(
                    any(
                        len(assgn_path) <= len(leaf_path)
                        and leaf_path[: len(assgn_path)] == assgn_path
                        for _, assgn_path in assignment.items()
                    )
                    for leaf_path, _ in orig_tree.leaves()
                )
                for assignment in result
            )
        )

    def test_parse_tar_heading(self):
        parser = mk_parser(rest.REST_GRAMMAR)("<underline>")
        print(parser("-----"))

    def test_level(self):
        correct_inp_1 = "{int x = 0;x;}"
        correct_inp_2 = "{int x = 0;{x;}}"
        correct_inp_3 = "{int x = 0;{{x;}}}"
        wrong_inp_1 = "{{int x = 0;}x;}"
        wrong_inp_2 = "{{int x = 0;}{x;}}"

        def get_assignment(tree: DerivationTree) -> Path:
            return tree.filter(lambda n: n.value == "<declaration>")[0][0]

        def get_x(tree: DerivationTree) -> Path:
            return tree.filter(lambda n: n.value == "<statement>" and str(n) == "x;")[
                0
            ][0]

        def to_tree(inp: str) -> DerivationTree:
            parser = EarleyParser(scriptsizec.SCRIPTSIZE_C_GRAMMAR)
            return DerivationTree.from_parse_tree(next(parser.parse(inp)))

        t = to_tree(correct_inp_1)
        x, a = get_x(t), get_assignment(t)
        for a1, a2 in [(x, a), (a, x)]:
            self.assertTrue(level_check(t, "EQ", "<block>", a1, a2))
            self.assertTrue(level_check(t, "LE", "<block>", a1, a2))
            self.assertTrue(level_check(t, "GE", "<block>", a1, a2))
            self.assertFalse(level_check(t, "LT", "<block>", a1, a2))
            self.assertFalse(level_check(t, "GT", "<block>", a1, a2))

        for inp in [correct_inp_2, correct_inp_3]:
            t = to_tree(inp)
            x, a = get_x(t), get_assignment(t)
            self.assertFalse(level_check(t, "EQ", "<block>", x, a))
            self.assertFalse(level_check(t, "EQ", "<block>", a, x))
            self.assertTrue(level_check(t, "LE", "<block>", x, a))
            self.assertFalse(level_check(t, "LE", "<block>", a, x))
            self.assertTrue(level_check(t, "GE", "<block>", a, x))
            self.assertFalse(level_check(t, "GE", "<block>", x, a))
            self.assertTrue(level_check(t, "LT", "<block>", x, a))
            self.assertFalse(level_check(t, "LT", "<block>", a, x))
            self.assertTrue(level_check(t, "GT", "<block>", a, x))
            self.assertFalse(level_check(t, "GT", "<block>", x, a))

        # TODO wrong_input_*

    def test_octal_to_decimal_concrete_octal(self):
        decimal = language.BoundVariable(
            "decimal", language.BoundVariable.NUMERIC_NTYPE
        )
        graph = gg.GrammarGraph.from_grammar(octal_conv_grammar)
        decimal_parser = mk_parser(graph.grammar)("<decimal_digits>")
        octal_parser = mk_parser(graph.grammar)("<octal_digits>")
        octal = DerivationTree.from_parse_tree(octal_parser("7123")[0]).children[0]

        expected_decimal = DerivationTree.from_parse_tree(
            decimal_parser("3667")[0]
        ).children[0]

        result = octal_to_dec(
            mk_parser(graph.grammar)("<octal_digits>"),
            mk_parser(graph.grammar)("<decimal_digits>"),
            octal,
            decimal,
        )

        self.assertTrue(isinstance(result, SemPredEvalResult))
        self.assertTrue(result.ready())
        self.assertTrue(isinstance(result.result, dict))
        self.assertEqual(1, len(result.result))
        self.assertEqual(decimal, next(iter(result.result.keys())))
        self.assertTrue(expected_decimal.structurally_equal(result.result[decimal]))

    def test_octal_to_decimal_concrete_decimal(self):
        octal = language.BoundVariable("octal", language.BoundVariable.NUMERIC_NTYPE)
        graph = gg.GrammarGraph.from_grammar(octal_conv_grammar)
        decimal_parser = mk_parser(graph.grammar)("<decimal_digits>")
        octal_parser = mk_parser(graph.grammar)("<octal_digits>")
        decimal = DerivationTree.from_parse_tree(decimal_parser("9123")[0]).children[0]

        expected_octal = DerivationTree.from_parse_tree(
            octal_parser("21643")[0]
        ).children[0]

        result = octal_to_dec(
            mk_parser(graph.grammar)("<octal_digits>"),
            mk_parser(graph.grammar)("<decimal_digits>"),
            octal,
            decimal,
        )

        self.assertTrue(isinstance(result, SemPredEvalResult))
        self.assertTrue(result.ready())
        self.assertTrue(isinstance(result.result, dict))
        self.assertEqual(1, len(result.result))
        self.assertEqual(octal, next(iter(result.result.keys())))
        self.assertTrue(expected_octal.structurally_equal(result.result[octal]))

    def test_octal_to_decimal_fuzz(self):
        decimal_grammar = copy.deepcopy(octal_conv_grammar)
        decimal_grammar["<start>"] = ["<decimal_digits>"]
        delete_unreachable(decimal_grammar)
        decimal_fuzzer = GrammarCoverageFuzzer(decimal_grammar)

        octal_grammar = copy.deepcopy(octal_conv_grammar)
        octal_grammar["<start>"] = ["<octal_digits>"]
        delete_unreachable(octal_grammar)
        octal_fuzzer = GrammarCoverageFuzzer(octal_grammar)

        def decimal_value():
            if random.random() < 0.3:
                return language.BoundVariable(
                    "decimal", language.BoundVariable.NUMERIC_NTYPE
                )

            tree = decimal_fuzzer.fuzz_tree().children[0]

            if random.random() < 0.5:
                return tree

            path, node = random.choice(tree.paths())
            if is_nonterminal(node.value):
                return tree.replace_path(path, DerivationTree(node.value))
            else:
                return tree

        def octal_value():
            if random.random() < 0.3:
                return language.BoundVariable(
                    "octal", language.BoundVariable.NUMERIC_NTYPE
                )

            tree = octal_fuzzer.fuzz_tree().children[0]

            if random.random() < 0.5:
                return tree

            path, node = random.choice(tree.paths())
            if is_nonterminal(node.value):
                return tree.replace_path(path, DerivationTree(node.value))
            else:
                return tree

        graph = gg.GrammarGraph.from_grammar(octal_conv_grammar)

        for _ in range(500):
            octal = octal_value()
            decimal = decimal_value()
            try:
                result = octal_to_dec(
                    mk_parser(graph.grammar)("<octal_digits>"),
                    mk_parser(graph.grammar)("<decimal_digits>"),
                    octal,
                    decimal,
                )

                if (
                    (
                        isinstance(octal, language.BoundVariable)
                        or not octal.is_complete()
                    )
                    and isinstance(decimal, DerivationTree)
                    and decimal.is_complete()
                ):
                    self.assertEqual(
                        oct(int(str(decimal)))[2:], str(result.result[octal])
                    )
                elif (
                    (
                        isinstance(decimal, language.BoundVariable)
                        or not decimal.is_complete()
                    )
                    and isinstance(octal, DerivationTree)
                    and octal.is_complete()
                ):
                    self.assertEqual(
                        str(eval("0o" + str(octal))), str(result.result[decimal])
                    )
                elif isinstance(octal, language.BoundVariable) or isinstance(
                    decimal, language.BoundVariable
                ):
                    self.assertTrue(
                        not isinstance(octal, language.BoundVariable)
                        or isinstance(decimal, DerivationTree)
                        and not decimal.is_complete()
                    )
                    self.assertTrue(
                        not isinstance(decimal, language.BoundVariable)
                        or isinstance(octal, DerivationTree)
                        and not octal.is_complete()
                    )
                else:
                    self.assertTrue(isinstance(octal, DerivationTree))
                    self.assertTrue(isinstance(decimal, DerivationTree))

                    if octal.is_complete() and decimal.is_complete():
                        self.assertTrue(oct(int(str(decimal)))[2:], str(octal))
                    else:
                        self.assertTrue(not result.ready())

                # No crash
            except AssertionError:
                self.assertTrue(type(octal) == type(decimal) == language.BoundVariable)

    def test_nth_predicate(self):
        csv_doc = DerivationTree.from_parse_tree(
            next(EarleyParser(CSV_GRAMMAR).parse("a;b;c;d\n"))
        )

        csv_row = csv_doc.get_subtree((0, 0, 0, 0))
        self.assertEqual("a;b;c;d", str(csv_row))
        self.assertEqual("<csv-string-list>", csv_row.value)

        c_column = csv_doc.get_subtree((0, 0, 0, 0, 2, 2, 0))
        self.assertEqual("c", str(c_column))
        self.assertEqual("<raw-field>", c_column.value)

        self.assertTrue(is_nth(csv_doc, "3", (0, 0, 0, 0, 2, 2, 0), (0, 0, 0, 0)))
        self.assertFalse(is_nth(csv_doc, "2", (0, 0, 0, 0, 2, 2, 0), (0, 0, 0, 0)))

        formula = parse_isla(
            """
        forall <csv-record> row in start:
          forall <raw-field> column in row:
            (nth("3", column, row) implies (= column "c"))""",
            CSV_GRAMMAR,
            structural_predicates={NTH_PREDICATE},
        )
        self.assertTrue(evaluate(formula, csv_doc, CSV_GRAMMAR))

        formula = parse_isla(
            """
        forall <csv-record> row in start:
          forall <raw-field> column in row:
            (nth("2", column, row) implies (= column "c"))""",
            CSV_GRAMMAR,
            structural_predicates={NTH_PREDICATE},
        )
        self.assertFalse(evaluate(formula, csv_doc, CSV_GRAMMAR))

        formula = parse_isla(
            """
forall <csv-record> row in start:
  forall <csv-string-list> column in row:
    (nth("3", column, row) implies (= column "c"))""",
            CSV_GRAMMAR,
            structural_predicates={NTH_PREDICATE},
        )
        self.assertFalse(evaluate(formula, csv_doc, CSV_GRAMMAR))

    def test_direct_child_predicate(self):
        formula = parse_isla(
            r"""
forall <xml-open-tag> ot in <start>:
    exists <xml-attribute> attr in ot:
        (direct_child(attr, ot) and attr = "id=\"asdf\"")
""",
            structural_predicates={DIRECT_CHILD_PREDICATE},
        )

        good_tree = DerivationTree.from_parse_tree(
            next(
                EarleyParser(XML_GRAMMAR).parse('<a id="asdf"><b c="d" id="asdf"/></a>')
            )
        )

        self.assertTrue(evaluate(formula, good_tree, XML_GRAMMAR))

        bad_tree_1 = DerivationTree.from_parse_tree(
            next(EarleyParser(XML_GRAMMAR).parse("<a>b</a>"))
        )
        bad_tree_2 = DerivationTree.from_parse_tree(
            next(EarleyParser(XML_GRAMMAR).parse('<a><b c="d" id="asdf"/></a>'))
        )

        self.assertTrue(evaluate(formula, bad_tree_1, XML_GRAMMAR).is_false())
        self.assertTrue(evaluate(formula, bad_tree_2, XML_GRAMMAR).is_false())

    @pytest.mark.skip("Fix!")
    def test_count_pred_var_as_third_arg(self):
        solver = ISLaSolver(
            LANG_GRAMMAR,
            """
forall <rhs> in <assgn>:
  exists <assgn> declaration:
    (before(declaration, <assgn>) and
    <rhs>.<var> = declaration.<var>) and
count(start, "<assgn>", "5")""",
        )
        solution = solver.fuzz()
        self.assertEqual(5, len(solution.filter(lambda n: n.value == "<assgn>")))


if __name__ == "__main__":
    unittest.main()
