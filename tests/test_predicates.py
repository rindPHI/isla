import unittest

import z3
from fuzzingbook.Parser import EarleyParser
from orderedset import OrderedSet

from isla import language
from isla.evaluator import evaluate
from isla.helpers import delete_unreachable
from isla.isla_predicates import embed_tree, mk_parser, level_check, OCTAL_TO_DEC_PREDICATE
from isla.language import DerivationTree
from isla.type_defs import Path
from isla_formalizations import tar, rest, scriptsizec
from isla_formalizations.tar import TAR_GRAMMAR, octal_conv_grammar


class TestPredicates(unittest.TestCase):
    def test_embed_tree_1(self):
        orig_tree = DerivationTree.from_parse_tree(
            ('<file_mode>', [
                ('<padded_octal_digits>', [
                    ('<maybe_zeroes>', [
                        ('<zeroes>', [('<ZERO>', [('0', [])]), ('<zeroes>', [('<ZERO>', [('0', [])])])])]),
                    ('<maybe_octal_digits>', [('<octal_digits>', [('<octal_digit>', [('7', [])])])])]),
                ('<SPACE>', [(' ', [])]), ('<NUL>', [('\x00', [])])]))

        padded_tree = DerivationTree.from_parse_tree(
            ('<file_mode>', [
                ('<padded_octal_digits>', [
                    ('<maybe_zeroes>', [
                        ('<zeroes>', [
                            ('<ZERO>', [('0', [])]),
                            ('<zeroes>', [('<ZERO>', [('0', [])]), ('<zeroes>', [('<ZERO>', [('0', [])])])])])]),
                    ('<maybe_octal_digits>', [
                        ('<octal_digits>', [('<octal_digit>', [('7', [])])])])]),
                ('<SPACE>', [(' ', [])]), ('<NUL>', [('\x00', [])])]))

        one_expected_match = {
            (0, 1): (0, 1),
            (0, 0, 0, 1): (0, 0, 0),
            (1,): (1,),
            (2,): (2,)
        }

        result = embed_tree(orig_tree, padded_tree)

        self.assertIn(one_expected_match, result)

        self.assertTrue(
            all(
                all(
                    any(
                        len(assgn_path) <= len(leaf_path) and
                        leaf_path[:len(assgn_path)] == assgn_path
                        for _, assgn_path in assignment.items())
                    for leaf_path, _ in orig_tree.leaves())
                for assignment in result))

    def test_embed_tree_2(self):
        grammar = dict(tar.TAR_GRAMMAR)
        grammar["<start>"] = ["<file_size>"]
        delete_unreachable(grammar)
        parser = EarleyParser(grammar)

        orig_tree = DerivationTree.from_parse_tree(list(parser.parse("032251413 "))[0])
        padded_tree = DerivationTree.from_parse_tree(list(parser.parse("0032251413 "))[0])

        one_expected_match = {
            (0, 0, 1): (0, 0),
            (0, 1): (0, 1)
        }

        result = embed_tree(orig_tree, padded_tree)

        self.assertIn(one_expected_match, result)

        self.assertTrue(
            all(
                all(
                    any(
                        len(assgn_path) <= len(leaf_path) and
                        leaf_path[:len(assgn_path)] == assgn_path
                        for _, assgn_path in assignment.items())
                    for leaf_path, _ in orig_tree.leaves())
                for assignment in result))

    def test_embed_tree_3(self):
        grammar = dict(tar.TAR_GRAMMAR)
        grammar["<start>"] = ["<file_size>"]
        delete_unreachable(grammar)
        parser = EarleyParser(grammar)

        orig_tree = DerivationTree.from_parse_tree(list(parser.parse("0111111 "))[0])
        padded_tree = DerivationTree.from_parse_tree(list(parser.parse("00111111 "))[0])

        one_expected_match = {
            (0, 0, 1): (0, 0),
            (0, 1): (0, 1)
        }

        result = list(embed_tree(orig_tree, padded_tree))
        print(len(result))

        self.assertIn(one_expected_match, result)

        self.assertTrue(
            all(
                all(
                    any(
                        len(assgn_path) <= len(leaf_path) and
                        leaf_path[:len(assgn_path)] == assgn_path
                        for _, assgn_path in assignment.items())
                    for leaf_path, _ in orig_tree.leaves())
                for assignment in result))

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
            return tree.filter(lambda n: n.value == "<statement>" and str(n) == "x;")[0][0]

        def to_tree(inp: str) -> DerivationTree:
            parser = EarleyParser(scriptsizec.SCRIPTSIZE_C_GRAMMAR)
            return DerivationTree.from_parse_tree(list(parser.parse(inp))[0])

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

    def test_octal_to_decimal(self):
        decimal = language.BoundVariable("decimal", "NUM")
        tree = DerivationTree('<octal_digits>', (
            DerivationTree('<octal_digit>', (
                DerivationTree('0', ()),)),
            DerivationTree('<octal_digits>', (
                DerivationTree('<octal_digit>', (
                    DerivationTree('0', (), ),), ),
                DerivationTree('<octal_digits>', (
                    DerivationTree('<octal_digit>', (
                        DerivationTree('0', ()),)),
                    DerivationTree('<octal_digits>', (
                        DerivationTree('<octal_digit>', (
                            DerivationTree('0', ()),)),
                        DerivationTree('<octal_digits>', (
                            DerivationTree('<octal_digit>', (
                                DerivationTree('0', ()),)),
                            DerivationTree('<octal_digits>', (
                                DerivationTree('<octal_digit>', (
                                    DerivationTree('0', ()),)),
                                DerivationTree('<octal_digits>', (
                                    DerivationTree('<octal_digit>', (
                                        DerivationTree('0', ()),)),
                                    DerivationTree('<octal_digits>', (
                                        DerivationTree('<octal_digit>', (
                                            DerivationTree('0', ()),)),
                                        DerivationTree('<octal_digits>', (
                                            DerivationTree('<octal_digit>', (
                                                DerivationTree('0', ()),)),
                                            DerivationTree('<octal_digits>', (
                                                DerivationTree('<octal_digit>', (
                                                    DerivationTree('1', ()),)),
                                                DerivationTree('<octal_digits>', (
                                                    DerivationTree('<octal_digit>', (
                                                        DerivationTree('4', ()),)),))), )))))))))))))))))))

        formula = language.ExistsIntFormula(
            decimal,
            language.SMTFormula(z3.StrToInt(decimal.to_smt()) >= z3.IntVal(10), decimal) &
            language.SMTFormula(z3.StrToInt(decimal.to_smt()) <= z3.IntVal(100), decimal, ) &
            language.SemanticPredicateFormula(
                OCTAL_TO_DEC_PREDICATE(octal_conv_grammar, "<octal_digits>", "<decimal_digits>"),
                tree, decimal),
        )

        self.assertTrue(evaluate(formula, tree, TAR_GRAMMAR))


if __name__ == '__main__':
    unittest.main()
