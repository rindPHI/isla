import unittest
from fuzzingbook.Parser import EarleyParser

from input_constraints.helpers import delete_unreachable
from input_constraints.isla import DerivationTree
from input_constraints.isla_predicates import embed_tree, mk_parser
from input_constraints.tests.subject_languages import tar, rest


class TestSemanticPredicates(unittest.TestCase):
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


if __name__ == '__main__':
    unittest.main()
