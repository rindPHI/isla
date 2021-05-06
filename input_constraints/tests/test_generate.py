import copy
import unittest
from typing import Optional

from fuzzingbook.Parser import EarleyParser, canonical
from grammar_graph.gg import GrammarGraph

from input_constraints.generate import insert_before, match_expansions
from input_constraints.helpers import delete_unreachable
from input_constraints.tests.test_data import *


class TestGenerate(unittest.TestCase):
    def test_insert(self):
        def parse(inp: str, start_symbol: Optional[str] = None) -> ParseTree:
            if start_symbol is None:
                return next(EarleyParser(LANG_GRAMMAR).parse(inp))
            else:
                grammar = copy.deepcopy(LANG_GRAMMAR)
                grammar["<start>"] = [start_symbol]
                delete_unreachable(grammar)
                return next(EarleyParser(grammar).parse(inp))[1][0]

        canonical_grammar = canonical(LANG_GRAMMAR)

        inp = "x := 1 ; y := z"
        tree = parse(inp)

        path = (0, 2, 0)
        to_insert = parse("y := 0", "<assgn>")
        result = insert_before(canonical_grammar, to_insert, tree, path)
        self.assertNotEqual(None, result)
        self.assertEqual("x := 1 ; y := 0 ; y := z", tree_to_string(result))

        path = (0, 0)
        result = insert_before(canonical_grammar, to_insert, tree, path)
        self.assertNotEqual(None, result)
        self.assertEqual("y := 0 ; x := 1 ; y := z", tree_to_string(result))

        inp = "x := 1 ; y := 2 ; y := z"
        tree = parse(inp)
        path = (0, 2, 2, 0)
        result = insert_before(canonical_grammar, to_insert, tree, path)
        self.assertNotEqual(None, result)
        self.assertEqual("x := 1 ; y := 2 ; y := 0 ; y := z", tree_to_string(result))

    def test_match_nonterminal_lists(self):
        result = match_expansions(
            GrammarGraph.from_grammar(LANG_GRAMMAR),
            ["<assgn>"],
            ["<assgn>", " ; ", "<stmt>"])

        self.assertEqual([{0: 0}, {0: 2}], result)

        result = match_expansions(
            GrammarGraph.from_grammar(LANG_GRAMMAR),
            ["<assgn>", " ; "],
            ["<assgn>", " ; ", "<stmt>"])

        self.assertEqual([{0: 0}], result)

        result = match_expansions(
            GrammarGraph.from_grammar(LANG_GRAMMAR),
            ["<assgn>", " ; ", "<stmt>"],
            ["<assgn>"])

        self.assertEqual([], result)


if __name__ == '__main__':
    unittest.main()
