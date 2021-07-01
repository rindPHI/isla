import copy
import unittest
from typing import Optional

from fuzzingbook.Grammars import JSON_GRAMMAR
from fuzzingbook.Parser import canonical
from grammar_graph.gg import GrammarGraph

from input_constraints.existential_helpers import insert_tree, match_expansions
from input_constraints.helpers import delete_unreachable
from input_constraints.tests.test_data import *
from input_constraints.type_defs import Grammar


def parse(inp: str, grammar: Grammar, start_symbol: Optional[str] = None) -> ParseTree:
    if start_symbol is None:
        return next(EarleyParser(grammar).parse(inp))
    else:
        grammar = copy.deepcopy(grammar)
        grammar["<start>"] = [start_symbol]
        delete_unreachable(grammar)
        return next(EarleyParser(grammar).parse(inp))[1][0]


class TestGenerate(unittest.TestCase):
    def test_insert_lang(self):
        canonical_grammar = canonical(LANG_GRAMMAR)

        inp = "x := 1 ; y := z"
        tree = parse(inp, LANG_GRAMMAR)

        path = (0, 2, 0)
        to_insert = parse("y := 0", LANG_GRAMMAR, "<assgn>")
        result = insert_tree(canonical_grammar, to_insert, tree, path)
        self.assertNotEqual(None, result)
        self.assertEqual("x := 1 ; y := 0 ; y := z", tree_to_string(result))

        path = (0, 0)
        result = insert_tree(canonical_grammar, to_insert, tree, path)
        self.assertNotEqual(None, result)
        self.assertEqual("y := 0 ; x := 1 ; y := z", tree_to_string(result))

        inp = "x := 1 ; y := 2 ; y := z"
        tree = parse(inp, LANG_GRAMMAR)
        path = (0, 2, 2, 0)
        result = insert_tree(canonical_grammar, to_insert, tree, path)
        self.assertNotEqual(None, result)
        self.assertEqual("x := 1 ; y := 2 ; y := 0 ; y := z", tree_to_string(result))

    def test_insert_json(self):
        inp = ' { "T" : { "I" : true , "" : [ false , "salami" ] , "" : true , "" : null , "" : false } } '
        tree = parse(inp, JSON_GRAMMAR)
        # print(display_tree(tree))
        to_insert = parse(' "key" : { "key" : null } ', JSON_GRAMMAR, "<member>")

        path = (0, 0, 1, 0, 1, 0, 4, 1, 0, 1, 1, 0, 1, 0)  # '"" : [ false , "salami" ]' (member)
        result = insert_tree(canonical(JSON_GRAMMAR), to_insert, tree, path)
        self.assertNotEqual(None, result)
        self.assertEqual(
            ' { "T" : { "I" : true , '
            '"key" : { "key" : null } , '
            '"" : [ false , "salami" ] , "" : true , "" : null , "" : false } } ',
            tree_to_string(result))

        path = (0, 0, 1, 0, 1, 0, 4, 1, 0, 1, 1, 0, 1, 0, 4, 1, 0, 1, 1, 0, 1, 0)  # ' "salami" ' (element)
        to_insert = parse(' "cheese" ', JSON_GRAMMAR, "<element>")
        result = insert_tree(canonical(JSON_GRAMMAR), to_insert, tree, path)
        self.assertNotEqual(None, result)
        self.assertEqual(
            ' { "T" : { "I" : true , "" : [ false , "cheese" , "salami" ] , "" : true , "" : null , "" : false } } ',
            tree_to_string(result))

        path = (0, 0, 1, 0, 1, 0, 4, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0)  # ' "" : true ' (member)
        result = insert_tree(canonical(JSON_GRAMMAR), to_insert, tree, path)
        self.assertNotEqual(None, result)
        self.assertEqual(
            ' { "T" : { "I" : true , "" : [ false , "salami" , "cheese" ] , "" : true , "" : null , "" : false } } ',
            tree_to_string(result))

        path = (0, 0, 1, 0, 1, 0, 4, 1, 0, 1, 1, 0, 1, 0)  # ' "" : [ false , "salami" ] ' (member)
        result = insert_tree(canonical(JSON_GRAMMAR), to_insert, tree, path)
        self.assertEqual(None, result)

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
