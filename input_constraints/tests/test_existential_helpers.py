import unittest

from fuzzingbook.Grammars import JSON_GRAMMAR
from fuzzingbook.Parser import canonical
from grammar_graph.gg import GrammarGraph

from input_constraints import isla
from input_constraints.existential_helpers import insert_tree, match_expansions
from input_constraints.isla import abstract_tree_to_string
from input_constraints.tests.test_data import *
from input_constraints.tests.test_helpers import parse


class TestExistentialHelpers(unittest.TestCase):
    def test_insert_lang(self):
        canonical_grammar = canonical(LANG_GRAMMAR)

        inp = "x := 1 ; y := z"
        tree = parse(inp, LANG_GRAMMAR)

        to_insert = parse("y := 0", LANG_GRAMMAR, "<assgn>")
        results = insert_tree(canonical_grammar, to_insert, tree)
        self.assertIn("x := 1 ; y := 0 ; y := z", [tree_to_string(result[1]) for result in results])
        for path, a_tree in results:
            self.assertEqual(to_insert, get_subtree(path, a_tree))

        results = insert_tree(canonical_grammar, to_insert, tree)
        self.assertIn("y := 0 ; x := 1 ; y := z", [tree_to_string(result[1]) for result in results])
        for path, a_tree in results:
            self.assertEqual(to_insert, get_subtree(path, a_tree))

        inp = "x := 1 ; y := 2 ; y := z"
        tree = parse(inp, LANG_GRAMMAR)
        results = insert_tree(canonical_grammar, to_insert, tree)
        self.assertIn("x := 1 ; y := 2 ; y := 0 ; y := z", [tree_to_string(result[1]) for result in results])
        for path, a_tree in results:
            self.assertEqual(to_insert, get_subtree(path, a_tree))

    def test_insert_json_1(self):
        inp = ' { "T" : { "I" : true , "" : [ false , "salami" ] , "" : true , "" : null , "" : false } } '
        tree = parse(inp, JSON_GRAMMAR)
        to_insert = parse(' "key" : { "key" : null } ', JSON_GRAMMAR, "<member>")

        results = insert_tree(canonical(JSON_GRAMMAR), to_insert, tree)

        self.assertIn(
            ' { "T" : { "I" : true , '
            '"key" : { "key" : null } , '
            '"" : [ false , "salami" ] , "" : true , "" : null , "" : false } } ',
            [tree_to_string(r[1]) for r in results])

        for path, a_tree in results:
            self.assertEqual(to_insert, get_subtree(path, a_tree))

    def test_insert_json_2(self):
        inp = ' { "T" : { "I" : true , "" : [ false , "salami" ] , "" : true , "" : null , "" : false } } '
        tree = parse(inp, JSON_GRAMMAR)
        to_insert = parse(' "cheese" ', JSON_GRAMMAR, "<element>")

        results = insert_tree(canonical(JSON_GRAMMAR), to_insert, tree)
        self.assertIn(
            ' { "T" : { "I" : true , "" : [ false , "cheese" , "salami" ] , "" : true , "" : null , "" : false } } ',
            [tree_to_string(result[1]) for result in results])

        for path, a_tree in results:
            self.assertEqual(to_insert, get_subtree(path, a_tree))

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

    def test_insert_assignment(self):
        assgn = isla.Constant("$assgn", "<assgn>", tuple())
        results = insert_tree(
            canonical(LANG_GRAMMAR),
            (assgn, None),
            ('<start>', [('<stmt>', [('<assgn>', [('<var>', None), (' := ', []), ('<rhs>', [('<var>', None)])])])]))

        self.assertEqual(
            ['<var> := <var> ; $assgn',
             '<var> := <var> ; $assgn ; <stmt>',
             '$assgn ; <var> := <var>',
             '<assgn> ; $assgn ; <var> := <var>',
             ],
            list(map(abstract_tree_to_string, [result[1] for result in results]))
        )


if __name__ == '__main__':
    unittest.main()
