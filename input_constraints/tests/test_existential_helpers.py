import unittest

from fuzzingbook.Grammars import JSON_GRAMMAR
from fuzzingbook.Parser import canonical
from grammar_graph.gg import GrammarGraph

from input_constraints import isla
from input_constraints.existential_helpers import insert_tree, wrap_in_tree_starting_in
from input_constraints.isla import DerivationTree
from input_constraints.tests.test_data import *
from input_constraints.tests.test_helpers import parse
from input_constraints.tests.tinyc import TINYC_GRAMMAR


class TestExistentialHelpers(unittest.TestCase):
    def test_insert_lang(self):
        canonical_grammar = canonical(LANG_GRAMMAR)

        inp = "x := 1 ; y := z"
        tree = DerivationTree.from_parse_tree(parse(inp, LANG_GRAMMAR))

        to_insert = DerivationTree.from_parse_tree(parse("y := 0", LANG_GRAMMAR, "<assgn>"))
        results = insert_tree(canonical_grammar, to_insert, tree)
        self.assertIn("x := 1 ; y := 0 ; y := z", map(str, results))

        results = insert_tree(canonical_grammar, to_insert, tree)
        self.assertIn("y := 0 ; x := 1 ; y := z", map(str, results))

        inp = "x := 1 ; y := 2 ; y := z"
        tree = DerivationTree.from_parse_tree(parse(inp, LANG_GRAMMAR))
        results = insert_tree(canonical_grammar, to_insert, tree)
        self.assertIn("x := 1 ; y := 2 ; y := 0 ; y := z", map(str, results))

    def test_insert_json_1(self):
        inp = ' { "T" : { "I" : true , "" : [ false , "salami" ] , "" : true , "" : null , "" : false } } '
        tree = DerivationTree.from_parse_tree(parse(inp, JSON_GRAMMAR))
        to_insert = DerivationTree.from_parse_tree(parse(' "key" : { "key" : null } ', JSON_GRAMMAR, "<member>"))

        results = insert_tree(canonical(JSON_GRAMMAR), to_insert, tree)

        self.assertIn(
            ' { "T" : { "I" : true , '
            '"key" : { "key" : null } , '
            '"" : [ false , "salami" ] , "" : true , "" : null , "" : false } } ',
            [result.to_string() for result in results])

    def test_insert_json_2(self):
        inp = ' { "T" : { "I" : true , "" : [ false , "salami" ] , "" : true , "" : null , "" : false } } '
        tree = DerivationTree.from_parse_tree(parse(inp, JSON_GRAMMAR))
        to_insert = DerivationTree.from_parse_tree(parse(' "cheese" ', JSON_GRAMMAR, "<element>"))

        results = insert_tree(canonical(JSON_GRAMMAR), to_insert, tree)
        self.assertIn(
            ' { "T" : { "I" : true , "" : [ false , "cheese" , "salami" ] , "" : true , "" : null , "" : false } } ',
            [result.to_string() for result in results])

    def test_insert_assignment(self):
        assgn = isla.Constant("$assgn", "<assgn>")
        tree = ('<start>', [('<stmt>', [('<assgn>', [('<var>', None), (' := ', []), ('<rhs>', [('<var>', None)])])])])
        results = insert_tree(
            canonical(LANG_GRAMMAR),
            DerivationTree(assgn),
            DerivationTree.from_parse_tree(tree))

        self.assertEqual(
            ['<var> := <var> ; $assgn',
             '<var> := <var> ; $assgn ; <stmt>',
             '$assgn ; <var> := <var>',
             '<assgn> ; $assgn ; <var> := <var>',
             ],
            list(map(str, results))
        )

    def test_insert_assignment_2(self):
        lhs = isla.Constant("$lhs", "<var>")
        var = isla.Constant("$var", "<var>")

        tree = ('<start>', [('<stmt>', [('<assgn>', [(lhs, None), (' := ', []), ('<rhs>', [(var, None)])])])])

        results = insert_tree(canonical(LANG_GRAMMAR),
                              DerivationTree("<assgn>", None),
                              DerivationTree.from_parse_tree(tree))

        self.assertEqual(
            ['$lhs := $var ; <assgn>',
             '$lhs := $var ; <assgn> ; <stmt>',
             '<assgn> ; $lhs := $var',
             '<assgn> ; <assgn> ; $lhs := $var'],
            list(map(str, results))
        )

    def test_insert_tinyc_assignment(self):
        tree = DerivationTree.from_parse_tree(('<start>', [
            ('<mwss>', None),
            ('<statements>', [
                ('<statement>', [
                    ('<mwss>', None),
                    ('<expr>', [('<test>', [('<sum>', [('<term>', [('<id>', None)])])])]),
                    ('<mwss>', None),
                    (';', [])]),
                ('<statement>', [
                    ('<mwss>', None),
                    ('<expr>', [
                        ('<id>', None), ('<mwss>', None), ('=', []), ('<mwss>', None),
                        ('<expr>', [
                            ('<id>', None), ('<mwss>', None), ('=', []), ('<mwss>', None),
                            ('<expr>', [
                                ('<id>', None), ('<mwss>', None), ('=', []), ('<mwss>', None),
                                ('<expr>', [
                                    ('<id>', None), ('<mwss>', None), ('=', []), ('<mwss>', None),
                                    ('<expr>', None)])])])]),
                    ('<mwss>', None),
                    (';', [])])]),
            ('<mwss>', None)]))

        to_insert = DerivationTree.from_parse_tree(
            ('<expr>', [('<id>', None), ('<mwss>', None), ('=', []), ('<mwss>', None), ('<expr>', None)]))

        wrapped = wrap_in_tree_starting_in(
            "<expr>", to_insert, canonical(TINYC_GRAMMAR), GrammarGraph.from_grammar(TINYC_GRAMMAR))

        self.assertTrue(wrapped.find_node(to_insert),
                        f"{to_insert} not found in result of wrapping in '<expr>': {wrapped}")

        results = insert_tree(canonical(TINYC_GRAMMAR), to_insert, DerivationTree.from_parse_tree(tree))

        for result in results:
            self.assertTrue(result.find_node(to_insert))

    # Test deactivated: Should assert that no prefix trees are generated. The implemented
    # check in insert_tree, however, was too expensive for the JSON examples. Stalling for now.
    # def test_insert_var(self):
    #    tree = ('<start>', [('<stmt>', [('<assgn>', None), ('<stmt>', None)])])
    #
    #    results = insert_tree(canonical(LANG_GRAMMAR),
    #                          DerivationTree("<var>", None),
    #                          DerivationTree.from_parse_tree(tree))
    #
    #    print(list(map(str, results)))
    #    self.assertEqual(
    #        ['<var> := <rhs><stmt>',
    #         '<assgn><var> := <rhs>',
    #         '<var> := <rhs> ; <assgn><stmt>',
    #         '<assgn> ; <var> := <rhs> ; <assgn><stmt>',
    #         '<assgn><var> := <rhs> ; <stmt>',
    #         '<assgn><assgn> ; <var> := <rhs> ; <stmt>'],
    #        list(map(str, results))
    #    )


if __name__ == '__main__':
    unittest.main()
