import unittest

from fuzzingbook.Grammars import JSON_GRAMMAR
from fuzzingbook.Parser import canonical, EarleyParser
from grammar_graph.gg import GrammarGraph

from input_constraints.existential_helpers import insert_tree, wrap_in_tree_starting_in
from input_constraints.isla import DerivationTree
from input_constraints.tests.subject_languages import tinyc
from input_constraints.tests.subject_languages.xml_lang import XML_GRAMMAR, XML_GRAMMAR_WITH_NAMESPACE_PREFIXES
from input_constraints.tests.test_data import LANG_GRAMMAR
from input_constraints.tests.test_helpers import parse


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

        results = insert_tree(canonical(JSON_GRAMMAR), to_insert, tree, max_num_solutions=10)

        self.assertIn(
            '[{ "key" : { "key" : null } ,: '
            '{ "T" : { "I" : true , "" : [ false , "salami" ] , "" : true , "" : null , "" : false } } '
            '}]',
            [result.to_string() for result in results])

    def test_insert_json_2(self):
        inp = ' { "T" : { "I" : true , "" : [ false , "salami" ] , "" : true , "" : null , "" : false } } '
        tree = DerivationTree.from_parse_tree(parse(inp, JSON_GRAMMAR))
        to_insert = DerivationTree.from_parse_tree(parse(' "cheese" ', JSON_GRAMMAR, "<element>"))

        results = insert_tree(canonical(JSON_GRAMMAR), to_insert, tree, max_num_solutions=10)

        self.assertIn(
            '['
            ' { "T" : { "I" : true , "" : [ false , "salami" ] , "" : true , "" : null , "" : false } } , '
            '"cheese" ]',
            [result.to_string() for result in results])

    def test_insert_assignment(self):
        assgn = DerivationTree.from_parse_tree(("<assgn>", None))
        tree = ('<start>', [('<stmt>', [('<assgn>', [('<var>', None), (' := ', []), ('<rhs>', [('<var>', None)])])])])
        results = insert_tree(
            canonical(LANG_GRAMMAR),
            assgn,
            DerivationTree.from_parse_tree(tree))

        self.assertEqual(
            ['<var> := <var> ; <assgn>',
             '<var> := <var> ; <assgn> ; <stmt>',
             '<assgn> ; <var> := <var>',
             '<assgn> ; <assgn> ; <var> := <var>'],
            list(map(str, results))
        )

    def test_wrap_tinyc_assignment(self):
        tree = DerivationTree.from_parse_tree(
            ('<expr>', [('<id>', None), ('<mwss>', None), ('=', []), ('<mwss>', None), ('<expr>', None)]))
        result = wrap_in_tree_starting_in(
            "<term>", tree, tinyc.TINYC_GRAMMAR, GrammarGraph.from_grammar(tinyc.TINYC_GRAMMAR))
        self.assertTrue(result.find_node(tree))

    def test_insert_xml_1(self):
        tree = DerivationTree.from_parse_tree(list(EarleyParser(XML_GRAMMAR).parse("<b>asdf</b>"))[0])
        to_insert = DerivationTree("<xml-open-tag>", [
            DerivationTree("<", []),
            DerivationTree("<id>", [
                DerivationTree("<id-start-char>", [
                    DerivationTree("a", [])])]),
            DerivationTree(">", [])
        ])

        result = insert_tree(canonical(XML_GRAMMAR), to_insert, tree)
        str_results = [str(t) for t in result]
        self.assertIn("<a><b>asdf</b><xml-close-tag>", str_results)

    def test_insert_xml_2(self):
        tree = DerivationTree('<start>', (
            DerivationTree('<xml-tree>', (
                DerivationTree('<xml-openclose-tag>', (
                    DerivationTree('<', ()),
                    DerivationTree('<id>', (
                        DerivationTree('<id-with-prefix>', (
                            DerivationTree('<id-no-prefix>', None),
                            DerivationTree(':', ()),
                            DerivationTree('<id-no-prefix>', None))),)),
                    DerivationTree('/>', ()))),)),))

        to_insert = DerivationTree('<xml-tree>', (
            DerivationTree('<xml-open-tag>', (
                DerivationTree('<', ()),
                DerivationTree('<id>', None),
                DerivationTree(' ', ()),
                DerivationTree('<xml-attribute>', None),
                DerivationTree('>', ()))),
            DerivationTree('<inner-xml-tree>', None),
            DerivationTree('<xml-close-tag>', (
                DerivationTree('</', ()),
                DerivationTree('<id>', None),
                DerivationTree('>', ())))))

        result = insert_tree(canonical(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES), to_insert, tree)
        self.assertTrue(result)

        str_results = [str(t) for t in result]
        self.assertIn("<<id> <xml-attribute>><<id-no-prefix>:<id-no-prefix>/></<id>>", str_results)

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
