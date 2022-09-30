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

import unittest

from grammar_graph.gg import GrammarGraph

from isla.derivation_tree import DerivationTree
from isla.existential_helpers import insert_tree, insert_trees, SELF_EMBEDDING, CONTEXT_ADDITION, DIRECT_EMBEDDING
from isla.parser import EarleyParser
from isla_formalizations import scriptsizec
from isla_formalizations.xml_lang import XML_GRAMMAR, XML_GRAMMAR_WITH_NAMESPACE_PREFIXES
from test_data import LANG_GRAMMAR, JSON_GRAMMAR
from test_helpers import parse, canonical


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

    def test_insert_lang_2(self):
        inserted_tree = DerivationTree('<assgn>', (
            DerivationTree('<var>', None),
            DerivationTree(' := ', ()),
            DerivationTree('<rhs>', None)))

        into_tree = DerivationTree('<start>', (
            DerivationTree('<stmt>', (
                DerivationTree('<assgn>', (
                    DerivationTree('<var>', None),
                    DerivationTree(' := ', ()),
                    DerivationTree('<rhs>', (
                        DerivationTree('<digit>', None),)))),
                DerivationTree(' ; ', ()),
                DerivationTree('<stmt>', (
                    DerivationTree('<assgn>', (
                        DerivationTree('<var>', None),
                        DerivationTree(' := ', ()),
                        DerivationTree('<rhs>', (
                            DerivationTree('<var>', None),)))),)))),))

        result = insert_tree(canonical(LANG_GRAMMAR), inserted_tree, into_tree, max_num_solutions=30)

        # str_results = [str(t) for t in result]
        # print("\n\n".join(str_results))

        self.assertTrue(all(t.find_node(inserted_tree) for t in result))
        self.assertTrue(all(t.find_node(into_tree.get_subtree((0, 0))) for t in result))
        self.assertTrue(all(t.find_node(into_tree.get_subtree((0, 2, 0))) for t in result))

    def test_insert_lang_3(self):
        canonical_grammar = canonical(LANG_GRAMMAR)

        in_tree = DerivationTree(
            '<start>', (
                DerivationTree(
                    '<stmt>', (
                        DerivationTree(
                            '<assgn>', (
                                DerivationTree('<var>', None, id=245),
                                DerivationTree(' := ', (), id=244),
                                DerivationTree('<rhs>', (
                                    DerivationTree(
                                        '<var>', (DerivationTree('x', (), id=12249),),
                                        id=12250),
                                ), id=240)
                            ), id=246),
                    ), id=247),
            ), id=237)

        tree = DerivationTree('<rhs>', (DerivationTree('<var>', None, id=12251),), id=12252)

        result = insert_tree(canonical_grammar, tree, in_tree, max_num_solutions=10)

        self.assertTrue(all(t.find_node(tree) for t in result))
        self.assertTrue(all(t.find_node(12249) for t in result))
        self.assertTrue(all(t.find_node(12250) for t in result))
        self.assertTrue(all(t.find_node(240) for t in result))
        self.assertTrue(all(t.find_node(245) for t in result))

    def test_insert_trees_lang(self):
        tree_to_insert = DerivationTree('<assgn>', (
            DerivationTree('<var>', None),
            DerivationTree(' := ', ()),
            DerivationTree('<rhs>', (DerivationTree('<digit>', None),))))

        into_tree = DerivationTree('<start>', (
            DerivationTree('<stmt>', (
                DerivationTree('<assgn>', (
                    DerivationTree('<var>', None),
                    DerivationTree(' := ', ()),
                    DerivationTree('<rhs>', None))),
                DerivationTree(' ; ', ()),
                DerivationTree('<stmt>', (
                    DerivationTree('<assgn>', (
                        DerivationTree('<var>', None)
                        , DerivationTree(' := ', ()),
                        DerivationTree('<rhs>', (DerivationTree('<var>', None),)))),)))),))

        result = insert_trees(
            [tree_to_insert],
            into_tree,
            canonical(LANG_GRAMMAR), GrammarGraph.from_grammar(LANG_GRAMMAR), 30)

        # str_results = [str(t) for t in result]
        # print("\n\n".join(str_results))

        self.assertTrue(all(t.find_node(tree_to_insert) for t in result))
        self.assertTrue(all(t.find_node(into_tree.get_subtree((0, 0))) for t in result))
        self.assertTrue(all(t.find_node(into_tree.get_subtree((0, 2, 0))) for t in result))

    def test_insert_json_1(self):
        inp = ' { "T" : { "I" : true , "" : [ false , "salami" ] , "" : true , "" : null , "" : false } } '
        tree = DerivationTree.from_parse_tree(parse(inp, JSON_GRAMMAR))
        to_insert = DerivationTree.from_parse_tree(parse(' "key" : { "key" : null } ', JSON_GRAMMAR, "<member>"))

        results = insert_tree(canonical(JSON_GRAMMAR), to_insert, tree, max_num_solutions=20)
        str_results = [result.to_string().strip() for result in results]

        self.assertIn(
            '{ "key" : { "key" : null } , '
            '"T" : { "I" : true , "" : [ false , "salami" ] , "" : true , "" : null , "" : false } }',
            str_results)

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
            DerivationTree.from_parse_tree(tree),
            max_num_solutions=None
        )

        self.assertEqual(
            [#'<var> := <var> ; <assgn> ; <stmt>',
             #'<var> := <var> ; <assgn>',
             '<assgn> ; <var> := <var>'],
            list(map(str, results))
        )

    def test_insert_assignment_2(self):
        tree = DerivationTree('<assgn>', id=1)
        in_tree = DerivationTree(
            "<start>", (
                DerivationTree(
                    "<stmt>", (
                        DerivationTree("<assgn>", id=4),
                        DerivationTree(" ; ", (), id=5),
                        DerivationTree("<stmt>", (DerivationTree("<assgn>", id=7),), id=6)),
                    id=3),),
            id=2)
        DerivationTree.next_id = 8

        methods = DIRECT_EMBEDDING + SELF_EMBEDDING + CONTEXT_ADDITION

        results = insert_tree(
            canonical(LANG_GRAMMAR),
            tree,
            in_tree,
            methods=methods)

        for idx, result in enumerate(results):
            for node_id in range(2, 7):
                self.assertTrue(
                    result.find_node(node_id) is not None,
                    f'Could not find node {node_id} in result no. {idx + 1}: {result}')

    def test_tree_insert_direct_embedding(self):
        in_tree = DerivationTree("<start>", (DerivationTree("<stmt>", None, id=0),), id=1)
        tree = DerivationTree('<assgn>', id=2)
        results = insert_tree(
            canonical(LANG_GRAMMAR),
            tree,
            in_tree,
            methods=DIRECT_EMBEDDING)
        self.assertTrue(all(result.find_node(node.id) is not None for result in results for _, node in result.paths()))

    def test_insert_trees_assignment(self):
        trees = [
            DerivationTree('<stmt>', (
                DerivationTree('<assgn>', (
                    DerivationTree('<var>', None),
                    DerivationTree(' := ', ()),
                    DerivationTree('<rhs>', (DerivationTree('<var>', None),)))),)),
            DerivationTree('<assgn>', None)]

        self_embedding_tree = DerivationTree('<stmt>', (
            DerivationTree('<assgn>', None),
            DerivationTree(' ; ', ()),
            DerivationTree('<stmt>', None)))

        result_trees = insert_trees(
            trees,
            self_embedding_tree,
            canonical(LANG_GRAMMAR),
            GrammarGraph.from_grammar(LANG_GRAMMAR),
            30)

        result_trees_str = [str(t) for t in result_trees]

        # self.assertIn('<var> := <var> ; <assgn>', result_trees_str)
        self.assertIn('<assgn> ; <var> := <var>', result_trees_str)

        print(result_trees_str)

    def test_insert_xml_1(self):
        tree = DerivationTree.from_parse_tree(next(EarleyParser(XML_GRAMMAR).parse("<b>asdf</b>")))
        to_insert = DerivationTree("<xml-open-tag>", [
            DerivationTree("<", []),
            DerivationTree("<id>", [
                DerivationTree("<id-start-char>", [
                    DerivationTree("a", [])])]),
            DerivationTree(">", [])
        ])

        result = insert_tree(canonical(XML_GRAMMAR), to_insert, tree)
        str_results = [str(t) for t in result]
        # print("\n\n".join(str_results))
        self.assertIn("<a><b>asdf</b><xml-close-tag>", str_results)
        self.assertIn("<b><a>asdf<xml-close-tag></b>", str_results)
        self.assertIn(
            "<xml-open-tag><b>asdf</b><a><inner-xml-tree><xml-close-tag><inner-xml-tree><xml-close-tag>",
            str_results)

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

    def test_insert_trees_xml_3(self):
        to_insert = DerivationTree('<xml-tree>', (
            DerivationTree('<xml-open-tag>', (
                DerivationTree('<', (), id=14120),
                DerivationTree('<id>', None, id=14121),
                DerivationTree(' ', (), id=14122),
                DerivationTree('<xml-attribute>', None, id=14123),
                DerivationTree('>', (), id=14124)), id=14034),
            DerivationTree('<inner-xml-tree>', None, id=14125),
            DerivationTree('<xml-close-tag>', (
                DerivationTree('</', (), id=14126),
                DerivationTree('<id>', None, id=14127),
                DerivationTree('>', (), id=14128)), id=14036)), id=14033)

        into_tree = DerivationTree('<start>', (
            DerivationTree('<xml-tree>', (
                DerivationTree('<xml-openclose-tag>', (
                    DerivationTree('<', (), id=13263),
                    DerivationTree('<id>', (
                        DerivationTree('<id-with-prefix>', (
                            DerivationTree('<id-no-prefix>', None, id=13810),
                            DerivationTree(':', (), id=13811),
                            DerivationTree('<id-no-prefix>', None, id=13812)), id=13602),), id=13264),
                    DerivationTree('/>', (), id=13265)), id=12596),), id=12592),), id=12591)

        results = insert_trees(
            [into_tree.children[0]],
            into_tree.replace_path((0,), to_insert),
            canonical(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES),
            GrammarGraph.from_grammar(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES),
            50)

        self.assertTrue(all(result.find_node(node) is not None for result in results for _, node in to_insert.paths()))
        self.assertTrue(all(result.find_node(node) is not None for result in results for _, node in into_tree.paths()))

    def test_insert_xml_4(self):
        to_insert = DerivationTree('<xml-attribute>', (
            DerivationTree('<id>', (
                DerivationTree('<id-with-prefix>', (
                    DerivationTree('<id-no-prefix>', (
                        DerivationTree('<id-start-char>', (
                            DerivationTree('x', (), id=139898),), id=139895),
                        DerivationTree('<id-chars>', (
                            DerivationTree('<id-char>', (
                                DerivationTree('<id-start-char>', (
                                    DerivationTree('m', (), id=139905),), id=139902),), id=139899),
                            DerivationTree('<id-chars>', (
                                DerivationTree('<id-char>', (
                                    DerivationTree('<id-start-char>', (
                                        DerivationTree('l', (), id=139909),), id=139906),), id=139903),
                                DerivationTree('<id-chars>', (
                                    DerivationTree('<id-char>', (
                                        DerivationTree('<id-start-char>', (
                                            DerivationTree('n', (), id=139912),), id=139910),), id=139907),
                                    DerivationTree('<id-chars>', (
                                        DerivationTree('<id-char>', (
                                            DerivationTree('<id-start-char>', (
                                                DerivationTree('s', (), id=139914),), id=139913),), id=139911),),
                                                   id=139908)), id=139904)), id=139900)), id=139896)), id=139891),
                    DerivationTree(':', (), id=139892),
                    DerivationTree('<id-no-prefix>', None, id=139915)), id=139889),), id=139885),
            DerivationTree('="', (), id=139916),
            DerivationTree('<text>', None, id=139917),
            DerivationTree('"', (), id=139918)), id=139884)

        into_tree = DerivationTree('<xml-attribute>', (
            DerivationTree('<id>', (
                DerivationTree('<id-no-prefix>', None, id=138999),), id=137339),
            DerivationTree('="', (), id=137340),
            DerivationTree('<text>', None, id=137341),
            DerivationTree('"', (), id=137342)), id=21903)

        results = insert_tree(
            canonical(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES),
            to_insert,
            into_tree,
            GrammarGraph.from_grammar(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES),
            30)

        self.assertTrue(all(result.find_node(node) is not None for result in results for _, node in to_insert.paths()))
        self.assertTrue(all(result.find_node(node) is not None for result in results for _, node in into_tree.paths()))

    def test_insert_scriptsizec(self):
        inserted_tree = DerivationTree(
            '<declaration>', (
                DerivationTree('int ', ()),
                DerivationTree('<id>', None),
                DerivationTree(';', ())))

        into_tree = DerivationTree(
            '<start>', (
                DerivationTree('<statement>', (
                    DerivationTree('<expr>', (
                        DerivationTree('<test>', (
                            DerivationTree('<sum>', (
                                DerivationTree('<term>', (
                                    DerivationTree('<id>', None),)),)),)),)),
                    DerivationTree(';', ()))),))

        result_trees = insert_tree(
            canonical(scriptsizec.SCRIPTSIZE_C_GRAMMAR),
            inserted_tree,
            into_tree,
            max_num_solutions=20
        )

        result_trees_str = [str(t) for t in result_trees]
        self.assertIn("{<id>;int <id>;<statements>}", result_trees_str)
        self.assertIn("{int <id>;<id>;<statements>}", result_trees_str)

    def test_insert_trees_scriptsizec(self):
        trees = [
            DerivationTree('<statement>', (
                DerivationTree('<expr>', (
                    DerivationTree('<test>', (
                        DerivationTree('<sum>', (
                            DerivationTree('<term>', (
                                DerivationTree('<id>', None),)),)),)),)),
                DerivationTree(';', ()))),
            DerivationTree('<declaration>', (
                DerivationTree('int ', ()),
                DerivationTree('<id>', None),
                DerivationTree(';', ())))]

        self_embedding_tree = DerivationTree('<statement>', (
            DerivationTree('<block>', (
                DerivationTree('{', ()),
                DerivationTree('<statements>', (
                    DerivationTree('<block_statement>', (
                        DerivationTree('<statement>', None),)),
                    DerivationTree('<statements>', None))),
                DerivationTree('}', ()))),))

        result_trees = insert_trees(
            trees,
            self_embedding_tree,
            canonical(scriptsizec.SCRIPTSIZE_C_GRAMMAR),
            GrammarGraph.from_grammar(scriptsizec.SCRIPTSIZE_C_GRAMMAR),
            30)

        result_trees_str = [str(t) for t in result_trees]
        self.assertIn("{int <id>;<id>;<statements>}", result_trees_str)
        self.assertIn("{<id>;int <id>;<statements>}", result_trees_str)

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
