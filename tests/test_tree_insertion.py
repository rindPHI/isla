import unittest

from grammar_graph.gg import GrammarGraph

from isla.derivation_tree import DerivationTree
from isla.parser import EarleyParser
from isla.tree_insertion import insert_tree_by_reverse_embedding, insert_tree, \
    insert_tree_by_self_embedding
from isla_formalizations.scriptsizec import SCRIPTSIZE_C_GRAMMAR
from isla_formalizations.xml_lang import XML_GRAMMAR_WITH_NAMESPACE_PREFIXES


class TestTreeInsertion(unittest.TestCase):
    def test_reverse_embedding_xml(self):
        def parse(s: str) -> DerivationTree:
            return DerivationTree.from_parse_tree(
                next(EarleyParser(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES).parse(s))
            )

        original_tree = parse("<A>x</A>")

        context_to_insert = DerivationTree.from_parse_tree(
            (
                "<xml-tree>",
                [
                    (
                        "<xml-open-tag>",
                        [
                            ("<", []),
                            ("<id>", None),
                            (">", []),
                        ],
                    ),
                    ("<inner-xml-tree>", None),
                    ("<xml-close-tag>", [("</", []), ("<id>", None), (">", [])]),
                ],
            )
        )

        graph = GrammarGraph.from_grammar(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES)
        assert graph.tree_is_valid(original_tree)
        assert graph.tree_is_valid(context_to_insert)

        insertion_result, path_to_inserted_tree = next(
            insert_tree_by_reverse_embedding(original_tree, context_to_insert, graph)
        )

        inner_xml_tree = context_to_insert.get_subtree((1,))
        self.assertEqual("<inner-xml-tree>", inner_xml_tree.value)
        self.assertIn(inner_xml_tree.id, {n.id for _, n in insertion_result.paths()})

    def test_insert_declaration_scriptsize_c(self):
        context_inp = "if(f < 10) ;"
        context_tree = DerivationTree.from_parse_tree(
            next(EarleyParser(SCRIPTSIZE_C_GRAMMAR).parse(context_inp))
        )
        print(context_tree.to_dot())

        decl = DerivationTree(
            "<declaration>",
            (
                DerivationTree("int ", ()),
                DerivationTree("<id>"),
                DerivationTree(";", ()),
            ),
        )

        graph = GrammarGraph.from_grammar(SCRIPTSIZE_C_GRAMMAR)

        results = list(insert_tree_by_self_embedding(context_tree, decl, graph))
        print("\n".join(map(lambda p: str(p[0]), results)))
        self.assertTrue(any(str(r).startswith("{int <id>;") for r in results))

if __name__ == "__main__":
    unittest.main()
