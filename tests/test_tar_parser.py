import unittest

from grammar_graph import gg

from isla.helpers import tree_to_string
from isla_formalizations import tar
from isla_formalizations.tar import TAR_GRAMMAR


class TestTarParser(unittest.TestCase):
    def test_parse_file_name_str(self):
        tar_parser = tar.TarParser()
        file_name_str = "bbb"
        parsed = tar_parser.parse_file_name_str(file_name_str)

        self.assertEqual(file_name_str, tree_to_string(parsed))

        graph = gg.GrammarGraph.from_grammar(TAR_GRAMMAR)
        self.assertTrue(graph.tree_is_valid(parsed))

    def test_parse_characters(self):
        tar_parser = tar.TarParser()
        file_name_str = "bbb"
        parsed = tar_parser.parse_characters(file_name_str)

        self.assertEqual(file_name_str, tree_to_string(parsed))

        graph = gg.GrammarGraph.from_grammar(TAR_GRAMMAR)
        self.assertTrue(graph.tree_is_valid(parsed))


if __name__ == '__main__':
    unittest.main()
