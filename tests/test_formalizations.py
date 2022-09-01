import os
import pathlib
import sys
import unittest

from grammar_graph import gg
from grammar_graph.gg import path_to_string

from isla.derivation_tree import DerivationTree
from isla_formalizations.tar import TarParser, TAR_GRAMMAR


class TestFormalizations(unittest.TestCase):
    def test_tar_parser_with_links(self):
        path = os.path.join(os.path.dirname(__file__), 'test_data/' 'test_with_links.tar')
        with pathlib.Path(path).open(mode='rb') as asdf:
            tar_file_content = asdf.read().decode('ascii')
        tree = TarParser().parse(tar_file_content)[0]

        graph = gg.GrammarGraph.from_grammar(TAR_GRAMMAR)

        all_2paths = {path_to_string(p) for p in graph.k_paths(2)}
        tree_2paths = {path_to_string(p) for p in graph.k_paths_in_tree(tree, 2)}
        self.assertFalse(tree_2paths.difference(all_2paths))

        self.assertTrue(graph.tree_is_valid(tree))

    def test_tar_parser_simple_file(self):
        path = os.path.join(os.path.dirname(__file__), 'test_data/' 'test_simple.tar')
        with pathlib.Path(path).open(mode='rb') as asdf:
            tar_file_content = asdf.read().decode('ascii')
        tree = TarParser().parse(tar_file_content)[0]

        graph = gg.GrammarGraph.from_grammar(TAR_GRAMMAR)

        all_2paths = {path_to_string(p) for p in graph.k_paths(2)}
        tree_2paths = {path_to_string(p) for p in graph.k_paths_in_tree(tree, 2)}
        self.assertFalse(tree_2paths.difference(all_2paths))

        self.assertTrue(graph.tree_is_valid(tree))


if __name__ == '__main__':
    unittest.main()
