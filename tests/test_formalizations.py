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

import os
import pathlib
import unittest

from grammar_graph import gg
from grammar_graph.gg import path_to_string

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
