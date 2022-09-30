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
