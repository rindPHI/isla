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

from isla.fuzzer import GrammarCoverageFuzzer
from isla.helpers import tree_to_string
from isla.derivation_tree import DerivationTree
from isla.parser import EarleyParser, EnhancedExtractor
from test_data import LANG_GRAMMAR


class TestParser(unittest.TestCase):
    def test_earley_parser_lang(self):
        parser = EarleyParser(LANG_GRAMMAR)
        fuzzer = GrammarCoverageFuzzer(LANG_GRAMMAR)
        for _ in range(100):
            tree = fuzzer.expand_tree(DerivationTree('<start>')).to_parse_tree()
            self.assertEqual(tree, EnhancedExtractor(parser, tree_to_string(tree)).extract_a_tree())


if __name__ == '__main__':
    unittest.main()
