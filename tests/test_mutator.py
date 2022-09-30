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

from isla.derivation_tree import DerivationTree
from isla.fuzzer import GrammarCoverageFuzzer
from isla.mutator import Mutator
from isla.parser import EarleyParser
from isla.type_defs import Grammar
from test_data import LANG_GRAMMAR


class TestMutator(unittest.TestCase):
    def test_replace_subtree_randomly(self):
        mutator = Mutator(LANG_GRAMMAR)
        fuzzer = GrammarCoverageFuzzer(LANG_GRAMMAR)
        graph = gg.GrammarGraph.from_grammar(LANG_GRAMMAR)

        for _ in range(10):
            inp = fuzzer.fuzz_tree()
            result = mutator.replace_subtree_randomly(inp)
            self.assertTrue(result.is_present())
            self.assertTrue(graph.tree_is_valid(result.get()))

    def test_swap_subtrees(self):
        mutator = Mutator(LANG_GRAMMAR)
        fuzzer = GrammarCoverageFuzzer(LANG_GRAMMAR)
        graph = gg.GrammarGraph.from_grammar(LANG_GRAMMAR)

        for _ in range(10):
            inp = fuzzer.fuzz_tree()
            result = mutator.swap_subtrees(inp)

            self.assertTrue(
                result.is_present()
                or len(inp.filter(lambda t: t.value == "<assgn>")) == 1
            )

            self.assertTrue(
                result.map(lambda tree: graph.tree_is_valid(result.get()))
                .orelse(lambda: True)
                .get()
            )

    def test_generalize_subtree(self):
        mutator = Mutator(LANG_GRAMMAR)
        fuzzer = GrammarCoverageFuzzer(LANG_GRAMMAR)
        graph = gg.GrammarGraph.from_grammar(LANG_GRAMMAR)

        for _ in range(10):
            inp = fuzzer.fuzz_tree()
            result = mutator.generalize_subtree(inp)
            self.assertTrue(result.is_present())
            self.assertTrue(graph.tree_is_valid(result.get()))

    def test_mutate(self):
        mutator = Mutator(LANG_GRAMMAR)
        fuzzer = GrammarCoverageFuzzer(LANG_GRAMMAR)
        graph = gg.GrammarGraph.from_grammar(LANG_GRAMMAR)

        for _ in range(10):
            inp = fuzzer.fuzz_tree()
            result = mutator.mutate(inp)
            self.assertTrue(graph.tree_is_valid(result))


def parse(inp: str, grammar: Grammar = LANG_GRAMMAR) -> DerivationTree:
    return DerivationTree.from_parse_tree(next(EarleyParser(grammar).parse(inp)))


if __name__ == "__main__":
    unittest.main()
