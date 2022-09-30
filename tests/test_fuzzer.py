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

import logging
import unittest

from isla.fuzzer import GrammarFuzzer, GrammarCoverageFuzzer
from isla_formalizations import csv as csvlang


class TestFuzzer(unittest.TestCase):
    def __init__(self, *args):
        super().__init__(*args)
        self.logger = logging.getLogger("TestFuzzer")

    def test_grammar_fuzzer(self):
        grammar = csvlang.CSV_GRAMMAR
        fuzzer = GrammarFuzzer(grammar)
        for _ in range(100):
            try:
                self.logger.info(fuzzer.fuzz())
            except:
                self.fail()

    def test_grammar_coverage_fuzzer(self):
        grammar = csvlang.CSV_GRAMMAR
        fuzzer = GrammarCoverageFuzzer(grammar)
        for _ in range(100):
            try:
                self.logger.info(fuzzer.fuzz())
            except:
                self.fail()


if __name__ == '__main__':
    unittest.main()
