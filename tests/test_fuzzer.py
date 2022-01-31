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
