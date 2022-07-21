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
