import unittest

from fuzzingbook.Parser import canonical

from input_constraints.prolog import translate_grammar, predicate_names_for_nonterminals
from input_constraints.tests.test_data import LANG_GRAMMAR


class TestProlog(unittest.TestCase):
    def test_translate_grammar(self):
        print(translate_grammar(
            canonical(LANG_GRAMMAR),
            predicate_names_for_nonterminals(LANG_GRAMMAR),
            {"<digit>": (0, 9)},
            {"<var>": 3}
        ))


if __name__ == '__main__':
    unittest.main()
