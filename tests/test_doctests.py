import doctest
import unittest

from isla import (
    helpers,
    cli,
    derivation_tree,
    evaluator,
    existential_helpers,
    fuzzer,
    isla_predicates,
    isla_shortcuts,
    language,
    optimizer,
    mutator,
    parser,
    performance_evaluator,
    three_valued_truth,
    solver,
    trie,
    type_defs,
    z3_helpers,
)


class TestDocstrings(unittest.TestCase):
    def test_cli(self):
        doctest_results = doctest.testmod(m=cli)
        self.assertFalse(doctest_results.failed)

    def test_derivation_tree(self):
        doctest_results = doctest.testmod(m=derivation_tree)
        self.assertFalse(doctest_results.failed)

    def test_evaluator(self):
        doctest_results = doctest.testmod(m=evaluator)
        self.assertFalse(doctest_results.failed)

    def test_existential_helpers(self):
        doctest_results = doctest.testmod(m=existential_helpers)
        self.assertFalse(doctest_results.failed)

    def test_fuzzer(self):
        doctest_results = doctest.testmod(m=fuzzer)
        self.assertFalse(doctest_results.failed)

    def test_helpers(self):
        doctest_results = doctest.testmod(m=helpers)
        self.assertFalse(doctest_results.failed)

    def test_isla_predicates(self):
        doctest_results = doctest.testmod(m=isla_predicates)
        self.assertFalse(doctest_results.failed)

    def test_isla_shortcuts(self):
        doctest_results = doctest.testmod(m=isla_shortcuts)
        self.assertFalse(doctest_results.failed)

    def test_language(self):
        doctest_results = doctest.testmod(m=language)
        self.assertFalse(doctest_results.failed)

    def test_mutator(self):
        doctest_results = doctest.testmod(m=mutator)
        self.assertFalse(doctest_results.failed)

    def test_optimizer(self):
        doctest_results = doctest.testmod(m=optimizer)
        self.assertFalse(doctest_results.failed)

    def test_parser(self):
        doctest_results = doctest.testmod(m=parser)
        self.assertFalse(doctest_results.failed)

    def test_performance_evaluator(self):
        doctest_results = doctest.testmod(m=performance_evaluator)
        self.assertFalse(doctest_results.failed)

    def test_solver(self):
        doctest_results = doctest.testmod(m=solver)
        self.assertFalse(doctest_results.failed)

    def test_three_valued_truth(self):
        doctest_results = doctest.testmod(m=three_valued_truth)
        self.assertFalse(doctest_results.failed)

    def test_trie(self):
        doctest_results = doctest.testmod(m=trie)
        self.assertFalse(doctest_results.failed)

    def test_type_defs(self):
        doctest_results = doctest.testmod(m=type_defs)
        self.assertFalse(doctest_results.failed)

    def test_z3_helpers(self):
        doctest_results = doctest.testmod(m=z3_helpers)
        self.assertFalse(doctest_results.failed)


if __name__ == "__main__":
    unittest.main()
