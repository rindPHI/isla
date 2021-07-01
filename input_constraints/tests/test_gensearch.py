import logging
import unittest
from typing import cast

import z3
from fuzzingbook.GrammarFuzzer import tree_to_string

from input_constraints import isla
from input_constraints import isla_shortcuts as sc
from input_constraints.gensearch import ISLaSolver
from input_constraints.tests.test_data import LANG_GRAMMAR


class TestGensearch(unittest.TestCase):
    def test_atomic_smt_formula(self):
        var1 = isla.Constant("$var1", "<var>")
        var2 = isla.Constant("$var2", "<var>")

        formula = isla.SMTFormula(cast(z3.BoolRef, var1.to_smt() == var2.to_smt()), var1, var2)

        solver = ISLaSolver(LANG_GRAMMAR, formula)
        for assignment in solver.find_solution():
            self.assertEqual(assignment[var1], assignment[var2])

    def test_conjunctive_formula(self):
        var1 = isla.Constant("$var1", "<var>")
        var2 = isla.Constant("$var2", "<var>")
        var3 = isla.Constant("$var3", "<var>")

        formula = isla.SMTFormula(
            cast(z3.BoolRef,
                 z3.And(var1.to_smt() == var2.to_smt(), z3.Not(var3.to_smt() == var1.to_smt()))
                 ), var1, var2, var3)

        solver = ISLaSolver(LANG_GRAMMAR, formula)

        for assignment in solver.find_solution():
            self.assertEqual(assignment[var1], assignment[var2])
            self.assertNotEqual(assignment[var1], assignment[var3])

    def test_simple_universal_formula(self):
        # logging.basicConfig(level=logging.DEBUG)
        start = isla.Constant("$start", "<start>")
        var1 = isla.BoundVariable("$var", "<var>")

        formula = sc.forall(
            var1, start,
            sc.smt_for(cast(z3.BoolRef, var1.to_smt() == z3.StringVal("x")), var1))

        solver = ISLaSolver(LANG_GRAMMAR, formula, 1)

        it = solver.find_solution()
        for _ in range(50):
            try:
                assignment = next(it)
                self.assertTrue(isla.evaluate(formula, {start: (tuple(), assignment[start])}))
            except StopIteration:
                self.fail()

    def test_simple_existential_formula(self):
        # logging.basicConfig(level=logging.DEBUG)
        start = isla.Constant("$start", "<start>")
        var1 = isla.BoundVariable("$var", "<var>")

        formula = sc.exists(
            var1, start,
            sc.smt_for(cast(z3.BoolRef, var1.to_smt() == z3.StringVal("x")), var1))

        solver = ISLaSolver(LANG_GRAMMAR, formula, 1)

        it = solver.find_solution()
        for _ in range(50):
            try:
                assignment = next(it)
                self.assertTrue(isla.evaluate(formula, {start: (tuple(), assignment[start])}))
            except StopIteration:
                self.fail()


if __name__ == '__main__':
    unittest.main()
