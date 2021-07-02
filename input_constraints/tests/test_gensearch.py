import logging
import unittest
from typing import cast, List

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

        self.execute_generation_test(formula, [var1, var2], num_solutions=1)

    def test_conjunctive_formula(self):
        var1 = isla.Constant("$var1", "<var>")
        var2 = isla.Constant("$var2", "<var>")
        var3 = isla.Constant("$var3", "<var>")

        formula = isla.SMTFormula(
            cast(z3.BoolRef,
                 z3.And(var1.to_smt() == var2.to_smt(), z3.Not(var3.to_smt() == var1.to_smt()))
                 ), var1, var2, var3)

        self.execute_generation_test(formula, [var1, var2, var3], num_solutions=1)

    def test_simple_universal_formula(self):
        # logging.basicConfig(level=logging.DEBUG)
        start = isla.Constant("$start", "<start>")
        var1 = isla.BoundVariable("$var", "<var>")

        formula = sc.forall(
            var1, start,
            sc.smt_for(cast(z3.BoolRef, var1.to_smt() == z3.StringVal("x")), var1))

        self.execute_generation_test(formula, [start])

    def test_simple_universal_formula_with_bind(self):
        start = isla.Constant("$start", "<start>")
        rhs = isla.BoundVariable("$rhs", "<rhs>")
        var1 = isla.BoundVariable("$var", "<var>")

        formula = sc.forall_bind(
            isla.BindExpression(var1),
            rhs, start,
            sc.smt_for(cast(z3.BoolRef, var1.to_smt() == z3.StringVal("x")), var1))

        self.execute_generation_test(formula, [start])

    def test_simple_existential_formula(self):
        # NOTE: Existential quantifier instantiation currently does not produce an infinite stream,
        #       since we basically look for paths through the grammar without repetition, which
        #       yields a finite (usually small) number of solutions. Check whether that's a problem.
        #       Usually, we will have universal quantifiers at top level in any case.
        # logging.basicConfig(level=logging.DEBUG)
        start = isla.Constant("$start", "<start>")
        var1 = isla.BoundVariable("$var", "<var>")

        formula = sc.exists(
            var1, start,
            sc.smt_for(cast(z3.BoolRef, var1.to_smt() == z3.StringVal("x")), var1))

        self.execute_generation_test(formula, [start],
                                     num_solutions=10,
                                     max_number_free_instantiations=5)

    def test_simple_existential_formula_with_bind(self):
        start = isla.Constant("$start", "<start>")
        rhs = isla.BoundVariable("$rhs", "<rhs>")
        var1 = isla.BoundVariable("$var", "<var>")

        formula = sc.exists_bind(
            isla.BindExpression(var1),
            rhs, start,
            sc.smt_for(cast(z3.BoolRef, var1.to_smt() == z3.StringVal("x")), var1))

        self.execute_generation_test(formula, [start], print_solutions=True)

    def execute_generation_test(self,
                                formula: isla.Formula,
                                constants: List[isla.Constant],
                                num_solutions=50,
                                print_solutions=False,
                                max_number_free_instantiations=1
                                ):
        solver = ISLaSolver(LANG_GRAMMAR, formula, max_number_free_instantiations)

        it = solver.find_solution()
        for _ in range(num_solutions):
            try:
                assignment = next(it)
                if print_solutions:
                    print(", ".join([tree_to_string(assignment[c]) for c in constants]))
                self.assertTrue(isla.evaluate(formula, {
                    c: (tuple(), assignment[c]) for c in constants
                }))
            except StopIteration:
                self.fail()


if __name__ == '__main__':
    unittest.main()
