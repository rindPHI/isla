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

    def test_semantic_conjunctive_formula(self):
        var1 = isla.Constant("$var1", "<var>")
        var2 = isla.Constant("$var2", "<var>")
        var3 = isla.Constant("$var3", "<var>")

        formula = isla.SMTFormula(
            cast(z3.BoolRef,
                 z3.And(var1.to_smt() == var2.to_smt(), z3.Not(var3.to_smt() == var1.to_smt()))
                 ), var1, var2, var3)

        self.execute_generation_test(formula, [var1, var2, var3], num_solutions=1)

    def test_simple_predicate_conjunction(self):
        # Idea: part of an assignment "var := rhs"
        var = isla.Constant("$var", "<var>", (0, 0, 0))
        rhs = isla.Constant("$rhs", "<rhs>", (0, 0, 2))

        formula = isla.ConjunctiveFormula(
            isla.SMTFormula(cast(z3.BoolRef, var.to_smt() == z3.StringVal("x")), var),
            sc.before(var, rhs))

        self.execute_generation_test(formula, [var, rhs],
                                     max_number_smt_instantiations=2,
                                     max_number_free_instantiations=10,
                                     num_solutions=10)

    def test_simple_universal_formula(self):
        start = isla.Constant("$start", "<start>")
        var1 = isla.BoundVariable("$var", "<var>")

        formula = sc.forall(
            var1, start,
            sc.smt_for(cast(z3.BoolRef, var1.to_smt() == z3.StringVal("x")), var1))

        self.execute_generation_test(formula, [start], num_solutions=10)
        # More solutions possible, but want to safe time. TODO Have to do profiling!

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

        self.execute_generation_test(formula, [start], num_solutions=10, max_number_free_instantiations=10)

    def test_conjunction_of_qfd_formulas(self):
        start = isla.Constant("$start", "<start>")
        assgn = isla.BoundVariable("$assgn", "<assgn>")
        rhs_1 = isla.BoundVariable("$rhs1", "<rhs>")
        rhs_2 = isla.BoundVariable("$rhs2", "<rhs>")
        var_1 = isla.BoundVariable("$var1", "<var>")
        var_2 = isla.BoundVariable("$var2", "<var>")

        # Below formula violates the normal form
        # formula = \
        #     sc.forall_bind(
        #         isla.BindExpression(var_1),
        #         rhs_1, start,
        #         sc.smt_for(cast(z3.BoolRef, var_1.to_smt() == z3.StringVal("x")), var_1)) & \
        #     sc.forall_bind(
        #         var_2 + " := " + rhs_2,
        #         assgn, start,
        #         sc.smt_for(cast(z3.BoolRef, var_2.to_smt() == z3.StringVal("y")), var_2))

        formula = \
            sc.forall_bind(
                var_2 + " := " + rhs_2,
                assgn, start,
                (sc.smt_for(cast(z3.BoolRef, var_2.to_smt() == z3.StringVal("y")), var_2) &
                 sc.forall(
                     var_1, rhs_2,
                     sc.smt_for(cast(z3.BoolRef, var_1.to_smt() == z3.StringVal("x")), var_1))
                 ))

        self.execute_generation_test(formula, [start], num_solutions=1, print_solutions=True)

    def test_declared_before_used(self):
        logging.basicConfig(level=logging.DEBUG)

        start = isla.Constant("$start", "<start>")
        lhs_1 = isla.BoundVariable("$lhs_1", "<var>")
        lhs_2 = isla.BoundVariable("$lhs_2", "<var>")
        rhs_1 = isla.BoundVariable("$rhs_1", "<rhs>")
        rhs_2 = isla.BoundVariable("$rhs_2", "<rhs>")
        assgn_1 = isla.BoundVariable("$assgn_1", "<assgn>")
        assgn_2 = isla.BoundVariable("$assgn_2", "<assgn>")
        var = isla.BoundVariable("$var", "<var>")

        formula: isla.Formula = sc.forall_bind(
            lhs_1 + " := " + rhs_1,
            assgn_1,
            start,
            sc.forall(
                var,
                rhs_1,
                sc.exists_bind(
                    lhs_2 + " := " + rhs_2,
                    assgn_2,
                    start,
                    sc.before(assgn_2, assgn_1) &
                    sc.smt_for(cast(z3.BoolRef, lhs_2.to_smt() == var.to_smt()), lhs_2, var)
                )
            )
        )

        self.execute_generation_test(formula, [start], print_solutions=True)

    def execute_generation_test(self,
                                formula: isla.Formula,
                                constants: List[isla.Constant],
                                num_solutions=50,
                                print_solutions=False,
                                max_number_free_instantiations=1,
                                max_number_smt_instantiations=1
                                ):
        solver = ISLaSolver(
            grammar=LANG_GRAMMAR,
            formula=formula,
            max_number_free_instantiations=max_number_free_instantiations,
            max_number_smt_instantiations=max_number_smt_instantiations)

        it = solver.find_solution()
        for idx in range(num_solutions):
            try:
                assignment = next(it)
                if print_solutions:
                    print(", ".join([tree_to_string(assignment[c]) for c in constants]))
                self.assertTrue(isla.evaluate(formula, {
                    c: (tuple() if c.path is None else c.path, assignment[c]) for c in constants
                }))
            except StopIteration:
                if idx == 0:
                    self.fail("No solution found.")
                self.fail(f"Only found {idx} solutions")


if __name__ == '__main__':
    unittest.main()
