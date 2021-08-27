import logging
import unittest
from typing import cast

import z3

from input_constraints import isla
from input_constraints import isla_shortcuts as sc
from input_constraints.solver import ISLaSolver
from input_constraints.tests import rest
from input_constraints.tests.test_data import LANG_GRAMMAR, CSV_GRAMMAR, SIMPLE_CSV_GRAMMAR


class TestSolver(unittest.TestCase):
    def test_atomic_smt_formula(self):
        assgn = isla.Constant("$assgn", "<assgn>")
        formula = isla.SMTFormula(cast(z3.BoolRef, assgn.to_smt() == z3.StringVal("x := x")), assgn)
        self.execute_generation_test(formula, assgn, num_solutions=1)

    def test_simple_universal_formula(self):
        start = isla.Constant("$start", "<start>")
        var1 = isla.BoundVariable("$var", "<var>")

        formula = sc.forall(
            var1, start,
            sc.smt_for(cast(z3.BoolRef, var1.to_smt() == z3.StringVal("x")), var1))

        self.execute_generation_test(formula, start, max_number_free_instantiations=1)

    def test_simple_universal_formula_with_bind(self):
        mgr = isla.VariableManager()
        formula = mgr.create(
            sc.forall_bind(
                isla.BindExpression(mgr.bv("$var1", "<var>")),
                mgr.bv("$rhs", "<rhs>"), mgr.const("$start", "<start>"),
                mgr.smt(cast(z3.BoolRef, mgr.bv("$var1").to_smt() == z3.StringVal("x"))))
        )

        self.execute_generation_test(formula, mgr.const("$start"))

    def test_simple_existential_formula(self):
        start = isla.Constant("$start", "<start>")
        var1 = isla.BoundVariable("$var", "<var>")

        formula = sc.exists(
            var1, start,
            sc.smt_for(cast(z3.BoolRef, var1.to_smt() == z3.StringVal("x")), var1))

        # TODO: Try to create infinite solution stream
        self.execute_generation_test(
            formula, start, num_solutions=17,
            max_number_free_instantiations=1,
            expand_after_existential_elimination=True
        )

    def test_simple_existential_formula_with_bind(self):
        start = isla.Constant("$start", "<start>")
        rhs = isla.BoundVariable("$rhs", "<rhs>")
        var1 = isla.BoundVariable("$var", "<var>")

        formula = sc.exists_bind(
            isla.BindExpression(var1),
            rhs, start,
            sc.smt_for(cast(z3.BoolRef, var1.to_smt() == z3.StringVal("x")), var1))

        # TODO: Try to create infinite solution stream
        self.execute_generation_test(formula, start, num_solutions=1)

    def test_conjunction_of_qfd_formulas(self):
        start = isla.Constant("$start", "<start>")
        assgn = isla.BoundVariable("$assgn", "<assgn>")
        rhs_1 = isla.BoundVariable("$rhs_1", "<rhs>")
        rhs_2 = isla.BoundVariable("$rhs_2", "<rhs>")
        var_1 = isla.BoundVariable("$var1", "<var>")
        var_2 = isla.BoundVariable("$var2", "<var>")

        formula = \
            sc.forall_bind(
                isla.BindExpression(var_1),
                rhs_1, start,
                sc.smt_for(cast(z3.BoolRef, var_1.to_smt() == z3.StringVal("x")), var_1)) & \
            sc.forall_bind(
                var_2 + " := " + rhs_2,
                assgn, start,
                sc.smt_for(cast(z3.BoolRef, var_2.to_smt() == z3.StringVal("y")), var_2))

        self.execute_generation_test(formula, start, num_solutions=15)

    def test_declared_before_used(self):
        mgr = isla.VariableManager()
        formula: isla.Formula = mgr.create(sc.forall_bind(
            mgr.bv("$lhs_1", "<var>") + " := " + mgr.bv("$rhs_1", "<rhs>"),
            mgr.bv("$assgn_1", "<assgn>"),
            mgr.const("$start", "<start>"),
            sc.forall(
                mgr.bv("$var", "<var>"),
                mgr.bv("$rhs_1"),
                sc.exists_bind(
                    mgr.bv("$lhs_2", "<var>") + " := " + mgr.bv("$rhs_2", "<rhs>"),
                    mgr.bv("$assgn_2", "<assgn>"),
                    mgr.const("$start"),
                    sc.before(mgr.bv("$assgn_2"), mgr.bv("$assgn_1")) &
                    mgr.smt(cast(z3.BoolRef, mgr.bv("$lhs_2").to_smt() == mgr.bv("$var").to_smt()))
                )
            )
        ))

        self.execute_generation_test(formula, mgr.const("$start"), max_number_free_instantiations=1)

    def test_simple_csv_rows_equal_length(self):
        mgr = isla.VariableManager()
        formula = mgr.create(
            mgr.smt(cast(z3.BoolRef, z3.StrToInt(mgr.num_const("$num").to_smt()) >= z3.IntVal(3))) &
            mgr.smt(cast(z3.BoolRef, z3.StrToInt(mgr.num_const("$num").to_smt()) <= z3.IntVal(5))) &
            sc.forall(
                mgr.bv("$hline", "<csv-header>"),
                mgr.const("$start", "<start>"),
                sc.count(mgr.bv("$hline"), "<csv-field>", mgr.num_const("$num"))) &
            sc.forall(
                mgr.bv("$line", "<csv-record>"),
                mgr.const("$start", "<start>"),
                sc.count(mgr.bv("$line"), "<csv-field>", mgr.num_const("$num")))
        )

        self.execute_generation_test(formula, mgr.const("$start"),
                                     grammar=SIMPLE_CSV_GRAMMAR,
                                     max_number_free_instantiations=1,
                                     max_number_smt_instantiations=2,
                                     enforce_unique_trees_in_queue=False)

    def test_csv_rows_equal_length(self):
        mgr = isla.VariableManager()
        formula = mgr.create(
            mgr.smt(cast(z3.BoolRef, z3.StrToInt(mgr.num_const("$num").to_smt()) >= z3.IntVal(3))) &
            mgr.smt(cast(z3.BoolRef, z3.StrToInt(mgr.num_const("$num").to_smt()) <= z3.IntVal(5))) &
            sc.forall(
                mgr.bv("$hline", "<csv-header>"),
                mgr.const("$start", "<start>"),
                sc.count(mgr.bv("$hline"), "<raw-string>", mgr.num_const("$num"))) &
            sc.forall(
                mgr.bv("$line", "<csv-record>"),
                mgr.const("$start", "<start>"),
                sc.count(mgr.bv("$line"), "<raw-string>", mgr.num_const("$num")))
        )

        self.execute_generation_test(formula, mgr.const("$start"),
                                     grammar=CSV_GRAMMAR,
                                     max_number_free_instantiations=1,
                                     max_number_smt_instantiations=2,
                                     enforce_unique_trees_in_queue=False)

    def test_rest_titles(self):
        self.execute_generation_test(
            rest.length_underline,
            isla.Constant("$start", "<start>"),
            grammar=rest.REST_GRAMMAR,
            max_number_free_instantiations=1,
            max_number_smt_instantiations=5,
            expand_after_existential_elimination=False,
            enforce_unique_trees_in_queue=False)

    def execute_generation_test(self,
                                formula: isla.Formula,
                                constant: isla.Constant,
                                grammar=LANG_GRAMMAR,
                                num_solutions=50,
                                print_solutions=False,
                                max_number_free_instantiations=1,
                                max_number_smt_instantiations=1,
                                expand_after_existential_elimination=False,
                                enforce_unique_trees_in_queue=True
                                ):
        solver = ISLaSolver(
            grammar=grammar,
            formula=formula,
            max_number_free_instantiations=max_number_free_instantiations,
            max_number_smt_instantiations=max_number_smt_instantiations,
            expand_after_existential_elimination=expand_after_existential_elimination,
            enforce_unique_trees_in_queue=enforce_unique_trees_in_queue,
        )

        it = solver.solve()
        for idx in range(num_solutions):
            try:
                assignment = next(it)
                logging.getLogger(type(self).__name__).info(f"Found solution: {assignment}")
                if print_solutions:
                    print(str(assignment))
                self.assertTrue(isla.evaluate(formula.substitute_expressions({constant: assignment})))
            except StopIteration:
                if idx == 0:
                    self.fail("No solution found.")
                self.fail(f"Only found {idx} solutions")


if __name__ == '__main__':
    unittest.main()
