import logging
import unittest
from typing import cast, List, Optional

import z3
from fuzzingbook.GrammarFuzzer import tree_to_string
from fuzzingbook.Parser import EarleyParser

from input_constraints import isla
from input_constraints import isla_shortcuts as sc
from input_constraints.gensearch_2 import ISLaSolver
from input_constraints.isla import DerivationTree
from input_constraints.tests.test_data import LANG_GRAMMAR
from input_constraints.type_defs import Path


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
        logging.basicConfig(level=logging.DEBUG)
        # Idea: part of an assignment "var := rhs"
        var = isla.Constant("$var", "<var>")
        rhs = isla.Constant("$rhs", "<rhs>")
        initial_tree = DerivationTree.from_parse_tree(
            ('<start>', [('<stmt>', [('<assgn>', [(var, None), (' := ', []), (rhs, None)])])]))

        formula = isla.ConjunctiveFormula(
            isla.SMTFormula(cast(z3.BoolRef, var.to_smt() == z3.StringVal("x")), var),
            sc.before(var, rhs))

        self.execute_generation_test(formula, [var, rhs],
                                     initial_derivation_tree=initial_tree,
                                     max_number_smt_instantiations=2,
                                     max_number_free_instantiations=10,
                                     num_solutions=10,
                                     print_solutions=True
                                     )

    def test_simple_universal_formula(self):
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
        # logging.basicConfig(level=logging.DEBUG)
        start = isla.Constant("$start", "<start>")
        var1 = isla.BoundVariable("$var", "<var>")

        formula = sc.exists(
            var1, start,
            sc.smt_for(cast(z3.BoolRef, var1.to_smt() == z3.StringVal("x")), var1))

        self.execute_generation_test(formula, [start],
                                     num_solutions=100,
                                     max_number_free_instantiations=1)

    def test_simple_existential_formula_with_bind(self):
        start = isla.Constant("$start", "<start>")
        rhs = isla.BoundVariable("$rhs", "<rhs>")
        var1 = isla.BoundVariable("$var", "<var>")

        formula = sc.exists_bind(
            isla.BindExpression(var1),
            rhs, start,
            sc.smt_for(cast(z3.BoolRef, var1.to_smt() == z3.StringVal("x")), var1))

        self.execute_generation_test(formula, [start])

    def test_conjunction_of_qfd_formulas(self):
        start = isla.Constant("$start", "<start>")
        assgn = isla.BoundVariable("$assgn", "<assgn>")
        rhs = isla.BoundVariable("$rhs", "<rhs>")
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
                var_1 + " := " + rhs,
                assgn, start,
                (sc.smt_for(cast(z3.BoolRef, var_1.to_smt() == z3.StringVal("y")), var_1) &
                 sc.forall(
                     var_2, rhs,
                     sc.smt_for(cast(z3.BoolRef, var_2.to_smt() == z3.StringVal("x")), var_2))
                 ))

        self.execute_generation_test(formula, [start], num_solutions=15)

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

        self.execute_generation_test(formula, [start], print_solutions=True,
                                     max_number_free_instantiations=1, max_number_smt_instantiations=1)

    def execute_generation_test(self,
                                formula: isla.Formula,
                                constants: List[isla.Constant],
                                initial_derivation_tree: Optional[DerivationTree] = None,
                                num_solutions=50,
                                print_solutions=False,
                                max_number_free_instantiations=1,
                                max_number_smt_instantiations=1
                                ):
        solver = ISLaSolver(
            grammar=LANG_GRAMMAR,
            formula=formula,
            initial_derivation_tree=initial_derivation_tree,
            max_number_free_instantiations=max_number_free_instantiations,
            max_number_smt_instantiations=max_number_smt_instantiations)

        constant_paths = {c: tuple() for c in constants}
        if initial_derivation_tree is not None:
            for constant in constants:
                constant_paths[constant] = initial_derivation_tree.filter(
                    lambda t: t.value == constant and t.children is None, enforce_unique=True)[0][0]

        it = solver.solve()
        for idx in range(num_solutions):
            try:
                assignment = next(it)
                if print_solutions:
                    print(", ".join([tree_to_string(assignment[c]) for c in constants]))
                self.assertTrue(isla.evaluate(formula, {
                    c: (constant_paths[c], assignment[c])
                    for c in constants
                }))
            except StopIteration:
                if idx == 0:
                    self.fail("No solution found.")
                self.fail(f"Only found {idx} solutions")


if __name__ == '__main__':
    unittest.main()
