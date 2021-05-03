import string
import unittest
from typing import cast

import z3
from fuzzingbook.GrammarFuzzer import tree_to_string
from fuzzingbook.Parser import EarleyParser

import input_constraints.shortcuts as sc
from input_constraints.lang import Constant, BoundVariable, Formula, well_formed, evaluate

LANG_GRAMMAR = {
    "<start>":
        ["<stmt>"],
    "<stmt>":
        ["<assgn>", "<assgn> ; <stmt>"],
    "<assgn>":
        ["<var> := <rhs>"],
    "<rhs>":
        ["<var>", "<digit>"],
    "<var>": list(string.ascii_lowercase),
    "<digit>": list(string.digits)
}


class TestEvaluation(unittest.TestCase):
    def test_wellformed(self):
        prog = Constant("$prog", "<prog>")
        lhs_1 = BoundVariable("$lhs_1", "<var>")
        lhs_2 = BoundVariable("$lhs_2", "<var>")
        rhs_1 = BoundVariable("$rhs_1", "<rhs>")
        rhs_2 = BoundVariable("$rhs_2", "<rhs>")
        assgn_1 = BoundVariable("$assgn_1", "<assgn>")
        assgn_2 = BoundVariable("$assgn_2", "<assgn>")
        var = BoundVariable("$var", "<var>")

        formula: Formula = sc.forall_bind(
            lhs_1 + " := " + rhs_1,
            assgn_1,
            prog,
            sc.forall(
                var,
                rhs_1,
                sc.exists_before_bind(
                    lhs_2 + " := " + rhs_2,
                    assgn_2,
                    assgn_1,
                    prog,
                    sc.smt_for(cast(z3.BoolRef, lhs_2.to_smt() == var.to_smt()), lhs_2, var)
                )
            )
        )

        self.assertTrue(well_formed(formula))

        bad_formula: Formula = sc.forall_bind(
            lhs_1 + " := " + rhs_1,
            assgn_1,
            prog,
            sc.exists_before_bind(
                lhs_2 + " := " + rhs_2,
                assgn_2,
                assgn_1,
                prog,
                sc.smt_for(cast(z3.BoolRef, lhs_2.to_smt() == var.to_smt()), lhs_2, var)
            )
        )

        self.assertFalse(well_formed(bad_formula))

        bad_formula_2: Formula = sc.forall(
            assgn_1,
            assgn_1,
            sc.smt_for(z3.BoolVal(True))
        )

        self.assertFalse(well_formed(bad_formula_2))
        self.assertFalse(bad_formula_2.free_variables())

        bad_formula_3: Formula = sc.forall(
            assgn_1,
            prog,
            sc.forall(
                assgn_1,
                prog,
                sc.smt_for(z3.BoolVal(True))
            )
        )

        self.assertFalse(well_formed(bad_formula_3))

        self.assertTrue(well_formed(-formula))
        self.assertFalse(well_formed(-bad_formula))
        self.assertFalse(well_formed(-bad_formula_2))
        self.assertFalse(well_formed(-bad_formula_3))

        self.assertFalse(well_formed(formula & bad_formula))
        self.assertFalse(well_formed(formula | bad_formula))

        bad_formula_4: Formula = sc.forall(
            assgn_1,
            prog,
            sc.SMTFormula(cast(z3.BoolRef, prog.to_smt() == z3.StringVal("")), prog)
        )

        self.assertFalse(well_formed(bad_formula_4))

        bad_formula_5: Formula = sc.forall(
            assgn_1,
            prog,
            sc.SMTFormula(cast(z3.BoolRef, assgn_1.to_smt() == z3.StringVal("")), assgn_1) & \
            sc.forall(
                var,
                assgn_1,
                sc.SMTFormula(z3.BoolVal(True))
            )
        )

        self.assertFalse(well_formed(bad_formula_5))

    def test_evaluate(self):
        prog = Constant("$prog", "<prog>")
        lhs_1 = BoundVariable("$lhs_1", "<var>")
        lhs_2 = BoundVariable("$lhs_2", "<var>")
        rhs_1 = BoundVariable("$rhs_1", "<rhs>")
        rhs_2 = BoundVariable("$rhs_2", "<rhs>")
        assgn_1 = BoundVariable("$assgn_1", "<assgn>")
        assgn_2 = BoundVariable("$assgn_2", "<assgn>")
        var = BoundVariable("$var", "<var>")

        formula: Formula = sc.forall_bind(
            lhs_1 + " := " + rhs_1,
            assgn_1,
            prog,
            sc.forall(
                var,
                rhs_1,
                sc.exists_bind(
                    lhs_2 + " := " + rhs_2,
                    assgn_2,
                    prog,
                    sc.before(assgn_2, assgn_1, prog) &
                    sc.smt_for(cast(z3.BoolRef, lhs_2.to_smt() == var.to_smt()), lhs_2, var)
                )
            )
        )

        valid_prog_1 = "x := 1 ; y := x"
        valid_prog_2 = "x := 1 ; y := x ; y := 2 ; z := y ; x := z"
        invalid_prog_1 = "x := x"
        invalid_prog_2 = "x := z"
        invalid_prog_3 = "x := 1 ; y := z"

        parser = EarleyParser(LANG_GRAMMAR)

        for valid_prog in [valid_prog_1, valid_prog_2]:
            self.assertTrue(evaluate(formula, {prog: next(parser.parse(valid_prog))}))
        for invalid_prog in [invalid_prog_1, invalid_prog_2, invalid_prog_3]:
            self.assertFalse(evaluate(formula, {prog: next(parser.parse(invalid_prog))}))

    def test_match(self):
        parser = EarleyParser(LANG_GRAMMAR)

        lhs = BoundVariable("$lhs", "<var>")
        rhs = BoundVariable("$rhs", "<var>")

        bind_expr = lhs + " := " + rhs
        tree = next(parser.parse("x := y"))

        match = bind_expr.match(tree)
        self.assertEqual(('<var>', [('x', [])]), match[lhs])
        self.assertEqual(('<var>', [('y', [])]), match[rhs])

        assgn_1 = BoundVariable("$assgn_1", "<assgn>")
        assgn_2 = BoundVariable("$assgn_2", "<assgn>")
        stmt = BoundVariable("$stmt", "<stmt>")

        bind_expr = assgn_1 + " ; " + assgn_2 + " ; " + stmt
        tree = next(parser.parse("x := y ; x := x ; y := z ; z := z"))

        match = bind_expr.match(tree)
        self.assertEqual(tree_to_string(match[assgn_1]), "x := y")
        self.assertEqual(tree_to_string(match[assgn_2]), "x := x")
        self.assertEqual(tree_to_string(match[stmt]), "y := z ; z := z")

        # The stmt variable matches the whole remaining program; assgn2 can no longer be matched
        bind_expr = assgn_1 + " ; " + stmt + " ; " + assgn_2
        match = bind_expr.match(tree)
        self.assertFalse(match)

        match = bind_expr.match(tree)


if __name__ == '__main__':
    unittest.main()
