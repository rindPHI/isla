import unittest
from typing import cast

import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer

import input_constraints.isla_shortcuts as sc
from input_constraints.isla import Constant, BoundVariable, Formula, well_formed, evaluate, BindExpression, \
    DerivationTree
from test_data import *


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
                sc.exists_bind(
                    lhs_2 + " := " + rhs_2,
                    assgn_2,
                    prog,
                    sc.before(assgn_2, assgn_1) &
                    sc.smt_for(cast(z3.BoolRef, lhs_2.to_smt() == var.to_smt()), lhs_2, var)
                )
            )
        )

        self.assertTrue(well_formed(formula))

        bad_formula: Formula = sc.forall_bind(
            lhs_1 + " := " + rhs_1,
            assgn_1,
            prog,
            sc.exists_bind(
                lhs_2 + " := " + rhs_2,
                assgn_2,
                prog,
                sc.before(assgn_2, assgn_1) &
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

        bad_formula_6: Formula = sc.forall(
            assgn_1,
            prog,
            sc.SMTFormula(cast(z3.BoolRef, prog.to_smt() == z3.StringVal("x := x")), prog)
        )

        self.assertFalse(well_formed(bad_formula_6))

        bad_formula_7: Formula = sc.forall(
            assgn_1,
            prog,
            sc.forall(
                assgn_2,
                assgn_1,
                sc.SMTFormula(cast(z3.BoolRef, assgn_1.to_smt() == z3.StringVal("x := x")), assgn_1)
            )
        )

        self.assertFalse(well_formed(bad_formula_7))

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
                    sc.before(assgn_2, assgn_1) &
                    sc.smt_for(cast(z3.BoolRef, lhs_2.to_smt() == var.to_smt()), lhs_2, var)
                )
            )
        )

        valid_prog_1 = "x := 1 ; y := x"
        valid_prog_2 = "x := 1 ; y := x ; y := 2 ; z := y ; x := z"
        invalid_prog_1 = "x := x"
        invalid_prog_2 = "x := z"
        invalid_prog_3 = "x := 1 ; y := z"
        invalid_prog_4 = "x := y ; y := 1"

        parser = EarleyParser(LANG_GRAMMAR)

        tree = DerivationTree.from_parse_tree(next(parser.parse(valid_prog_1)))
        self.assertTrue(evaluate(formula, {prog: ((), tree)}))

        for valid_prog in [valid_prog_1, valid_prog_2]:
            tree = DerivationTree.from_parse_tree(next(parser.parse(valid_prog)))
            self.assertTrue(evaluate(formula, {prog: ((), tree)}))

        for invalid_prog in [invalid_prog_1, invalid_prog_2, invalid_prog_3, invalid_prog_4]:
            tree = DerivationTree.from_parse_tree(next(parser.parse(invalid_prog)))
            self.assertFalse(evaluate(formula, {prog: ((), tree)}))

    def test_evaluate_concrete_in_expr(self):
        parser = EarleyParser(LANG_GRAMMAR)

        prog = "x := 1 ; x := x"
        tree = DerivationTree.from_parse_tree(next(parser.parse(prog)))
        var = BoundVariable("$var", "<var>")

        formula = sc.forall(var, tree, sc.smt_for(cast(z3.BoolRef, var.to_smt() == z3.StringVal("x")), var))
        self.assertTrue(evaluate(formula, {}))
        formula = sc.forall(var, tree, sc.smt_for(cast(z3.BoolRef, var.to_smt() == z3.StringVal("y")), var))
        self.assertFalse(evaluate(formula, {}))

        formula = sc.exists(var, tree, sc.smt_for(cast(z3.BoolRef, var.to_smt() == z3.StringVal("x")), var))
        self.assertTrue(evaluate(formula, {}))
        formula = sc.exists(var, tree, sc.smt_for(cast(z3.BoolRef, var.to_smt() == z3.StringVal("y")), var))
        self.assertFalse(evaluate(formula, {}))


    def test_match(self):
        parser = EarleyParser(LANG_GRAMMAR)

        lhs = BoundVariable("$lhs", "<var>")
        rhs = BoundVariable("$rhs", "<var>")

        bind_expr = lhs + " := " + rhs
        tree = DerivationTree.from_parse_tree(next(parser.parse("x := y")))

        match = bind_expr.match(tree)
        self.assertEqual(('<var>', [('x', [])]), match[lhs][1].to_parse_tree())
        self.assertEqual(('<var>', [('y', [])]), match[rhs][1].to_parse_tree())

        assgn_1 = BoundVariable("$assgn_1", "<assgn>")
        assgn_2 = BoundVariable("$assgn_2", "<assgn>")
        stmt = BoundVariable("$stmt", "<stmt>")

        bind_expr = assgn_1 + " ; " + assgn_2 + " ; " + stmt
        tree = DerivationTree.from_parse_tree(next(parser.parse("x := y ; x := x ; y := z ; z := z")))

        match = bind_expr.match(tree)
        self.assertEqual(str(match[assgn_1][1]), "x := y")
        self.assertEqual(str(match[assgn_2][1]), "x := x")
        self.assertEqual(str(match[stmt][1]), "y := z ; z := z")

        # The stmt variable matches the whole remaining program; assgn2 can no longer be matched
        bind_expr = assgn_1 + " ; " + stmt + " ; " + assgn_2
        match = bind_expr.match(tree)
        self.assertFalse(match)

    def test_use_constraint_as_filter(self):
        prog = Constant("$prog", "<start>")
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
                    sc.before(assgn_2, assgn_1) &
                    sc.smt_for(cast(z3.BoolRef, lhs_2.to_smt() == var.to_smt()), lhs_2, var)
                )
            )
        )

        fuzzer = GrammarCoverageFuzzer(LANG_GRAMMAR)

        success = 0
        fail = 0
        for _ in range(100):
            tree = DerivationTree.from_parse_tree(fuzzer.expand_tree(("<start>", None)))
            if evaluate(formula, {prog: (tuple(), tree)}):
                inp = tree_to_string(tree)
                try:
                    eval_lang(inp)
                    print(inp)
                except KeyError:
                    self.fail()
                success += 1
            else:
                fail += 1

        success_rate = success / (success + fail)
        self.assertGreater(success_rate, .25)

    def test_bind_expression_to_tree(self):
        lhs = BoundVariable("$lhs", "<var>")
        rhs = BoundVariable("$rhs", "<rhs>")
        assgn = BoundVariable("$assgn", "<assgn>")

        bind_expr: BindExpression = lhs + " := " + rhs
        tree, bindings = bind_expr.to_tree_prefix(assgn.n_type, LANG_GRAMMAR)
        self.assertEqual("$lhs := $rhs", str(tree))
        self.assertEqual((0,), bindings[lhs])
        self.assertEqual((2,), bindings[rhs])

        prog = BoundVariable("$prog ", "<stmt>")
        lhs_2 = BoundVariable("$lhs_2 ", "<var>")
        rhs_2 = BoundVariable("$rhs_2", "<rhs>")
        semicolon = BoundVariable("$semi", " ; ")

        bind_expr: BindExpression = lhs + " := " + rhs + semicolon + lhs_2 + " := " + rhs_2
        tree, bindings = bind_expr.to_tree_prefix(prog.n_type, LANG_GRAMMAR)
        self.assertEqual("$lhs := $rhs$semi$lhs_2  := $rhs_2", str(tree))

        self.assertEqual((1,), bindings[semicolon])
        self.assertEqual((0, 0), bindings[lhs])
        self.assertEqual((0, 2), bindings[rhs])
        self.assertEqual((2, 0, 0), bindings[lhs_2])
        self.assertEqual((2, 0, 2), bindings[rhs_2])


if __name__ == '__main__':
    unittest.main()
