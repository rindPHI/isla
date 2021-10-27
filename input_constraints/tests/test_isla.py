import random
import unittest
from typing import cast

import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer

import input_constraints.isla_shortcuts as sc
from input_constraints.isla import Constant, BoundVariable, Formula, well_formed, evaluate, BindExpression, \
    DerivationTree, convert_to_dnf, convert_to_nnf, ensure_unique_bound_variables, SemPredEvalResult, VariableManager, \
    matches_for_quantified_formula, QuantifiedFormula, DummyVariable, parse_isla
from input_constraints.isla_predicates import count, is_before, COUNT_PREDICATE
from input_constraints.tests.subject_languages import tinyc, tar
from input_constraints.tests.test_data import *
from input_constraints.tests.test_helpers import parse


class TestISLa(unittest.TestCase):
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
            sc.SMTFormula(cast(z3.BoolRef, assgn_1.to_smt() == z3.StringVal("")), assgn_1) &
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
        lhs_1 = BoundVariable("$lhs_1", "<var>")
        lhs_2 = BoundVariable("$lhs_2", "<var>")
        rhs_1 = BoundVariable("$rhs_1", "<rhs>")
        rhs_2 = BoundVariable("$rhs_2", "<rhs>")
        assgn_1 = BoundVariable("$assgn_1", "<assgn>")
        assgn_2 = BoundVariable("$assgn_2", "<assgn>")
        var = BoundVariable("$var", "<var>")

        formula: Callable[[DerivationTree], Formula] = lambda tree: sc.forall_bind(
            lhs_1 + " := " + rhs_1,
            assgn_1,
            tree,
            sc.forall(
                var,
                rhs_1,
                sc.exists_bind(
                    lhs_2 + " := " + rhs_2,
                    assgn_2,
                    tree,
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
        self.assertTrue(evaluate(formula(tree)).to_bool())

        for valid_prog in [valid_prog_1, valid_prog_2]:
            tree = DerivationTree.from_parse_tree(next(parser.parse(valid_prog)))
            self.assertTrue(evaluate(formula(tree)).to_bool())

        for invalid_prog in [invalid_prog_1, invalid_prog_2, invalid_prog_3, invalid_prog_4]:
            tree = DerivationTree.from_parse_tree(next(parser.parse(invalid_prog)))
            self.assertFalse(evaluate(formula(tree)).to_bool())

    def test_evaluate_concrete_in_expr(self):
        parser = EarleyParser(LANG_GRAMMAR)

        prog = "x := 1 ; x := x"
        tree = DerivationTree.from_parse_tree(next(parser.parse(prog)))
        var = BoundVariable("$var", "<var>")

        formula = sc.forall(var, tree, sc.smt_for(cast(z3.BoolRef, var.to_smt() == z3.StringVal("x")), var))
        self.assertTrue(evaluate(formula).to_bool())
        formula = sc.forall(var, tree, sc.smt_for(cast(z3.BoolRef, var.to_smt() == z3.StringVal("y")), var))
        self.assertFalse(evaluate(formula).to_bool())

        formula = sc.exists(var, tree, sc.smt_for(cast(z3.BoolRef, var.to_smt() == z3.StringVal("x")), var))
        self.assertTrue(evaluate(formula).to_bool())
        formula = sc.exists(var, tree, sc.smt_for(cast(z3.BoolRef, var.to_smt() == z3.StringVal("y")), var))
        self.assertFalse(evaluate(formula).to_bool())

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

    def test_match_tinyc_assignment(self):
        mgr = VariableManager(tinyc.TINYC_GRAMMAR)
        bind_expr = mgr.bv("$id_2", "<id>") + " = <expr>;"
        tree = DerivationTree.from_parse_tree(
            ('<statement>', [('<id>', [('c', [])]), (' = ', []), ('<expr>', None), (';', [])]))
        match = bind_expr.match(tree)
        self.assertTrue(match)

    def test_use_constraint_as_filter(self):
        lhs_1 = BoundVariable("$lhs_1", "<var>")
        lhs_2 = BoundVariable("$lhs_2", "<var>")
        rhs_1 = BoundVariable("$rhs_1", "<rhs>")
        rhs_2 = BoundVariable("$rhs_2", "<rhs>")
        assgn_1 = BoundVariable("$assgn_1", "<assgn>")
        assgn_2 = BoundVariable("$assgn_2", "<assgn>")
        var = BoundVariable("$var", "<var>")

        formula: Callable[[DerivationTree], Formula] = lambda tree: sc.forall_bind(
            lhs_1 + " := " + rhs_1,
            assgn_1,
            tree,
            sc.forall(
                var,
                rhs_1,
                sc.exists_bind(
                    lhs_2 + " := " + rhs_2,
                    assgn_2,
                    tree,
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
            if evaluate(formula(tree)).to_bool():
                inp = tree_to_string(tree)
                try:
                    eval_lang(inp)
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
        self.assertEqual("<var> := <rhs>", str(tree))
        self.assertEqual((0,), bindings[lhs])
        self.assertEqual((2,), bindings[rhs])

        prog = BoundVariable("$prog ", "<stmt>")
        lhs_2 = BoundVariable("$lhs_2 ", "<var>")
        rhs_2 = BoundVariable("$rhs_2", "<rhs>")
        semicolon = BoundVariable("$semi", " ; ")

        bind_expr: BindExpression = lhs + " := " + rhs + semicolon + lhs_2 + " := " + rhs_2
        tree, bindings = bind_expr.to_tree_prefix(prog.n_type, LANG_GRAMMAR)
        self.assertEqual("<var> := <rhs> ; <var> := <rhs>", str(tree))

        self.assertEqual((1,), bindings[semicolon])
        self.assertEqual((0, 0), bindings[lhs])
        self.assertEqual((0, 2), bindings[rhs])
        self.assertEqual((2, 0, 0), bindings[lhs_2])
        self.assertEqual((2, 0, 2), bindings[rhs_2])

    def test_dnf_conversion(self):
        a = Constant("$a", "<var>")
        w = sc.smt_for(a.to_smt() == z3.StringVal("1"), a)
        x = sc.smt_for(a.to_smt() == z3.StringVal("2"), a)
        y = sc.smt_for(a.to_smt() > z3.StringVal("0"), a)
        z = sc.smt_for(a.to_smt() < z3.StringVal("3"), a)

        formula = (w | x) & (y | z)
        self.assertEqual((w & y) | (w & z) | (x & y) | (x & z), convert_to_dnf(formula))

        formula = w & (y | z)
        self.assertEqual((w & y) | (w & z), convert_to_dnf(formula))

        formula = w & (x | y | z)
        self.assertEqual((w & x) | (w & y) | (w & z), convert_to_dnf(formula))

    def test_push_in_negation(self):
        a = Constant("$a", "<var>")
        w = sc.smt_for(a.to_smt() == z3.StringVal("1"), a)
        x = sc.smt_for(a.to_smt() == z3.StringVal("2"), a)
        y = sc.smt_for(a.to_smt() > z3.StringVal("0"), a)
        z = sc.smt_for(a.to_smt() < z3.StringVal("3"), a)

        formula = -((w | x) & (y | z))
        self.assertEqual(-w & -x | -y & -z, formula)

    def test_ensure_unique_bound_variables(self):
        start = Constant("$start", "<start>")
        assgn = BoundVariable("$assgn", "<assgn>")
        rhs_1 = BoundVariable("$rhs_1", "<rhs>")
        var_1 = BoundVariable("$var1", "<var>")

        DummyVariable.cnt = 0
        formula = \
            sc.forall_bind(
                BindExpression(var_1),
                rhs_1, start,
                sc.smt_for(cast(z3.BoolRef, var_1.to_smt() == z3.StringVal("x")), var_1)) & \
            sc.forall_bind(
                var_1 + " := " + rhs_1,
                assgn, start,
                sc.smt_for(cast(z3.BoolRef, var_1.to_smt() == z3.StringVal("y")), var_1))

        rhs_1_0 = BoundVariable("$rhs_1_0", "<rhs>")
        var_1_0 = BoundVariable("$var1_0", "<var>")

        DummyVariable.cnt = 0
        expected = \
            sc.forall_bind(
                BindExpression(var_1),
                rhs_1, start,
                sc.smt_for(cast(z3.BoolRef, var_1.to_smt() == z3.StringVal("x")), var_1)) & \
            sc.forall_bind(
                var_1_0 + " := " + rhs_1_0,
                assgn, start,
                sc.smt_for(cast(z3.BoolRef, var_1_0.to_smt() == z3.StringVal("y")), var_1_0))

        self.assertEqual(expected, ensure_unique_bound_variables(formula))
        self.assertEqual(expected, ensure_unique_bound_variables(expected))

    def test_count(self):
        prog = "x := 1 ; x := 1 ; x := 1"
        tree = DerivationTree.from_parse_tree(parse(prog, LANG_GRAMMAR))

        result = count(LANG_GRAMMAR, tree, "<assgn>", Constant("n", "NUM"))
        self.assertEqual("{n: 3}", str(result))

        result = count(LANG_GRAMMAR, tree, "<assgn>", DerivationTree("3", None))
        self.assertEqual(SemPredEvalResult(True), result)

        result = count(LANG_GRAMMAR, tree, "<assgn>", DerivationTree("4", None))
        self.assertEqual(SemPredEvalResult(False), result)

        tree = DerivationTree("<start>", [DerivationTree("<stmt>", None)])
        result = count(LANG_GRAMMAR, tree, "<assgn>", DerivationTree("4", None))
        self.assertEqual("{<stmt>: <assgn> ; <assgn> ; <assgn> ; <assgn>}", str(result))

        result = count(LANG_GRAMMAR, tree, "<start>", DerivationTree("2", None))
        self.assertEqual(SemPredEvalResult(False), result)

    def test_csv_prop(self):
        mgr = VariableManager(CSV_GRAMMAR)
        formula = lambda tree: mgr.create(
            sc.forall(
                mgr.bv("$header", "<csv-header>"),
                tree,
                sc.count(CSV_GRAMMAR, mgr.bv("$header"), "<raw-string>", mgr.num_const("$num")) &
                sc.forall(
                    mgr.bv("$line", "<csv-record>"),
                    tree,
                    sc.count(CSV_GRAMMAR, mgr.bv("$line"), "<raw-string>", mgr.num_const("$num"))
                )
            )
        )

        csv_doc = "a;b;c\nd;e;f\n"
        tree = DerivationTree.from_parse_tree(parse(csv_doc, CSV_GRAMMAR))
        self.assertTrue(evaluate(formula(tree)).to_bool())

        csv_doc = "a;b;c\nd;e;f\ng;h;i;j\n"
        tree = DerivationTree.from_parse_tree(parse(csv_doc, CSV_GRAMMAR))
        self.assertFalse(evaluate(formula(tree)).to_bool())

        return

        mgr = VariableManager(CSV_GRAMMAR)
        formula = lambda tree: mgr.create(
            sc.forall(
                mgr.bv("$header", "<csv-header>"),
                tree,
                sc.count(mgr.bv("$header"), "<raw-string>", mgr.num_const("$num")) &
                sc.forall(
                    mgr.bv("$line", "<csv-record>"),
                    tree,
                    sc.count(mgr.bv("$line"), "<raw-string>", mgr.num_const("$num2")) &
                    mgr.smt(cast(z3.BoolRef,
                                 z3.StrToInt(mgr.num_const("$num").to_smt()) >=
                                 z3.StrToInt(mgr.num_const("$num2").to_smt())))
                )
            )
        )

        csv_doc = "a;b;c\nd;e\ng;h;i\n"
        tree = DerivationTree.from_parse_tree(parse(csv_doc, CSV_GRAMMAR))
        self.assertTrue(evaluate(formula(tree)).to_bool())

        csv_doc = "a;b;c\nd;e\ng;h;i;j\n"
        tree = DerivationTree.from_parse_tree(parse(csv_doc, CSV_GRAMMAR))
        self.assertFalse(evaluate(formula(tree)).to_bool())

    def test_to_tree_prefix_tar_file_name(self):
        mgr = VariableManager(tar.TAR_GRAMMAR)
        bind_expression = mgr.bv("$file_name_chars", "<characters>") + "<maybe_nuls>"
        self.assertEqual(('<file_name>', [('<characters>', None), ('<maybe_nuls>', None)]),
                         bind_expression.to_tree_prefix("<file_name>", tar.TAR_GRAMMAR)[0].to_parse_tree())

    def test_matches_xml_property(self):
        inp = "<a/><b>k</b>"
        tree = DerivationTree.from_parse_tree(list(EarleyParser(XML_GRAMMAR).parse(inp))[0])

        mgr = VariableManager(XML_GRAMMAR)
        start = mgr.const("$start", "<start>")
        formula: QuantifiedFormula = cast(QuantifiedFormula, mgr.create(sc.forall_bind(
            sc.bexpr("<") + mgr.bv("$oid", "<id>") + ">" +
            "<xml-tree>" +
            "</" + mgr.bv("$cid", "<id>") + ">",
            "<xml-tree>",
            start,
            mgr.smt(mgr.bv("$oid").to_smt() == mgr.bv("$cid").to_smt())
        )))

        matches = matches_for_quantified_formula(formula, tree, {start: tree})
        self.assertEqual(1, len(matches))

    def test_xml_property(self):
        mgr = VariableManager(XML_GRAMMAR)
        start = mgr.const("$start", "<start>")
        formula: Formula = mgr.create(sc.forall_bind(
            sc.bexpr("<") + mgr.bv("$oid", "<id>") + ">" +
            "<xml-tree>" +
            "</" + mgr.bv("$cid", "<id>") + ">",
            "<xml-tree>",
            start,
            mgr.smt(mgr.bv("$oid").to_smt() == mgr.bv("$cid").to_smt())
        ))

        correct_tree = DerivationTree.from_parse_tree(list(EarleyParser(XML_GRAMMAR).parse("<a/><b>k</b>"))[0])
        wrong_tree = DerivationTree.from_parse_tree(
            list(EarleyParser(XML_GRAMMAR).parse("8Cf<2>5</4n><Y i=s/>"))[0])

        self.assertTrue(evaluate(formula.substitute_expressions({start: correct_tree})).is_true())
        self.assertFalse(evaluate(formula.substitute_expressions({start: wrong_tree})).is_true())

    def test_csv_property(self):
        property = """
const start: <start>;

vars {
  colno: <NUM>;
  hline: <csv-header>;
  line: <csv-line>;
}

constraint {
  forall hline in start:
    num colno:
      ((>= (str.to_int colno) 3) and 
      ((<= (str.to_int colno) 5) and 
       (count(hline, "<raw-string>", colno) and 
       forall line in start:
         count(line, "<raw-string>", colno))))
}
"""
        valid_test_input = """a;b;c
XYZ;\" asdf \";ABC
123;!@#$;\"456 \n 789\"\n"""

        # self.assertTrue(evaluate(
        #     property,
        #     reference_tree=DerivationTree.from_parse_tree(list(EarleyParser(CSV_GRAMMAR).parse(valid_test_input))[0]),
        #     semantic_predicates={"count": COUNT_PREDICATE(CSV_GRAMMAR)}))

        invalid_test_input = """a;b;c
XYZ;\" asdf \"
123;!@#$;\"456 \n 789\"\n"""

        self.assertFalse(evaluate(
            property,
            reference_tree=DerivationTree.from_parse_tree(list(EarleyParser(CSV_GRAMMAR).parse(invalid_test_input))[0]),
            semantic_predicates={"count": COUNT_PREDICATE(CSV_GRAMMAR)}))


if __name__ == '__main__':
    unittest.main()
