import unittest
from typing import cast

import z3
from fuzzingbook.Parser import EarleyParser

from input_constraints import isla, evaluator
import input_constraints.isla_shortcuts as sc
from input_constraints.tests.test_data import XML_GRAMMAR, LANG_GRAMMAR


class TestEvaluator(unittest.TestCase):
    def test_vacuously_satisfied_xml(self):
        mgr = isla.VariableManager(XML_GRAMMAR)
        start = mgr.const("$start", "<start>")
        formula: isla.Formula = mgr.create(
            sc.forall_bind(
                sc.bexpr("<") + mgr.bv("$oid", "<id>") + ">" +
                "<xml-tree>" +
                "</" + mgr.bv("$cid", "<id>") + ">",
                "<xml-tree>",
                start,
                mgr.smt(mgr.bv("$oid").to_smt() == mgr.bv("$cid").to_smt())
            ) &
            sc.forall_bind(
                sc.bexpr("<") + mgr.bv("$oid", "<id>") + " " + "<xml-attribute>" + ">" +
                "<xml-tree>" +
                "</" + mgr.bv("$cid", "<id>") + ">",
                "<xml-tree>",
                start,
                mgr.smt(mgr.bv("$oid").to_smt() == mgr.bv("$cid").to_smt())
            )
        )

        inp = "<vM/><a xhILyXld8=Tpm7R/>"
        tree = isla.DerivationTree.from_parse_tree(list(EarleyParser(XML_GRAMMAR).parse(inp))[0])
        self.assertTrue(evaluator.vacuously_satisfies(tree, formula))

        inp = "<a><b/>Test</a>"
        tree = isla.DerivationTree.from_parse_tree(list(EarleyParser(XML_GRAMMAR).parse(inp))[0])
        self.assertFalse(evaluator.vacuously_satisfies(tree, formula))

    def test_vacuously_satisfied_lang(self):
        mgr = isla.VariableManager(LANG_GRAMMAR)
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

        inp = "x := 1 ; y := 2 ; z := 3"
        tree = isla.DerivationTree.from_parse_tree(list(EarleyParser(LANG_GRAMMAR).parse(inp))[0])
        self.assertTrue(evaluator.vacuously_satisfies(tree, formula))

        inp = "x := 1 ; y := x ; z := 3"
        tree = isla.DerivationTree.from_parse_tree(list(EarleyParser(LANG_GRAMMAR).parse(inp))[0])
        self.assertFalse(evaluator.vacuously_satisfies(tree, formula))


if __name__ == '__main__':
    unittest.main()
