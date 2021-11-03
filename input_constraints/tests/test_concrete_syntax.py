import unittest
from typing import cast

import z3

from input_constraints import isla
from input_constraints.isla import DummyVariable, parse_isla
from input_constraints.isla_predicates import BEFORE_PREDICATE
from input_constraints.tests.test_data import LANG_GRAMMAR, XML_GRAMMAR
import input_constraints.isla_shortcuts as sc


class TestConcreteSyntax(unittest.TestCase):
    def test_declared_before_used(self):
        DummyVariable.cnt = 0

        mgr = isla.VariableManager(LANG_GRAMMAR)
        python_formula: isla.Formula = mgr.create(sc.forall_bind(
            mgr.bv("lhs_1", "<var>") + " := " + mgr.bv("rhs_1", "<rhs>"),
            mgr.bv("assgn_1", "<assgn>"),
            mgr.const("start", "<start>"),
            sc.forall(
                mgr.bv("var", "<var>"),
                mgr.bv("rhs_1"),
                sc.exists_bind(
                    mgr.bv("lhs_2", "<var>") + " := " + mgr.bv("rhs_2", "<rhs>"),
                    mgr.bv("assgn_2", "<assgn>"),
                    mgr.const("start"),
                    sc.before(mgr.bv("assgn_2"), mgr.bv("assgn_1")) &
                    mgr.smt(cast(z3.BoolRef, mgr.bv("lhs_2").to_smt() == mgr.bv("var").to_smt()))
                )
            )
        ))

        DummyVariable.cnt = 0
        concr_syntax_formula = """
             const start: <start>;

             vars {
                 lhs_1, var, lhs_2: <var>;
                 rhs_1, rhs_2: <rhs>;
                 assgn_1, assgn_2: <assgn>;
             }

             constraint {
               forall assgn_1="{lhs_1} := {rhs_1}" in start:
                 forall var in rhs_1:
                   exists assgn_2="{lhs_2} := {rhs_2}" in start:
                     (before(assgn_2, assgn_1) and (= lhs_2 var))
             }"""

        parsed_formula = parse_isla(concr_syntax_formula, structural_predicates={BEFORE_PREDICATE})

        self.assertEqual(python_formula, parsed_formula)

    def test_xml(self):
        # TODO: Check whether we can express this in concrete syntax (angular brackets in bind expressions!)
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


if __name__ == '__main__':
    unittest.main()
