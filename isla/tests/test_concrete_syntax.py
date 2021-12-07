import unittest
from typing import cast

import z3

from isla import isla
from isla.isla import DummyVariable, parse_isla
from isla.isla_predicates import BEFORE_PREDICATE, LEVEL_PREDICATE
from isla.tests.subject_languages.xml_lang import XML_GRAMMAR
from isla.tests.test_data import LANG_GRAMMAR
import isla.isla_shortcuts as sc


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

    def test_parse_conditional_bind_expression(self):
        constr = """
const start: <start>;

vars {
  expr: <expr>;
  def_id, use_id: <id>;
  decl: <declaration>;
}

constraint {
  forall expr in start:
    forall use_id in expr:
      exists decl="int {def_id}[ = <expr>];" in start:
        (level("GE", "<block>", decl, expr) and 
        (before(decl, expr) and 
        (= use_id def_id)))
}
"""

        parsed_formula = parse_isla(constr, structural_predicates={BEFORE_PREDICATE, LEVEL_PREDICATE})
        self.assertTrue(
            any(isinstance(e, list)
                for e in
                cast(isla.ForallFormula,
                     cast(isla.ForallFormula,
                          cast(isla.ForallFormula,
                               parsed_formula).inner_formula).inner_formula).bind_expression.bound_elements))


if __name__ == '__main__':
    unittest.main()
