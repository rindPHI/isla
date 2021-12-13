import unittest
from typing import cast

import z3

import isla.isla_shortcuts as sc
from isla import isla
from isla.isla import DummyVariable, parse_isla
from isla.isla_predicates import BEFORE_PREDICATE, LEVEL_PREDICATE
from isla.tests.test_data import LANG_GRAMMAR


class TestConcreteSyntax(unittest.TestCase):
    def test_simple_formula(self):
        DummyVariable.cnt = 0

        mgr = isla.VariableManager(LANG_GRAMMAR)
        python_formula: isla.Formula = mgr.create(sc.forall(
            mgr.bv("var_1", "<var>"),
            mgr.const("start", "<start>"),
            sc.forall(
                mgr.bv("var_2", "<var>"),
                mgr.bv("start"),
                mgr.smt(cast(z3.BoolRef, mgr.bv("var_1").to_smt() == mgr.bv("var_2").to_smt()))
            )))

        DummyVariable.cnt = 0
        concr_syntax_formula = """
             const start: <start>;

             vars {
                 var_1, var_2: <var>;
             }

             constraint {
               forall var_1 in start:
                   forall var_2 in start:
                       (= var_1 var_2)
             }"""

        parsed_formula = parse_isla(concr_syntax_formula)

        self.assertEqual(python_formula, parsed_formula)

    def test_declared_before_used(self):
        DummyVariable.cnt = 0
        dummy_2 = DummyVariable(" := ")
        dummy_1 = DummyVariable(" := ")

        mgr = isla.VariableManager(LANG_GRAMMAR)
        python_formula: isla.Formula = mgr.create(sc.forall_bind(
            mgr.bv("lhs_1", "<var>") + dummy_1 + mgr.bv("rhs_1", "<rhs>"),
            mgr.bv("assgn_1", "<assgn>"),
            mgr.const("start", "<start>"),
            sc.forall(
                mgr.bv("var", "<var>"),
                mgr.bv("rhs_1"),
                sc.exists_bind(
                    mgr.bv("lhs_2", "<var>") + dummy_2 + mgr.bv("rhs_2", "<rhs>"),
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
