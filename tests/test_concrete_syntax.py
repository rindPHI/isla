import string
import unittest
from typing import cast

import pytest
import z3
from fuzzingbook.Grammars import srange
from orderedset import OrderedSet

from isla.helpers import strip_ws
from isla import language
from isla.language import DummyVariable, parse_isla, ISLaUnparser, VariableManager, used_variables_in_concrete_syntax
from isla.isla_predicates import BEFORE_PREDICATE, LEVEL_PREDICATE
from isla.z3_helpers import z3_eq
from isla_formalizations import scriptsizec
from isla_formalizations.xml_lang import XML_GRAMMAR_WITH_NAMESPACE_PREFIXES
from test_data import LANG_GRAMMAR
import isla.isla_shortcuts as sc


class TestConcreteSyntax(unittest.TestCase):
    def test_simple_formula(self):
        DummyVariable.cnt = 0

        mgr = language.VariableManager(LANG_GRAMMAR)
        python_formula: language.Formula = mgr.create(sc.forall(
            mgr.bv("var_1", "<var>"),
            mgr.const("start", "<start>"),
            sc.forall(
                mgr.bv("var_2", "<var>"),
                mgr.bv("start"),
                mgr.smt(z3_eq(mgr.bv("var_1").to_smt(), mgr.bv("var_2").to_smt()))
            )))

        DummyVariable.cnt = 0
        concr_syntax_formula = """
forall <var> var_1 in start:
    forall <var> var_2 in start:
        (= var_1 var_2)"""

        parsed_formula = parse_isla(concr_syntax_formula, LANG_GRAMMAR)

        self.assertEqual(python_formula, parsed_formula)

    def test_declared_before_used(self):
        DummyVariable.cnt = 0
        dummy_2 = DummyVariable(" := ")
        dummy_1 = DummyVariable(" := ")

        mgr = language.VariableManager(LANG_GRAMMAR)
        python_formula: language.Formula = mgr.create(sc.forall_bind(
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
                    mgr.smt(z3_eq(mgr.bv("lhs_2").to_smt(), mgr.bv("var").to_smt()))
                )
            )
        ))

        DummyVariable.cnt = 0
        concr_syntax_formula = """
forall <assgn> assgn_1="{<var> lhs_1} := {<rhs> rhs_1}" in start:
  forall <var> var in rhs_1:
    exists <assgn> assgn_2="{<var> lhs_2} := {<rhs> rhs_2}" in start:
      (before(assgn_2, assgn_1) and (= lhs_2 var))"""

        parsed_formula = parse_isla(concr_syntax_formula, LANG_GRAMMAR, structural_predicates={BEFORE_PREDICATE})

        self.assertEqual(python_formula, parsed_formula)

    def test_parse_conditional_bind_expression(self):
        constr = """
forall <expr> expr in start:
  forall <id> use_id in expr:
    exists <declaration> decl="int {<id> def_id}[ = <expr>];" in start:
      (level("GE", "<block>", decl, expr) and
      (before(decl, expr) and
      (= use_id def_id)))"""

        parsed_formula = parse_isla(
            constr,
            scriptsizec.SCRIPTSIZE_C_GRAMMAR,
            structural_predicates={BEFORE_PREDICATE, LEVEL_PREDICATE})
        self.assertTrue(
            any(isinstance(e, list)
                for e in
                cast(language.ForallFormula,
                     cast(language.ForallFormula,
                          cast(language.ForallFormula,
                               parsed_formula).inner_formula).inner_formula).bind_expression.bound_elements))

    def test_circumflex_in_smt_formula(self):
        formula = """
forall <key_value> container="{<key> key} = {<value> value}" in start:
  ((= key "date") implies
   (str.in_re value (re.++ ((_ re.loop 4 4) (re.range "0" "9"))
                           (str.to_re "-")
                           ((_ re.loop 2 2) (re.range "0" "9"))
                           (str.to_re "-")
                           ((_ re.loop 2 2) (re.range "0" "9")))))"""

        grammar = {
            "<start>": ["<key_value>"],
            "<key_value>": ["<key> = <value>"],
            "<key>": ["<chars>"],
            "<chars>": ["", "<char><chars>"],
            "<char>": srange(string.ascii_letters + string.digits + "_-"),
            "<value>": ["<chars>"]
        }

        mgr = VariableManager(grammar)
        expected = sc.forall_bind(
            mgr.bv("key", "<key>") + " = " + mgr.bv("value", "<value>"),
            mgr.bv("container", "<key_value>"),
            mgr.const("start", "<start>"),
            -mgr.smt(z3_eq(mgr.bv("key").to_smt(), z3.StringVal("date"))) |
            mgr.smt(
                z3.InRe(mgr.bv("value").to_smt(),
                        z3.Concat(
                            z3.Loop(z3.Range("0", "9"), 4, 4),
                            z3.Re("-"),
                            z3.Loop(z3.Range("0", "9"), 2, 2),
                            z3.Re("-"),
                            z3.Loop(z3.Range("0", "9"), 2, 2),
                        ))))

        self.assertEqual(parse_isla(formula, grammar), expected)

    def test_smt_formula_to_sexpr(self):
        formula = """
(str.in_re 
  start 
  (re.++ 
    (re.++ 
      (re.++ 
        (re.++ 
          ((_ re.loop 4 4) (re.range "0" "9")) 
          (str.to_re "-")) 
        ((_ re.loop 2 2) (re.range "0" "9")))
      (str.to_re "-")) 
    ((_ re.loop 2 2) (re.range "0" "9"))))"""

        grammar = {
            "<start>": ["<key_value>"],
            "<key_value>": ["<key> = <value>"],
            "<key>": ["<chars>"],
            "<chars>": ["", "<char><chars>"],
            "<char>": srange(string.ascii_letters + string.digits + "_-"),
            "<value>": ["<chars>"]
        }

        self.assertEqual(
            strip_ws(ISLaUnparser(parse_isla(formula, grammar)).unparse()),
            strip_ws(formula))

    def test_ite(self):
        result = parse_isla("(ite true true true)")
        self.assertIsInstance(result, language.SMTFormula)
        self.assertEqual(z3.If(True, True, True), result.formula)

    def test_quotes_in_mexpr(self):
        result = parse_isla('''
exists <xml-attribute> attr="<id>=\\"{<text> text}\\"" in start:
  (= text "")''', XML_GRAMMAR_WITH_NAMESPACE_PREFIXES)

    def test_used_variables(self):
        concr_syntax_formula = """
forall <assgn> assgn_1="{<var> lhs_1} := {<rhs> rhs_1}" in start:
  forall <var> var in rhs_1:
    exists <assgn> assgn_2="{<var> lhs_2} := {<rhs> rhs_2}" in start:
      (before(assgn_2, assgn_1) and (= lhs_2 var))"""

        result = used_variables_in_concrete_syntax(concr_syntax_formula)
        expected = OrderedSet(['assgn_1', 'lhs_1', 'rhs_1', 'var', 'assgn_2', 'lhs_2', 'rhs_2'])

        self.assertEqual(expected, result)

    def test_used_variables_default_name(self):
        result = used_variables_in_concrete_syntax('forall <var> in start: exists <elem> elem in start: (= var elem)')
        self.assertEqual(result, OrderedSet(['elem']))

    def test_free_nonterminal(self):
        result = parse_isla('(= <var> "x")')
        expected = parse_isla('forall <var> var in start: (= var "x")')

        self.assertEqual(expected, result)

    def test_free_nonterminal_name_collision(self):
        result = parse_isla('exists <var> var in start: (= var <var>)')
        expected = parse_isla('forall <var> var_0 in start: exists <var> var in start: (= var var_0)')

        self.assertEqual(expected, result)

    def test_free_nonterminal_predicate(self):
        result = parse_isla('before(<var>, <expr>)', structural_predicates={BEFORE_PREDICATE})
        expected = parse_isla(
            'forall <var> var in start: forall <expr> expr in start: before(var, expr)',
            structural_predicates={BEFORE_PREDICATE})

        self.assertEqual(expected, result)

    def test_free_nonterminal_scope(self):
        result = parse_isla('(= <var> "x") and (= <expr> "1")')
        expected = parse_isla('forall <var> var in start: (= var "x") and forall <expr> expr in start: (= expr "1")')

        self.assertEqual(expected, result)

    def test_default_name_forall(self):
        result = parse_isla('forall <var> in start: (= <var> "x")')
        expected = parse_isla('forall <var> var in start: (= var "x")')

        self.assertEqual(expected, result)

    def test_default_name_exists(self):
        result = parse_isla('exists <var> in start: (= <var> "x")')
        expected = parse_isla('exists <var> var in start: (= var "x")')

        self.assertEqual(expected, result)

    # TODO (2022-07-20): Continue from here!
    def test_default_name_nested(self):
        result = parse_isla('forall <expr> in start: exists <elem> in <var>: (= <elem> "x")')
        expected = parse_isla('forall <expr> expr in start: forall <var> var in start: exists <elem> elem in var: (= elem "x")')

        self.assertEqual(expected, result)

    def test_omit_start(self):
        result = parse_isla('forall <var>: (= <var> "x")')
        expected = parse_isla('forall <var> var in start: (= var "x")')

        self.assertEqual(expected, result)


if __name__ == '__main__':
    unittest.main()
