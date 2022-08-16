import string
import unittest
from typing import cast

import pytest
import z3
from orderedset import OrderedSet

import isla.isla_shortcuts as sc
from isla import language
from isla.helpers import strip_ws, srange, crange
from isla.isla_predicates import BEFORE_PREDICATE, LEVEL_PREDICATE, STANDARD_STRUCTURAL_PREDICATES
from isla.language import DummyVariable, parse_isla, ISLaUnparser, VariableManager, used_variables_in_concrete_syntax, \
    unparse_isla, parse_bnf, unparse_grammar
from isla.z3_helpers import z3_eq
from isla_formalizations import scriptsizec
from isla_formalizations.tar import TAR_CHECKSUM_PREDICATE, TAR_GRAMMAR
from isla_formalizations.xml_lang import XML_GRAMMAR_WITH_NAMESPACE_PREFIXES, XML_GRAMMAR
from test_data import LANG_GRAMMAR


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

    def test_default_name_nested(self):
        result = parse_isla('forall <expr> in start: exists <elem> in <var>: (= <elem> "x")')
        expected = parse_isla(
            'forall <var> var in start: '
            '  forall <expr> expr in start: exists <elem> elem in var: (= elem "x")')

        self.assertEqual(expected, result)

    def test_omit_start(self):
        result = parse_isla('forall <var>: (= <var> "x")')
        expected = parse_isla('forall <var> var in start: (= var "x")')

        self.assertEqual(expected, result)

    def test_infix(self):
        result = parse_isla('forall <var>: <var> = "x"')
        expected = parse_isla('forall <var> var in start: (= var "x")')

        self.assertEqual(expected, result)

    def test_xpath_syntax_xml_simplified(self):
        result = parse_isla('(= <xml-tree>.<xml-open-tag>.<id> "a")', grammar=XML_GRAMMAR_WITH_NAMESPACE_PREFIXES)

        expected = parse_isla('''
forall <xml-tree> xml-tree="<{<id> id} <xml-attribute>><inner-xml-tree><xml-close-tag>" in start:
    (= id "a") and
forall <xml-tree> xml-tree_0="<{<id> id_0}><inner-xml-tree><xml-close-tag>" in start:
    (= id_0 "a")''')

        self.assertEqual(unparse_isla(expected), unparse_isla(result))

    def test_xpath_syntax_xml(self):
        result = parse_isla(
            '(= <xml-tree>.<xml-open-tag>.<id> <xml-tree>.<xml-close-tag>.<id>)',
            grammar=XML_GRAMMAR_WITH_NAMESPACE_PREFIXES)

        expected = parse_isla('''
forall <xml-tree> xml-tree="<{<id> id} <xml-attribute>><inner-xml-tree></{<id> id_0}>" in start:
    (= id id_0) and
forall <xml-tree> xml-tree_0="<{<id> id_1}><inner-xml-tree></{<id> id_2}>" in start:
    (= id_1 id_2)''')

        self.assertEqual(expected, result)

    def test_xpath_syntax_tar_checksum(self):
        result = parse_isla('''
forall <checksum> in <header>:
  tar_checksum(<header>, <checksum>)''', semantic_predicates={TAR_CHECKSUM_PREDICATE})

        expected = parse_isla('''
forall <header> header in start:
  forall <checksum> checksum in header:
    tar_checksum(header, checksum)''', semantic_predicates={TAR_CHECKSUM_PREDICATE})

        self.assertEqual(expected, result)

    def test_xpath_for_bound_variable_assgn_lang_simplified(self):
        result = parse_isla(
            '''exists <assgn> assgn:
                 (before(assgn, <assgn>) and (= <assgn>.<rhs>.<var> "x"))''',
            grammar=LANG_GRAMMAR,
            structural_predicates={BEFORE_PREDICATE})

        expected = parse_isla('''
forall <assgn> assgn_1="<var> := {<var> var}" in start:
  exists <assgn> assgn in start:
    (before(assgn, assgn_1) and (= var "x")))''', structural_predicates={BEFORE_PREDICATE})

        self.assertEqual(expected, result)

    def test_xpath_infix_for_bound_variable_assgn_lang_unbound_identifier(self):
        self.assertRaises(
            SyntaxError,
            parse_isla,
            '''exists <assgn> assgn:
                 before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>''',
            LANG_GRAMMAR,
            STANDARD_STRUCTURAL_PREDICATES)

    def test_xpath_infix_for_bound_variable_assgn_lang(self):
        result = parse_isla(
            '''exists <assgn> assgn:
                 (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)''',
            grammar=LANG_GRAMMAR,
            structural_predicates=STANDARD_STRUCTURAL_PREDICATES)

        expected = parse_isla('''
forall <assgn> assgn_1="<var> := {<var> var}" in start:
  exists <assgn> assgn="{<var> var_0} := <rhs>" in start:
    (before(assgn, assgn_1) and (= var var_0)))''', structural_predicates=STANDARD_STRUCTURAL_PREDICATES)

        self.assertEqual(expected, result)

    def test_xpath_syntax_xml_conflicting_xpaths(self):
        self.assertRaises(
            SyntaxError,
            parse_isla,
            '(= <xml-tree>.<xml-open-tag>.<id> <xml-tree>.<xml-open-tag>)',
            XML_GRAMMAR_WITH_NAMESPACE_PREFIXES)

    def test_xpath_already_existing_match_expression(self):
        result = parse_isla(
            '''exists <assgn> assgn="<var> := <rhs>" in start:
                 (before(assgn, <assgn>) and (= <assgn>.<rhs>.<var> assgn.<var>))''',
            LANG_GRAMMAR,
            {BEFORE_PREDICATE})

        expected = parse_isla(
            '''forall <assgn> assgn_1="<var> := {<var> var}" in start:
                 exists <assgn> assgn="{<var> var_0} := <rhs>" in start:
                   (before(assgn, assgn_1) and (= var var_0))''',
            LANG_GRAMMAR,
            {BEFORE_PREDICATE})

        self.assertEqual(expected, result)

    def test_xpath_infix_c_defuse(self):
        result = parse_isla(
            '''forall <id> in <expr>:
                 exists <declaration>:
                    <id> = <declaration>.<id>''',
            grammar=scriptsizec.SCRIPTSIZE_C_GRAMMAR,
            structural_predicates={BEFORE_PREDICATE, LEVEL_PREDICATE})

        expected = parse_isla('''
forall <expr> expr in start:
  forall <id> id in expr: (
    exists <declaration> declaration="int {<id> id_0} = <expr>;" in start:
       (= id id_0) or
    exists <declaration> declaration_0="int {<id> id_1};" in start:
       (= id id_1))''', structural_predicates={BEFORE_PREDICATE, LEVEL_PREDICATE})

        self.assertEqual(unparse_isla(expected), unparse_isla(result))

    def test_xpath_with_index(self):
        grammar = {
            '<start>': ['<A>'],
            '<A>': ['<B><B><B>', '<B><B><B>\n<A>'],
            '<B>': ['a', 'b']
        }

        result = parse_isla(r'<A>.<B>[2] = "a"', grammar)
        expected = parse_isla('''forall <A> A="<B>{<B> B}<B>" in start:
   (= B "a") and
forall <A> A_0="<B>{<B> B_0}<B>\n<A>" in start:
  (= B_0 "a"))''')
        self.assertEqual(expected, result)

    def test_infix_equation_xml(self):
        result = parse_isla(
            '<xml-tree>.<xml-open-tag>.<id> = <xml-tree>.<xml-close-tag>.<id>',
            grammar=XML_GRAMMAR_WITH_NAMESPACE_PREFIXES)

        expected = parse_isla('''
    forall <xml-tree> xml-tree="<{<id> id} <xml-attribute>><inner-xml-tree></{<id> id_0}>" in start:
        (= id id_0) and
    forall <xml-tree> xml-tree_0="<{<id> id_1}><inner-xml-tree></{<id> id_2}>" in start:
        (= id_1 id_2)''')

        self.assertEqual(unparse_isla(expected), unparse_isla(result))

    def test_prefix_multiple_args(self):
        result = parse_isla('forall <a>: exists <b>: str.contains(a, b)')
        expected = parse_isla('forall <a> a in start: exists <b> b in start: (str.contains a b)')
        self.assertEqual(expected, result)

    def test_prefix_no_args(self):
        result = parse_isla('str.in_re("17", re.all())')
        expected_string = '(str.in_re "17" re.all)'
        self.assertEqual(expected_string, unparse_isla(result))
        expected = parse_isla('(str.in_re "17" re.all)')
        self.assertEqual(expected, result)

    def test_modulo_infix(self):
        result = parse_isla('(= (str.to.int <pagesize>) mod 7 0)')
        expected = parse_isla('(= (mod (str.to.int <pagesize>) 7) 0)')
        self.assertEqual(expected, result)

    def test_length_prefixed_strings(self):
        PASCAL_STRING_GRAMMAR = {
            "<start>": ["<string>"],
            "<string>": ["<length><chars>"],
            "<length>": ["<high-byte><low-byte>"],
            "<high-byte>": ["<byte>"],
            "<low-byte>": ["<byte>"],
            "<byte>": crange('\x00', '\xff'),
            "<chars>": ["", "<char><chars>"],
            "<char>": list(string.printable),
        }

        result = parse_isla('''
str.to_code(<string>.<length>.<low-byte>) +
str.to_code(<string>.<length>.<high-byte>) * 256 =
str.len(<string>.<chars>)''', grammar=PASCAL_STRING_GRAMMAR)

        expected = parse_isla('''
forall <string> string="{<high-byte> high-byte}{<low-byte> low-byte}{<chars> chars}" in start:
  (= (* (+ (str.to_code low-byte) (str.to_code high-byte)) 256) (str.len chars))''')

        self.assertEqual(expected, result)

    def test_complex_expression_with_and(self):
        # Should parse w/o errors
        parse_isla('''
forall <number> number_1:
  forall <number> number_2:
    ((= (str.to.int number_2) (+ (str.to.int number_1) 1)) and (> (str.to.int number_1) 0))''')

    @pytest.mark.skip('Functionality yet to be implemented.')
    def test_xpath_syntax_twodot_axis_tar_checksum(self):
        result = parse_isla(
            'tar_checksum(<header>, <header>..<checksum>)',
            grammar=TAR_GRAMMAR,
            semantic_predicates={TAR_CHECKSUM_PREDICATE})

        expected = parse_isla('''
    forall <header> header in start:
      forall <checksum> checksum in header:
        tar_checksum(header, checksum)''', semantic_predicates={TAR_CHECKSUM_PREDICATE})

        # self.assertEqual(expected, result)
        unparsed_result = ISLaUnparser(result).unparse()
        unparsed_expected = ISLaUnparser(expected).unparse()
        self.assertEqual(unparsed_expected, unparsed_result)

    def test_bnf_syntax(self):
        result = parse_bnf(f'''
<start> ::= <stmt> 
<stmt> ::=   <assgn>
           | <assgn> " ; " <stmt> 
<assgn> ::= <var> " := " <rhs> 
<rhs> ::=   <var> 
          | <digit> 
<var> ::= {' | '.join(map(lambda c: f'"{c}"', string.ascii_lowercase))} 
<digit> ::= {' | '.join(map(lambda c: f'"{c}"', string.digits))}''')

        expected = {
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

        self.assertEqual(expected, result)

    def test_unparse_grammar(self):
        expected = f'''<start> ::= <stmt>
<stmt> ::= <assgn> | <assgn> " ; " <stmt>
<assgn> ::= <var> " := " <rhs>
<rhs> ::= <var> | <digit>
<var> ::= {' | '.join(map(lambda c: f'"{c}"', string.ascii_lowercase))}
<digit> ::= {' | '.join(map(lambda c: f'"{c}"', string.digits))}'''

        result = unparse_grammar({
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
        })

        self.assertEqual(expected, result)

    def test_simple_xml_descendant_axis(self):
        result = parse_isla(
            'forall <xml-open-tag> optag="<{<id> id}>" in start: id..<id-char> = "a"',
            grammar=XML_GRAMMAR)

        expected = parse_isla('''
forall <xml-open-tag> optag="<{<id> id}>" in start: 
  forall <id-char> id-char in id:
    id-char = "a" ''')

        self.assertEqual(unparse_isla(expected), unparse_isla(result))

    def test_simple_xml_descendant_axis_disjunction(self):
        result = parse_isla(
            'forall <xml-open-tag> optag="<{<id> id}>" in start: (id..<id-char> = "a" or id..<id-char> = "b")',
            grammar=XML_GRAMMAR)
        expected = parse_isla('''
forall <xml-open-tag> optag="<{<id> id}>" in start: 
  forall <id-char> id-char in id:
    (id-char = "a" or id-char = "b")''')
        self.assertEqual(expected, result)

    def test_xml_descendant_axis(self):
        result = parse_isla('<xml-open-tag>.<id>..<id-char> = "a"', grammar=XML_GRAMMAR)
        expected = parse_isla('''
forall <xml-open-tag> xml-open-tag="<{<id> id}>" in start: 
  forall <id-char> id-char in id:
    id-char = "a" and
forall <xml-open-tag> xml-open-tag_0="<{<id> id_0} <xml-attribute>>" in start:
  forall <id-char> id-char_0 in id_0:
    id-char_0 = "a"''')
        self.assertEqual(unparse_isla(expected), unparse_isla(result))


if __name__ == '__main__':
    unittest.main()
