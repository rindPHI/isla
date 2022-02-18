import string
import unittest
from typing import cast, Callable

import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import srange
from fuzzingbook.Parser import EarleyParser
from orderedset import OrderedSet

import isla.isla_shortcuts as sc
from isla import language
from isla.evaluator import evaluate, matches_for_quantified_formula
from isla.helpers import tree_to_string
from isla.isla_predicates import BEFORE_PREDICATE, LEVEL_PREDICATE, IN_TREE_PREDICATE, \
    SAME_POSITION_PREDICATE
from isla.isla_predicates import COUNT_PREDICATE
from isla.language import BoundVariable
from isla.language import Constant, Formula, BindExpression, \
    DerivationTree, VariableManager, \
    QuantifiedFormula, parse_isla
from isla_formalizations import rest, scriptsizec
from isla_formalizations.csv import CSV_GRAMMAR, CSV_HEADERBODY_GRAMMAR
from isla_formalizations.xml_lang import XML_GRAMMAR_WITH_NAMESPACE_PREFIXES, validate_xml, \
    xml_no_attr_redef_constraint, XML_GRAMMAR, XML_NAMESPACE_CONSTRAINT
from test_data import LANG_GRAMMAR, eval_lang


class TestEvaluator(unittest.TestCase):
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
        self.assertTrue(evaluate(formula(tree), tree, LANG_GRAMMAR))

        for valid_prog in [valid_prog_1, valid_prog_2]:
            tree = DerivationTree.from_parse_tree(next(parser.parse(valid_prog)))
            self.assertTrue(evaluate(formula(tree), tree, LANG_GRAMMAR).to_bool())

        for invalid_prog in [invalid_prog_1, invalid_prog_2, invalid_prog_3, invalid_prog_4]:
            tree = DerivationTree.from_parse_tree(next(parser.parse(invalid_prog)))
            self.assertFalse(evaluate(formula(tree), tree, LANG_GRAMMAR).to_bool())

    def test_evaluate_concrete_in_expr(self):
        parser = EarleyParser(LANG_GRAMMAR)

        prog = "x := 1 ; x := x"
        tree = DerivationTree.from_parse_tree(next(parser.parse(prog)))
        var = BoundVariable("$var", "<var>")

        formula = sc.forall(var, tree, sc.smt_for(cast(z3.BoolRef, var.to_smt() == z3.StringVal("x")), var))
        self.assertTrue(evaluate(formula, tree, LANG_GRAMMAR))
        formula = sc.forall(var, tree, sc.smt_for(cast(z3.BoolRef, var.to_smt() == z3.StringVal("y")), var))
        self.assertFalse(evaluate(formula, tree, LANG_GRAMMAR))

        formula = sc.exists(var, tree, sc.smt_for(cast(z3.BoolRef, var.to_smt() == z3.StringVal("x")), var))
        self.assertTrue(evaluate(formula, tree, LANG_GRAMMAR))
        formula = sc.exists(var, tree, sc.smt_for(cast(z3.BoolRef, var.to_smt() == z3.StringVal("y")), var))
        self.assertFalse(evaluate(formula, tree, LANG_GRAMMAR))

    def test_match(self):
        parser = EarleyParser(LANG_GRAMMAR)

        # lhs = BoundVariable("$lhs", "<var>")
        # rhs = BoundVariable("$rhs", "<var>")
        #
        # bind_expr = lhs + " := " + rhs
        # tree = DerivationTree.from_parse_tree(next(parser.parse("x := y")))
        #
        # match = bind_expr.match(tree, LANG_GRAMMAR)
        # self.assertEqual(('<var>', [('x', [])]), match[lhs][1].to_parse_tree())
        # self.assertEqual(('<var>', [('y', [])]), match[rhs][1].to_parse_tree())

        assgn_1 = BoundVariable("$assgn_1", "<assgn>")
        assgn_2 = BoundVariable("$assgn_2", "<assgn>")
        stmt = BoundVariable("$stmt", "<stmt>")

        bind_expr = assgn_1 + " ; " + assgn_2 + " ; " + stmt
        tree = DerivationTree.from_parse_tree(next(parser.parse("x := y ; x := x ; y := z ; z := z"))[1][0])

        match = dict(bind_expr.match(tree, LANG_GRAMMAR))
        self.assertEqual("x := y", str(match[assgn_1][1]))
        self.assertEqual("x := x", str(match[assgn_2][1]))
        self.assertEqual("y := z ; z := z", str(match[stmt][1]))

        # The stmt variable matches the whole remaining program; assgn2 can no longer be matched
        bind_expr = assgn_1 + " ; " + stmt + " ; " + assgn_2
        match = bind_expr.match(tree, LANG_GRAMMAR)
        self.assertFalse(match)

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
            if evaluate(formula(tree), tree, LANG_GRAMMAR):
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

    def test_matches_xml_property(self):
        inp = "<b>k</b>"
        tree = DerivationTree.from_parse_tree(list(EarleyParser(XML_GRAMMAR).parse(inp))[0])

        mgr = VariableManager(XML_GRAMMAR)
        start = mgr.const("$start", "<start>")
        formula: QuantifiedFormula = cast(QuantifiedFormula, mgr.create(sc.forall_bind(
            sc.bexpr("<") + mgr.bv("$oid", "<id>") + ">" +
            "<inner-xml-tree>" +
            "</" + mgr.bv("$cid", "<id>") + ">",
            "<xml-tree>",
            start,
            mgr.smt(mgr.bv("$oid").to_smt() == mgr.bv("$cid").to_smt())
        )))

        matches = matches_for_quantified_formula(formula, XML_GRAMMAR, tree, {start: tree})
        self.assertEqual(1, len(matches))

    def test_match_scriptsize_c(self):
        in_inst = DerivationTree('<start>', (
            DerivationTree('<statement>', (
                DerivationTree('<block>', (
                    DerivationTree('{', (), id=44),
                    DerivationTree('<statements>', (
                        DerivationTree('<block_statement>', (
                            DerivationTree('<statement>', (
                                DerivationTree('if', (), id=438),
                                DerivationTree('<paren_expr>', (
                                    DerivationTree('(', (), id=1183),
                                    DerivationTree('<expr>', (
                                        DerivationTree('<id>', None, id=2220),
                                        DerivationTree(' = ', (), id=2221),
                                        DerivationTree('<expr>', (
                                            DerivationTree('<test>', (
                                                DerivationTree('<sum>', (
                                                    DerivationTree('<term>', (
                                                        DerivationTree('<id>', None, id=41940),), id=41938),
                                                ), id=41931),), id=40917),), id=2222)), id=1184),
                                    DerivationTree(')', (), id=1185)), id=439),
                                DerivationTree(' ', (), id=440),
                                DerivationTree('<statement>', (DerivationTree(';', (), id=1208),), id=441),
                                DerivationTree(' else ', (), id=442),
                                DerivationTree('<statement>', (
                                    DerivationTree('<block>', (
                                        DerivationTree('{', (), id=2224),
                                        DerivationTree('<statements>', (), id=2225),
                                        DerivationTree('}', (), id=2226)
                                    ), id=1209),), id=443)), id=436),), id=52),
                        DerivationTree('<statements>', (
                            DerivationTree('<block_statement>', (
                                DerivationTree('<declaration>', (
                                    DerivationTree('int ', (), id=0),
                                    DerivationTree('<id>', None, id=1),
                                    DerivationTree(';', (), id=2)
                                ), id=3),), id=106),
                            DerivationTree('<statements>', None, id=103)), id=49)), id=50),
                    DerivationTree('}', (), id=46)), id=47),), id=43),), id=132)

        formula = language.ExistsFormula(
            BoundVariable("decl", "<declaration>"),
            in_inst,
            language.ConjunctiveFormula(
                language.ConjunctiveFormula(
                    language.StructuralPredicateFormula(
                        LEVEL_PREDICATE,
                        "GE",
                        "<block>",
                        BoundVariable("decl", "<declaration>"),
                        in_inst.get_subtree(in_inst.find_node(2222))
                    ),
                    language.StructuralPredicateFormula(
                        BEFORE_PREDICATE,
                        BoundVariable("decl", "<declaration>"),
                        in_inst.get_subtree(in_inst.find_node(2222))
                    )),
                language.SMTFormula(
                    Constant("use_id", "<id>").to_smt() == BoundVariable("def_id", "<id>").to_smt(),
                    BoundVariable("def_id", "<id>"),
                    instantiated_variables=OrderedSet([BoundVariable("use_id", "<id>")]),
                    substitutions={Constant("use_id", "<id>"): in_inst.get_subtree(in_inst.find_node(41940))})),
            BindExpression(
                "int ",
                BoundVariable("def_id", "<id>"),
                [" = ", "<expr>"],
                ";"))

        assignments = matches_for_quantified_formula(
            cast(language.QuantifiedFormula, formula),
            scriptsizec.SCRIPTSIZE_C_GRAMMAR,
            in_inst,
            {})

        self.assertTrue(all(
            in_inst.is_valid_path(path) and
            in_inst.find_node(tree) and
            in_inst.get_subtree(path) == tree
            for assignment in assignments
            for path, tree in assignment.values()))

    def test_xml_property(self):
        mgr = VariableManager(XML_GRAMMAR)
        start = mgr.const("$start", "<start>")
        formula: Formula = mgr.create(sc.forall_bind(
            sc.bexpr("<") + mgr.bv("$oid", "<id>") + ">" +
            "<inner-xml-tree>" +
            "</" + mgr.bv("$cid", "<id>") + ">",
            "<xml-tree>",
            start,
            mgr.smt(mgr.bv("$oid").to_smt() == mgr.bv("$cid").to_smt())
        ))

        correct_tree = DerivationTree.from_parse_tree(list(EarleyParser(XML_GRAMMAR).parse("<b>k</b>"))[0])
        wrong_tree = DerivationTree.from_parse_tree(
            list(EarleyParser(XML_GRAMMAR).parse("<a>asdf</r>"))[0])

        self.assertTrue(evaluate(formula.substitute_expressions({start: correct_tree}), correct_tree, XML_GRAMMAR))
        self.assertFalse(evaluate(formula.substitute_expressions({start: wrong_tree}), wrong_tree, XML_GRAMMAR))

    def test_xml_with_prefixes(self):
        inp = '<a xmlns:ns="salami"><ns:asdf>asdf</ns:asdf></a>'
        tree = language.DerivationTree.from_parse_tree(
            list(EarleyParser(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES).parse(inp))[0])
        assert validate_xml(tree)

        self.assertTrue(evaluate(
            XML_NAMESPACE_CONSTRAINT.substitute_expressions({Constant("start", "<start>"): tree}),
            grammar=XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
            reference_tree=tree,
            structural_predicates={IN_TREE_PREDICATE}))

        inp = '<a xmlns:ns="salami" xmlns:ns1="toast"><ns:asdf ns1:asdf="asdf">asdf</ns:asdf></a>'
        tree = language.DerivationTree.from_parse_tree(
            list(EarleyParser(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES).parse(inp))[0])
        assert validate_xml(tree)

        self.assertTrue(evaluate(
            XML_NAMESPACE_CONSTRAINT.substitute_expressions({Constant("start", "<start>"): tree}),
            grammar=XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
            reference_tree=tree,
            structural_predicates={IN_TREE_PREDICATE}))

        inp = '<a xmlns:ons="salami"><ns:asdf>asdf</ns:asdf></a>'
        tree = language.DerivationTree.from_parse_tree(
            list(EarleyParser(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES).parse(inp))[0])
        assert not validate_xml(tree)

        self.assertFalse(evaluate(
            XML_NAMESPACE_CONSTRAINT.substitute_expressions({Constant("start", "<start>"): tree}),
            grammar=XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
            reference_tree=tree,
            structural_predicates={IN_TREE_PREDICATE}))

        inp = '<xmlns:S47 s1="mr"/>'
        tree = language.DerivationTree.from_parse_tree(
            list(EarleyParser(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES).parse(inp))[0])
        assert not validate_xml(tree)

        self.assertFalse(evaluate(
            XML_NAMESPACE_CONSTRAINT.substitute_expressions({Constant("start", "<start>"): tree}),
            grammar=XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
            reference_tree=tree,
            structural_predicates={IN_TREE_PREDICATE}))

    def test_xml_attr_redefs(self):
        inp = '<a b="..." c="...">asdf</a>'
        tree = language.DerivationTree.from_parse_tree(
            list(EarleyParser(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES).parse(inp))[0])
        assert validate_xml(tree)

        self.assertTrue(evaluate(
            xml_no_attr_redef_constraint,
            grammar=XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
            reference_tree=tree,
            structural_predicates={
                IN_TREE_PREDICATE,
                SAME_POSITION_PREDICATE}))

        inp = '<a b="..." b="...">asdf</a>'
        tree = language.DerivationTree.from_parse_tree(
            list(EarleyParser(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES).parse(inp))[0])
        assert not validate_xml(tree)

        self.assertFalse(evaluate(
            xml_no_attr_redef_constraint,
            grammar=XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
            reference_tree=tree,
            structural_predicates={
                IN_TREE_PREDICATE,
                SAME_POSITION_PREDICATE}))

        inp = '<x xmlns:ns="..."><a ns:b="..." ns:c="..."/></x>'
        tree = language.DerivationTree.from_parse_tree(
            list(EarleyParser(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES).parse(inp))[0])
        assert validate_xml(tree)

        self.assertTrue(evaluate(
            xml_no_attr_redef_constraint,
            grammar=XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
            reference_tree=tree,
            structural_predicates={
                IN_TREE_PREDICATE,
                SAME_POSITION_PREDICATE}))

        inp = '<x xmlns:ns="..."><a ns:b="..." ns:b="..."/></x>'
        tree = language.DerivationTree.from_parse_tree(
            list(EarleyParser(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES).parse(inp))[0])
        assert not validate_xml(tree)

        self.assertFalse(evaluate(
            xml_no_attr_redef_constraint,
            grammar=XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
            reference_tree=tree,
            structural_predicates={
                IN_TREE_PREDICATE,
                SAME_POSITION_PREDICATE}))

    def test_csv_property(self):
        property = """
forall <csv-header> hline in start:
  exists int colno:
    ((>= (str.to.int colno) 3) and 
    ((<= (str.to.int colno) 5) and 
     (count(hline, "<raw-field>", colno) and 
     forall <csv-record> line in start:
       count(line, "<raw-field>", colno))))
"""
        valid_test_input = """a;b;c
XYZ;\" asdf \";ABC
123;!@#$;\"456 \n 789\"\n"""

        self.assertTrue(evaluate(
            property,
            reference_tree=DerivationTree.from_parse_tree(list(EarleyParser(CSV_GRAMMAR).parse(valid_test_input))[0]),
            semantic_predicates={COUNT_PREDICATE},
            grammar=CSV_GRAMMAR
        ))

        invalid_test_input = """a;b;c
XYZ;\" asdf \"
123;!@#$;\"456 \n 789\"\n"""

        self.assertFalse(evaluate(
            property,
            reference_tree=DerivationTree.from_parse_tree(list(EarleyParser(CSV_GRAMMAR).parse(invalid_test_input))[0]),
            semantic_predicates={COUNT_PREDICATE},
            grammar=CSV_GRAMMAR
        ))

    def test_more_complex_csv_property(self):
        str_property = """
exists int colno_1:
  forall <csv-header> hline in start:
    (count(hline, "<raw-field>", colno_1) and 
      forall int colno_2:
        forall <csv-record> line in start:
          (count(line, "<raw-field>", colno_2) implies
           (= colno_1 colno_2)))"""
        property = parse_isla(str_property, CSV_GRAMMAR, semantic_predicates={COUNT_PREDICATE})
        negated_property = -property

        valid_test_input = """a;b;c
    XYZ;\" asdf \";ABC
    123;!@#$;\"456 \n 789\"\n"""

        self.assertTrue(evaluate(
            property,
            reference_tree=DerivationTree.from_parse_tree(list(EarleyParser(CSV_GRAMMAR).parse(valid_test_input))[0]),
            semantic_predicates={COUNT_PREDICATE},
            grammar=CSV_GRAMMAR
        ))

        self.assertFalse(evaluate(
            negated_property,
            reference_tree=DerivationTree.from_parse_tree(list(EarleyParser(CSV_GRAMMAR).parse(valid_test_input))[0]),
            semantic_predicates={COUNT_PREDICATE},
            grammar=CSV_GRAMMAR
        ))

        invalid_test_input = """a;b;c
    XYZ;\" asdf \"
    123;!@#$;\"456 \n 789\"\n"""

        self.assertTrue(evaluate(
            negated_property,
            reference_tree=DerivationTree.from_parse_tree(list(EarleyParser(CSV_GRAMMAR).parse(invalid_test_input))[0]),
            semantic_predicates={COUNT_PREDICATE},
            grammar=CSV_GRAMMAR
        ))

        self.assertFalse(evaluate(
            property,
            reference_tree=DerivationTree.from_parse_tree(list(EarleyParser(CSV_GRAMMAR).parse(invalid_test_input))[0]),
            semantic_predicates={COUNT_PREDICATE},
            grammar=CSV_GRAMMAR
        ))

    def test_negated_csv_property(self):
        tree = ('<start>', [
            ('<csv-file>', [
                ('<csv-header>', [
                    ('<csv-record>', [
                        ('<csv-string-list>', [
                            ('<raw-field>', [
                                ('<quoted-field>', [
                                    ('"', []),
                                    ('<escaped-field>', [
                                        ('<escaped-character-1>', [
                                            ('<escaped-character>', [('i', [])]),
                                            ('<escaped-character-1>', [('', [])])])]),
                                    ('"', [])])])]),
                        ('\n', [])])]),
                ('<csv-body>', [
                    ('<csv-record-1>', [
                        ('<csv-record>', [
                            ('<csv-string-list>', [
                                ('<raw-field>', [
                                    ('<simple-field>', [
                                        ('<spaces-1>', [
                                            ('<spaces>', [(' ', []), ('<spaces>', [(' ', [])])])]),
                                        ('<simple-character-1>', [('', [])]),
                                        ('<spaces-2>', [('', [])])])]),
                                (';', []),
                                ('<csv-string-list>', [
                                    ('<raw-field>', [
                                        ('<simple-field>', [
                                            ('<spaces-1>', [('', [])]),
                                            ('<simple-character-1>', [
                                                ('<simple-character>', [('P', [])]),
                                                ('<simple-character-1>', [('', [])])]),
                                            ('<spaces-2>', [('<spaces>', [(' ', [])])])])])])]),
                            ('\n', [])]),
                        ('<csv-record-1>', [('', [])])])])])])

        property = """
forall <csv-header> header in start:
  forall <csv-body> body in start:
    forall <csv-record> hline in header:
      exists int colno_1:
        ((>= (str.to.int colno_1) 3) and 
         (<= (str.to.int colno_1) 5) and
         count(hline, "<raw-field>", colno_1) and 
         forall <csv-record> line in body:
           forall int colno_2:
             ((= colno_1 colno_2) implies
              count(line, "<raw-field>", colno_2)))"""

        negated_property = -parse_isla(property, CSV_HEADERBODY_GRAMMAR, semantic_predicates={COUNT_PREDICATE})

        self.assertTrue(evaluate(
            negated_property,
            reference_tree=DerivationTree.from_parse_tree(tree),
            semantic_predicates={COUNT_PREDICATE},
            grammar=CSV_HEADERBODY_GRAMMAR
        ))

        self.assertFalse(evaluate(
            property,
            reference_tree=DerivationTree.from_parse_tree(tree),
            semantic_predicates={COUNT_PREDICATE},
            grammar=CSV_HEADERBODY_GRAMMAR
        ))

    def test_rest_property_1(self):
        tree = DerivationTree.from_parse_tree(list(EarleyParser(rest.REST_GRAMMAR).parse("0\n-\n\n"))[0])
        self.assertTrue(evaluate(rest.LENGTH_UNDERLINE, tree, rest.REST_GRAMMAR))

    def test_rest_property_2(self):
        formula = rest.LENGTH_UNDERLINE

        inp = "123\n--\n"
        tree = DerivationTree.from_parse_tree(list(EarleyParser(rest.REST_GRAMMAR).parse(inp))[0])
        self.assertTrue(tree.filter(lambda n: n.value == "<section-title>"))
        self.assertFalse(evaluate(
            formula.substitute_expressions({Constant("start", "<start>"): tree}), tree, rest.REST_GRAMMAR))

        inp = "00\n--------\n"
        tree = DerivationTree.from_parse_tree(list(EarleyParser(rest.REST_GRAMMAR).parse(inp))[0])
        self.assertTrue(tree.filter(lambda n: n.value == "<section-title>"))
        self.assertTrue(evaluate(
            formula.substitute_expressions({Constant("start", "<start>"): tree}), tree, rest.REST_GRAMMAR))

    def test_def_before_use(self):
        tree = DerivationTree.from_parse_tree(
            list(EarleyParser(LANG_GRAMMAR).parse("c := 6 ; x := c ; c := c ; c := c ; c := 9 ; x := c"))[0])
        formula = """
forall <assgn> assgn_1="{<var> lhs_1} := {<rhs> rhs_1}" in start:
  forall <var> var in rhs_1:
    exists <assgn> assgn_2="{<var> lhs_2} := {<rhs> rhs_2}" in start:
      (before(assgn_2, assgn_1) and (= lhs_2 var))
"""
        self.assertTrue(evaluate(formula, tree, structural_predicates={BEFORE_PREDICATE}, grammar=LANG_GRAMMAR))

    def test_scriptsize_c_defuse_property(self):
        constr = """
forall <expr> expr in start:
  forall <id> use_id in expr:
    exists <declaration> decl="int {<id> def_id}[ = <expr>];" in start:
      (level("GE", "<block>", decl, expr) and 
      (before(decl, expr) and 
      (= use_id def_id)))
"""
        inp = "{int c;c;}"
        tree = DerivationTree.from_parse_tree(list(EarleyParser(scriptsizec.SCRIPTSIZE_C_GRAMMAR).parse(inp))[0])
        self.assertTrue(evaluate(
            constr, tree, scriptsizec.SCRIPTSIZE_C_GRAMMAR, structural_predicates={BEFORE_PREDICATE, LEVEL_PREDICATE}))

        inp = "{int c;{c;}}"
        tree = DerivationTree.from_parse_tree(list(EarleyParser(scriptsizec.SCRIPTSIZE_C_GRAMMAR).parse(inp))[0])
        self.assertTrue(evaluate(
            constr, tree, scriptsizec.SCRIPTSIZE_C_GRAMMAR, structural_predicates={BEFORE_PREDICATE, LEVEL_PREDICATE}))

        inp = "{int c = 17;c;}"
        tree = DerivationTree.from_parse_tree(list(EarleyParser(scriptsizec.SCRIPTSIZE_C_GRAMMAR).parse(inp))[0])
        self.assertTrue(evaluate(
            constr, tree, scriptsizec.SCRIPTSIZE_C_GRAMMAR, structural_predicates={BEFORE_PREDICATE, LEVEL_PREDICATE}))

        inp = "{int c = 17;{c;}}"
        tree = DerivationTree.from_parse_tree(list(EarleyParser(scriptsizec.SCRIPTSIZE_C_GRAMMAR).parse(inp))[0])
        self.assertTrue(evaluate(
            constr, tree, scriptsizec.SCRIPTSIZE_C_GRAMMAR, structural_predicates={BEFORE_PREDICATE, LEVEL_PREDICATE}))

        inp = "{{int c;}c;}"
        tree = DerivationTree.from_parse_tree(list(EarleyParser(scriptsizec.SCRIPTSIZE_C_GRAMMAR).parse(inp))[0])
        self.assertFalse(evaluate(
            constr, tree, scriptsizec.SCRIPTSIZE_C_GRAMMAR, structural_predicates={BEFORE_PREDICATE, LEVEL_PREDICATE}))

        inp = "{{int c;}{c;}}"
        tree = DerivationTree.from_parse_tree(list(EarleyParser(scriptsizec.SCRIPTSIZE_C_GRAMMAR).parse(inp))[0])
        self.assertFalse(evaluate(
            constr, tree, scriptsizec.SCRIPTSIZE_C_GRAMMAR, structural_predicates={BEFORE_PREDICATE, LEVEL_PREDICATE}))

    def test_evaluate_with_preconditions(self):
        tree = DerivationTree('<start>', (DerivationTree('<csv-file>', (
            DerivationTree('<csv-header>', (DerivationTree('<csv-record>', None, id=592),), id=595),
            DerivationTree('<csv-record-1>', None, id=593)), id=596),), id=591)

        colno_0 = Constant("colno_0", "NUM")

        precondition_one = language.SemanticPredicateFormula(
            COUNT_PREDICATE,
            tree.get_subtree(tree.find_node(592)),
            '<raw-field>',
            colno_0)

        precondition_two = language.ExistsFormula(
            BoundVariable("record", "<csv-record>"),
            tree,
            -language.SemanticPredicateFormula(
                COUNT_PREDICATE,
                BoundVariable("record", "<csv-record>"),
                '<raw-field>',
                colno_0))

        to_prove_1 = language.ExistsIntFormula(
            BoundVariable("colno", "NUM"),
            language.ExistsFormula(
                BoundVariable("record_0", "<csv-record>"),
                tree,
                language.SemanticPredicateFormula(
                    COUNT_PREDICATE,
                    BoundVariable("record_0", "<csv-record>"),
                    '<raw-field>',
                    BoundVariable("colno", "NUM"))))

        self.assertTrue(evaluate(to_prove_1, tree, CSV_GRAMMAR, assumptions={precondition_one, precondition_two}))

        to_prove_2 = language.ExistsIntFormula(
            BoundVariable("colno", "NUM"),
            language.ExistsFormula(
                BoundVariable("record", "<csv-record>"),
                tree,
                -language.SemanticPredicateFormula(
                    COUNT_PREDICATE,
                    BoundVariable("record", "<csv-record>"),
                    '<raw-field>',
                    BoundVariable("colno", "NUM"))))

        self.assertTrue(evaluate(to_prove_2, tree, CSV_GRAMMAR, assumptions={precondition_one, precondition_two}))

        to_prove_3 = language.ExistsIntFormula(
            BoundVariable("colno", "NUM"),
            language.ExistsFormula(
                BoundVariable("record_0", "<csv-record>"),
                tree,
                language.SemanticPredicateFormula(
                    COUNT_PREDICATE,
                    BoundVariable("record_0", "<csv-record>"),
                    '<raw-field>',
                    BoundVariable("colno", "NUM"))) &
            language.ExistsFormula(
                BoundVariable("record", "<csv-record>"),
                tree,
                -language.SemanticPredicateFormula(
                    COUNT_PREDICATE,
                    BoundVariable("record", "<csv-record>"),
                    '<raw-field>',
                    BoundVariable("colno", "NUM"))))

        self.assertTrue(evaluate(to_prove_3, tree, CSV_GRAMMAR, assumptions={precondition_one, precondition_two}))

    def test_evaluate_negative_square_root(self):
        # TODO: Add corresponding solver test
        property = """
        forall <arith_expr> container in start:
          exists <number> elem in container:
            (<= (str.to.int elem) (str.to.int "-1")))"""

        grammar = {
            "<start>": ["<arith_expr>"],
            "<arith_expr>": ["<function>(<number>)"],
            "<function>": ["sqrt", "sin", "cos", "tan"],
            "<number>": ["<maybe_minus><onenine><maybe_digits><maybe_frac>"],
            "<maybe_minus>": ["", "-"],
            "<onenine>": [str(num) for num in range(1, 10)],
            "<digit>": srange(string.digits),
            "<maybe_digits>": ["", "<digits>"],
            "<digits>": ["<digit>", "<digit><digits>"],
            "<maybe_frac>": ["", ".<digits>"]
        }

        inp = DerivationTree.from_parse_tree(next(EarleyParser(grammar).parse("sqrt(-2)")))
        self.assertTrue(evaluate(property, inp, grammar))

        inp = DerivationTree.from_parse_tree(next(EarleyParser(grammar).parse("sqrt(2)")))
        self.assertFalse(evaluate(property, inp, grammar))

        inp = DerivationTree.from_parse_tree(next(EarleyParser(grammar).parse("sqrt(-2.0)")))
        self.assertTrue(evaluate(property, inp, grammar))


if __name__ == '__main__':
    unittest.main()
