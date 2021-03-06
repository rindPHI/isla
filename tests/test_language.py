import copy
import random
import unittest

import pytest
import z3
from grammar_graph import gg

import isla.isla_shortcuts as sc
from isla import language
from isla.evaluator import well_formed
from isla.fuzzer import GrammarCoverageFuzzer
from isla.helpers import delete_unreachable
from isla.isla_predicates import BEFORE_PREDICATE, LEVEL_PREDICATE, SAME_POSITION_PREDICATE
from isla.isla_predicates import count, COUNT_PREDICATE
from isla.language import Constant, BoundVariable, Formula, BindExpression, \
    convert_to_dnf, ensure_unique_bound_variables, VariableManager, \
    DummyVariable, parse_isla, ISLaUnparser, SMTFormula
from isla.derivation_tree import DerivationTree
from isla.parser import EarleyParser
from isla.z3_helpers import z3_eq
from isla_formalizations import rest, scriptsizec, tar
from isla_formalizations.csv import CSV_GRAMMAR, CSV_COLNO_PROPERTY
from isla_formalizations.scriptsizec import SCRIPTSIZE_C_DEF_USE_CONSTR_TEXT, SCRIPTSIZE_C_NO_REDEF_TEXT
from isla_formalizations.xml_lang import XML_GRAMMAR, XML_GRAMMAR_WITH_NAMESPACE_PREFIXES
from test_data import LANG_GRAMMAR


def path_to_string(p) -> str:
    return " ".join([f'"{n.symbol}" ({n.id})' if isinstance(n, gg.TerminalNode) else n.symbol for n in p])


class TestLanguage(unittest.TestCase):
    def test_wellformed(self):
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
                    sc.smt_for(z3_eq(lhs_2.to_smt(), var.to_smt()), lhs_2, var)
                )
            )
        )

        self.assertTrue(well_formed(formula, LANG_GRAMMAR)[0])

        bad_formula: Formula = sc.forall_bind(
            lhs_1 + " := " + rhs_1,
            assgn_1,
            prog,
            sc.exists_bind(
                lhs_2 + " := " + rhs_2,
                assgn_2,
                prog,
                sc.before(assgn_2, assgn_1) &
                sc.smt_for(z3_eq(lhs_2.to_smt(), var.to_smt()), lhs_2, var)
            )
        )

        self.assertFalse(well_formed(bad_formula, LANG_GRAMMAR)[0])

        bad_formula_2: Formula = sc.forall(
            assgn_1,
            assgn_1,
            sc.smt_for(z3.BoolVal(True))
        )

        self.assertFalse(well_formed(bad_formula_2, LANG_GRAMMAR)[0])
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

        self.assertFalse(well_formed(bad_formula_3, LANG_GRAMMAR)[0])

        self.assertTrue(well_formed(-formula, LANG_GRAMMAR)[0])
        self.assertFalse(well_formed(-bad_formula, LANG_GRAMMAR)[0])
        self.assertFalse(well_formed(-bad_formula_2, LANG_GRAMMAR)[0])
        self.assertFalse(well_formed(-bad_formula_3, LANG_GRAMMAR)[0])

        self.assertFalse(well_formed(formula & bad_formula, LANG_GRAMMAR)[0])
        self.assertFalse(well_formed(formula | bad_formula, LANG_GRAMMAR)[0])

        bad_formula_4: Formula = sc.forall(
            assgn_1,
            prog,
            sc.SMTFormula(z3_eq(prog.to_smt(), z3.StringVal("")), prog)
        )

        self.assertFalse(well_formed(bad_formula_4, LANG_GRAMMAR)[0])

        bad_formula_5: Formula = sc.forall(
            assgn_1,
            prog,
            sc.SMTFormula(z3_eq(assgn_1.to_smt(), z3.StringVal("")), assgn_1) &
            sc.forall(
                var,
                assgn_1,
                sc.SMTFormula(z3.BoolVal(True))
            )
        )

        self.assertFalse(well_formed(bad_formula_5, LANG_GRAMMAR)[0])

        bad_formula_6: Formula = sc.forall(
            assgn_1,
            prog,
            sc.SMTFormula(z3_eq(prog.to_smt(), z3.StringVal("x := x")), prog)
        )

        self.assertFalse(well_formed(bad_formula_6, LANG_GRAMMAR)[0])

        bad_formula_7: Formula = sc.forall(
            assgn_1,
            prog,
            sc.forall(
                assgn_2,
                assgn_1,
                sc.SMTFormula(z3_eq(assgn_1.to_smt(), z3.StringVal("x := x")), assgn_1)
            )
        )

        self.assertFalse(well_formed(bad_formula_7, LANG_GRAMMAR)[0])

    def test_equality_hash_smt_formulas(self):
        elem = BoundVariable("elem", "<digits>")

        f_1 = SMTFormula(z3.StrToInt(elem.to_smt()) <= z3.StrToInt(z3.StringVal("092")), elem)
        f_2 = SMTFormula(z3.StrToInt(elem.to_smt()) <= z3.StrToInt(z3.StringVal("92")), elem)

        self.assertNotEqual(hash(f_1), hash(f_2))
        self.assertNotEqual(f_1, f_2)

    def test_bind_expression_to_tree(self):
        lhs = BoundVariable("$lhs", "<var>")
        rhs = BoundVariable("$rhs", "<rhs>")
        assgn = BoundVariable("$assgn", "<assgn>")

        bind_expr: BindExpression = lhs + " := " + rhs
        tree, bindings = bind_expr.to_tree_prefix(assgn.n_type, LANG_GRAMMAR)[0]
        self.assertEqual("<var> := <rhs>", str(tree))
        self.assertEqual((0,), bindings[lhs])
        self.assertEqual((2,), bindings[rhs])

        prog = BoundVariable("$prog ", "<stmt>")
        lhs_2 = BoundVariable("$lhs_2 ", "<var>")
        rhs_2 = BoundVariable("$rhs_2", "<rhs>")
        semicolon = BoundVariable("$semi", " ; ")

        bind_expr: BindExpression = lhs + " := " + rhs + semicolon + lhs_2 + " := " + rhs_2
        tree, bindings = bind_expr.to_tree_prefix(prog.n_type, LANG_GRAMMAR)[0]
        self.assertEqual("<var> := <rhs> ; <var> := <rhs>", str(tree))

        self.assertEqual((1,), bindings[semicolon])
        self.assertEqual((0, 0), bindings[lhs])
        self.assertEqual((0, 2), bindings[rhs])
        self.assertEqual((2, 0, 0), bindings[lhs_2])
        self.assertEqual((2, 0, 2), bindings[rhs_2])

    def test_dnf_conversion(self):
        a = Constant("$a", "<var>")
        pred = language.StructuralPredicate("pred", 1, lambda arg: True)
        w = language.StructuralPredicateFormula(pred, "w")
        x = language.StructuralPredicateFormula(pred, "x")
        y = language.StructuralPredicateFormula(pred, "y")
        z = language.StructuralPredicateFormula(pred, "z")

        formula = (w | x) & (y | z)
        self.assertEqual((w & y) | (w & z) | (x & y) | (x & z), convert_to_dnf(formula))

        formula = w & (y | z)
        self.assertEqual((w & y) | (w & z), convert_to_dnf(formula))

        formula = w & (x | y | z)
        self.assertEqual((w & x) | (w & y) | (w & z), convert_to_dnf(formula))

    def test_push_in_negation(self):
        a = Constant("$a", "<var>")
        w = sc.smt_for(z3_eq(a.to_smt(), z3.StringVal("1")), a)
        x = sc.smt_for(z3_eq(a.to_smt(), z3.StringVal("2")), a)
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
                sc.smt_for(z3_eq(var_1.to_smt(), z3.StringVal("x")), var_1)) & \
            sc.forall_bind(
                var_1 + " := " + rhs_1,
                assgn, start,
                sc.smt_for(z3_eq(var_1.to_smt(), z3.StringVal("y")), var_1))

        rhs_1_0 = BoundVariable("$rhs_1_0", "<rhs>")
        var_1_0 = BoundVariable("$var1_0", "<var>")

        DummyVariable.cnt = 0
        expected = \
            sc.forall_bind(
                BindExpression(var_1),
                rhs_1, start,
                sc.smt_for(z3_eq(var_1.to_smt(), z3.StringVal("x")), var_1)) & \
            sc.forall_bind(
                var_1_0 + " := " + rhs_1_0,
                assgn, start,
                sc.smt_for(z3_eq(var_1_0.to_smt(), z3.StringVal("y")), var_1_0))

        self.assertEqual(expected, ensure_unique_bound_variables(formula))
        self.assertEqual(expected, ensure_unique_bound_variables(expected))

    def test_count(self):
        # prog = "x := 1 ; x := 1 ; x := 1"
        # tree = DerivationTree.from_parse_tree(parse(prog, LANG_GRAMMAR))
        #
        # result = count(LANG_GRAMMAR, tree, "<assgn>", Constant("n", "NUM"))
        # self.assertEqual("{n: 3}", str(result))
        #
        # result = count(LANG_GRAMMAR, tree, "<assgn>", DerivationTree("3", None))
        # self.assertEqual(SemPredEvalResult(True), result)
        #
        # result = count(LANG_GRAMMAR, tree, "<assgn>", DerivationTree("4", None))
        # self.assertEqual(SemPredEvalResult(False), result)

        tree = DerivationTree("<start>", [DerivationTree("<stmt>", None)])
        result = count(gg.GrammarGraph.from_grammar(LANG_GRAMMAR), tree, "<assgn>", DerivationTree("4", None))
        self.assertEqual("{<stmt>: <assgn> ; <assgn> ; <assgn> ; <assgn>}", str(result))
        #
        # result = count(LANG_GRAMMAR, tree, "<start>", DerivationTree("2", None))
        # self.assertEqual(SemPredEvalResult(False), result)

    def test_to_tree_prefix_tar_file_name(self):
        mgr = VariableManager(tar.TAR_GRAMMAR)
        bind_expression = mgr.bv("$file_name_str", "<file_name_str>") + "<maybe_nuls>"
        self.assertEqual(
            ('<file_name>', [('<file_name_str>', None), ('<maybe_nuls>', None)]),
            bind_expression.to_tree_prefix("<file_name>", tar.TAR_GRAMMAR)[0][0].to_parse_tree())

    def test_to_tree_prefix_rest_ref(self):
        mexpr = BindExpression(
            BoundVariable("label", "<label>"),
            DummyVariable("\n\n"),
            DummyVariable("<paragraph>"))
        tree_prefix = mexpr.to_tree_prefix('<labeled_paragraph>', rest.REST_GRAMMAR)
        self.assertTrue(tree_prefix)

    def test_to_tree_prefix_rest_ref_2(self):
        mexpr = BindExpression(
            DummyVariable(".. _"),
            BoundVariable("def_id", "<id>"),
            DummyVariable(":\n\n"),
            DummyVariable("<paragraph>"))
        in_nonterminal = "<labeled_paragraph>"

        result = mexpr.to_tree_prefix(in_nonterminal, rest.REST_GRAMMAR)
        self.assertEqual(1, len(result))
        tree_prefix, bind_paths = result[0]
        self.assertEqual(".. _<id>:\n\n<paragraph>", str(tree_prefix))

    @pytest.mark.skip(reason="This works when run alone, but somehow not in the test suite.")
    def test_bind_epxr_to_tree_prefix_recursive_nonterminal(self):
        bind_expression = BindExpression("<xml-attribute> <xml-attribute>")

        self.assertTrue(
            DerivationTree(
                "<xml-attribute>", [
                    DerivationTree("<xml-attribute>", None),
                    DerivationTree(" ", ()),
                    DerivationTree("<xml-attribute>", None)]).structurally_equal(
                bind_expression.to_tree_prefix("<xml-attribute>", XML_GRAMMAR)[0][0])
        )

    def test_bind_expr_match_recursive_nonterminal(self):
        bind_expression = BindExpression("<xml-attribute> <xml-attribute>")

        attr_grammar = copy.deepcopy(XML_GRAMMAR)
        attr_grammar["<start>"] = ["<xml-attribute>"]
        delete_unreachable(attr_grammar)

        tree = DerivationTree.from_parse_tree(list(EarleyParser(attr_grammar).parse('a="..." b="..."'))[0][1][0])
        self.assertTrue(bind_expression.match(tree, XML_GRAMMAR))

    def test_bind_expr_match_lang_assgn_1(self):
        bind_expression = BindExpression(DummyVariable("<var>"), DummyVariable(" := "), BoundVariable("rhs", "<var>"))
        tree = DerivationTree(
            '<assgn>', (
                DerivationTree('<var>'),
                DerivationTree(' := ', ()),
                DerivationTree('<rhs>', (DerivationTree('<var>'),))))

        self.assertTrue(bind_expression.match(tree, LANG_GRAMMAR))

    def test_bind_expr_match_lang_assgn_2(self):
        bind_expression = BindExpression(BoundVariable("rhs", "<var>"))
        tree = DerivationTree('<rhs>', (DerivationTree('<var>'),))
        self.assertTrue(bind_expression.match(tree, LANG_GRAMMAR))

    def test_match_expr_match_xml(self):
        match_expression = BindExpression(
            "<",
            BoundVariable("prefix_use", "<id-no-prefix>"),
            ":",
            "<id-no-prefix>",
            [" ", "<xml-attribute>"],
            ["/"],
            ">",
            ["<inner-xml-tree>", "<xml-close-tag>"])

        tree = DerivationTree(
            '<xml-tree>', (
                DerivationTree('<xml-open-tag>', (
                    DerivationTree('<', (), id=2091),
                    DerivationTree('<id>', (
                        DerivationTree('<id-with-prefix>', (
                            DerivationTree('<id-no-prefix>', None, id=13531),
                            DerivationTree(':', (), id=13532),
                            DerivationTree('<id-no-prefix>', None, id=13533)), id=5800),), id=2092),
                    DerivationTree('>', (), id=2093)), id=1085),
                DerivationTree('<inner-xml-tree>', (
                    DerivationTree('<xml-tree>', (
                        DerivationTree('<xml-open-tag>', (
                            DerivationTree('<', (), id=13581),
                            DerivationTree('<id>', None, id=13582),
                            DerivationTree(' ', (), id=13583),
                            DerivationTree('<xml-attribute>', None, id=13584),
                            DerivationTree('>', (), id=13585)), id=5801),
                        DerivationTree('<inner-xml-tree>', (
                            DerivationTree('<text>', None, id=13586),), id=5802),
                        DerivationTree('<xml-close-tag>', (
                            DerivationTree('</', (), id=13634),
                            DerivationTree('<id>', None, id=13635),
                            DerivationTree('>', (), id=13636)), id=5803)), id=2100),), id=1086),
                DerivationTree('<xml-close-tag>', (
                    DerivationTree('</', (), id=2147),
                    DerivationTree('<id>', None, id=2148),
                    DerivationTree('>', (), id=2149)), id=1087)), id=1084)

        maybe_match = match_expression.match(tree, XML_GRAMMAR_WITH_NAMESPACE_PREFIXES)

        self.assertTrue(maybe_match)
        match_paths = [path for path, _ in maybe_match.values()]

        # "<"
        self.assertIn(tree.find_node(2091), match_paths)
        # BoundVariable("prefix_use", "<id-no-prefix>")
        self.assertIn(tree.find_node(13531), match_paths)
        # ":"
        self.assertIn(tree.find_node(13532), match_paths)
        # "<id-no-prefix>"
        self.assertIn(tree.find_node(13533), match_paths)
        # ">"
        self.assertIn(tree.find_node(2093), match_paths)
        # "<inner-xml-tree>"
        self.assertIn(tree.find_node(1086), match_paths)
        # "<xml-close-tag>"
        self.assertIn(tree.find_node(1087), match_paths)

    def test_tree_k_paths(self):
        graph = gg.GrammarGraph.from_grammar(scriptsizec.SCRIPTSIZE_C_GRAMMAR)

        fuzzer = GrammarCoverageFuzzer(scriptsizec.SCRIPTSIZE_C_GRAMMAR)
        for k in range(1, 5):
            for i in range(10):
                tree = fuzzer.expand_tree(DerivationTree("<start>"))
                self.assertEqual(
                    {path_to_string(p) for p in tree.k_paths(graph, k)},
                    {path_to_string(p) for p in set(graph.k_paths_in_tree(tree.to_parse_tree(), k))},
                    f"Paths for tree {tree} differ"
                )

    def test_open_tree_k_paths(self):
        graph = gg.GrammarGraph.from_grammar(scriptsizec.SCRIPTSIZE_C_GRAMMAR)

        fuzzer = GrammarCoverageFuzzer(scriptsizec.SCRIPTSIZE_C_GRAMMAR)
        for k in range(1, 5):
            for i in range(20):
                tree = DerivationTree("<start>")
                for _ in range(random.randint(1, 10)):
                    tree = fuzzer.expand_tree_once(tree)
                self.assertEqual(
                    {path_to_string(p) for p in tree.k_paths(graph, k)},
                    {path_to_string(p) for p in set(graph.k_paths_in_tree(tree.to_parse_tree(), k))},
                    f"Paths for tree {tree} differ"
                )

    def test_open_tree_paths_replace(self):
        graph = gg.GrammarGraph.from_grammar(scriptsizec.SCRIPTSIZE_C_GRAMMAR)

        tree = DerivationTree.from_parse_tree(('<start>', [('<statement>', [('<block>', None)])]))
        for k in range(1, 6):
            self.assertEqual(graph.k_paths_in_tree(tree.to_parse_tree(), k), tree.k_paths(graph, k))

        tree = DerivationTree.from_parse_tree(('<start>', [('<statement>', None)]))
        for k in range(1, 6):
            self.assertEqual(graph.k_paths_in_tree(tree.to_parse_tree(), k), tree.k_paths(graph, k))

        rtree = tree.replace_path(
            (0,), DerivationTree("<statement>", [DerivationTree("<block>", None)])
        )

        for k in range(1, 6):
            self.assertEqual(
                {path_to_string(p) for p in graph.k_paths_in_tree(rtree.to_parse_tree(), k)},
                {path_to_string(p) for p in rtree.k_paths(graph, k)}
            )

        tree = DerivationTree.from_parse_tree(('<start>', [('<statement>', None)]))

        for k in range(1, 6):
            self.assertEqual(graph.k_paths_in_tree(tree.to_parse_tree(), k), tree.k_paths(graph, k))

        rtree = tree.replace_path(
            (0,), DerivationTree.from_parse_tree(("<statement>", [
                ('if', []), ('<paren_expr>', None), (' ', []), ('<statement>', None),
                (' else ', []), ('<statement>', None)]))
        )

        for k in range(1, 6):
            self.assertEqual(
                {path_to_string(p) for p in graph.k_paths_in_tree(rtree.to_parse_tree(), k)},
                {path_to_string(p) for p in rtree.k_paths(graph, k)}
            )

    def test_open_paths_replace_2(self):
        graph = gg.GrammarGraph.from_grammar(scriptsizec.SCRIPTSIZE_C_GRAMMAR)
        tree = DerivationTree('<start>', None)
        for k in range(1, 6):
            self.assertEqual(
                {path_to_string(p) for p in graph.k_paths_in_tree(tree.to_parse_tree(), k)},
                {path_to_string(p) for p in tree.k_paths(graph, k)})

        tree_1 = tree.replace_path(
            (),
            DerivationTree("<start>", [DerivationTree("<statement>", None)]),
        )

        self.assertTrue(graph.tree_is_valid(tree_1.to_parse_tree()))

        for k in range(1, 6):
            self.assertEqual(
                {path_to_string(p) for p in graph.k_paths_in_tree(tree_1.to_parse_tree(), k)},
                {path_to_string(p) for p in tree_1.k_paths(graph, k)})

        tree_2 = tree_1.replace_path(
            (0,),
            DerivationTree.from_parse_tree(
                ('<statement>', [('if', []), ('<paren_expr>', None), (' ', []), ('<statement>', None)])),
        )

        self.assertTrue(graph.tree_is_valid(tree_2.to_parse_tree()))

        for k in range(1, 6):
            self.assertEqual(
                {path_to_string(p) for p in graph.k_paths_in_tree(tree_2.to_parse_tree(), k)},
                {path_to_string(p) for p in tree_2.k_paths(graph, k)})

    def test_unparse_isla(self):
        unparsed = ISLaUnparser(CSV_COLNO_PROPERTY).unparse()
        self.assertEqual(CSV_COLNO_PROPERTY, parse_isla(unparsed, CSV_GRAMMAR, semantic_predicates={COUNT_PREDICATE}))

        DummyVariable.cnt = 0
        scriptsize_c_def_use_constr = parse_isla(
            SCRIPTSIZE_C_DEF_USE_CONSTR_TEXT,
            scriptsizec.SCRIPTSIZE_C_GRAMMAR,
            structural_predicates={BEFORE_PREDICATE, LEVEL_PREDICATE})
        unparsed = ISLaUnparser(scriptsize_c_def_use_constr).unparse()

        DummyVariable.cnt = 0
        self.assertEqual(
            scriptsize_c_def_use_constr,
            parse_isla(
                unparsed,
                scriptsizec.SCRIPTSIZE_C_GRAMMAR,
                structural_predicates={BEFORE_PREDICATE, LEVEL_PREDICATE}))

        DummyVariable.cnt = 0
        scriptsize_c_no_redef_constr = parse_isla(
            SCRIPTSIZE_C_NO_REDEF_TEXT, scriptsizec.SCRIPTSIZE_C_GRAMMAR,
            structural_predicates={SAME_POSITION_PREDICATE})
        unparsed = ISLaUnparser(scriptsize_c_no_redef_constr).unparse()
        DummyVariable.cnt = 0
        self.assertEqual(
            scriptsize_c_no_redef_constr,
            parse_isla(unparsed, scriptsizec.SCRIPTSIZE_C_GRAMMAR, structural_predicates={SAME_POSITION_PREDICATE}))

    def test_can_pickle_formula(self):
        constraint = parse_isla("""
forall <xml-tree> tree="<<id>><inner-xml-tree></<id>>" in start:
    (= tree "<a></a>")
""", XML_GRAMMAR_WITH_NAMESPACE_PREFIXES)

        import dill as pickle
        pickle.dumps(constraint)


if __name__ == '__main__':
    unittest.main()
