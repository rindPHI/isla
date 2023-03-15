# Copyright © 2022 CISPA Helmholtz Center for Information Security.
# Author: Dominic Steinhöfel.
#
# This file is part of ISLa.
#
# ISLa is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# ISLa is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with ISLa.  If not, see <http://www.gnu.org/licenses/>.

import copy
import random
import unittest

import pytest
import z3
from grammar_graph import gg
from orderedset import OrderedSet

import isla.isla_shortcuts as sc
from isla import language
from isla.derivation_tree import DerivationTree
from isla.evaluator import well_formed
from isla.fuzzer import GrammarCoverageFuzzer
from isla.helpers import delete_unreachable
from isla.isla_predicates import (
    BEFORE_PREDICATE,
    LEVEL_PREDICATE,
    SAME_POSITION_PREDICATE,
)
from isla.isla_predicates import count, COUNT_PREDICATE
from isla.language import (
    Constant,
    BoundVariable,
    Formula,
    BindExpression,
    convert_to_dnf,
    ensure_unique_bound_variables,
    VariableManager,
    DummyVariable,
    parse_isla,
    ISLaUnparser,
    SMTFormula,
    ExistsFormula,
    match,
    unparse_isla,
    start_constant,
    true,
)
from isla.parser import EarleyParser
from isla.z3_helpers import z3_eq
from isla_formalizations import rest, scriptsizec, tar
from isla_formalizations.csv import CSV_GRAMMAR, CSV_COLNO_PROPERTY
from isla_formalizations.scriptsizec import (
    SCRIPTSIZE_C_DEF_USE_CONSTR_TEXT,
    SCRIPTSIZE_C_NO_REDEF_TEXT,
)
from isla_formalizations.xml_lang import (
    XML_GRAMMAR,
    XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
)
from test_data import LANG_GRAMMAR, CONFIG_GRAMMAR


def path_to_string(p) -> str:
    return " ".join(
        [
            f'"{n.symbol}" ({n.id})' if isinstance(n, gg.TerminalNode) else n.symbol
            for n in p
        ]
    )


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
                    sc.before(assgn_2, assgn_1)
                    & sc.smt_for(z3_eq(lhs_2.to_smt(), var.to_smt()), lhs_2, var),
                ),
            ),
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
                sc.before(assgn_2, assgn_1)
                & sc.smt_for(z3_eq(lhs_2.to_smt(), var.to_smt()), lhs_2, var),
            ),
        )

        self.assertFalse(well_formed(bad_formula, LANG_GRAMMAR)[0])

        bad_formula_2: Formula = sc.forall(
            assgn_1, assgn_1, sc.smt_for(z3.BoolVal(True))
        )

        self.assertFalse(well_formed(bad_formula_2, LANG_GRAMMAR)[0])
        self.assertFalse(bad_formula_2.free_variables())

        bad_formula_3: Formula = sc.forall(
            assgn_1, prog, sc.forall(assgn_1, prog, sc.smt_for(z3.BoolVal(True)))
        )

        self.assertFalse(well_formed(bad_formula_3, LANG_GRAMMAR)[0])

        self.assertTrue(well_formed(-formula, LANG_GRAMMAR)[0])
        self.assertFalse(well_formed(-bad_formula, LANG_GRAMMAR)[0])
        self.assertFalse(well_formed(-bad_formula_2, LANG_GRAMMAR)[0])
        self.assertFalse(well_formed(-bad_formula_3, LANG_GRAMMAR)[0])

        self.assertFalse(well_formed(formula & bad_formula, LANG_GRAMMAR)[0])
        self.assertFalse(well_formed(formula | bad_formula, LANG_GRAMMAR)[0])

        bad_formula_4: Formula = sc.forall(
            assgn_1, prog, sc.SMTFormula(z3_eq(prog.to_smt(), z3.StringVal("")), prog)
        )

        self.assertFalse(well_formed(bad_formula_4, LANG_GRAMMAR)[0])

        bad_formula_5: Formula = sc.forall(
            assgn_1,
            prog,
            sc.SMTFormula(z3_eq(assgn_1.to_smt(), z3.StringVal("")), assgn_1)
            & sc.forall(var, assgn_1, sc.SMTFormula(z3.BoolVal(True))),
        )

        self.assertFalse(well_formed(bad_formula_5, LANG_GRAMMAR)[0])

        bad_formula_6: Formula = sc.forall(
            assgn_1,
            prog,
            sc.SMTFormula(z3_eq(prog.to_smt(), z3.StringVal("x := x")), prog),
        )

        self.assertFalse(well_formed(bad_formula_6, LANG_GRAMMAR)[0])

        bad_formula_7: Formula = sc.forall(
            assgn_1,
            prog,
            sc.forall(
                assgn_2,
                assgn_1,
                sc.SMTFormula(z3_eq(assgn_1.to_smt(), z3.StringVal("x := x")), assgn_1),
            ),
        )

        self.assertFalse(well_formed(bad_formula_7, LANG_GRAMMAR)[0])

    def test_wellformed_exists_int(self):
        formula = parse_isla(
            'exists int i: count(<start>, "<assgn>", i)',
            LANG_GRAMMAR,
            semantic_predicates={COUNT_PREDICATE},
        )

        self.assertTrue(well_formed(formula, LANG_GRAMMAR)[0])

        formula = language.ForallFormula(
            BoundVariable("start", "<start>"),
            Constant("start", "<start>"),
            language.ExistsIntFormula(
                BoundVariable("i", "NUM"),
                language.ExistsIntFormula(
                    BoundVariable("i", "NUM"),
                    language.SemanticPredicateFormula(
                        COUNT_PREDICATE,
                        BoundVariable("start", "<start>"),
                        "<assgn>",
                        BoundVariable("i", "NUM"),
                    ),
                ),
            ),
        )

        self.assertFalse(well_formed(formula, LANG_GRAMMAR)[0])

        formula = language.ForallFormula(
            BoundVariable("start", "<start>"),
            Constant("start", "<start>"),
            language.ExistsIntFormula(
                BoundVariable("i", "NUM"),
                language.SemanticPredicateFormula(
                    COUNT_PREDICATE,
                    BoundVariable("start", "<start>"),
                    "<assgn>",
                    BoundVariable("k", "NUM"),
                ),
            ),
        )

        self.assertFalse(well_formed(formula, LANG_GRAMMAR)[0])

    def test_free_variables(self):
        # TODO: Remove if not refined, trivial that way
        formula: ExistsFormula = parse_isla(
            "exists <assgn> assgn in start: before(assgn, assgn)",
            structural_predicates={BEFORE_PREDICATE},
        )

        self.assertEqual(
            OrderedSet([formula.bound_variable]), formula.inner_formula.free_variables()
        )

    def test_equality_hash_smt_formulas(self):
        elem = BoundVariable("elem", "<digits>")

        f_1 = SMTFormula(
            z3.StrToInt(elem.to_smt()) <= z3.StrToInt(z3.StringVal("092")), elem
        )
        f_2 = SMTFormula(
            z3.StrToInt(elem.to_smt()) <= z3.StrToInt(z3.StringVal("92")), elem
        )

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

        prog = BoundVariable("$prog", "<stmt>")
        lhs_2 = BoundVariable("$lhs_2", "<var>")
        rhs_2 = BoundVariable("$rhs_2", "<rhs>")

        bind_expr: BindExpression = lhs + " := " + rhs + " ; " + lhs_2 + " := " + rhs_2
        tree, bindings = bind_expr.to_tree_prefix(prog.n_type, LANG_GRAMMAR)[0]
        self.assertEqual("<var> := <rhs> ; <var> := <rhs>", str(tree))

        self.assertEqual((0, 0), bindings[lhs])
        self.assertEqual((0, 2), bindings[rhs])
        self.assertEqual((2, 0, 0), bindings[lhs_2])
        self.assertEqual((2, 0, 2), bindings[rhs_2])

    def test_bind_expr_match_less_specific_tree(self):
        tree = DerivationTree(
            "<int>", (DerivationTree("<leaddigit>"), DerivationTree("<digits>"))
        )

        mexpr = BindExpression(DummyVariable("<leaddigit>"))

        self.assertFalse(mexpr.match(tree, CONFIG_GRAMMAR))

    def test_match_less_specific_tree(self):
        tree = DerivationTree(
            "<int>", (DerivationTree("<leaddigit>"), DerivationTree("<digits>"))
        )

        mexpr_tree = DerivationTree(
            "<int>", (DerivationTree("<leaddigit>"), DerivationTree("<digits>", ()))
        )

        # The match expression requires an empty <digits> element, while the value
        # for the <digits> element of the matched tree is not yet fixed. Thus, there
        # should be *no* match.

        self.assertFalse(
            match(
                tree,
                mexpr_tree,
                {DummyVariable("<leaddigit>"): (0,), DummyVariable(""): (1,)},
            )
        )

    def test_match_same_tree_empty_children(self):
        tree = DerivationTree(
            "<int>", (DerivationTree("<leaddigit>"), DerivationTree("<digits>", ()))
        )

        self.assertTrue(
            match(
                tree,
                tree,
                {DummyVariable("<leaddigit>"): (0,), DummyVariable(""): (1,)},
            )
        )

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
        formula = sc.forall_bind(
            BindExpression(var_1),
            rhs_1,
            start,
            sc.smt_for(z3_eq(var_1.to_smt(), z3.StringVal("x")), var_1),
        ) & sc.forall_bind(
            var_1 + " := " + rhs_1,
            assgn,
            start,
            sc.smt_for(z3_eq(var_1.to_smt(), z3.StringVal("y")), var_1),
        )

        rhs_1_0 = BoundVariable("$rhs_0", "<rhs>")
        var_1_0 = BoundVariable("$var1_0", "<var>")

        DummyVariable.cnt = 0
        expected = sc.forall_bind(
            BindExpression(var_1),
            rhs_1,
            start,
            sc.smt_for(z3_eq(var_1.to_smt(), z3.StringVal("x")), var_1),
        ) & sc.forall_bind(
            var_1_0 + " := " + rhs_1_0,
            assgn,
            start,
            sc.smt_for(z3_eq(var_1_0.to_smt(), z3.StringVal("y")), var_1_0),
        )

        self.assertEqual(expected, ensure_unique_bound_variables(formula))
        self.assertEqual(expected, ensure_unique_bound_variables(expected))

    def test_ensure_unique_bound_variables_2(self):
        formula = parse_isla(
            """forall <assgn> assgn_0="<var> := {<var> var}" in start:
  exists <assgn> assgn in start:
    (before(assgn, assgn_0) and
    (= var "x"))""",
            structural_predicates={BEFORE_PREDICATE},
        )

        self.assertEqual(formula, ensure_unique_bound_variables(formula))

    def test_ensure_unique_bound_variables_3(self):
        mgr = language.VariableManager(LANG_GRAMMAR)
        formula: language.Formula = mgr.create(
            sc.exists(mgr.bv("var", "<var>"), mgr.const("start", "<start>"), sc.true())
            & sc.forall_bind(
                BindExpression("<var>") + " := " + mgr.bv("var", "<var>"),
                mgr.bv("assgn_1", "<assgn>"),
                mgr.const("start", "<start>"),
                sc.exists_bind(
                    mgr.bv("var_0", "<var>") + " := " + "<rhs>",
                    mgr.bv("assgn", "<assgn>"),
                    mgr.const("start"),
                    mgr.smt(z3_eq(mgr.bv("var").to_smt(), mgr.bv("var_0").to_smt())),
                ),
            )
        )

        mgr = language.VariableManager(LANG_GRAMMAR)
        expected: language.Formula = mgr.create(
            sc.exists(mgr.bv("var", "<var>"), mgr.const("start", "<start>"), sc.true())
            & sc.forall_bind(
                BindExpression("<var>") + " := " + mgr.bv("var_1", "<var>"),
                mgr.bv("assgn_1", "<assgn>"),
                mgr.const("start", "<start>"),
                sc.exists_bind(
                    mgr.bv("var_0", "<var>") + " := " + "<rhs>",
                    mgr.bv("assgn", "<assgn>"),
                    mgr.const("start"),
                    mgr.smt(z3_eq(mgr.bv("var_1").to_smt(), mgr.bv("var_0").to_smt())),
                ),
            )
        )

        self.assertEqual(
            unparse_isla(expected), unparse_isla(ensure_unique_bound_variables(formula))
        )

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
        result = count(
            gg.GrammarGraph.from_grammar(LANG_GRAMMAR),
            tree,
            "<assgn>",
            DerivationTree("4", None),
        )
        self.assertEqual("{<stmt>: <assgn> ; <assgn> ; <assgn> ; <assgn>}", str(result))
        #
        # result = count(LANG_GRAMMAR, tree, "<start>", DerivationTree("2", None))
        # self.assertEqual(SemPredEvalResult(False), result)

    def test_to_tree_prefix_tar_file_name(self):
        mgr = VariableManager(tar.TAR_GRAMMAR)
        bind_expression = mgr.bv("$file_name_str", "<file_name_str>") + "<maybe_nuls>"
        self.assertEqual(
            ("<file_name>", [("<file_name_str>", None), ("<maybe_nuls>", None)]),
            bind_expression.to_tree_prefix("<file_name>", tar.TAR_GRAMMAR)[0][
                0
            ].to_parse_tree(),
        )

    def test_to_tree_prefix_rest_ref(self):
        mexpr = BindExpression(
            BoundVariable("label", "<label>"),
            DummyVariable("\n\n"),
            DummyVariable("<paragraph>"),
        )
        tree_prefix = mexpr.to_tree_prefix("<labeled_paragraph>", rest.REST_GRAMMAR)
        self.assertTrue(tree_prefix)

    def test_to_tree_prefix_rest_ref_2(self):
        mexpr = BindExpression(
            DummyVariable(".. _"),
            BoundVariable("def_id", "<id>"),
            DummyVariable(":\n\n"),
            DummyVariable("<paragraph>"),
        )
        in_nonterminal = "<labeled_paragraph>"

        result = mexpr.to_tree_prefix(in_nonterminal, rest.REST_GRAMMAR)
        self.assertEqual(1, len(result))
        tree_prefix, bind_paths = result[0]
        self.assertEqual(".. _<id>:\n\n<paragraph>", str(tree_prefix))

    @pytest.mark.skip(
        reason="This works when run alone, but somehow not in the test suite."
    )
    def test_bind_epxr_to_tree_prefix_recursive_nonterminal(self):
        bind_expression = BindExpression("<xml-attribute> <xml-attribute>")

        self.assertTrue(
            DerivationTree(
                "<xml-attribute>",
                [
                    DerivationTree("<xml-attribute>", None),
                    DerivationTree(" ", ()),
                    DerivationTree("<xml-attribute>", None),
                ],
            ).structurally_equal(
                bind_expression.to_tree_prefix("<xml-attribute>", XML_GRAMMAR)[0][0]
            )
        )

    def test_bind_expr_match_recursive_nonterminal(self):
        bind_expression = BindExpression("<xml-attribute> <xml-attribute>")

        attr_grammar = copy.deepcopy(XML_GRAMMAR)
        attr_grammar["<start>"] = ["<xml-attribute>"]
        attr_grammar = delete_unreachable(attr_grammar)

        tree = DerivationTree.from_parse_tree(
            next(EarleyParser(attr_grammar).parse('a="..." b="..."'))[1][0]
        )
        self.assertTrue(bind_expression.match(tree, XML_GRAMMAR))

    def test_bind_expr_match_lang_assgn_1(self):
        bind_expression = BindExpression(
            DummyVariable("<var>"), DummyVariable(" := "), BoundVariable("rhs", "<var>")
        )
        tree = DerivationTree(
            "<assgn>",
            (
                DerivationTree("<var>"),
                DerivationTree(" := ", ()),
                DerivationTree("<rhs>", (DerivationTree("<var>"),)),
            ),
        )

        self.assertTrue(bind_expression.match(tree, LANG_GRAMMAR))

    def test_bind_expr_match_lang_assgn_2(self):
        bind_expression = BindExpression(BoundVariable("rhs", "<var>"))
        tree = DerivationTree("<rhs>", (DerivationTree("<var>"),))
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
            ["<inner-xml-tree>", "<xml-close-tag>"],
        )

        tree = DerivationTree(
            "<xml-tree>",
            (
                DerivationTree(
                    "<xml-open-tag>",
                    (
                        DerivationTree("<", (), id=2091),
                        DerivationTree(
                            "<id>",
                            (
                                DerivationTree(
                                    "<id-with-prefix>",
                                    (
                                        DerivationTree(
                                            "<id-no-prefix>", None, id=13531
                                        ),
                                        DerivationTree(":", (), id=13532),
                                        DerivationTree(
                                            "<id-no-prefix>", None, id=13533
                                        ),
                                    ),
                                    id=5800,
                                ),
                            ),
                            id=2092,
                        ),
                        DerivationTree(">", (), id=2093),
                    ),
                    id=1085,
                ),
                DerivationTree(
                    "<inner-xml-tree>",
                    (
                        DerivationTree(
                            "<xml-tree>",
                            (
                                DerivationTree(
                                    "<xml-open-tag>",
                                    (
                                        DerivationTree("<", (), id=13581),
                                        DerivationTree("<id>", None, id=13582),
                                        DerivationTree(" ", (), id=13583),
                                        DerivationTree(
                                            "<xml-attribute>", None, id=13584
                                        ),
                                        DerivationTree(">", (), id=13585),
                                    ),
                                    id=5801,
                                ),
                                DerivationTree(
                                    "<inner-xml-tree>",
                                    (DerivationTree("<text>", None, id=13586),),
                                    id=5802,
                                ),
                                DerivationTree(
                                    "<xml-close-tag>",
                                    (
                                        DerivationTree("</", (), id=13634),
                                        DerivationTree("<id>", None, id=13635),
                                        DerivationTree(">", (), id=13636),
                                    ),
                                    id=5803,
                                ),
                            ),
                            id=2100,
                        ),
                    ),
                    id=1086,
                ),
                DerivationTree(
                    "<xml-close-tag>",
                    (
                        DerivationTree("</", (), id=2147),
                        DerivationTree("<id>", None, id=2148),
                        DerivationTree(">", (), id=2149),
                    ),
                    id=1087,
                ),
            ),
            id=1084,
        )

        maybe_match = match_expression.match(tree, XML_GRAMMAR_WITH_NAMESPACE_PREFIXES)

        self.assertTrue(maybe_match)
        match_paths = [path for path, _ in maybe_match.values()]

        # BoundVariable("prefix_use", "<id-no-prefix>")
        self.assertIn(tree.find_node(13531), match_paths)
        # "<id-no-prefix>"
        self.assertIn(tree.find_node(13533), match_paths)
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
                    {
                        path_to_string(p)
                        for p in set(
                            graph.k_paths_in_tree(tree, k, include_terminals=False)
                        )
                    },
                    f"Paths for tree {tree} differ",
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
                    {
                        path_to_string(p)
                        for p in set(
                            graph.k_paths_in_tree(tree, k, include_terminals=False)
                        )
                    },
                    f"Paths for tree {tree} differ",
                )

    def test_open_tree_paths_replace(self):
        graph = gg.GrammarGraph.from_grammar(scriptsizec.SCRIPTSIZE_C_GRAMMAR)

        tree = DerivationTree.from_parse_tree(
            ("<start>", [("<statement>", [("<block>", None)])])
        )
        for k in range(1, 6):
            self.assertEqual(
                graph.k_paths_in_tree(tree, k, include_terminals=False),
                tree.k_paths(graph, k),
            )

        tree = DerivationTree.from_parse_tree(("<start>", [("<statement>", None)]))
        for k in range(1, 6):
            self.assertEqual(
                graph.k_paths_in_tree(tree, k, include_terminals=False),
                tree.k_paths(graph, k),
            )

        rtree = tree.replace_path(
            (0,), DerivationTree("<statement>", [DerivationTree("<block>", None)])
        )

        for k in range(1, 6):
            self.assertEqual(
                {
                    path_to_string(p)
                    for p in graph.k_paths_in_tree(rtree, k, include_terminals=False)
                },
                {path_to_string(p) for p in rtree.k_paths(graph, k)},
            )

        tree = DerivationTree.from_parse_tree(("<start>", [("<statement>", None)]))

        for k in range(1, 6):
            self.assertEqual(
                graph.k_paths_in_tree(tree, k, include_terminals=False),
                tree.k_paths(graph, k),
            )

        rtree = tree.replace_path(
            (0,),
            DerivationTree.from_parse_tree(
                (
                    "<statement>",
                    [
                        ("if", []),
                        ("<paren_expr>", None),
                        (" ", []),
                        ("<statement>", None),
                        (" else ", []),
                        ("<statement>", None),
                    ],
                )
            ),
        )

        for k in range(1, 6):
            self.assertEqual(
                {
                    path_to_string(p)
                    for p in graph.k_paths_in_tree(rtree, k, include_terminals=False)
                },
                {path_to_string(p) for p in rtree.k_paths(graph, k)},
            )

    def test_open_paths_replace_2(self):
        graph = gg.GrammarGraph.from_grammar(scriptsizec.SCRIPTSIZE_C_GRAMMAR)
        tree = DerivationTree("<start>", None)
        for k in range(1, 6):
            self.assertEqual(
                {
                    path_to_string(p)
                    for p in graph.k_paths_in_tree(tree, k, include_terminals=False)
                },
                {path_to_string(p) for p in tree.k_paths(graph, k)},
            )

        tree_1 = tree.replace_path(
            (),
            DerivationTree("<start>", [DerivationTree("<statement>", None)]),
        )

        self.assertTrue(graph.tree_is_valid(tree_1))

        for k in range(1, 6):
            self.assertEqual(
                {
                    path_to_string(p)
                    for p in graph.k_paths_in_tree(tree_1, k, include_terminals=False)
                },
                {path_to_string(p) for p in tree_1.k_paths(graph, k)},
            )

        tree_2 = tree_1.replace_path(
            (0,),
            DerivationTree.from_parse_tree(
                (
                    "<statement>",
                    [
                        ("if", []),
                        ("<paren_expr>", None),
                        (" ", []),
                        ("<statement>", None),
                    ],
                )
            ),
        )

        self.assertTrue(graph.tree_is_valid(tree_2))

        for k in range(1, 6):
            self.assertEqual(
                {
                    path_to_string(p)
                    for p in graph.k_paths_in_tree(tree_2, k, include_terminals=False)
                },
                {path_to_string(p) for p in tree_2.k_paths(graph, k)},
            )

    def test_unparse_isla(self):
        unparsed = ISLaUnparser(CSV_COLNO_PROPERTY).unparse()
        self.assertEqual(
            CSV_COLNO_PROPERTY,
            parse_isla(unparsed, CSV_GRAMMAR, semantic_predicates={COUNT_PREDICATE}),
        )

        DummyVariable.cnt = 0
        scriptsize_c_def_use_constr = parse_isla(
            SCRIPTSIZE_C_DEF_USE_CONSTR_TEXT,
            scriptsizec.SCRIPTSIZE_C_GRAMMAR,
            structural_predicates={BEFORE_PREDICATE, LEVEL_PREDICATE},
        )
        unparsed = ISLaUnparser(scriptsize_c_def_use_constr).unparse()

        DummyVariable.cnt = 0
        self.assertEqual(
            scriptsize_c_def_use_constr,
            parse_isla(
                unparsed,
                scriptsizec.SCRIPTSIZE_C_GRAMMAR,
                structural_predicates={BEFORE_PREDICATE, LEVEL_PREDICATE},
            ),
        )

        DummyVariable.cnt = 0
        scriptsize_c_no_redef_constr = parse_isla(
            SCRIPTSIZE_C_NO_REDEF_TEXT,
            scriptsizec.SCRIPTSIZE_C_GRAMMAR,
            structural_predicates={SAME_POSITION_PREDICATE},
        )
        unparsed = ISLaUnparser(scriptsize_c_no_redef_constr).unparse()
        DummyVariable.cnt = 0
        self.assertEqual(
            scriptsize_c_no_redef_constr,
            parse_isla(
                unparsed,
                scriptsizec.SCRIPTSIZE_C_GRAMMAR,
                structural_predicates={SAME_POSITION_PREDICATE},
            ),
        )

    def test_can_pickle_formula(self):
        constraint = parse_isla(
            """
forall <xml-tree> tree="<<id>><inner-xml-tree></<id>>" in start:
    (= tree "<a></a>")
""",
            XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
        )

        import dill as pickle

        pickle.dumps(constraint)

    def test_match(self):
        # We assume a match expression `{<var> lhs} := {<var> rhs} ; <assgn>` for the assignment language.
        lhs = BoundVariable("<lhs>", "<var>")
        rhs = BoundVariable("<rhs>", "<var>")

        mexpr_tree = DerivationTree.from_parse_tree(
            (
                "<stmt>",
                [
                    (
                        "<assgn>",
                        [("<var>", None), (" := ", []), ("<rhs>", [("<var>", None)])],
                    ),
                    (" ; ", []),
                    ("<stmt>", [("<assgn>", None)]),
                ],
            )
        )
        mexpr_var_paths = {
            lhs: (0, 0),
            DummyVariable(" := "): (0, 1),
            rhs: (0, 2, 0),
            DummyVariable(" ; "): (1,),
            DummyVariable("<assgn>"): (2, 0),
        }

        def parse(inp: str) -> DerivationTree:
            return DerivationTree.from_parse_tree(
                next(EarleyParser(LANG_GRAMMAR).parse(inp))
            )

        inp: DerivationTree = parse("a := b ; c := d").children[0]
        result = match(inp, mexpr_tree, mexpr_var_paths)
        self.assertEqual(((0, 0), inp.get_subtree((0, 0))), result[lhs])
        self.assertEqual(((0, 2, 0), inp.get_subtree((0, 2, 0))), result[rhs])

        inp: DerivationTree = parse("a := b")
        result = match(inp.children[0], mexpr_tree, mexpr_var_paths)
        self.assertEqual(None, result)

        # We now assume a match expression `{<var> lhs} := {<var> rhs}` for the assignment language.
        mexpr_tree = DerivationTree.from_parse_tree(
            ("<assgn>", [("<var>", None), (" := ", []), ("<rhs>", [("<var>", None)])])
        )

        mexpr_var_paths = {lhs: (0,), DummyVariable(" := "): (1,), rhs: (2, 0)}

        inp: DerivationTree = parse("a := b ; c := d").get_subtree((0, 0))
        result = match(inp, mexpr_tree, mexpr_var_paths)
        self.assertEqual(((0,), inp.get_subtree((0,))), result[lhs])
        self.assertEqual(((2, 0), inp.get_subtree((2, 0))), result[rhs])

        inp: DerivationTree = parse("a := b").get_subtree((0, 0))
        result = match(inp, mexpr_tree, mexpr_var_paths)
        self.assertEqual(((0,), inp.get_subtree((0,))), result[lhs])
        self.assertEqual(((2, 0), inp.get_subtree((2, 0))), result[rhs])

        inp: DerivationTree = parse("a := b ; c := d").get_subtree((0, 2, 0))
        result = match(inp, mexpr_tree, mexpr_var_paths)
        self.assertEqual(((0,), inp.get_subtree((0,))), result[lhs])
        self.assertEqual(((2, 0), inp.get_subtree((2, 0))), result[rhs])

        inp: DerivationTree = parse("a := b ; c := d").get_subtree((0, 2))
        result = match(inp, mexpr_tree, mexpr_var_paths)
        self.assertEqual(None, result)

    def test_subsitute_in_existential_formula(self):
        def parse(inp: str, start_symbol: str = "<start>") -> DerivationTree:
            if start_symbol != "<start>":
                grammar = copy.deepcopy(LANG_GRAMMAR)
                grammar["<start>"] = [start_symbol]
                grammar = delete_unreachable(grammar)
            else:
                grammar = LANG_GRAMMAR

            return DerivationTree.from_parse_tree(
                next(EarleyParser(grammar).parse(inp))
            )

        inp = parse("x := y")
        digit = BoundVariable("digit", "<digit>")

        formula = ExistsFormula(
            digit,
            inp,
            SMTFormula(z3_eq(digit.to_smt(), z3.StringVal("0")), digit),
        )

        result = formula.substitute_expressions({digit: parse("0", "<digit>")})

        # Although the inner formula is "true," the bound variable does no longer
        # occur in the quantifier's core, and there's no match expression, the
        # formula should *not* simplify to "true" since the demanded structure
        # element `<digit>` does not exist in the input. In fact, we *could* simplify
        # the formula to "false" here, which we, however, don't, to not disturb the
        # solver, which might attempt to insert a tree establishing truth of the
        # formula. The mentioned simplification used to be a (wrong!) part of the
        # implementation.
        expected = ExistsFormula(
            digit,
            inp,
            true(),
        )

        self.assertEqual(expected, result)


if __name__ == "__main__":
    unittest.main()
