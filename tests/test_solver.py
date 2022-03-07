import functools
import logging
import os
import random
import unittest
from typing import cast, Optional, Dict, List, Callable, Union, Set
from xml.dom import minidom
from xml.sax.saxutils import escape

import pytest
import z3

import isla.evaluator
from isla import isla_shortcuts as sc
from isla import language
from isla.existential_helpers import DIRECT_EMBEDDING, SELF_EMBEDDING, CONTEXT_ADDITION
from isla.fuzzer import GrammarFuzzer, GrammarCoverageFuzzer
from isla.isla_predicates import BEFORE_PREDICATE, COUNT_PREDICATE, STANDARD_SEMANTIC_PREDICATES, \
    STANDARD_STRUCTURAL_PREDICATES
from isla.language import VariablesCollector, parse_isla
from isla.solver import ISLaSolver, SolutionState, STD_COST_SETTINGS, CostSettings, CostWeightVector, \
    get_quantifier_chains
from isla.type_defs import Grammar
from isla.z3_helpers import z3_eq
from isla_formalizations import rest, tar, simple_tar, scriptsizec
from isla_formalizations.csv import csv_lint, CSV_GRAMMAR, CSV_HEADERBODY_GRAMMAR
from isla_formalizations.tar import extract_tar
from isla_formalizations.xml_lang import XML_GRAMMAR_WITH_NAMESPACE_PREFIXES, \
    XML_NAMESPACE_CONSTRAINT, XML_WELLFORMEDNESS_CONSTRAINT, XML_GRAMMAR, validate_xml, XML_NO_ATTR_REDEF_CONSTRAINT
from test_data import LANG_GRAMMAR, SIMPLE_CSV_GRAMMAR


class TestSolver(unittest.TestCase):
    def test_qfd_formula_might_match(self):
        mgr = language.VariableManager(LANG_GRAMMAR)
        solver = ISLaSolver(LANG_GRAMMAR, mgr.smt(z3_eq(mgr.const("$DUMMY", "<start>").to_smt(), z3.StringVal(""))))

        tree = language.DerivationTree.from_parse_tree(
            ('<start>', [
                ('<stmt>', [
                    ('<assgn>', [
                        ('<var>', None),  # Path (0, 0, 0)
                        (' := ', []), ('<rhs>', [('<var>', None)])]),
                    (' ; ', []),
                    ('<stmt>', [('<assgn>', [('<var>', None), (' := ', []), ('<rhs>', None)])])])]))

        formula = cast(language.QuantifiedFormula, mgr.create(sc.forall_bind(
            language.BindExpression(mgr.bv("$var1", "<var>")),
            mgr.bv("$rhs1", "<rhs>"),
            tree,
            mgr.smt(z3_eq(mgr.bv("$var1").to_smt(), z3.StringVal("x")))
        )))

        assert tree.get_subtree((0, 0, 2, 0)).value == "<var>"
        # assert not tree.get_subtree((0, 0, 2, 0)).children

        self.assertTrue(solver.quantified_formula_might_match(formula, (0, 0, 2, 0), tree))

    def test_atomic_smt_formula(self):
        assgn = language.Constant("$assgn", "<assgn>")
        formula = language.SMTFormula(z3_eq(assgn.to_smt(), z3.StringVal("x := x")), assgn)
        self.execute_generation_test(formula, num_solutions=1)

    def test_simple_universal_formula(self):
        start = language.Constant("$start", "<start>")
        var1 = language.BoundVariable("$var", "<var>")

        formula = sc.forall(
            var1, start,
            sc.smt_for(cast(z3.BoolRef, z3_eq(var1.to_smt(), z3.StringVal("x"))), var1))

        self.execute_generation_test(formula, max_number_free_instantiations=1)

    def test_simple_universal_formula_with_bind(self):
        mgr = language.VariableManager(LANG_GRAMMAR)
        formula = mgr.create(
            sc.forall_bind(
                language.BindExpression(mgr.bv("$var1", "<var>")),
                mgr.bv("$rhs", "<rhs>"), mgr.const("$start", "<start>"),
                mgr.smt(cast(z3.BoolRef, z3_eq(mgr.bv("$var1").to_smt(), z3.StringVal("x")))))
        )

        self.execute_generation_test(formula)

    def test_simple_existential_formula(self):
        mgr = language.VariableManager(LANG_GRAMMAR)
        start = language.Constant("$start", "<start>")

        formula = mgr.create(
            sc.exists(
                mgr.bv("$var", "<var>"), start,
                mgr.smt(z3_eq(mgr.bv("$var").to_smt(), z3.StringVal("x"))))
        )

        self.execute_generation_test(
            formula,
            num_solutions=50,
            max_number_free_instantiations=1,
        )

    def test_simple_existential_formula_with_bind(self):
        start = language.Constant("$start", "<start>")
        rhs = language.BoundVariable("$rhs", "<rhs>")
        var1 = language.BoundVariable("$var", "<var>")

        formula = sc.exists_bind(
            language.BindExpression(var1),
            rhs, start,
            sc.smt_for(z3_eq(var1.to_smt(), z3.StringVal("x")), var1))

        self.execute_generation_test(formula, num_solutions=50)

    def test_conjunction_of_qfd_formulas(self):
        start = language.Constant("$start", "<start>")
        assgn = language.BoundVariable("$assgn", "<assgn>")
        rhs_1 = language.BoundVariable("$rhs_1", "<rhs>")
        rhs_2 = language.BoundVariable("$rhs_2", "<rhs>")
        var_1 = language.BoundVariable("$var1", "<var>")
        var_2 = language.BoundVariable("$var2", "<var>")

        formula = \
            sc.forall_bind(
                language.BindExpression(var_1),
                rhs_1, start,
                sc.smt_for(z3_eq(var_1.to_smt(), z3.StringVal("x")), var_1)) & \
            sc.forall_bind(
                var_2 + " := " + rhs_2,
                assgn, start,
                sc.smt_for(z3_eq(var_2.to_smt(), z3.StringVal("y")), var_2))

        self.execute_generation_test(formula)

    def test_xml(self):
        constraint = """
forall <xml-tree> tree="<{<id> opid}[ <xml-attribute>]><inner-xml-tree></{<id> clid}>" in start:
    (= opid clid)"""

        self.execute_generation_test(
            constraint,
            grammar=XML_GRAMMAR,
            max_number_free_instantiations=1,
            num_solutions=30,
            cost_settings=CostSettings(
                weight_vectors=(
                    CostWeightVector(
                        tree_closing_cost=28,
                        vacuous_penalty=5,
                        constraint_cost=40,
                        derivation_depth_penalty=3,
                        low_k_coverage_penalty=23,
                        low_global_k_path_coverage_penalty=5)
                    ,),
                cost_phase_lengths=(200,)),
        )

    def test_get_quantifier_chains(self):
        chains_1 = get_quantifier_chains(XML_WELLFORMEDNESS_CONSTRAINT)
        self.assertEqual(1, len(chains_1))
        chains_2 = get_quantifier_chains(XML_NAMESPACE_CONSTRAINT)
        self.assertEqual(2, len(chains_2))
        all_chains = get_quantifier_chains(XML_WELLFORMEDNESS_CONSTRAINT & XML_NAMESPACE_CONSTRAINT)
        self.assertEqual(3, len(all_chains))
        self.assertEqual(set(chains_1) | set(chains_2), set(all_chains))

    def test_xml_with_prefixes(self):
        self.execute_generation_test(
            XML_NAMESPACE_CONSTRAINT & XML_WELLFORMEDNESS_CONSTRAINT & XML_NO_ATTR_REDEF_CONSTRAINT,
            grammar=XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
            max_number_free_instantiations=1,
            num_solutions=50,
            enforce_unique_trees_in_queue=True,
            custom_test_func=validate_xml,
            cost_settings=CostSettings(
                weight_vectors=(
                    CostWeightVector(
                        tree_closing_cost=10,
                        vacuous_penalty=0,
                        constraint_cost=4,
                        derivation_depth_penalty=10,
                        low_k_coverage_penalty=23,
                        low_global_k_path_coverage_penalty=25),
                    # CostWeightVector(
                    #     tree_closing_cost=10,
                    #     vacuous_penalty=0,
                    #     constraint_cost=0,
                    #     derivation_depth_penalty=3,
                    #     low_k_coverage_penalty=0,
                    #     low_global_k_path_coverage_penalty=0),
                ),
                cost_phase_lengths=(200,),
                k=3
            ),
        )

    def test_declared_before_used(self):
        mgr = language.VariableManager(LANG_GRAMMAR)
        formula: language.Formula = mgr.create(sc.forall_bind(
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
                    mgr.smt(z3_eq(mgr.bv("$lhs_2").to_smt(), mgr.bv("$var").to_smt()))
                )
            )
        ))

        self.execute_generation_test(
            formula,
            max_number_free_instantiations=1,
            max_number_smt_instantiations=1,
            num_solutions=40,
        )

    def test_declared_before_used_concrete_syntax(self):
        formula = """
forall <assgn> assgn_1="{<var> lhs_1} := {<rhs> rhs_1}" in start:
  forall <var> var in rhs_1:
    exists <assgn> assgn_2="{<var> lhs_2} := {<rhs> rhs_2}" in start:
      (before(assgn_2, assgn_1) and (= lhs_2 var))
"""

        self.execute_generation_test(
            formula,
            structural_predicates={BEFORE_PREDICATE},
            max_number_free_instantiations=1,
            num_solutions=30)

    def test_simple_csv_rows_equal_length(self):
        property = """
forall <csv-header> hline in start:
  exists int colno:
    ((>= (str.to.int colno) 3) and 
    ((<= (str.to.int colno) 5) and 
     (count(hline, "<csv-field>", colno) and 
     forall <csv-record> line in start:
       count(line, "<csv-field>", colno))))
"""

        self.execute_generation_test(
            property,
            grammar=SIMPLE_CSV_GRAMMAR,
            semantic_predicates={COUNT_PREDICATE},
            max_number_free_instantiations=1,
            max_number_smt_instantiations=3,
            enforce_unique_trees_in_queue=False,
            num_solutions=20)

    def test_csv_rows_equal_length_simpler(self):
        property = """
exists int num:
   forall <csv-record> elem in start:
     ((>= (str.to.int num) 1) and
      count(elem, "<raw-field>", num))"""

        self.execute_generation_test(
            property,
            semantic_predicates={COUNT_PREDICATE},
            grammar=CSV_GRAMMAR,
            custom_test_func=csv_lint,
            num_solutions=50,
            max_number_free_instantiations=10,
            max_number_smt_instantiations=10,
            enforce_unique_trees_in_queue=False,
            global_fuzzer=False,
            fuzzer_factory=functools.partial(GrammarFuzzer, min_nonterminals=0, max_nonterminals=30),
        )

    def test_csv_rows_equal_length(self):
        property = """
forall <csv-header> hline in start:
  exists int colno:
    ((>= (str.to.int colno) 3) and 
    ((<= (str.to.int colno) 5) and 
     (count(hline, "<raw-field>", colno) and 
     forall <csv-record> line in start:
       count(line, "<raw-field>", colno))))
"""

        self.execute_generation_test(
            property,
            semantic_predicates={COUNT_PREDICATE},
            grammar=CSV_GRAMMAR,
            custom_test_func=csv_lint,
            num_solutions=50,
            max_number_free_instantiations=1,
            max_number_smt_instantiations=1,
            enforce_unique_trees_in_queue=False,
            global_fuzzer=False,
            fuzzer_factory=functools.partial(GrammarFuzzer, min_nonterminals=0, max_nonterminals=30),
            cost_settings=CostSettings(
                weight_vectors=(
                    CostWeightVector(
                        tree_closing_cost=1,
                        vacuous_penalty=0,
                        constraint_cost=0,
                        derivation_depth_penalty=1,
                        low_k_coverage_penalty=0,
                        low_global_k_path_coverage_penalty=0),
                ),
                cost_phase_lengths=(200,),
                k=3
            ),
        )

    def test_csv_rows_equal_length_more_complex(self):
        property = """
forall <csv-header> header in start:
  forall <csv-body> body in start:
    forall <csv-record> hline in header:
      exists int colno:
        ((>= (str.to.int colno) 3) and 
         (<= (str.to.int colno) 5) and
         count(hline, "<raw-field>", colno) and 
         forall <csv-record> line in body:
            count(line, "<raw-field>", colno))
"""

        self.execute_generation_test(
            property,
            semantic_predicates={COUNT_PREDICATE},
            grammar=CSV_HEADERBODY_GRAMMAR,
            custom_test_func=csv_lint,
            num_solutions=20,
            max_number_free_instantiations=1,
            max_number_smt_instantiations=1,
            enforce_unique_trees_in_queue=False,
            global_fuzzer=True
        )

    def test_negated_csv_rows_equal_length(self):
        property = parse_isla("""
exists <csv-header> header in start:
  exists <csv-body> body in start:
    exists <csv-record> hline in header:
      forall int colno:
        (not(>= (str.to_int colno) 3) or 
         not(<= (str.to_int colno) 5) or
         not(count(hline, "<raw-field>", colno)) or 
         exists <csv-record> line in body:
           not(count(line, "<raw-field>", colno)))
""", CSV_HEADERBODY_GRAMMAR, semantic_predicates={COUNT_PREDICATE})

        # We don't find infinite solutions here, problem with existentially quantified top-level formulas...
        self.execute_generation_test(
            property,
            semantic_predicates={COUNT_PREDICATE},
            grammar=CSV_HEADERBODY_GRAMMAR,
            custom_test_func=lambda t: isinstance(csv_lint(t), str),
            num_solutions=32,  # Max number reachable
            max_number_free_instantiations=2,
            max_number_smt_instantiations=1,
            enforce_unique_trees_in_queue=False,
            global_fuzzer=True,
            debug=True
        )

    def test_simple_equal_length_csv_negated(self):
        # Original property:
        # exists int colno:
        #   forall <csv-record> record in start:
        #     count(record, "<raw-field>", colno)
        property = """
forall int colno:
  exists <csv-record> record in start:
    not(count(record, "<raw-field>", colno))"""

        self.execute_generation_test(
            property,
            grammar=CSV_GRAMMAR,
            custom_test_func=lambda t: isinstance(csv_lint(t), str),
            num_solutions=40,
            max_number_free_instantiations=1,
            max_number_smt_instantiations=1,
            enforce_unique_trees_in_queue=False,
            global_fuzzer=True,
            debug=True
        )

    @pytest.mark.flaky(reruns=3, reruns_delay=2)
    def test_rest(self):
        random.seed(1234)
        self.execute_generation_test(
            rest.LENGTH_UNDERLINE & rest.DEF_LINK_TARGETS &
            rest.NO_LINK_TARGET_REDEF & rest.LIST_NUMBERING_CONSECUTIVE,
            custom_test_func=rest.render_rst,
            grammar=rest.REST_GRAMMAR,
            max_number_free_instantiations=1,
            max_number_smt_instantiations=1,
            num_solutions=50,
            enforce_unique_trees_in_queue=False,
        )

    def test_scriptsize_c_def_before_use(self):
        self.execute_generation_test(
            scriptsizec.SCRIPTSIZE_C_DEF_USE_CONSTR & scriptsizec.SCRIPTSIZE_C_NO_REDEF_CONSTR,
            grammar=scriptsizec.SCRIPTSIZE_C_GRAMMAR,
            max_number_free_instantiations=1,
            max_number_smt_instantiations=2,
            enforce_unique_trees_in_queue=True,
            custom_test_func=scriptsizec.compile_scriptsizec_clang,
            num_solutions=50,
            cost_settings=CostSettings(
                (CostWeightVector(tree_closing_cost=10, vacuous_penalty=0, constraint_cost=0,
                                  derivation_depth_penalty=9, low_k_coverage_penalty=28,
                                  low_global_k_path_coverage_penalty=4),),
                cost_phase_lengths=(200,),
                k=4
            ),
            # print_only=True
        )

    def test_scriptsize_c_redef(self):
        self.execute_generation_test(
            scriptsizec.SCRIPTSIZE_C_NO_REDEF_CONSTR,
            grammar=scriptsizec.SCRIPTSIZE_C_GRAMMAR,
            max_number_free_instantiations=1,
            max_number_smt_instantiations=2,
            enforce_unique_trees_in_queue=True,
            # custom_test_func=scriptsizec.compile_scriptsizec_clang,
            num_solutions=50,
            cost_settings=CostSettings(
                (CostWeightVector(tree_closing_cost=10, vacuous_penalty=0, constraint_cost=0,
                                  derivation_depth_penalty=9, low_k_coverage_penalty=28,
                                  low_global_k_path_coverage_penalty=4),),
                cost_phase_lengths=(200,),
                k=4
            ),
            # print_only=True
        )

    @pytest.mark.skip(reason="Have to disable assertions to run this test, disabling in CI pipeline.")
    def test_tar(self):
        self.execute_generation_test(
            tar.TAR_CONSTRAINTS,
            grammar=tar.TAR_GRAMMAR,
            max_number_free_instantiations=1,
            max_number_smt_instantiations=1,
            enforce_unique_trees_in_queue=False,
            # debug=True,
            num_solutions=60,
            precompute_reachability=False,
            # custom_test_func=extract_tar,
            cost_settings=CostSettings(
                (STD_COST_SETTINGS.weight_vectors[0],),
                (200,),
                k=4
            ),
            tree_insertion_methods=DIRECT_EMBEDDING | SELF_EMBEDDING
            # cost_settings=CostSettings(
            #     (CostWeightVector(1, 1, 1, 1, 1, 1),),
            #     (200,),
            #     k=1
            # ),
        )

    def test_simple_tar(self):
        self.execute_generation_test(
            simple_tar.TAR_CONSTRAINTS,
            grammar=simple_tar.SIMPLE_TAR_GRAMMAR,
            max_number_free_instantiations=1,
            max_number_smt_instantiations=1,
            enforce_unique_trees_in_queue=False,
            debug=True,
            num_solutions=10,
            precompute_reachability=False,
            cost_settings=STD_COST_SETTINGS,
        )

    def execute_generation_test(
            self,
            formula: Union[language.Formula, str],
            structural_predicates: Set[language.StructuralPredicate] = STANDARD_STRUCTURAL_PREDICATES,
            semantic_predicates: Set[language.SemanticPredicate] = STANDARD_SEMANTIC_PREDICATES,
            grammar=LANG_GRAMMAR,
            num_solutions=50,
            print_solutions=False,
            max_number_free_instantiations=1,
            max_number_smt_instantiations=1,
            enforce_unique_trees_in_queue=True,
            precompute_reachability=False,
            debug=False,
            state_tree_out="/tmp/state_tree.xml",
            log_out="/tmp/isla_log.txt",
            custom_test_func: Optional[Callable[[language.DerivationTree], Union[bool, str]]] = None,
            cost_settings=STD_COST_SETTINGS,
            print_only: bool = False,
            timeout_seconds: Optional[int] = None,
            global_fuzzer: bool = False,
            fuzzer_factory: Callable[[Grammar], GrammarFuzzer] = lambda grammar: GrammarCoverageFuzzer(grammar),
            tree_insertion_methods=DIRECT_EMBEDDING + SELF_EMBEDDING + CONTEXT_ADDITION):
        logger = logging.getLogger(type(self).__name__)

        if debug:
            for f in [f for f in [state_tree_out, log_out] if os.path.exists(f)]:
                os.remove(f)

        solver = ISLaSolver(
            grammar=grammar,
            formula=formula,
            structural_predicates=structural_predicates,
            semantic_predicates=semantic_predicates,
            max_number_free_instantiations=max_number_free_instantiations,
            max_number_smt_instantiations=max_number_smt_instantiations,
            enforce_unique_trees_in_queue=enforce_unique_trees_in_queue,
            precompute_reachability=precompute_reachability,
            debug=debug,
            cost_settings=cost_settings,
            timeout_seconds=timeout_seconds,
            global_fuzzer=global_fuzzer,
            fuzzer_factory=fuzzer_factory,
            tree_insertion_methods=tree_insertion_methods
        )

        if debug:
            file_handler = logging.FileHandler(log_out)
            for name in logging.root.manager.loggerDict:
                logging.getLogger(name).addHandler(file_handler)

        if isinstance(formula, str):
            formula = parse_isla(formula, grammar, structural_predicates, semantic_predicates)

        constant = next(
            c for c in VariablesCollector.collect(formula)
            if isinstance(c, language.Constant) and not c.is_numeric())

        def print_tree():
            if debug:
                with open(state_tree_out, 'w') as file:
                    file.write(TestSolver.state_tree_to_xml(
                        solver.state_tree_root, solver.state_tree, solver.costs))
                    print(f"Written derivation data (XML) to {state_tree_out}")
                    print(f"Written log {log_out}")

        it = solver.solve()
        solutions_found = 0
        for idx in range(num_solutions):
            try:
                assignment = next(it)

                solutions_found += 1
                logger.info(f"Found solution no. %d: %s", solutions_found, assignment)

                if not print_only:
                    self.assertTrue(
                        isla.evaluator.evaluate(formula.substitute_expressions({constant: assignment}), assignment,
                                                grammar),
                        f"Solution {assignment} does not satisfy constraint {formula}"
                    )

                    if custom_test_func:
                        test_result = custom_test_func(assignment)
                        if test_result is not True:
                            self.fail(f"Solution WRONG: '{assignment}'" if not isinstance(test_result, str)
                                      else f"Solution WRONG: '{assignment}', message: {test_result}")

                if print_solutions:
                    print(str(assignment))
            except StopIteration:
                print_tree()
                if idx == 0:
                    self.fail("No solution found.")
                self.fail(f"Only found {idx} solutions")

        print_tree()

    @staticmethod
    def state_tree_to_xml(
            root: SolutionState,
            tree: Dict[SolutionState, List[SolutionState]],
            costs: Dict[SolutionState, float],
            prettify=True,
            seen: Optional[Set[SolutionState]] = None) -> str:
        if seen and root in seen:
            return ""

        if root not in tree:
            children_string = ""
        else:
            children_string = (
                    "<children>" +
                    "".join([TestSolver.state_tree_to_xml(
                        child, tree, costs, False, (seen or set()) | {root}
                    ) for child in tree[root]]) +
                    "</children>")

        special_char_map = {
            "\x00": "&lt;NUL&gt;",
            "\x0b": "&lt;VTAB&gt;",
            "\x0c": "&lt;FFEED&gt;",
        }

        result = ("<state>" +
                  "<constraint>" + escape(str(root.constraint), special_char_map) + "</constraint>" +
                  "<tree>" + escape(str(root.tree), special_char_map) + "</tree>" +
                  "<cost>" + str(costs[root]) + "</cost>" +
                  "<hash>" + str(hash(root)) + "</hash>" +
                  children_string +
                  "</state>")

        if prettify:
            return minidom.parseString(result).toprettyxml(indent="    ")
        else:
            return result

    if __name__ == '__main__':
        unittest.main()
