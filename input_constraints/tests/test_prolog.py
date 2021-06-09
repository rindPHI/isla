import string
import typing
import unittest
from typing import List, Tuple, cast

import z3
from fuzzingbook.Grammars import srange
from fuzzingbook.Parser import canonical, EarleyParser

import input_constraints.isla as isla
from input_constraints import isla_shortcuts as sc
from input_constraints.helpers import pyswip_output_to_str, pyswip_clp_constraints_to_str, pyswip_var_mapping
from input_constraints.isla import Constant, BoundVariable, Formula, SMTFormula
from input_constraints.prolog import Translator
from input_constraints.tests.test_data import LANG_GRAMMAR


class TestProlog(unittest.TestCase):
    def get_test_constraint(self):
        prog = Constant("$prog", "<prog>")
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
                    sc.smt_for(cast(z3.BoolRef, lhs_2.to_smt() == var.to_smt()), lhs_2, var)
                )
            )
        )

        return formula

    def test_compute_numeric_nonterminals(self):
        grammar = canonical(LANG_GRAMMAR)
        translator = Translator(grammar, self.get_test_constraint())
        self.assertEqual({"<digit>": (0, 9)}, translator.numeric_nonterminals)

    def test_compute_atomic_string_nonterminals(self):
        grammar = canonical(LANG_GRAMMAR)
        translator = Translator(grammar, self.get_test_constraint())
        self.assertEqual({'<var>': Translator.FUZZING_DEPTH_ATOMIC_STRING_NONTERMINALS},
                         translator.atomic_string_nonterminals)

    def test_compute_atomic_string_nonterminals_2(self):
        grammar = canonical(LANG_GRAMMAR)
        var = Constant("$var", "<var>")

        regex = z3.Concat(z3.Re("a"), z3.Star(z3.Re("b")))
        translator = Translator(grammar, SMTFormula(z3.InRe(var.to_smt(), regex), var))
        self.assertNotIn("<var>", translator.atomic_string_nonterminals.keys())

        translator = Translator(
            grammar,
            SMTFormula(typing.cast(z3.BoolRef, z3.SubSeq(var.to_smt(), 0, 1) == z3.StringVal("a")), var))
        self.assertNotIn("<var>", translator.atomic_string_nonterminals.keys())

    def test_translate_simple_equation(self):
        var1 = Constant("$var1", "<var>")
        var2 = Constant("$var2", "<var>")
        constraint = SMTFormula(typing.cast(z3.BoolRef, var1.to_smt() == var2.to_smt()), var1, var2)
        translator = Translator(canonical(LANG_GRAMMAR), constraint)

        rule = translator.translate_smt_formula(constraint, 0)[0][0]
        self.assertEqual("pred0(Var1, Var2, Result) :- "
                         "_ - Tree1 = Var1, "
                         "_ - Tree2 = Var2, "
                         "equal(Tree1, Tree2, Result)", str(rule))

        prolog = translator.translate()
        var_predicate = translator.predicate_map["var"]
        outer_query = prolog.query(f"{var_predicate}(V1), {var_predicate}(V2), pred0([] - V2, [] - V1, 1), "
                                   f"term_variables([V1, V2], Vs), copy_term(Vs, Vs, Gs).")

        result = list(outer_query)
        self.assertEqual(1, len(result))

        var_name_mapping = pyswip_var_mapping(result[0])
        var1inst = pyswip_output_to_str(result[0]["V1"], var_name_mapping)
        var2inst = pyswip_output_to_str(result[0]["V2"], var_name_mapping)
        constraints = pyswip_clp_constraints_to_str(result[0]["Gs"], var_name_mapping)
        self.assertEqual(var1inst, var2inst)
        outer_query.close()

        inner_query = prolog.query(f"V1={var1inst}, V2={var2inst}, "
                                   f"{constraints}, "
                                   f"term_variables(V1, Vars1), term_variables(V2, Vars2), "
                                   f"append([Vars1, Vars2], Vars), "
                                   f"label(Vars), "
                                   f"tree_to_string(V1, V1Str), tree_to_string(V2, V2Str)")
        for _ in range(9):
            result = next(inner_query)
            self.assertEqual(pyswip_output_to_str(result["V1Str"]), pyswip_output_to_str(result["V2Str"]))

        inner_query.close()

        outer_query = prolog.query(f"{var_predicate}(V1), {var_predicate}(V2), pred0([] - V1, [] - V2, 0), "
                                   f"term_variables([V1, V2], Vs), copy_term(Vs, Vs, Gs).")

        result = list(outer_query)
        self.assertEqual(1, len(result))
        var_name_mapping = pyswip_var_mapping(result[0])
        var1inst = pyswip_output_to_str(result[0]["V1"], var_name_mapping)
        var2inst = pyswip_output_to_str(result[0]["V2"], var_name_mapping)
        constraints = pyswip_clp_constraints_to_str(result[0]["Gs"], var_name_mapping)
        self.assertNotEqual(var1inst, var2inst)
        outer_query.close()

        inner_query = prolog.query(f"V1={var1inst}, V2={var2inst}, "
                                   f"{constraints}, "
                                   f"term_variables(V1, Vars1), term_variables(V2, Vars2), "
                                   f"append([Vars1, Vars2], Vars), "
                                   f"label(Vars), "
                                   f"tree_to_string(V1, V1Str), tree_to_string(V2, V2Str)")
        for _ in range(9):
            result = next(inner_query)
            self.assertNotEqual(pyswip_output_to_str(result["V1Str"]), pyswip_output_to_str(result["V2Str"]))

        inner_query.close()

    def test_translate_unknown_smt_op(self):
        """This test depends on the fact that there is no translation for the SMT function/pred being used to
        Prolog, so we use a foreign function connecting to Z3. Tested SMT function currently is substring,
        in case this is later implemented in Prolog, have to change test case.

        NOTE: Executing the SMT test grounds all involved CLP variables!"""
        variable = Constant("$var", "<var>")
        constraint = SMTFormula(typing.cast(z3.BoolRef,
                                            z3.Or(
                                                z3.SubString(variable.to_smt(), 0, 1) == z3.StringVal("y"),
                                                z3.SubString(variable.to_smt(), 0, 1) == z3.StringVal("z"))),
                                variable)
        translator = Translator(canonical(LANG_GRAMMAR), constraint)

        prolog = translator.translate()
        var_predicate = translator.predicate_map["var"]

        outer_query = prolog.query(f"{var_predicate}(V), pred0([] - V, 1), tree_to_string(V, Str).")
        result = list(outer_query)
        outer_query.close()

        self.assertEqual(2, len(result))
        strinsts = [pyswip_output_to_str(r["Str"])[1:-1] for r in result]
        self.assertEqual(["y", "z"], strinsts)

        outer_query = prolog.query(f"{var_predicate}(V), pred0([] - V, 0), tree_to_string(V, Str).")
        result = list(outer_query)
        outer_query.close()

        self.assertEqual(24, len(result))
        strinsts = [pyswip_output_to_str(r["Str"])[1:-1] for r in result]
        self.assertEqual([c for c in srange(string.ascii_lowercase) if c not in ["y", "z"]], strinsts)

    def test_unknown_predicate(self):
        assignment = Constant("$assgn", "<assgn>")

        pred = isla.Predicate("mypred", 1, lambda pair: pair[1] == "x := x")

        constraint = isla.PredicateFormula(pred, assignment)
        translator = Translator(canonical(LANG_GRAMMAR), constraint)

        prolog = translator.translate()
        stmt_predicate = translator.predicate_map["assgn"]

        outer_query = prolog.query(f"{stmt_predicate}(V), pred0([] - V, 1), tree_to_string(V, Str).")
        for i in range(4):
            result = next(outer_query)
            self.assertEqual('"x := x"', pyswip_output_to_str(result["Str"]))
        outer_query.close()

        outer_query = prolog.query(f"{stmt_predicate}(V), pred0([] - V, 0), tree_to_string(V, Str).")
        for i in range(20):
            result = next(outer_query)
            self.assertNotEqual('"x := x"', pyswip_output_to_str(result["Str"]))
        outer_query.close()

    def test_translate_conjunction(self):
        variable = Constant("$var", "<var>")

        subconstraint_1 = SMTFormula(typing.cast(z3.BoolRef,
                                                 z3.SubString(variable.to_smt(), 0, 1) == z3.StringVal("y")),
                                     variable)
        subconstraint_2 = SMTFormula(typing.cast(z3.BoolRef,
                                                 z3.SubString(variable.to_smt(), 0, 1) == z3.StringVal("z")),
                                     variable)
        constraint = sc.DisjunctiveFormula(subconstraint_1, subconstraint_2)
        translator = Translator(canonical(LANG_GRAMMAR), constraint)

        prolog = translator.translate()
        var_predicate = translator.predicate_map["var"]

        outer_query = prolog.query(f"{var_predicate}(V), pred0([] - V, 1), tree_to_string(V, Str).")
        strinsts = [pyswip_output_to_str(r["Str"])[1:-1] for r in list(outer_query)]
        self.assertEqual(["y", "z"], strinsts)
        outer_query.close()

        outer_query = prolog.query(f"{var_predicate}(V), pred0([] - V, 0), tree_to_string(V, Str).")
        strinsts = [pyswip_output_to_str(r["Str"])[1:-1] for r in list(outer_query)]
        self.assertEqual([c for c in srange(string.ascii_lowercase) if c not in ["y", "z"]], strinsts)
        outer_query.close()

    def test_translate_before(self):
        variable1 = Constant("$var1", "<var>")
        variable2 = Constant("$var2", "<var>")
        constraint = isla.PredicateFormula(isla.BEFORE_PREDICATE, variable1, variable2)
        translator = Translator(canonical(LANG_GRAMMAR), constraint)

        prolog = translator.translate()
        var_predicate = translator.predicate_map["var"]

        outer_query = prolog.query(f"{var_predicate}(V1), {var_predicate}(V2), "
                                   f"pred0([1,0] - V1, [1,1] - V2, 1), "
                                   f"term_variables([V1, V2], Vars), label(Vars), "
                                   f"tree_to_string(V1, Str1), tree_to_string(V2, Str2).")

        self.assertTrue(any(outer_query))
        outer_query.close()

        outer_query = prolog.query(f"{var_predicate}(V1), {var_predicate}(V2), "
                                   f"pred0([1,2] - V1, [1,1] - V2, 1), "
                                   f"term_variables([V1, V2], Vars), label(Vars), "
                                   f"tree_to_string(V1, Str1), tree_to_string(V2, Str2).")

        self.assertFalse(any(outer_query))
        outer_query.close()

    def test_translate_grammar(self):
        translator = Translator(LANG_GRAMMAR, self.get_test_constraint())
        prolog = translator.translate()

        stmt_predicate = translator.predicate_map["stmt"]
        outer_query = prolog.query(f"{stmt_predicate}(S), term_variables(S, Vs), copy_term(Vs, Vs, Gs)")

        outer_results: List[Tuple[str, str]] = []
        for _ in range(10):
            result = next(outer_query)
            var_name_mapping = pyswip_var_mapping(result)
            outer_results.append((pyswip_output_to_str(result["S"], var_name_mapping),
                                  pyswip_clp_constraints_to_str(result["Gs"], var_name_mapping)))
        outer_query.close()

        for outer_result in outer_results:
            inner_query = prolog.query(f"S={outer_result[0]}, {outer_result[1]}, term_variables(S, Vs), "
                                       f"sum(Vs, #=, Sum), "
                                       f"labeling([min(Sum)], Vs), tree_to_string(S, Str).")
            parser = EarleyParser(LANG_GRAMMAR)
            for _ in range(9):
                result = next(inner_query)
                prog = pyswip_output_to_str(result["Str"])[1:-1]  # strip quotation marks
                try:
                    next(parser.parse(prog))
                except SyntaxError:
                    self.fail()

            inner_query.close()


if __name__ == '__main__':
    unittest.main()
