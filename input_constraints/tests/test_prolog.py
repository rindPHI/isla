import typing
import unittest
from typing import List, Dict, Tuple, cast

import pyswip
import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Parser import canonical, EarleyParser
from grammar_graph.gg import GrammarGraph
from pyswip import Prolog, registerForeign

from input_constraints.helpers import pyswip_output_to_str, pyswip_clp_constraints_to_str, pyswip_var_mapping
from input_constraints.lang import Constant, BoundVariable, Formula, SMTFormula
from input_constraints import shortcuts as sc
from input_constraints.prolog import translate_grammar, Translator
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
                    sc.before(assgn_2, assgn_1, prog) &
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
        self.assertEqual({'<digit>': 10, '<stmt>': 10, '<var>': 10, '<start>': 10},
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

    def test_translate_grammar(self):
        numeric_nonterminals = {"<digit>": (0, 9)}
        atomic_string_nonterminals = {"<var>": 10}

        def numeric_nonterminal(atom: pyswip.easy.Atom) -> bool:
            return f"<{atom.value}>" in numeric_nonterminals

        def atomic_string_nonterminal(atom: pyswip.easy.Atom) -> bool:
            return f"<{atom.value}>" in atomic_string_nonterminals

        fuzz_results: Dict[str, List[str]] = {}
        fuzzers: Dict[str, GrammarCoverageFuzzer] = {}

        def fuzz(atom: pyswip.easy.Atom, idx: int, result: pyswip.easy.Variable) -> bool:
            nonterminal = f"<{atom.value}>"

            grammar = GrammarGraph.from_grammar(LANG_GRAMMAR).subgraph(nonterminal).to_grammar()
            fuzzer = fuzzers.setdefault(nonterminal, GrammarCoverageFuzzer(grammar))
            fuzz_results.setdefault(nonterminal, [])

            while len(fuzz_results[nonterminal]) <= idx:
                fuzz_results[nonterminal].append(fuzzer.fuzz())

            result.value = fuzz_results[nonterminal][idx]
            return True

        prolog = Prolog()
        prolog.consult("../prolog_defs.pl")

        for pred in ["atomic_nonterminal/1", "atomic_string_nonterminal/1", "fuzz/3"]:
            next(prolog.query(f"abolish({pred})"))

        registerForeign(numeric_nonterminal, arity=1)
        registerForeign(atomic_string_nonterminal, arity=1)
        registerForeign(fuzz, arity=3)

        pl_grammar = translate_grammar(
            canonical(LANG_GRAMMAR),
            Translator(LANG_GRAMMAR, None).compute_predicate_names_for_nonterminals(),
            numeric_nonterminals,
            atomic_string_nonterminals
        )

        next(prolog.query("use_module(library(clpfd))"))

        for rule in pl_grammar:
            prolog.assertz(str(rule))

        outer_query = prolog.query("stmt(S), term_variables(S, Vs), copy_term(Vs, Vs, Gs)")

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
