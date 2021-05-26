import unittest
from typing import List, Dict, Tuple

import pyswip
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Parser import canonical, EarleyParser
from grammar_graph.gg import GrammarGraph
from pyswip import Prolog, registerForeign

from input_constraints.helpers import pyswip_output_to_str, pyswip_clp_constraints_to_str, pyswip_var_mapping
from input_constraints.prolog import translate_grammar, predicate_names_for_nonterminals
from input_constraints.tests.test_data import LANG_GRAMMAR


class TestProlog(unittest.TestCase):
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
            predicate_names_for_nonterminals(LANG_GRAMMAR),
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
            print(outer_result[0])
            print(outer_result[1])
            inner_query = prolog.query(f"S={outer_result[0]}, {outer_result[1]}, term_variables(S, Vs), "
                                       f"sum(Vs, #=, Sum), "
                                       f"labeling([min(Sum)], Vs), tree_to_string(S, Str).")
            parser = EarleyParser(LANG_GRAMMAR)
            for _ in range(9):
                result = next(inner_query)
                prog = pyswip_output_to_str(result["Str"])[1:-1]  # strip quotation marks
                print(prog)
                try:
                    next(parser.parse(prog))
                except SyntaxError:
                    self.fail()

            inner_query.close()


if __name__ == '__main__':
    unittest.main()
