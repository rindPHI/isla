import unittest
from typing import Dict, List, Tuple

import pyswip.easy
import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer

from input_constraints.helpers import pyswip_output_to_str, pyswip_var_mapping, pyswip_clp_constraints_to_str, \
    pyswip_output_to_python, tree_list_to_str
from input_constraints.prolog import Translator
from input_constraints.tests import minipy
from input_constraints.tests.minipy import to_real_python
from input_constraints import isla
from input_constraints import isla_shortcuts as sc


class MinipyTest(unittest.TestCase):
    def test_minipy_grammar(self):
        grammar = minipy.GRAMMAR

        translator = Translator(grammar, isla.SMTFormula(z3.BoolVal(True)),
                                numeric_nonterminals={"<NUMBER>": (0, 100), "<DIGIT>": (0, 9)},
                                atomic_string_nonterminals={
                                    "<NAME>": 10, "<IDCHAR>": 10, "<INIT_CHAR>": 10, "<IDCHARS>": 10})
        # print("\n".join(map(str, translator.translate_grammar())))

        prolog = translator.translate()
        min_depth, max_depth, sols_per_level, labelings = 10, 20, 50, 10
        query = prolog.query(
            f"D in {min_depth}..{max_depth}, "
            f"indomain(D), "
            f"findnsols_nobt({sols_per_level}, S, stmt(S, D), OS), "
            f"maplist([In, Out]>>("
            f"findnsols_nobt({labelings}, Str, (term_variables(In, Vars), label(Vars), tree_to_string(In, Str)), Out)"
            f"), OS, IS)")

        for _ in range((max_depth - min_depth) * sols_per_level * labelings):
            result = next(query)
            var_name_mapping = pyswip_var_mapping(result)
            result_list = pyswip_output_to_python(result["IS"], var_name_mapping)
            for labeled_progs in result_list:
                for prog in labeled_progs:
                    print(to_real_python(prog[1:-1]))

        query.close()

    def test_minipy(self):
        grammar = minipy.GRAMMAR

        # "while <expression>: <block><maybe_else_block>"
        # "{<NEWLINE><stmts>}"

        prog = isla.Constant("$prog", "<start>")
        break_stmt = isla.BoundVariable("$break", "break")
        while_stmt = isla.BoundVariable("$while", "<while_stmt>")
        guard = isla.BoundVariable("$guard", "<expression>")
        maybe_else_block = isla.BoundVariable("$maybe_else_block", "<maybe_else_block>")
        curly_start = isla.BoundVariable("$curly_start", "{")
        curly_end = isla.BoundVariable("$curly_start", "}")
        stmts = isla.BoundVariable("$stmts", "<stmts>")

        break_in_loop: isla.Formula = sc.forall(
            break_stmt,
            prog,
            sc.exists_bind(
                isla.BindExpression("while ") + guard + " " + curly_start + "\n" + stmts + curly_end + maybe_else_block,
                while_stmt,
                prog,
                (sc.before(curly_start, break_stmt) & sc.before(break_stmt, curly_end))
            )
        )

        fuzzer = GrammarCoverageFuzzer(grammar)

        translator = Translator(grammar, break_in_loop,
                                # numeric_nonterminals={"<NUMBER>": (0, 1000), "<DIGIT>": (0, 9)},
                                # atomic_string_nonterminals={"<NAME>": 10, "<IDCHAR>": 10, "<INIT_CHAR>": 10, "<IDCHARS>": 10}
                                )
        prolog = translator.translate()

        print("\n".join(map(str, translator.translate_grammar())))
        print("\n".join(map(str, translator.translate_quantified_formula(break_in_loop, 0)[0])))
        return

        syntactic_problems: Dict[str, int] = {}
        semantic_problems: Dict[str, int] = {}

        valid_counter = 0
        invalid_counter = 0
        semantically_invalid_counter = 0

        query = prolog.query("start(S), term_variables(S, Vars), label(Vars), tree_to_string(S, Str)")

        for _ in range(10):
            # prog = to_real_python(fuzzer.fuzz())
            prog = to_real_python(pyswip_output_to_str(next(query)["Str"]))[1:-1]
            print(prog)

            try:
                exec(prog)
                valid_counter += 1

                # print("Syntactically VALID:")
                # print(prog)
            except SyntaxError as e:
                invalid_counter += 1

                problem = self.get_problem_descr(str(e))
                syntactic_problems.setdefault(problem, 0)
                syntactic_problems[problem] += 1

                # print(f"Syntactically INVALID ({problem}):")
                # print(prog)
            except Exception as e:
                semantically_invalid_counter += 1

                problem = self.get_problem_descr(str(e))
                semantic_problems.setdefault(problem, 0)
                semantic_problems[problem] += 1

                # print(prog)

        print(f"VALID: {valid_counter}, "
              f"INVALID: {invalid_counter}, "
              f"SEMANTICALLY INVALID: {semantically_invalid_counter}")
        print(syntactic_problems)
        print(semantic_problems)

        # Result for 1000 runs:
        # VALID: 806, INVALID: 187, SEMANTICALLY INVALID: 7
        # {"'break' outside loop": 89, "'continue' not properly in loop": 98}
        # {'integer division or modulo by zero': 7}

    def get_problem_descr(self, exc_string: str) -> str:
        if " (" in exc_string:
            return exc_string[:exc_string.index(" (")]
        else:
            return exc_string


if __name__ == '__main__':
    unittest.main()
