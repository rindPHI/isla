import subprocess
import unittest
from tempfile import NamedTemporaryFile
from typing import Tuple

from isla import __version__ as isla_version
from isla.language import unparse_grammar, unparse_isla
from isla.solver import ISLaSolver
from isla.type_defs import Grammar
from test_data import LANG_GRAMMAR


def run_isla(*args) -> Tuple[str, str, int]:
    try:
        result = subprocess.run(
            ["isla"] + [str(arg) for arg in args],
            capture_output=True,
            check=True,
            text=True,
        )
    except subprocess.CalledProcessError as cpe:
        return cpe.stdout, cpe.stderr, cpe.returncode

    return result.stdout, result.stderr, 0


def write_constraint_file(formula: str) -> NamedTemporaryFile:
    constraint_file = NamedTemporaryFile(suffix=".isla")
    constraint_file.write(formula.strip().encode("utf-8"))
    constraint_file.seek(0)
    return constraint_file


def write_grammar_file(grammar: Grammar) -> NamedTemporaryFile:
    grammar_file = NamedTemporaryFile(suffix=".bnf")
    grammar_file.write(unparse_grammar(grammar).encode("utf-8"))
    grammar_file.seek(0)
    return grammar_file


class TestCli(unittest.TestCase):
    def test_version(self):
        stdout, stderr, code = run_isla("-v")
        self.assertFalse(code)
        self.assertFalse(stderr)
        self.assertEqual(isla_version, stdout.split(" ")[-1].strip())

    def test_solve_no_grammar_no_constraing(self):
        stdout, stderr, code = run_isla("solve", "-n", -1, "-t", 10)

        self.assertEqual(2, code)
        self.assertFalse(stdout)
        self.assertTrue("must specify a grammar" in stderr)

    def test_solve_no_grammar(self):
        constraint_file = NamedTemporaryFile(suffix=".isla")

        stdout, stderr, code = run_isla(
            "solve", constraint_file.name, "-n", -1, "-t", 10
        )

        self.assertEqual(2, code)
        self.assertFalse(stdout)
        self.assertTrue("must specify a grammar" in stderr)

        constraint_file.close()

    def test_solve_no_constraint(self):
        grammar_file = NamedTemporaryFile(suffix=".bnf")

        stdout, stderr, code = run_isla("solve", grammar_file.name, "-n", -1, "-t", 10)

        self.assertEqual(2, code)
        self.assertFalse(stdout)
        self.assertTrue("must specify a constraint" in stderr)

        grammar_file.close()

    def test_solve_assgn_lang(self):
        grammar_1 = {nt: exp for nt, exp in LANG_GRAMMAR.items() if ord(nt[1]) <= 114}
        grammar_2 = {nt: exp for nt, exp in LANG_GRAMMAR.items() if ord(nt[1]) > 114}
        self.assertEqual(len(grammar_1), len(grammar_2))
        self.assertEqual(LANG_GRAMMAR, grammar_1 | grammar_2)

        grammar_file_1 = write_grammar_file(grammar_1)
        grammar_file_2 = write_grammar_file(grammar_2)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        stdout, stderr, code = run_isla(
            "solve",
            grammar_file_1.name,
            constraint_file.name,
            grammar_file_2.name,
            "-n",
            -1,
            "-t",
            4,
        )

        self.assertFalse(code)
        self.assertFalse(stderr)
        self.assertTrue(stdout)

        solver = ISLaSolver(LANG_GRAMMAR, constraint)
        for line in stdout.split("\n"):
            if line.isnumeric():
                self.assertEqual(ISLaSolver.TIMEOUT, int(line))
                break

            self.assertTrue(solver.evaluate(line))

        grammar_file_1.close()
        grammar_file_2.close()
        constraint_file.close()


if __name__ == "__main__":
    unittest.main()
