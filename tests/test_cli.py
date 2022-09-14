import io
import os
import string
import tempfile
import unittest
from tempfile import NamedTemporaryFile
from typing import Tuple

import pytest

from isla import __version__ as isla_version
from isla import cli
from isla.cli import DATA_FORMAT_ERROR
from isla.language import unparse_grammar
from isla.solver import (
    ISLaSolver,
)
from isla.type_defs import Grammar
from test_data import LANG_GRAMMAR


def run_isla(*args) -> Tuple[str, str, int]:
    stdout, stderr = io.StringIO(), io.StringIO()
    try:
        cli.main(*[str(arg) for arg in args], stdout=stdout, stderr=stderr)
        code = 0
    except SystemExit as sys_exit:
        code = sys_exit.code

    return stdout.getvalue().strip(), stderr.getvalue().strip(), code


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
            self.assertTrue(solver.evaluate(line))

        grammar_file_1.close()
        grammar_file_2.close()
        constraint_file.close()

    def test_solve_assgn_lang_parameter_grammar(self):
        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""

        stdout, stderr, code = run_isla(
            "solve",
            "--grammar",
            " ".join(unparse_grammar(LANG_GRAMMAR).split("\n")),
            "--constraint",
            " ".join(constraint.split("\n")),
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
            self.assertTrue(solver.evaluate(line))

    def test_solve_assgn_lang_output_directory(self):
        grammar_1 = {nt: exp for nt, exp in LANG_GRAMMAR.items() if ord(nt[1]) <= 114}
        grammar_2 = {nt: exp for nt, exp in LANG_GRAMMAR.items() if ord(nt[1]) > 114}
        self.assertEqual(len(grammar_1), len(grammar_2))
        self.assertEqual(LANG_GRAMMAR, grammar_1 | grammar_2)

        grammar_file_1 = write_grammar_file(grammar_1)
        grammar_file_2 = write_grammar_file(grammar_2)

        out_dir = tempfile.TemporaryDirectory()

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
            "-d",
            out_dir.name,
        )

        self.assertFalse(code)
        self.assertFalse(stderr)
        self.assertFalse(stdout)

        files = os.listdir(out_dir.name)
        self.assertTrue(files)

        solver = ISLaSolver(LANG_GRAMMAR, constraint)
        for file_name in files:
            with open(os.path.join(out_dir.name, file_name), "rb") as file:
                self.assertTrue(solver.evaluate(file.read().decode("utf-8")))

        grammar_file_1.close()
        grammar_file_2.close()
        constraint_file.close()
        out_dir.cleanup()

    def test_solve_parser_errors_grammar(self):
        stdout, stderr, code = run_isla(
            "solve", "--grammar", "<start> ::=", "--constraint", "true"
        )

        self.assertEqual(DATA_FORMAT_ERROR, code)
        self.assertFalse(stdout)
        self.assertTrue("ParseCancellationException" in stderr)
        self.assertTrue("parsing the grammar" in stderr)

    def test_solve_parser_errors_constraint(self):
        stdout, stderr, code = run_isla(
            "solve",
            "--grammar",
            '<start> ::= <a> <a> ::= "A"',
            "--constraint",
            "salami",
        )

        self.assertEqual(DATA_FORMAT_ERROR, code)
        self.assertFalse(stdout)
        self.assertTrue("SyntaxError" in stderr)
        self.assertTrue("parsing the constraint" in stderr)

    def test_solve_unsat(self):
        stdout, stderr, code = run_isla(
            "solve",
            "--grammar",
            '<start> ::= <a> <a> ::= "A"',
            "--constraint",
            'exists <a>: <a> = "B"',
        )

        self.assertFalse(code)
        self.assertFalse(stdout)
        self.assertEqual("UNSAT", stderr)

    @pytest.mark.skip("TODO")
    def test_fuzz_bash(self):
        grammar = f"""
<start> ::= <lines>
<lines> ::= <line> "\n" <lines> | <line>
<line> ::= <echo> | <exit>
<echo> ::= "echo " <string>
<exit> ::= "exit " <code>
<string> ::= "\\"" <chars> "\\""
<chars> ::= <char><chars> | <char>
<char> ::= {" | ".join(map(lambda c: '"' + c + '"', set(string.ascii_letters).union([' '])))}
<code> ::= "0" | "1" | "2"
"""

        constraint = 'exists <code>: not <code> = "0"'

        out_dir = tempfile.TemporaryDirectory()

        stdout, stderr, code = run_isla(
            "fuzz",
            "bash {}",
            "-e",
            ".sh",
            "--grammar",
            " ".join(grammar.split("\n")),
            "--constraint",
            " ".join(constraint.split("\n")),
            "-d",
            out_dir.name,
            "-n",
            -1,
            "-t",
            4,
        )

        out_dir.cleanup()


if __name__ == "__main__":
    unittest.main()
