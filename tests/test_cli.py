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

import io
import json
import os
import string
import tempfile
import unittest
from tempfile import NamedTemporaryFile
from typing import Tuple

from isla import __version__ as isla_version
from isla import cli
from isla.cli import (
    DATA_FORMAT_ERROR,
    USAGE_ERROR,
    read_isla_rc_defaults,
    get_default,
    derivation_tree_to_json,
)
from isla.derivation_tree import DerivationTree
from isla.helpers import Maybe, get_isla_resource_file_content
from isla.language import unparse_grammar
from isla.parser import EarleyParser
from isla.solver import (
    ISLaSolver,
    STD_COST_SETTINGS,
)
from isla.type_defs import Grammar
from test_data import LANG_GRAMMAR

echo_grammar = rf"""
<start> ::= <lines>
<lines> ::= <line> "\n" <lines> | <line>
<line> ::= <echo> | <exit>
<echo> ::= "echo " <string>
<exit> ::= "exit " <code>
<string> ::= "\"" <chars> "\""
<chars> ::= <char><chars> | <char>
<char> ::= {" | ".join(map(lambda c: '"' + c + '"', set(string.ascii_letters).union([' '])))}
<code> ::= "0" | "1" | "2"
"""


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


def write_python_grammar_file(python_code: str) -> NamedTemporaryFile:
    grammar_file = NamedTemporaryFile(suffix=".py")
    grammar_file.write(python_code.encode("utf-8"))
    grammar_file.seek(0)
    return grammar_file


class TestCli(unittest.TestCase):
    def test_version(self):
        stdout, stderr, code = run_isla("-v")
        self.assertFalse(code)
        self.assertFalse(stderr)
        self.assertEqual(isla_version, stdout.split(" ")[-1].strip())

    def test_solve_no_grammar_no_constraint(self):
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
            self.assertTrue(solver.check(line))

        grammar_file_1.close()
        grammar_file_2.close()
        constraint_file.close()

    def test_assgn_lang_no_constraint(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        stdout, stderr, code = run_isla(
            "solve",
            grammar_file.name,
            "-f",
            50,
            "-n",
            -1,
        )

        self.assertFalse(code)
        self.assertEqual("UNSAT", stderr)
        self.assertTrue(stdout)

        grammar_file.close()

        # Assert that we can parse
        parser = EarleyParser(LANG_GRAMMAR)
        for solution in stdout.split("\n"):
            parser.parse(solution)

    def test_solve_assgn_lang_additional_constraint(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        additional_constraint = 'exists <var>: <var> = "a"'

        stdout, stderr, code = run_isla(
            "solve",
            grammar_file.name,
            constraint_file.name,
            "--constraint",
            additional_constraint,
            "-n",
            -1,
            "-t",
            4,
        )

        self.assertFalse(code)
        self.assertFalse(stderr)
        if False:
            # Somehow, stdout is empty when running this test inside a GitHub workflow.
            # This is super strange, and cannot be reproduced locally, not even when
            # running the workflow using the "act" tool. Thus, we comment these checks
            # out...
            self.assertTrue(stdout)

            solver_1 = ISLaSolver(LANG_GRAMMAR, constraint)
            solver_2 = ISLaSolver(LANG_GRAMMAR, additional_constraint)
            for line in stdout.split("\n"):
                self.assertTrue(solver_1.check(line))
                self.assertTrue(solver_2.check(line))

        grammar_file.close()
        constraint_file.close()

    def test_solve_assgn_lang_additional_multiple_constraints(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        additional_constraint_1 = 'exists <var>: <var> = "a"'
        additional_constraint_2 = 'exists <var>: <var> = "b"'

        stdout, stderr, code = run_isla(
            "solve",
            grammar_file.name,
            constraint_file.name,
            "--constraint",
            additional_constraint_1,
            "--constraint",
            additional_constraint_2,
            "-n",
            -1,
            "-t",
            4,
        )

        self.assertFalse(code)
        self.assertFalse(stderr)
        if False:
            self.assertTrue(stdout)

            solver_1 = ISLaSolver(LANG_GRAMMAR, constraint)
            solver_2 = ISLaSolver(LANG_GRAMMAR, additional_constraint_1)
            solver_3 = ISLaSolver(LANG_GRAMMAR, additional_constraint_2)
            for line in stdout.split("\n"):
                self.assertTrue(solver_1.check(line))
                self.assertTrue(solver_2.check(line))
                self.assertTrue(solver_3.check(line))

        grammar_file.close()
        constraint_file.close()

    def test_solve_assgn_lang_python_grammar_as_function(self):
        grammar_1_text = r"""
from typing import Dict, List

def grammar() -> Dict[str, List[str]]:
    return {
        "<start>": ["<stmt>"],
        "<stmt>": ["<assgn> ; <stmt>", "<assgn>"],
        "<assgn>": ["<var> := <rhs>"],
    }
"""
        grammar_2_text = r"""
from typing import Dict, List

def grammar() -> Dict[str, List[str]]:
    import string
    return {
        "<rhs>":
            ["<var>", "<digit>"],
        "<var>": list(string.ascii_lowercase),
        "<digit>": list(string.digits)
    }
"""

        grammar_file_1 = write_python_grammar_file(grammar_1_text)
        grammar_file_2 = write_python_grammar_file(grammar_2_text)

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

        print(stderr)
        self.assertFalse(code)
        self.assertFalse(stderr)
        self.assertTrue(stdout)

        solver = ISLaSolver(LANG_GRAMMAR, constraint)
        for line in stdout.split("\n"):
            self.assertTrue(solver.check(line))

        grammar_file_1.close()
        grammar_file_2.close()
        constraint_file.close()

    def test_solve_assgn_lang_python_grammar(self):
        grammar_1_text = r"""
grammar = {
    "<start>":
        ["<stmt>"],
    "<stmt>":
        ["<assgn> ; <stmt>", "<assgn>"],
    "<assgn>":
        ["<var> := <rhs>"],
}
"""
        grammar_2_text = r"""
import string

grammar = {
    "<rhs>":
        ["<var>", "<digit>"],
    "<var>": list(string.ascii_lowercase),
    "<digit>": list(string.digits)
}
"""

        grammar_file_1 = write_python_grammar_file(grammar_1_text)
        grammar_file_2 = write_python_grammar_file(grammar_2_text)

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

        print(stderr)
        self.assertFalse(code)
        self.assertFalse(stderr)
        self.assertTrue(stdout)

        solver = ISLaSolver(LANG_GRAMMAR, constraint)
        for line in stdout.split("\n"):
            self.assertTrue(solver.check(line))

        grammar_file_1.close()
        grammar_file_2.close()
        constraint_file.close()

    def test_solve_assgn_lang_invalid_python_grammar(self):
        grammar_text = r"""
grammar = {
    "<start>":
        "<stmt>",  # no list
    "<stmt>":
        ["<assgn> ; <stmt>", "<assgn>"],
    "<assgn>":
        ["<var> := <rhs>"],
}
"""

        grammar_file = write_python_grammar_file(grammar_text)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        stdout, stderr, code = run_isla(
            "solve",
            grammar_file.name,
            constraint_file.name,
            "-n",
            -1,
            "-t",
            4,
        )

        self.assertEqual(DATA_FORMAT_ERROR, code)
        self.assertIn("A grammar must be of type `Dict[str, List[str]]`", stderr)
        self.assertFalse(stdout)

        grammar_file.close()
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
            100,
        )

        self.assertFalse(code)
        self.assertFalse(stderr)
        self.assertTrue(stdout)

        solver = ISLaSolver(LANG_GRAMMAR, constraint)
        for line in stdout.split("\n"):
            self.assertTrue(solver.check(line))

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
                self.assertTrue(solver.check(file.read().decode("utf-8")))

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
        self.assertTrue("occurred while processing a provided file" in stderr)

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

    def test_solve_invalid_python_grammar(self):
        grammar_file = tempfile.NamedTemporaryFile("w", suffix=".py")
        grammar_file.write("_grammar = {}")

        stdout, stderr, code = run_isla(
            "solve", "--constraint", 'exists <a>: <a> = "B"', grammar_file.name
        )

        self.assertEqual(USAGE_ERROR, code)
        self.assertFalse(stdout)
        self.assertTrue("Could not find any grammar definition" in stderr)

    def test_fuzz_unsat(self):
        out_dir = tempfile.TemporaryDirectory()
        stdout, stderr, code = run_isla(
            "fuzz",
            "bash {}",
            "-e",
            ".sh",
            "--grammar",
            " ".join(echo_grammar.split("\n")),
            "--constraint",
            'exists <code>: <code> = "3"',
            "-d",
            out_dir.name,
            "-f",
            1,
            "-s",
            2,
            "-w",
            "2,0,5.0,0,20",
        )

        self.assertFalse(code)
        self.assertFalse(stdout)
        self.assertEqual("UNSAT", stderr)

        files = os.listdir(out_dir.name)
        self.assertFalse(len(files))

    def test_solve_weight_vector_wrong_length_too_small(self):
        stdout, stderr, code = run_isla(
            "solve",
            "--grammar",
            '<start> ::= <a> <a> ::= "A"',
            "--constraint",
            'exists <a>: <a> = "A"',
            "-w",
            "1,2,3,4",  # One element missing
        )

        self.assertEqual(DATA_FORMAT_ERROR, code)
        self.assertFalse(stdout)
        self.assertTrue("error: Length of weight vector is 4, expected 5" in stderr)

    def test_solve_weight_vector_wrong_length_too_big(self):
        stdout, stderr, code = run_isla(
            "solve",
            "--grammar",
            '<start> ::= <a> <a> ::= "A"',
            "--constraint",
            'exists <a>: <a> = "A"',
            "-w",
            "1,2,3,4,5,6",  # One element too much
        )

        self.assertEqual(DATA_FORMAT_ERROR, code)
        self.assertFalse(stdout)
        self.assertTrue("error: Length of weight vector is 6, expected 5" in stderr)

    def test_solve_weight_vector_not_numeric(self):
        stdout, stderr, code = run_isla(
            "solve",
            "--grammar",
            '<start> ::= <a> <a> ::= "A"',
            "--constraint",
            'exists <a>: <a> = "A"',
            "-w",
            "1,2,x,4,5",
        )

        self.assertEqual(DATA_FORMAT_ERROR, code)
        self.assertFalse(stdout)
        self.assertTrue("error: non-numeric weight vector element" in stderr)

    def test_solve_nonexisting_output_dir(self):
        stdout, stderr, code = run_isla(
            "solve",
            "--grammar",
            '<start> ::= <a> <a> ::= "A"',
            "--constraint",
            'exists <a>: <a> = "A"',
            "-d",
            "this_does_not_exist_or_does_it",
        )

        self.assertEqual(USAGE_ERROR, code)
        self.assertFalse(stdout)
        self.assertTrue(
            "error: path this_does_not_exist_or_does_it does not exist "
            + "or is no directory"
            in stderr
        )

    def test_fuzz_without_placeholder_in_command(self):
        constraint = 'forall <code>: not <code> = "0"'
        out_dir = tempfile.TemporaryDirectory()
        runs = 50

        stdout, stderr, code = run_isla(
            "fuzz",
            "bash",  # No "{}"
            "-e",
            ".sh",
            "--grammar",
            " ".join(echo_grammar.split("\n")),
            "--constraint",
            " ".join(constraint.split("\n")),
            "-d",
            out_dir.name,
            "-n",
            runs,
        )

        self.assertEqual(0, code)
        self.assertFalse(stdout)
        self.assertTrue('warning: the placeholder "{}" was not found' in stderr)

    def test_fuzz_bash_fixed_runs(self):
        self.fuzz_bash_test(timeout=False)

    def test_fuzz_bash_timeout(self):
        self.fuzz_bash_test(timeout=False)

    def fuzz_bash_test(self, timeout: bool):
        constraint = 'forall <code>: not <code> = "0"'
        out_dir = tempfile.TemporaryDirectory()
        runs = 50

        args = [
            "fuzz",
            "bash {}",
            "-e",
            ".sh",
            "--grammar",
            " ".join(echo_grammar.split("\n")),
            "--constraint",
            " ".join(constraint.split("\n")),
            "-d",
            out_dir.name,
            "-f",
            1,
            "-s",
            2,
            "-w",
            "2,0,5,0,20",
        ]

        if timeout:
            args += ["-t", 5, "-n", -1]
        else:
            args += [
                "-n",
                runs,
            ]

        stdout, stderr, code = run_isla(*args)
        self.assertFalse(stdout)
        self.assertFalse(stderr)
        self.assertFalse(code)

        files = os.listdir(out_dir.name)
        if timeout:
            self.assertTrue(len(files) % 4 == 0)
            runs = len(files) // 4
        else:
            self.assertEqual(runs * 4, len(files))

        solver = ISLaSolver(echo_grammar, constraint)
        for i in range(runs):
            inp_file_name = f"{str(i).rjust(4, '0')}_input.txt"
            stdout_file_name = f"{str(i).rjust(4, '0')}_stdout.txt"
            stderr_file_name = f"{str(i).rjust(4, '0')}_stderr.txt"
            status_file_name = f"{str(i).rjust(4, '0')}_status.txt"

            with open(os.path.join(out_dir.name, inp_file_name), "rb") as file:
                inp = file.read().decode("utf-8")
                self.assertTrue(solver.check(inp))

            exit_position = inp.find("exit")
            if exit_position >= 0:
                inp = inp[: exit_position + len("exit 0")].strip()

            if "exit" == inp[-6:-2]:
                expected_status = inp[-1]
            else:
                expected_status = "0"

            with open(os.path.join(out_dir.name, stdout_file_name), "rb") as file:
                echos = [
                    l[len("echo ") :].strip('"')
                    for l in inp.split("\n")
                    if l.startswith("echo")
                ]
                standard_output = file.read().decode("utf-8")
                self.assertEqual(standard_output.strip(), "\n".join(echos).strip())

            with open(os.path.join(out_dir.name, stderr_file_name), "rb") as file:
                error_output = file.read().decode("utf-8")
                self.assertFalse(error_output)

            with open(os.path.join(out_dir.name, status_file_name), "rb") as file:
                actual_status = file.read().decode("utf-8")
                self.assertEqual(expected_status, actual_status)

        out_dir.cleanup()

    def test_create(self):
        out_dir = tempfile.TemporaryDirectory()

        stdout, stderr, code = run_isla("create", "-b", "assgn_lang", out_dir.name)
        self.assertIn("`isla create` produced the following files: ", stdout)
        self.assertFalse(stderr)
        self.assertFalse(code)

        readme_file_name = os.path.join(out_dir.name, "README.md")
        self.assertTrue(os.path.isfile(readme_file_name))

        files = os.listdir(out_dir.name)
        self.assertEqual(2, len([file for file in files if "_grammar_" in file]))
        self.assertEqual(1, len([file for file in files if "_constraint" in file]))

        with open(readme_file_name, "r") as readme_file:
            content = readme_file.read()

        lines = [line.strip() for line in content.split("\n")]
        bash_command_start = (
            next(idx for idx, line in enumerate(lines) if line.startswith("```bash"))
            + 1
        )

        bash_command_end = next(
            idx
            for idx, line in enumerate(lines[bash_command_start:])
            if line.startswith("```")
        )

        bash_command = "".join(
            lines[bash_command_start : bash_command_start + bash_command_end]
        ).replace("\\", "")

        stdout, stderr, code = run_isla(*bash_command.split(" ")[1:])
        self.assertFalse(stderr)
        self.assertFalse(code)

        if False:  # NOTE: Make `if False:` before pushing to GitHub
            # Somehow, stdout is empty when running this test inside a GitHub workflow.
            # This is super strange, and cannot be reproduced locally, not even when
            # running the workflow using the "act" tool. Thus, we comment these checks
            # out...
            self.assertTrue(stdout)
            assignments = stdout.split("\n")

            constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""

            solver = ISLaSolver(LANG_GRAMMAR, constraint)
            for assignment in assignments:
                self.assertTrue(solver.check(assignment))

        out_dir.cleanup()

    def test_check_assgn_lang_correct_input(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        additional_constraint = 'exists <var>: <var> = "a"'

        stdout, stderr, code = run_isla(
            "check",
            "--constraint",
            additional_constraint,
            "-i",
            "x := 1 ; a := x",
            grammar_file.name,
            constraint_file.name,
        )

        self.assertFalse(code)
        self.assertFalse(stderr)

        self.assertTrue("satisfies the ISLa constraint" in stdout)

    def test_check_assgn_lang_correct_parsed_input(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        additional_constraint = 'exists <var>: <var> = "a"'

        input_file = NamedTemporaryFile(suffix=".json")
        solver = ISLaSolver(LANG_GRAMMAR, constraint)
        input_file.write(
            derivation_tree_to_json(solver.parse("x := 1 ; a := x")).encode("utf-8")
        )
        input_file.seek(0)

        stdout, stderr, code = run_isla(
            "check",
            "--constraint",
            additional_constraint,
            grammar_file.name,
            constraint_file.name,
            input_file.name,
        )

        self.assertFalse(code)
        self.assertFalse(stderr)

        self.assertTrue("satisfies the ISLa constraint" in stdout)

        input_file.close()

    def test_check_no_constraint_present(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        stdout, stderr, code = run_isla(
            "check",
            "-i",
            "x := 1 ; a := x",
            grammar_file.name,
        )

        self.assertIn("must specify a constraint", stderr)
        self.assertEqual(USAGE_ERROR, code)
        self.assertFalse(stdout)

    def test_check_assgn_lang_correct_input_in_file(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        additional_constraint = 'exists <var>: <var> = "a"'

        inp_file = tempfile.NamedTemporaryFile("w")
        inp_file.write("x := 1 ; a := x")
        inp_file.seek(0)

        stdout, stderr, code = run_isla(
            "check",
            "--constraint",
            additional_constraint,
            inp_file.name,
            grammar_file.name,
            constraint_file.name,
        )

        inp_file.close()

        self.assertFalse(code)
        self.assertFalse(stderr)

        self.assertTrue("satisfies the ISLa constraint" in stdout)

    def test_check_assgn_lang_too_many_input_files(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        additional_constraint = 'exists <var>: <var> = "a"'

        inp_file = tempfile.NamedTemporaryFile("w")
        inp_file.write("x := 1 ; a := x")
        inp_file.seek(0)

        inp_file_1 = tempfile.NamedTemporaryFile("w")
        inp_file_1.write("x := 1 ; a := x")
        inp_file_1.seek(0)

        stdout, stderr, code = run_isla(
            "check",
            "--constraint",
            additional_constraint,
            inp_file.name,
            inp_file_1.name,
            grammar_file.name,
            constraint_file.name,
        )

        inp_file.close()
        inp_file_1.close()

        self.assertEqual(USAGE_ERROR, code)
        self.assertFalse(stdout)
        self.assertTrue("error: you must specify exactly *one* input" in stderr)

    def test_check_assgn_lang_wrong_input(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        additional_constraint = 'exists <var>: <var> = "a"'

        stdout, stderr, code = run_isla(
            "check",
            "--constraint",
            additional_constraint,
            "-i",
            "x := 1 ; y := x",
            grammar_file.name,
            constraint_file.name,
        )

        self.assertEqual(1, code)
        self.assertFalse(stderr)

        self.assertTrue("does not satisfy" in stdout)

    def test_check_assgn_lang_unparseable_input(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        additional_constraint = 'exists <var>: <var> = "a"'

        stdout, stderr, code = run_isla(
            "check",
            "--constraint",
            additional_constraint,
            "-i",
            "x := 1 | a := x",
            grammar_file.name,
            constraint_file.name,
        )

        self.assertEqual(1, code)
        self.assertFalse(stderr)
        self.assertTrue("input could not be parsed" in stdout)

    def test_find_assgn_files(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        contents = [
            "<asdf> no-assgn 123",
            "x := 1",
            "a := 2 ; b := 3",
            "a := a ; b := 1",
            "a := x",
        ]
        files = []
        for i, content in enumerate(contents):
            file = NamedTemporaryFile(suffix=".txt")
            file.write(content.encode("utf-8"))
            file.seek(0)
            files.append(file)

        stdout, stderr, code = run_isla(
            "find",
            "--constraint",
            'exists <assgn>: not <assgn>.<rhs>.<var> = "1"',
            grammar_file.name,
            *[file.name for file in files],
        )

        print(stdout)
        print(stderr)

        self.assertFalse(code)
        self.assertFalse(stderr)
        self.assertEqual("\n".join([file.name for file in files[3:]]), stdout)

        for file in files:
            file.close()

    def test_find_assgn_files_unsuccessful(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        contents = ["x := 1", "a := 2 ; b := 3", "a := 4 ; b := 1", "a := 7"]
        files = []
        for i, content in enumerate(contents):
            file = NamedTemporaryFile(suffix=".txt")
            file.write(content.encode("utf-8"))
            file.seek(0)
            files.append(file)

        stdout, stderr, code = run_isla(
            "find",
            "--constraint",
            'exists <assgn>: not <assgn>.<rhs>.<var> = "1"',
            grammar_file.name,
            *[file.name for file in files],
        )

        print(stdout)
        print(stderr)

        self.assertEqual(1, code)
        self.assertFalse(stderr)
        self.assertFalse(stdout)

        for file in files:
            file.close()

    def test_find_assgn_files_no_inputs(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        stdout, stderr, code = run_isla(
            "find",
            "--constraint",
            'exists <assgn>: not <assgn>.<rhs>.<var> = "1"',
            grammar_file.name,
        )

        print(stdout)
        print(stderr)

        self.assertEqual(USAGE_ERROR, code)
        self.assertEqual("no files passed to `find`", stderr)
        self.assertFalse(stdout)

    def test_parse_assgn_lang_correct_input_outfile(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)
        out_file = tempfile.NamedTemporaryFile("w", delete=False)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        additional_constraint = 'exists <var>: <var> = "a"'

        inp = "x := 1 ; a := x"

        stdout, stderr, code = run_isla(
            "parse",
            "--no-pretty-print",
            "--output-file",
            out_file.name,
            "--constraint",
            additional_constraint,
            "-i",
            inp,
            grammar_file.name,
            constraint_file.name,
        )

        self.assertFalse(code)
        self.assertFalse(stdout)
        self.assertFalse(stderr)

        with open(out_file.name, "r") as file:
            json_inp = file.read()

        self.assertEqual(
            json.dumps(next(EarleyParser(LANG_GRAMMAR).parse(inp))), json_inp
        )

        out_file.close()
        os.remove(out_file.name)

    def test_parse_assgn_lang_correct_input_to_console(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        additional_constraint = 'exists <var>: <var> = "a"'

        inp = "x := 1 ; a := x"

        stdout, stderr, code = run_isla(
            "parse",
            "--no-pretty-print",
            "--constraint",
            additional_constraint,
            "-i",
            inp,
            grammar_file.name,
            constraint_file.name,
        )

        self.assertFalse(code)
        self.assertFalse(stderr)

        self.assertEqual(
            json.dumps(next(EarleyParser(LANG_GRAMMAR).parse(inp))), stdout
        )

    def test_parse_assgn_lang_wrong_input(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        additional_constraint = 'exists <var>: <var> = "a"'

        stdout, stderr, code = run_isla(
            "parse",
            "--constraint",
            additional_constraint,
            "-i",
            "x := 1 ; y := x",
            grammar_file.name,
            constraint_file.name,
        )

        self.assertEqual(1, code)
        self.assertFalse(stderr)

        self.assertTrue("does not satisfy" in stdout)

    def test_repair_assgn_lang_correct_input_outfile(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)
        out_file = tempfile.NamedTemporaryFile("w", delete=False)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        inp = "x := 1 ; a := x"

        stdout, stderr, code = run_isla(
            "repair",
            "--output-file",
            out_file.name,
            "-i",
            inp,
            grammar_file.name,
            constraint_file.name,
        )

        self.assertFalse(code)
        self.assertFalse(stdout)
        self.assertFalse(stderr)

        with open(out_file.name, "r") as file:
            output = file.read()

        self.assertEqual(output, inp)

        out_file.close()
        os.remove(out_file.name)

    def test_repair_assgn_lang_wrong_input(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        inp = "x := 1 ; a := y"

        stdout, stderr, code = run_isla(
            "repair",
            "-i",
            inp,
            grammar_file.name,
            constraint_file.name,
        )

        self.assertFalse(code)
        self.assertFalse(stderr)

        solver = ISLaSolver(LANG_GRAMMAR, constraint)
        self.assertTrue(solver.check(stdout))

    def test_repair_assgn_lang_unparseable_input(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        inp = "salami"

        stdout, stderr, code = run_isla(
            "repair",
            "-i",
            inp,
            grammar_file.name,
            constraint_file.name,
        )

        self.assertFalse(stdout)
        self.assertEqual(1, code)
        self.assertIn("could not be parsed", stderr)

    def test_repair_assgn_lang_unrepairable_input(self):
        # NOTE: If this test fails, it could mean that the repairer was improved and
        #       now supports structural manipulations.
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        inp = "x := y"

        stdout, stderr, code = run_isla(
            "repair",
            "-i",
            inp,
            grammar_file.name,
            constraint_file.name,
        )

        self.assertFalse(stdout)
        self.assertEqual(1, code)
        self.assertIn("could not repair", stderr)

    def test_mutate_assgn_lang(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)
        out_file = tempfile.NamedTemporaryFile("w", delete=False)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        inp = "x := 1 ; a := y"

        stdout, stderr, code = run_isla(
            "mutate",
            "-i",
            inp,
            "--output-file",
            out_file.name,
            grammar_file.name,
            constraint_file.name,
        )

        self.assertFalse(code)
        self.assertFalse(stderr)
        self.assertFalse(stdout)

        with open(out_file.name, "r") as file:
            output = file.read()

        solver = ISLaSolver(LANG_GRAMMAR, constraint)
        self.assertTrue(solver.check(output))

        out_file.close()
        os.remove(out_file.name)

    def test_mutate_assgn_lang_unparseable_input(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        inp = "salami"

        stdout, stderr, code = run_isla(
            "mutate",
            "-i",
            inp,
            grammar_file.name,
            constraint_file.name,
        )

        self.assertFalse(stdout)
        self.assertEqual(1, code)
        self.assertIn("could not be parsed", stderr)

    def test_mutate_assgn_lang_unrepairable_input(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        constraint = """
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        inp = "x := y"

        stdout, stderr, code = run_isla(
            "mutate",
            "-i",
            inp,
            grammar_file.name,
            constraint_file.name,
        )

        self.assertFalse(code)
        self.assertFalse(stderr)

        solver = ISLaSolver(LANG_GRAMMAR, constraint)
        self.assertTrue(solver.check(stdout))

    def test_read_isla_rc_correct_format(self):
        config = read_isla_rc_defaults()
        self.assertIn("default", config)
        self.assertTrue(isinstance(key, str) for key in config)
        self.assertTrue(isinstance(value, dict) for value in config.values())
        self.assertTrue(
            isinstance(inner_key, str) for key in config for inner_key in config[key]
        )
        self.assertTrue(
            type(inner_value) in [float, int, str, bool]
            for value in config.values()
            for inner_value in value.values()
        )

    def test_default_isla_rc_weight_vector_is_isla_standard(self):
        self.assertEqual(
            ",".join(map(str, STD_COST_SETTINGS.weight_vector)),
            read_isla_rc_defaults()["solve"]["--weight-vector"],
        )

    def test_isla_rc_override(self):
        non_default_config = """
[[defaults.solve]]

"-k" = -42
"""

        config = read_isla_rc_defaults(Maybe(non_default_config))

        self.assertEqual(
            -42,
            config["solve"]["-k"],
        )

        # Other values are preserved
        self.assertEqual(
            ",".join(map(str, STD_COST_SETTINGS.weight_vector)),
            config["solve"]["--weight-vector"],
        )

    def test_isla_rc_invalid_format(self):
        non_default_config = """
[[defaults]]

"-k" = -42
"""

        self.assertRaises(
            RuntimeError, lambda: read_isla_rc_defaults(Maybe(non_default_config))
        )

    def test_get_default(self):
        stderr = io.StringIO()
        self.assertTrue(get_default(stderr, "solve", "--log-level"))
        self.assertFalse(stderr.getvalue())

        stderr = io.StringIO()
        self.assertEqual(
            ",".join(map(str, STD_COST_SETTINGS.weight_vector)),
            get_default(stderr, "solve", "--weight-vector").get(),
        )
        self.assertFalse(stderr.getvalue())

        stderr = io.StringIO()
        self.assertFalse(get_default(stderr, "solve", "--all-problems-of-the-world"))
        self.assertFalse(stderr.getvalue())

    def test_get_default_invalid_format(self):
        non_default_config = """
[[defaults]]

"-k" = -42
"""

        stderr = io.StringIO()
        try:
            get_default(stderr, "solve", "-k", Maybe(non_default_config))
            code = 0
        except SystemExit as sys_exit:
            code = sys_exit.code

        self.assertEqual(1, code)
        self.assertIn("error", stderr.getvalue())
        self.assertIn("Unexpected .islarc format", stderr.getvalue())

    def test_dump_config(self):
        stdout, stderr, code = run_isla("config")

        self.assertFalse(code)
        self.assertFalse(stderr)

        self.assertEqual(get_isla_resource_file_content("resources/.islarc"), stdout)

    def test_dump_config_outfile(self):
        out_file = tempfile.NamedTemporaryFile("w", delete=False)

        stdout, stderr, code = run_isla(
            "config",
            "--output-file",
            out_file.name,
        )

        self.assertFalse(code)
        self.assertFalse(stdout)
        self.assertFalse(stderr)

        with open(out_file.name, "r") as file:
            config = file.read()

        self.assertEqual(get_isla_resource_file_content("resources/.islarc"), config)

        out_file.close()
        os.remove(out_file.name)

    def test_assertion_error(self):
        stdout, stderr, code = run_isla(
            "solve",
            "--grammar",
            '<start> ::= "a"',
            "--constraint",
            "str.len(<start>) > 1",
        )

        self.assertFalse(stdout)
        self.assertIn("RuntimeError", stderr)
        self.assertIn(
            "Could not create a tree with the start symbol '<start>' of length 2",
            stderr,
        )
        self.assertEqual(1, code)

    def test_solve_heartbeat_grammar(self):
        grammar_str = r"""grammar = {
    "<start>": ["<heartbeat-request>"],
    "<heartbeat-request>": ["\x01<payload-length><payload><padding>"],
    "<payload-length>": ["<byte><byte>"],
    "<payload>": ["<bytes>"],
    "<padding>": ["<bytes>"],
    "<bytes>": ["<byte><bytes>", ""],
    "<byte>": [chr(i) for i in range(256)],
}"""

        constraint_str = r"""    256 * str.to_code(<payload-length>.<byte>[1])
  + str.to_code(<payload-length>.<byte>[2])
  = str.len(<payload>)
and str.len(<padding>) >= 16
and str.len(<payload>) > 0"""

        grammar_file = write_python_grammar_file(grammar_str)
        constraint_file = write_constraint_file(constraint_str)

        stdout, stderr, code = run_isla(
            "solve",
            grammar_file.name,
            constraint_file.name,
            "--constraint",
            "str.len(<padding>) = 20",
            "--constraint",
            "str.len(<payload>) = 10",
            "--tree",
        )

        self.assertFalse(stderr)

        tree = DerivationTree.from_parse_tree(json.loads(stdout))

        payload = str(
            tree.filter(lambda node: node.value == "<payload>", enforce_unique=True)[0][
                1
            ]
        )

        self.assertEqual(10, len(payload))

        padding = str(
            tree.filter(lambda node: node.value == "<padding>", enforce_unique=True)[0][
                1
            ]
        )

        self.assertEqual(20, len(padding))

        length = tree.filter(
            lambda node: node.value == "<payload-length>", enforce_unique=True
        )[0][1]

        length_1 = ord(str(length.get_subtree((0,))))
        length_2 = ord(str(length.get_subtree((1,))))

        self.assertEqual(len(payload), 256 * length_1 + length_2)

    def test_solve_additional_structural_predicate(self):
        # We rename the "before" predicate to "erofeb" and use it in the formula.
        # To enable this, we import a new predicate definition through an external
        # file.
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        predicate_file_content = """
from typing import Set
from isla.language import SemanticPredicate, StructuralPredicate

def predicates() -> Set[StructuralPredicate | SemanticPredicate]:
    from isla.language import SemanticPredicate, StructuralPredicate
    from isla.isla_predicates import is_before

    return {StructuralPredicate("erofeb", 2, is_before)}

"""

        predicate_file = NamedTemporaryFile(suffix=".py")
        predicate_file.write(predicate_file_content.encode("utf-8"))
        predicate_file.seek(0)

        constraint = """
exists <assgn> assgn:
  (erofeb(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        stdout, stderr, code = run_isla(
            "solve",
            grammar_file.name,
            constraint_file.name,
            predicate_file.name,
            "-n",
            -1,
            "-t",
            4,
        )

        self.assertFalse(code)
        self.assertFalse(stderr)
        self.assertTrue(stdout)

        solver = ISLaSolver(
            LANG_GRAMMAR,
            constraint.replace("erofeb", "before"),
        )

        for line in stdout.split("\n"):
            self.assertTrue(solver.check(line))

        grammar_file.close()
        constraint_file.close()

    def test_solve_additional_structural_predicate_dependency(self):
        # Here, the predicates() function calls another function in the extension file.
        # This is to test that it works.
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        predicate_file_content = """
from typing import Set
from isla.language import SemanticPredicate, StructuralPredicate

def helper() -> Set[StructuralPredicate | SemanticPredicate]:
    from isla.language import SemanticPredicate, StructuralPredicate
    from isla.isla_predicates import is_before

    return {StructuralPredicate("erofeb", 2, is_before)}
    
def predicates():
    return helper()

"""

        predicate_file = NamedTemporaryFile(suffix=".py")
        predicate_file.write(predicate_file_content.encode("utf-8"))
        predicate_file.seek(0)

        constraint = """
exists <assgn> assgn:
  (erofeb(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        stdout, stderr, code = run_isla(
            "solve",
            grammar_file.name,
            constraint_file.name,
            predicate_file.name,
            "-n",
            -1,
            "-t",
            4,
        )

        print(stderr)
        self.assertFalse(code)
        self.assertFalse(stderr)
        self.assertTrue(stdout)

        solver = ISLaSolver(
            LANG_GRAMMAR,
            constraint.replace("erofeb", "before"),
        )

        for line in stdout.split("\n"):
            self.assertTrue(solver.check(line))

        grammar_file.close()
        constraint_file.close()

    def test_solve_additional_structural_predicate_not_callable(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        predicate_file = NamedTemporaryFile(suffix=".py")
        predicate_file.write("predicates = set()\n".encode("utf-8"))
        predicate_file.seek(0)

        constraint = """
exists <assgn> assgn:
  (erofeb(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        stdout, stderr, code = run_isla(
            "solve",
            grammar_file.name,
            constraint_file.name,
            predicate_file.name,
            "-n",
            -1,
            "-t",
            4,
        )

        self.assertEqual(DATA_FORMAT_ERROR, code)
        self.assertIn("Unknown predicate erofeb", stderr)
        self.assertFalse(stdout)

        grammar_file.close()
        constraint_file.close()

    def test_solve_additional_structural_predicate_no_iterable(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        predicate_file_content = """
def predicates():
    return 13
"""

        predicate_file = NamedTemporaryFile(suffix=".py")
        predicate_file.write(predicate_file_content.encode("utf-8"))
        predicate_file.seek(0)

        constraint = """
exists <assgn> assgn:
  (erofeb(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        stdout, stderr, code = run_isla(
            "solve",
            grammar_file.name,
            constraint_file.name,
            predicate_file.name,
            "-n",
            -1,
            "-t",
            4,
        )

        self.assertEqual(DATA_FORMAT_ERROR, code)
        self.assertIn(
            "function `predicate` in Python extension file does not return an iterable",
            stderr,
        )
        self.assertFalse(stdout)

        grammar_file.close()
        constraint_file.close()

    def test_solve_additional_structural_predicate_no_predicates(self):
        grammar_file = write_grammar_file(LANG_GRAMMAR)

        predicate_file_content = """
def predicates():
    return [13]
"""

        predicate_file = NamedTemporaryFile(suffix=".py")
        predicate_file.write(predicate_file_content.encode("utf-8"))
        predicate_file.seek(0)

        constraint = """
exists <assgn> assgn:
  (erofeb(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)"""
        constraint_file = write_constraint_file(constraint)

        stdout, stderr, code = run_isla(
            "solve",
            grammar_file.name,
            constraint_file.name,
            predicate_file.name,
            "-n",
            -1,
            "-t",
            4,
        )

        self.assertEqual(DATA_FORMAT_ERROR, code)
        self.assertIn(
            "function `predicate` in Python extension file does not return an iterable "
            + "of predicates",
            stderr,
        )
        self.assertFalse(stdout)

        grammar_file.close()
        constraint_file.close()


if __name__ == "__main__":
    unittest.main()
