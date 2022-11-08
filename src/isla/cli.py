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

import argparse
import collections.abc
import json
import logging
import os
import pathlib
import subprocess
import sys
from argparse import Namespace, ArgumentParser
from contextlib import redirect_stdout, redirect_stderr
from functools import lru_cache
from functools import partial
from io import TextIOWrapper
from typing import Dict, Tuple, List, Optional, Iterable, cast, Any, Set

import toml
from grammar_graph import gg

from isla import __version__ as isla_version, language
from isla.derivation_tree import DerivationTree
from isla.helpers import (
    is_float,
    Maybe,
    get_isla_resource_file_content,
    Exceptional,
    eassert,
)
from isla.isla_predicates import (
    STANDARD_STRUCTURAL_PREDICATES,
    STANDARD_SEMANTIC_PREDICATES,
)
from isla.isla_shortcuts import true
from isla.language import parse_bnf, parse_isla, StructuralPredicate, SemanticPredicate
from isla.solver import (
    ISLaSolver,
    GrammarBasedBlackboxCostComputer,
    CostSettings,
    CostWeightVector,
    CostComputer,
    SemanticError,
)
from isla.type_defs import Grammar

# Exit Codes
USAGE_ERROR = 2
DATA_FORMAT_ERROR = 65


def main(*args: str, stdout=sys.stdout, stderr=sys.stderr):
    if "-O" in sys.argv:
        sys.argv.remove("-O")
        os.execl(sys.executable, sys.executable, "-O", *sys.argv)
        sys.exit(0)

    read_isla_rc_defaults()
    parser = create_parsers(stdout, stderr)

    with redirect_stdout(stdout):
        with redirect_stderr(stderr):
            args = parser.parse_args(args or sys.argv[1:])

    if not args.command and not args.version:
        parser.print_usage(file=stderr)
        print(
            "isla: error: You have to choose a global option or one of the commands "
            + "`solve`, `fuzz`, `check`, or `parse`",
            file=stderr,
        )
        exit(USAGE_ERROR)

    if args.version:
        print(f"ISLa version {isla_version}", file=stdout)
        sys.exit(0)

    level_mapping = {
        "ERROR": logging.ERROR,
        "WARNING": logging.WARNING,
        "INFO": logging.INFO,
        "DEBUG": logging.DEBUG,
    }

    if hasattr(args, "log_level"):
        logging.basicConfig(stream=stderr, level=level_mapping[args.log_level])
    else:
        get_default(stderr, args.command, "--log-level").if_present(
            lambda level: logging.basicConfig(
                stream=stderr,
                level=level_mapping[level],
            )
        )

    args.func(args)


def solve(stdout, stderr, parser: ArgumentParser, args: Namespace):
    files = read_files(args.files)
    ensure_grammar_present(stderr, parser, args, files)

    command = args.command

    output_dir = args.output_dir
    if output_dir:
        assert_path_is_dir(stderr, command, output_dir)

    grammar = parse_grammar(command, args.grammar, files, stderr)
    structural_predicates, semantic_predicates = read_predicates(files, stderr)
    constraint = parse_constraint(
        command,
        args.constraint,
        files,
        grammar,
        stderr,
        structural_predicates=structural_predicates,
        semantic_predicates=semantic_predicates,
    )
    cost_computer = parse_cost_computer_spec(
        command, grammar, args.k, stderr, args.weight_vector
    )

    solver = ISLaSolver(
        grammar,
        constraint,
        max_number_free_instantiations=args.free_instantiations,
        max_number_smt_instantiations=args.smt_instantiations,
        enforce_unique_trees_in_queue=args.unique_trees,
        cost_computer=cost_computer,
        timeout_seconds=args.timeout if args.timeout > 0 else None,
        activate_unsat_support=args.unsat_support,
        grammar_unwinding_threshold=args.unwinding_depth,
        structural_predicates=structural_predicates,
        semantic_predicates=semantic_predicates,
    )

    try:
        num_solutions = args.num_solutions
        i = 0
        while not (0 < num_solutions <= i):
            try:
                tree = solver.solve()
                result = (
                    derivation_tree_to_json(tree, args.pretty_print)
                    if args.tree
                    else str(tree)
                )

                if not output_dir:
                    print(
                        result,
                        flush=True,
                        file=stdout,
                    )
                else:
                    with open(
                        os.path.join(
                            output_dir, f"{i}.{'json' if args.tree else 'txt'}"
                        ),
                        "wb",
                    ) as out_file:
                        out_file.write(result.encode("utf-8"))
            except StopIteration:
                print("UNSAT", flush=True, file=stderr)
                break
            except TimeoutError:
                break
            except Exception as exc:
                print(
                    f"isla solve: error: An exception ({type(exc).__name__}) occurred "
                    + f"during constraint solving, message: `{exc}`",
                    file=stderr,
                )
                sys.exit(1)

            i += 1
    except KeyboardInterrupt:
        sys.exit(0)


def read_predicates(
    files: Dict[str, str], stderr
) -> Tuple[Set[StructuralPredicate], Set[SemanticPredicate]]:
    """
    Executes a Python extension file, if any, and extracts predicates defined there.
    Returns those together with the standard predicates.
    :param files: The passed files (mapping from names to contents).
    :param stderr: Standard error sink.
    :return: The predicates.
    """

    _, maybe_structural_predicates, maybe_semantic_predicates = (
        Maybe.from_iterator(
            file_content
            for file_name, file_content in files.items()
            if file_name.endswith(".py")
        )
        .map(
            lambda file_content: process_python_extension("solve", file_content, stderr)
        )
        .orelse(lambda: (Maybe.nothing(), Maybe.nothing(), Maybe.nothing()))
    ).get()

    structural_predicates = (
        STANDARD_STRUCTURAL_PREDICATES
        | maybe_structural_predicates.orelse(lambda: set()).get()
    )
    semantic_predicates = (
        STANDARD_SEMANTIC_PREDICATES
        | maybe_semantic_predicates.orelse(lambda: set()).get()
    )

    return structural_predicates, semantic_predicates


def fuzz(_, stderr, parser: ArgumentParser, args: Namespace):
    input_ending = "_input.txt"
    stdout_ending = "_stdout.txt"
    stderr_ending = "_stderr.txt"
    status_ending = "_status.txt"

    files = read_files(args.files)
    ensure_grammar_present(stderr, parser, args, files)

    command = args.command

    output_dir = args.output_dir
    assert_path_is_dir(stderr, command, output_dir)

    grammar = parse_grammar(command, args.grammar, files, stderr)
    structural_predicates, semantic_predicates = read_predicates(files, stderr)
    constraint = parse_constraint(
        command,
        args.constraint,
        files,
        grammar,
        stderr,
        structural_predicates=structural_predicates,
        semantic_predicates=semantic_predicates,
    )
    cost_computer = parse_cost_computer_spec(
        command, grammar, args.k, stderr, args.weight_vector
    )

    solver = ISLaSolver(
        grammar,
        constraint,
        max_number_free_instantiations=args.free_instantiations,
        max_number_smt_instantiations=args.smt_instantiations,
        enforce_unique_trees_in_queue=args.unique_trees,
        cost_computer=cost_computer,
        timeout_seconds=args.timeout if args.timeout > 0 else None,
        activate_unsat_support=False,
        grammar_unwinding_threshold=args.unwinding_depth,
        structural_predicates=structural_predicates,
        semantic_predicates=semantic_predicates,
    )

    fuzz_command = get_fuzz_command(args, command, stderr)

    def inst_fuzz_command(inp_file: str) -> str:
        return fuzz_command.replace("{}", inp_file)

    try:
        num_solutions = args.num_solutions
        i = 0
        while not (0 < num_solutions <= i):
            istr = str(i).rjust(4, "0")

            try:
                result = solver.solve()
            except StopIteration:
                print("UNSAT", flush=True, file=stderr)
                break
            except TimeoutError:
                break

            # Write input file
            with open(
                os.path.join(output_dir, f"{istr}{input_ending}"), "wb"
            ) as inp_file:
                inp_file.write(str(result).encode("utf-8"))
                inp_file.seek(0)
                inp_file_name = inp_file.name

            try:
                # Execute fuzz target
                target_result = subprocess.run(
                    inst_fuzz_command(inp_file_name),
                    shell=True,
                    capture_output=True,
                    check=True,
                    text=True,
                )

                standard_output = target_result.stdout
                error_output = target_result.stderr
                return_code = target_result.returncode
            except subprocess.CalledProcessError as cpe:
                standard_output = cpe.stdout
                error_output = cpe.stderr
                return_code = cpe.returncode

            # Write results
            with open(
                os.path.join(output_dir, f"{istr}{stdout_ending}"), "wb"
            ) as stdout_file:
                stdout_file.write(standard_output.encode("utf-8"))

            with open(
                os.path.join(output_dir, f"{istr}{stderr_ending}"), "wb"
            ) as stderr_file:
                stderr_file.write(error_output.encode("utf-8"))

            with open(
                os.path.join(output_dir, f"{istr}{status_ending}"), "wb"
            ) as stat_file:
                stat_file.write(str(return_code).encode("utf-8"))

            i += 1
    except KeyboardInterrupt:
        sys.exit(0)


def get_fuzz_command(args: Namespace, command, stderr):
    fuzz_command: str = args.test_target
    if "{}" not in fuzz_command:
        print(
            f'isla {command}: warning: the placeholder "{{}}" was not found in '
            f'the fuzz command "{fuzz_command}"; the generated inputs will not be '
            f"accessible for the test target.",
            file=stderr,
        )
    return fuzz_command


def check(stdout, stderr, parser: ArgumentParser, args: Namespace):
    code, msg, _ = do_check(stdout, stderr, parser, args)
    print(msg, file=stdout)
    sys.exit(code)


def find(stdout, stderr, parser: ArgumentParser, args: Namespace):
    language_spec_files: List[TextIOWrapper] = [
        io_wrapper
        for io_wrapper in args.files or []
        if io_wrapper.name.endswith(".bnf")
        or io_wrapper.name.endswith(".py")
        or io_wrapper.name.endswith(".isla")
    ]

    input_files: List[TextIOWrapper] = [
        io_wrapper
        for io_wrapper in args.files or []
        if io_wrapper not in language_spec_files
    ]

    if not input_files:
        print("no files passed to `find`", file=stderr)
        sys.exit(USAGE_ERROR)

    success = False
    for input_file in input_files:
        args.files = language_spec_files + [input_file]
        code, _, _ = do_check(stdout, stderr, parser, args)
        if not code:
            success = True
            print(input_file.name, file=stdout)

    if success:
        sys.exit(0)
    else:
        sys.exit(1)


def parse(stdout, stderr, parser: ArgumentParser, args: Namespace):
    code, msg, maybe_tree = do_check(stdout, stderr, parser, args)
    if code:
        print(msg, file=stdout)
        sys.exit(code)

    def write_tree(tree: DerivationTree):
        json_str = derivation_tree_to_json(tree, args.pretty_print)
        if args.output_file:
            with open(args.output_file, "w") as file:
                file.write(json_str)
        else:
            print(json_str, file=stdout)

    maybe_tree.if_present(write_tree)


def repair(stdout, stderr, parser: ArgumentParser, args: Namespace):
    files = read_files(args.files)
    ensure_grammar_present(stderr, parser, args, files)
    ensure_constraint_present(stderr, parser, args, files)
    command = args.command

    grammar = parse_grammar(command, args.grammar, files, stderr)
    structural_predicates, semantic_predicates = read_predicates(files, stderr)
    constraint = parse_constraint(
        command,
        args.constraint,
        files,
        grammar,
        stderr,
        structural_predicates=structural_predicates,
        semantic_predicates=semantic_predicates,
    )

    try:
        inp = get_input_string(command, stderr, args, files, grammar, constraint)
    except SyntaxError:
        print("input could not be parsed", file=stderr)
        sys.exit(1)

    solver = ISLaSolver(
        grammar,
        constraint,
        structural_predicates=structural_predicates,
        semantic_predicates=semantic_predicates,
    )
    maybe_repaired = solver.repair(inp, fix_timeout_seconds=args.timeout)

    if not maybe_repaired.is_present():
        print(
            "sorry, I could not repair this input (tip: try `isla mutate` instead)",
            file=stderr,
        )
        sys.exit(1)

    def write_result(tree: DerivationTree):
        if args.output_file:
            with open(args.output_file, "w") as file:
                file.write(str(tree))
        else:
            print(str(tree), file=stdout)

    maybe_repaired.if_present(write_result)
    sys.exit(0)


def mutate(stdout, stderr, parser: ArgumentParser, args: Namespace):
    files = read_files(args.files)
    ensure_grammar_present(stderr, parser, args, files)
    ensure_constraint_present(stderr, parser, args, files)
    command = args.command

    grammar = parse_grammar(command, args.grammar, files, stderr)
    structural_predicates, semantic_predicates = read_predicates(files, stderr)
    constraint = parse_constraint(
        command,
        args.constraint,
        files,
        grammar,
        stderr,
        structural_predicates=structural_predicates,
        semantic_predicates=semantic_predicates,
    )

    try:
        inp = get_input_string(command, stderr, args, files, grammar, constraint)
    except SyntaxError:
        print("input could not be parsed", file=stderr)
        sys.exit(1)

    solver = ISLaSolver(
        grammar,
        constraint,
        structural_predicates=structural_predicates,
        semantic_predicates=semantic_predicates,
    )

    mutated = solver.mutate(
        inp,
        fix_timeout_seconds=args.timeout,
        min_mutations=args.min_mutations,
        max_mutations=args.max_mutations,
    )

    if args.output_file:
        with open(args.output_file, "w") as file:
            file.write(str(mutated))
    else:
        print(str(mutated), file=stdout)

    sys.exit(0)


def do_check(
    stdout, stderr, parser: ArgumentParser, args: Namespace
) -> Tuple[int, str, Maybe[DerivationTree]]:
    files = read_files(args.files)
    ensure_grammar_present(stderr, parser, args, files)
    ensure_constraint_present(stderr, parser, args, files)
    command = args.command

    grammar = parse_grammar(command, args.grammar, files, stderr)
    structural_predicates, semantic_predicates = read_predicates(files, stderr)
    constraint = parse_constraint(
        command,
        args.constraint,
        files,
        grammar,
        stderr,
        structural_predicates=structural_predicates,
        semantic_predicates=semantic_predicates,
    )

    try:
        tree = get_input_string(command, stderr, args, files, grammar, constraint)
    except SyntaxError:
        return (
            1,
            "input could not be parsed",
            Maybe.nothing(),
        )

    try:
        solver = ISLaSolver(
            grammar,
            constraint,
            structural_predicates=structural_predicates,
            semantic_predicates=semantic_predicates,
        )

        if not solver.check(tree):
            raise SemanticError()
    except SemanticError:
        return 1, "input does not satisfy the ISLa constraint", Maybe.nothing()

    return 0, "input satisfies the ISLa constraint", Maybe(tree)


def create(stdout, stderr, parser: ArgumentParser, args: Namespace):
    command = args.command
    out_dir = args.output_dir
    base_name = args.base_name

    assert_path_is_dir(stderr, command, out_dir)

    grammar_1_file = open(os.path.join(out_dir, f"{base_name}_grammar_1.bnf"), "w")
    grammar_2_file = open(os.path.join(out_dir, f"{base_name}_grammar_2.py"), "w")
    constraint_file = open(os.path.join(out_dir, f"{base_name}_constraint.isla"), "w")

    grammar_1_text = get_isla_resource_file_content("resources/cli_stubs/grammar.bnf")
    grammar_2_text = get_isla_resource_file_content("resources/cli_stubs/grammar.py")
    constraint_text = get_isla_resource_file_content(
        "resources/cli_stubs/constraint.isla"
    )

    readme_text = (
        get_isla_resource_file_content("resources/cli_stubs/README.md")
        .replace("{grammar_1_file.name}", grammar_1_file.name)
        .replace("{grammar_2_file.name}", grammar_2_file.name)
        .replace("{constraint_file.name}", constraint_file.name)
    )

    grammar_1_file.write(grammar_1_text)
    grammar_1_file.close()

    grammar_2_file.write(grammar_2_text)
    grammar_2_file.close()

    constraint_file.write(constraint_text)
    constraint_file.close()

    readme_path = os.path.join(out_dir, "README.md")
    with open(readme_path, "w") as readme_file:
        readme_file.write(readme_text)

    print(
        "`isla create` produced the following files: "
        + ", ".join(
            map(
                str,
                [
                    readme_path,
                    grammar_1_file.name,
                    grammar_2_file.name,
                    constraint_file.name,
                ],
            )
        ),
        file=stdout,
    )


def dump_config(stdout, stderr, parser: ArgumentParser, args: Namespace):
    config_file_content = get_isla_resource_file_content("resources/.islarc")

    if args.output_file:
        with open(args.output_file, "w") as file:
            file.write(config_file_content)
    else:
        print(config_file_content, file=stdout)


def create_parsers(stdout, stderr):
    parser = argparse.ArgumentParser(
        prog="isla",
        description="""
The ISLa command line interface.""",
    )

    parser.add_argument(
        "-v", "--version", help="Print the ISLa version number", action="store_true"
    )

    subparsers = parser.add_subparsers(title="Commands", dest="command", required=False)

    create_solve_parser(subparsers, stdout, stderr)
    create_fuzz_parser(subparsers, stdout, stderr)
    create_check_parser(subparsers, stdout, stderr)
    create_find_parser(subparsers, stdout, stderr)
    create_parse_parser(subparsers, stdout, stderr)
    create_repair_parser(subparsers, stdout, stderr)
    create_mutate_parser(subparsers, stdout, stderr)
    create_create_parser(subparsers, stdout, stderr)
    create_dump_config_parser(subparsers, stdout, stderr)

    return parser


def read_files(files: Iterable[TextIOWrapper]) -> Dict[str, str]:
    return {io_wrapper.name: io_wrapper.read() for io_wrapper in files}


def ensure_grammar_present(
    stderr, parser: ArgumentParser, args: Namespace, files: Dict[str, str]
) -> None:
    if not args.grammar and all(
        not file.endswith(".bnf") and not file.endswith(".py") for file in files
    ):
        parser.print_usage(file=stderr)
        print(
            "isla solve: error: You must specify a grammar by `--grammar` "
            "or FILES arguments with `.bnf` or `.py` ending.",
            file=stderr,
        )

        exit(USAGE_ERROR)


def ensure_constraint_present(
    stderr, parser: ArgumentParser, args: Namespace, files: Dict[str, str]
) -> None:
    if not args.constraint and all(not file.endswith(".isla") for file in files):
        parser.print_usage(file=stderr)
        print(
            "isla solve: error: You must specify a constraint by `--constraint` "
            "or FILES arguments with `.isla` ending.",
            file=stderr,
        )

        exit(USAGE_ERROR)


def parse_constraint(
    subcommand: str,
    constraint_arg: Optional[List[str]],
    files: Dict[str, str],
    grammar: Grammar,
    stderr,
    structural_predicates: Set[StructuralPredicate] = STANDARD_STRUCTURAL_PREDICATES,
    semantic_predicates: Set[SemanticPredicate] = STANDARD_SEMANTIC_PREDICATES,
) -> language.Formula:
    constraint_arg = constraint_arg or []
    assert isinstance(constraint_arg, list)
    assert all(isinstance(elem, str) for elem in constraint_arg)

    constraint = true()

    try:
        for constraint_str in constraint_arg:
            with redirect_stderr(stderr):
                constraint &= parse_isla(
                    constraint_str,
                    structural_predicates=structural_predicates,
                    semantic_predicates=semantic_predicates,
                    grammar=grammar,
                )

        for constraint_file_name in filter(lambda f: f.endswith(".isla"), files):
            with open(constraint_file_name, "r") as constraint_file:
                with redirect_stderr(stderr):
                    constraint &= parse_isla(
                        constraint_file.read(),
                        structural_predicates=structural_predicates,
                        semantic_predicates=semantic_predicates,
                        grammar=grammar,
                    )
    except Exception as exc:
        exc_string = str(exc)
        print(
            f"isla {subcommand}: error: A {type(exc).__name__} occurred "
            + f"while parsing the constraint{f' ({exc_string})' if exc_string else ''}",
            file=stderr,
        )
        sys.exit(DATA_FORMAT_ERROR)

    return constraint


def parse_grammar(
    subcommand: str, grammar_arg: str, files: Dict[str, str], stderr
) -> Grammar:
    try:
        if grammar_arg:
            with redirect_stderr(stderr):
                grammar = parse_bnf(grammar_arg)
        else:
            grammar = {}
            for grammar_file_name in filter(
                lambda f: f.endswith(".bnf") or f.endswith(".py"), files
            ):
                with open(grammar_file_name, "r") as grammar_file:
                    with redirect_stderr(stderr):
                        grammar_file_content = grammar_file.read()
                        if grammar_file_name.endswith(".bnf"):
                            grammar |= parse_bnf(grammar_file_content)
                        else:
                            grammar |= (
                                process_python_extension(
                                    subcommand, grammar_file_content, stderr
                                )[0]
                                .orelse(lambda: {})
                                .get()
                            )

            if not grammar:
                print(
                    "Could not find any grammar definition in the given files "
                    + f"{', '.join(files)}; either supply a BNF grammar as file "
                    + "(`*.bnf`) or command line argument, or a Python grammar "
                    + " as file(`*.py`) defining a variable `grammar`.",
                    file=stderr,
                )
                sys.exit(USAGE_ERROR)

    except Exception as exc:
        exc_string = str(exc)
        if exc_string == "None":
            exc_string = ""
        print(
            f"isla {subcommand}: error: A {type(exc).__name__} occurred "
            + "while processing a provided file"
            + (f" ({exc_string})" if exc_string else ""),
            file=stderr,
        )
        sys.exit(DATA_FORMAT_ERROR)

    return grammar


def process_python_extension(
    subcommand: str, python_file_content: str, stderr
) -> Tuple[
    Maybe[Grammar], Maybe[Set[StructuralPredicate]], Maybe[Set[SemanticPredicate]]
]:
    query_program = """
try:
    grammar_ = grammar() if callable(grammar) else grammar
except NameError:
    grammar_ = None

try:
    predicates_ = predicates() if callable(predicates) else None
except NameError as err:
    predicates_ = None
    err_ = err
"""

    python_file_content = f"{python_file_content}\n{query_program}"

    new_symbols = {}
    exec(python_file_content, new_symbols)

    def assert_is_set_of_predicates(
        maybe_set_of_predicates: Any,
    ) -> Set[StructuralPredicate | SemanticPredicate]:
        if not isinstance(maybe_set_of_predicates, collections.abc.Iterable):
            print(
                f"isla {subcommand}: error: function `predicate` in Python extension "
                + "file does not return an iterable.",
                file=stderr,
            )
            sys.exit(DATA_FORMAT_ERROR)

        if any(
            not isinstance(elem, StructuralPredicate)
            and not isinstance(elem, SemanticPredicate)
            for elem in maybe_set_of_predicates
        ):
            print(
                f"isla {subcommand}: error: function `predicate` in Python extension "
                + "file does not return an iterable of predicates.",
                file=stderr,
            )
            sys.exit(DATA_FORMAT_ERROR)

        return set(maybe_set_of_predicates)

    def assert_is_valid_grammar(maybe_grammar: Any) -> Grammar:
        if (
            not isinstance(maybe_grammar, dict)
            or not all(isinstance(key, str) for key in maybe_grammar)
            or not all(
                isinstance(expansions, list) for expansions in maybe_grammar.values()
            )
            or not all(
                isinstance(expansion, str)
                for expansions in maybe_grammar.values()
                for expansion in expansions
            )
        ):
            print(
                f"isla {subcommand}: error: A grammar must be of type "
                + "`Dict[str, List[str]]`.",
                file=stderr,
            )
            sys.exit(DATA_FORMAT_ERROR)

        return maybe_grammar

    grammar = cast(Maybe[Grammar], Maybe(new_symbols["grammar_"])).map(
        assert_is_valid_grammar
    )

    predicates = Maybe(new_symbols["predicates_"]).map(assert_is_set_of_predicates)

    structural_predicates = cast(
        Maybe[Set[StructuralPredicate]],
        predicates.map(partial(filter, StructuralPredicate.__instancecheck__)).map(set),
    )

    semantic_predicates = cast(
        Maybe[Set[SemanticPredicate]],
        predicates.map(partial(filter, SemanticPredicate.__instancecheck__)).map(set),
    )

    return grammar, structural_predicates, semantic_predicates


def parse_cost_computer_spec(
    command: str, grammar: Grammar, k_arg: int, stderr, weight_vector_arg: str
) -> CostComputer:
    weight_vector = weight_vector_arg.split(",")
    if len(weight_vector) != 5:
        print(
            f"isla {command}: error: Length of weight vector is "
            f"{len(weight_vector)}, expected 5",
            file=stderr,
        )
        sys.exit(DATA_FORMAT_ERROR)
    if any(not is_float(w) for w in weight_vector):
        print(
            f"isla {command}: error: non-numeric weight vector element encountered",
            file=stderr,
        )
        sys.exit(DATA_FORMAT_ERROR)
    weight_vector = list(map(float, weight_vector))
    cost_computer = GrammarBasedBlackboxCostComputer(
        CostSettings(
            CostWeightVector(
                tree_closing_cost=weight_vector[0],
                constraint_cost=weight_vector[1],
                derivation_depth_penalty=weight_vector[2],
                low_k_coverage_penalty=weight_vector[3],
                low_global_k_path_coverage_penalty=weight_vector[4],
            ),
            k=k_arg,
        ),
        gg.GrammarGraph.from_grammar(grammar),
    )
    return cost_computer


def get_input_string(
    command: str,
    stderr,
    args: Namespace,
    files: Dict[str, str],
    grammar: Grammar,
    constraint: language.Formula,
) -> DerivationTree:
    """
    Looks for a passed input (either via `args.input_string` or a file name) and
    parses it, if any. Terminates with a `USAGE_ERROR` if no input can be found.
    Raises a `SyntaxError` if the input could not be parsed. If an input is recognized
    as a valid derivation tree in JSON format, it is treated as such and not parsed.

    :param command: The calling command.
    :param stderr: The standard error sink to use.
    :param args: The command line arguments.
    :param files: The passed files.
    :param grammar: The specified grammar.
    :param constraint: The specified constraint.
    :return: A derivation tree of the given input.
    """

    if hasattr(args, "input_string") and args.input_string:
        inp = args.input_string
    else:
        possible_inputs = [
            file
            for file in files
            if not file.endswith(".bnf")
            and not file.endswith(".isla")
            and not file.endswith(".py")
        ]

        if len(possible_inputs) != 1:
            print(
                f"isla {command}: error: you must specify exactly *one* input to check "
                + f"via `--input-string` or a file; found {len(possible_inputs)} "
                + "inputs",
                file=stderr,
            )
            sys.exit(USAGE_ERROR)

        inp = files[possible_inputs[0]]

        # Somehow, spurious newlines appear when reading files...
        inp = inp[:-1] if inp[-1] == "\n" else inp

    def solver():
        return ISLaSolver(grammar, constraint)

    def graph():
        return gg.GrammarGraph.from_grammar(grammar)

    return (
        Exceptional.of(lambda: json.loads(inp))
        .map(DerivationTree.from_parse_tree)
        .map(lambda tree: eassert(tree, graph().tree_is_valid(tree)))
        .recover(lambda _: solver().parse(inp, skip_check=True))
        .reraise()
        .get()
    )


def create_solve_parser(subparsers, stdout, stderr):
    parser = subparsers.add_parser(
        "solve",
        help="create solutions to ISLa constraints or check their unsatisfiability",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
        description="""
Create solutions to an ISLa constraint and a reference grammar.""",
    )
    parser.set_defaults(func=lambda *args: solve(stdout, stderr, parser, *args))

    grammar_arg(parser)
    constraint_arg(parser)
    output_dir_arg(parser)

    parser.add_argument(
        "-T",
        "--tree",
        action=argparse.BooleanOptionalAction,
        default=get_default(sys.stderr, "solve", "--tree").get(),
        help="""
outputs derivation trees in JSON format instead of strings""",
    )

    parser.add_argument(
        "-p",
        "--pretty-print",
        type=bool,
        action=argparse.BooleanOptionalAction,
        default=get_default(stderr, "solve", "--pretty-print").get(),
        help="""
If this flag is set, created JSON parse trees are printed on multiple lines with
indentation; otherwise the whole string is printed on a single line. Only relevant
if `--tree` is used.""",
    )

    num_solutions_arg(parser)
    timeout_arg(parser)
    parser.add_argument(
        "--unsat-support",
        action="store_true",
        default=get_default(stderr, "solve", "--unsat-support").get(),
        help="""
Activate support for unsatisfiable constraints. This can be required to make the
analysis of unsatisfiable constraints terminate, but reduces the performance of the
generator for satisfiable formulas""",
    )
    free_insts_arg(parser)
    smt_insts_arg(parser)
    unique_trees_arg(parser)
    unwinding_depth_arg(parser)
    weight_vector_arg(parser)
    k_arg(parser)
    log_level_arg(parser)
    grammar_constraint_extension_files_arg(parser)


def create_fuzz_parser(subparsers, stdout, stderr):
    parser = subparsers.add_parser(
        "fuzz",
        help="pass solutions to an ISLa constraint to a test subject",
        description="""
Create solutions to an ISLa constraint and a reference grammar, and pass these to
a test subject. An output directory must be specified (`-d`). Into this directory,
ISLa writes three files per generated test input: (1) the input (`..._input.txt`),
(2) the standard output of the fuzzed program (`..._stdout.txt`), (3) the standard
error of the fuzzed program (`..._stderr.txt`), and (4) the returned status code of
the fuzzed program (`..._status.txt`).""",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.set_defaults(func=lambda *args: fuzz(stdout, stderr, parser, *args))

    parser.add_argument(
        "test_target",
        metavar="TEST_TARGET",
        help="""
A command to run the test target. The placeholder `{}` will be replaced by a path to
the input file""",
    )

    output_dir_arg(parser, required=True)

    parser.add_argument(
        "-e",
        "--ending",
        metavar="FILE_ENDING",
        default=get_default(stderr, "fuzz", "--ending").get(),
        help="""
The file ending for the generated files that are passed to the test target, if the
test target expects a particular format""",
    )

    grammar_arg(parser)
    constraint_arg(parser)
    num_solutions_arg(parser)
    timeout_arg(parser)
    free_insts_arg(parser)
    smt_insts_arg(parser)
    unique_trees_arg(parser)
    unwinding_depth_arg(parser)
    weight_vector_arg(parser)
    k_arg(parser)
    log_level_arg(parser)
    grammar_constraint_extension_files_arg(parser)


def create_check_parser(subparsers, stdout, stderr):
    parser = subparsers.add_parser(
        "check",
        help="check whether an input satisfies an ISLa constraint",
        description="""
Check whether an input is derivable from a grammar and satisfies and an ISLa
constraint.""",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.set_defaults(func=lambda *args: check(stdout, stderr, parser, *args))

    input_string_arg(parser)

    grammar_arg(parser)
    constraint_arg(parser)
    log_level_arg(parser)
    grammar_constraint_or_input_files_arg(parser)


def create_find_parser(subparsers, stdout, stderr):
    parser = subparsers.add_parser(
        "find",
        help="filter files satisfying syntactic & semantic constraints",
        description="""
From a list of passed files, lists those that can be parsed with the given grammar and
satisfy the given ISLa constraint(s).""",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.set_defaults(func=lambda *args: find(stdout, stderr, parser, *args))

    grammar_arg(parser)
    constraint_arg(parser)
    log_level_arg(parser)
    grammar_constraint_or_input_files_arg(parser)


def create_parse_parser(subparsers, stdout, stderr):
    parser = subparsers.add_parser(
        "parse",
        help="parse an input into a derivation tree if it satisfies an ISLa constraint",
        description="""
Parse an input into a derivation tree if it is derivable from a grammar and
satisfies an ISLa constraint.""",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.set_defaults(func=lambda *args: parse(stdout, stderr, parser, *args))

    input_string_arg(parser)

    parser.add_argument(
        "-o",
        "--output-file",
        default=get_default(stderr, "parse", "--output-file").get_unsafe(),
        help="""
The file into which to write the (JSON) derivation tree in case that the input
could be successfully parsed and checked. If no file is given, the tree is printed
to stdout""",
    )

    parser.add_argument(
        "-p",
        "--pretty-print",
        type=bool,
        action=argparse.BooleanOptionalAction,
        default=get_default(stderr, "parse", "--pretty-print").get(),
        help="""
if this flag is set, the created JSON parse tree is printed on multiple lines with
indentation; otherwise the whole string is printed on a single line""",
    )

    grammar_arg(parser)
    constraint_arg(parser)
    log_level_arg(parser)
    grammar_constraint_or_input_files_arg(parser)


def create_repair_parser(subparsers, stdout, stderr):
    parser = subparsers.add_parser(
        "repair",
        help="try to repair an existing input such that it satisfies an ISLa constraint",
        description="""
Parses an input and, if it does not already satisfy the specified constraint, gradually
abstracts the input and tries to instantiate the abstracted parts such that the result
satisfies the constraint. The input must be parseable using the grammar. Note that
currently, no intensive structural manipulations are performed; we rather intend to fix
the valuation of SMT-LIB and semantic predicate constraints.""",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.set_defaults(func=lambda *args: repair(stdout, stderr, parser, *args))

    input_string_arg(parser)

    parser.add_argument(
        "-o",
        "--output-file",
        default=get_default(stderr, "repair", "--output-file").get_unsafe(),
        help="""
The file into which to write the repaired result in case that the input could be
successfully repaired. If no file is given, the result is printed to stdout""",
    )

    grammar_arg(parser)
    constraint_arg(parser)

    parser.add_argument(
        "-t",
        "--timeout",
        type=float,
        default=get_default(stderr, "repair", "--timeout").get(),
        help="""
the number of (fractions of) seconds after which the solver should stop finding
solutions when trying to repair an incomplete input""",
    )

    log_level_arg(parser)
    grammar_constraint_or_input_files_arg(parser)


def create_mutate_parser(subparsers, stdout, stderr):
    parser = subparsers.add_parser(
        "mutate",
        help="mutate an input such that the result satisfies an ISLa constraint",
        description="""
Performs structural mutations on the given input and repairs it afterward (see
`isla repair` such that the result satisfies the given constraint(s).""",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.set_defaults(func=lambda *args: mutate(stdout, stderr, parser, *args))

    input_string_arg(parser)

    parser.add_argument(
        "-o",
        "--output-file",
        default=get_default(stderr, "mutate", "--output-file").get_unsafe(),
        help="""
The file into which to write the mutated result. If no file is given, the result is
printed to stdout""",
    )

    grammar_arg(parser)
    constraint_arg(parser)

    parser.add_argument(
        "-x",
        "--min-mutations",
        type=int,
        default=get_default(stderr, "mutate", "--min-mutations").get(),
        help="the minimum number of mutation steps to perform",
    )

    parser.add_argument(
        "-X",
        "--max-mutations",
        type=int,
        default=get_default(stderr, "mutate", "--max-mutations").get(),
        help="the maximum number of mutation steps to perform",
    )

    parser.add_argument(
        "-t",
        "--timeout",
        type=float,
        default=get_default(stderr, "mutate", "--timeout").get(),
        help="""
the number of (fractions of) seconds after which the solver should stop finding
solutions when trying to repair a mutated input""",
    )

    log_level_arg(parser)
    grammar_constraint_or_input_files_arg(parser)


def create_create_parser(subparsers, stdout, stderr):
    parser = subparsers.add_parser(
        "create",
        help="create grammar and constraint stubs",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
        description="""
Create grammar and constraint stub files to help kickstart a new
specification project.""",
    )
    parser.set_defaults(func=lambda *args: create(stdout, stderr, parser, *args))

    parser.add_argument(
        "-b",
        "--base-name",
        default=get_default(stderr, "create", "--base-name").get(),
        help="the base name for the created stubs",
    )

    parser.add_argument(
        "output_dir",
        metavar="OUTPUT_DIR",
        help="the directory into which to write the created stubs",
    )


def create_dump_config_parser(subparsers, stdout, stderr):
    parser = subparsers.add_parser(
        "config",
        help="dumps the default configuration file",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
        description="""
Dumps the default `.islarc` configuration file.""",
    )
    parser.set_defaults(func=lambda *args: dump_config(stdout, stderr, parser, *args))

    parser.add_argument(
        "-o",
        "--output-file",
        help="""
The file into which to write the current default `.islarc`. If no file is given, the
configuration is printed to stdout""",
    )


def grammar_constraint_extension_files_arg(parser):
    parser.add_argument(
        "files",
        nargs="*",
        metavar="FILES",
        type=argparse.FileType("r", encoding="UTF-8"),
        help="""
Possibly multiple ISLa constraint (`*.isla`), BNF grammar (`*.bnf`) or Python
extension (`*.py`) files. Multiple grammar files will be simply merged; multiple ISLa
constraints will be combined to a disjunction. Grammars must declare a rule for a
nonterminal "<start>" (the start symbol) expanding to a single other nonterminal.
Python extension files can specify a grammar by declaring a variable `grammar` of type
`Dict[str, List[str]]`, or (preferably) by specifying a function `grammar()` returning
Dict objects of that type. Furthermore, they can specify additional structural or
semantic predicates by declaring a function

```python
def predicates() -> typing.Set[
        isla.language.StructuralPredicate |
        isla.language.SemanticPredicate]:
    # ...
```

Note that you can _either_ pass a grammar as a file _or_ via the `--grammar` option.
For constraints, it is possible to use both the option and a file input. However, a
grammar and a constraint must be specified somehow.""",
    )


def grammar_constraint_or_input_files_arg(parser):
    parser.add_argument(
        "files",
        nargs="*",
        metavar="FILES",
        type=argparse.FileType("r", encoding="UTF-8"),
        help="""
Possibly multiple ISLa constraint (`*.isla`), BNF grammar (`*.bnf`), Python
extension (`*.py`) files, and/or input files to process (currently, only the `find`
command accepts more than one input file). Multiple grammar files will be simply merged;
multiple ISLa constraints will be combined to a disjunction. Grammars must declare a
rule for a nonterminal "<start>" (the start symbol) expanding to a single other
nonterminal. Python extension files can specify a grammar by declaring a variable
`grammar` of type `Dict[str, List[str]]`, or (preferably) by specifying a function
`grammar()` returning Dict objects of that type. Furthermore, they can specify
additional structural or semantic predicates by declaring a function

```python
def predicates() -> typing.Set[
        isla.language.StructuralPredicate |
        isla.language.SemanticPredicate]:
    # ...
```

Note that you can _either_ pass a grammar as a file _or_ via the `--grammar` option.
For constraints, it is possible to use both the option and a file input. However, a
grammar and a constraint must be specified somehow.""",
    )


def log_level_arg(parser):
    command = parser.prog.split(" ")[-1]

    parser.add_argument(
        "-l",
        "--log-level",
        choices=["ERROR", "WARNING", "INFO", "DEBUG"],
        default=get_default(sys.stderr, command, "--log-level").get(),
        help="set the logging level",
    )


def weight_vector_arg(parser):
    command = parser.prog.split(" ")[-1]

    parser.add_argument(
        "-w",
        "--weight-vector",
        help="""
Set the ISLa weight vector. Expects a comma-separated list of floating point values
for the following cost factors: (1) Tree closing cost, (2) constraint cost, (3)
derivation depth penalty, (4) low per-input k-path coverage penalty, and (5)
low global k-path coverage penalty""",
        default=get_default(sys.stderr, command, "--weight-vector").get(),
    )


def k_arg(parser):
    command = parser.prog.split(" ")[-1]

    parser.add_argument(
        "-k",
        type=int,
        help="""
set the length of the k-paths to be considered for coverage computations""",
        default=get_default(sys.stderr, command, "-k").get(),
    )


def unwinding_depth_arg(parser):
    command = parser.prog.split(" ")[-1]

    parser.add_argument(
        "--unwinding-depth",
        type=int,
        default=get_default(sys.stderr, command, "--unwinding-depth").get(),
        help="""
Set the depth until which nonregular grammar elements in SMT-LIB expressions are
unwound to make them regular before the SMT solver is queried""",
    )


def unique_trees_arg(parser):
    command = parser.prog.split(" ")[-1]

    parser.add_argument(
        "--unique-trees",
        action="store_true",
        default=get_default(sys.stderr, command, "--unique-trees").get(),
        help="""
Enforces the uniqueness of derivation trees in the solver queue. This setting can
improve the generator performance, but can also lead to omitted interesting solutions
in certain cases""",
    )


def smt_insts_arg(parser):
    command = parser.prog.split(" ")[-1]

    parser.add_argument(
        "-s",
        "--smt-instantiations",
        type=int,
        default=get_default(sys.stderr, command, "--smt-instantiations").get(),
        help="""
the number of solutions obtained from the SMT solver for atomic SMT-LIB formulas""",
    )


def free_insts_arg(parser):
    command = parser.prog.split(" ")[-1]

    parser.add_argument(
        "-f",
        "--free-instantiations",
        type=int,
        default=get_default(sys.stderr, command, "--free-instantiations").get(),
        help="""
the number of times an unconstrained nonterminal should be randomly instantiated
""",
    )


def timeout_arg(parser):
    command = parser.prog.split(" ")[-1]

    parser.add_argument(
        "-t",
        "--timeout",
        type=float,
        default=get_default(sys.stderr, command, "--timeout").get(),
        help="""
The number of (fractions of) seconds after which the solver should stop finding
solutions. Negative numbers imply that no timeout is set""",
    )


def num_solutions_arg(parser):
    command = parser.prog.split(" ")[-1]

    parser.add_argument(
        "-n",
        "--num-solutions",
        type=int,
        default=get_default(sys.stderr, command, "--num-solutions").get(),
        help="""
The number of solutions to generate. Negative numbers indicate an infinite number of
solutions (you need ot set a `--timeout` or forcefully stop ISLa)""",
    )


def output_dir_arg(parser: ArgumentParser, required: bool = False):
    command = parser.prog.split(" ")[-1]

    parser.add_argument(
        "-d",
        "--output-dir",
        default=get_default(sys.stderr, command, "--output-dir").get_unsafe(),
        required=required,
        help="a directory into which to place generated output files",
    )


def constraint_arg(parser):
    parser.add_argument(
        "-c",
        "--constraint",
        help="Add ISLa constraints to the solver. All constraints passed via "
        "`--constraint` as well as constraints passed as file(s) "
        "are combined to a single conjunction",
        action="append",
    )


def grammar_arg(parser):
    parser.add_argument(
        "-g", "--grammar", help="the grammar in BNF (if not passed as a file)"
    )


def input_string_arg(parser):
    parser.add_argument(
        "-i",
        "--input-string",
        help="the input to check",
    )


def assert_path_is_dir(stderr, command: str, out_dir: str) -> None:
    if not os.path.isdir(out_dir):
        print(
            f"isla {command}: error: path {out_dir} does not exist or is no directory",
            file=stderr,
        )
        sys.exit(USAGE_ERROR)


@lru_cache
def read_isla_rc_defaults(
    content: Maybe[str] = Maybe.nothing(),
) -> Dict[str, Dict[str, str | int | float | bool]]:
    """
    Attempts to read an `.islarc` configuration from the following source, in the
    given order:

    1. The `content` parameter
    2. The file `./.islarc` (in the current working directory)
    3. The file `~/.islarc` (in the current user's home directory)
    4. The file `resources/.islarc` (bundled with the ISLa distribution)

    Returns a configuration dictionary. The keys are ISLa commands or "default" for a
    fallback; the values are dictionaries from command line parameters to default
    values. Configurations in the files listed above are merged; Defaults specified in
    configuration sources earlier in the list take precedence in case of conflicts.

    :param content: An optional TOML configuration string (not a path!).
    :return: The configuration dictionary.
    """

    sources: List[str] = []
    content.if_present(lambda c: sources.append(c))

    dirs = (os.getcwd(), pathlib.Path.home())
    candidate_locations = [os.path.join(dir, ".islarc") for dir in dirs]
    sources.extend(
        [
            pathlib.Path(location).read_text()
            for location in candidate_locations
            if os.path.exists(location)
        ]
    )

    sources.append(get_isla_resource_file_content("resources/.islarc"))

    all_defaults = [toml.loads(source).get("defaults", {}) for source in sources]

    result: Dict[str, Dict[str, str | int | float | bool]] = {}

    for defaults in all_defaults:
        # Expecting something like
        #
        # {
        #     "default": [{"--log-level": "WARNING"}],
        #     "create": [{"--base-name": "project", "--output-dir": "."}],
        #     ...
        # }

        if (
            not isinstance(defaults, dict)
            or any(not isinstance(key, str) for key in defaults)
            or not all(
                isinstance(value, list)
                and len(value) == 1
                and isinstance(value[0], dict)
                and all(isinstance(inner_key, str) for inner_key in value[0])
                and all(
                    isinstance(inner_value, str)
                    or isinstance(inner_value, int)
                    or isinstance(inner_value, float)
                    or isinstance(inner_value, bool)
                    for inner_value in value[0].values()
                )
                for value in defaults.values()
            )
        ):
            raise RuntimeError(
                "Unexpected .islarc format: defaults should be a "
                + "non-nested array of tables"
            )

        for key, value in defaults.items():
            for inner_key, inner_value in value[0].items():
                result.setdefault(key, {}).setdefault(inner_key, inner_value)

    return result


def get_default(
    stderr, command: str, argument: str, content: Maybe[str] = Maybe.nothing()
) -> Maybe[str | int | float | bool]:
    try:
        config = read_isla_rc_defaults(content)
    except RuntimeError as err:
        print(f"isla {command}: error: could not load .islarc ({err})", file=stderr)
        sys.exit(1)

    default = config.get("default", {}).get(argument, None)
    return Maybe(config.get(command, {}).get(argument, default))


def derivation_tree_to_json(tree: DerivationTree, pretty_print: bool = False) -> str:
    return json.dumps(tree.to_parse_tree(), indent=None if not pretty_print else 4)


if __name__ == "__main__":
    if "-O" in sys.argv:
        sys.argv.remove("-O")
        os.execl(sys.executable, sys.executable, "-O", *sys.argv)
    else:
        main()
