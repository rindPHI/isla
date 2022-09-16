import argparse
import logging
import os
import string
import subprocess
import sys
from contextlib import redirect_stdout, redirect_stderr
from typing import Dict

from grammar_graph import gg

from isla import __version__ as isla_version, language
from isla.derivation_tree import DerivationTree
from isla.helpers import is_float
from isla.isla_predicates import (
    STANDARD_STRUCTURAL_PREDICATES,
    STANDARD_SEMANTIC_PREDICATES,
)
from isla.isla_shortcuts import true
from isla.language import parse_bnf, parse_isla
from isla.parser import EarleyParser
from isla.solver import (
    ISLaSolver,
    GrammarBasedBlackboxCostComputer,
    CostSettings,
    CostWeightVector,
    CostComputer,
)
from isla.type_defs import Grammar

# Exit Codes
USAGE_ERROR = 2
DATA_FORMAT_ERROR = 65


def main(*args: str, stdout=sys.stdout, stderr=sys.stderr):
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

    args.func(args)


def solve(stdout, stderr, parser, args):
    files = read_files(args)
    ensure_grammar_constraint_present(stderr, parser, args, files)

    command = args.command

    output_dir = args.output_dir
    if output_dir:
        assert_path_is_dir(stderr, command, output_dir)

    grammar = parse_grammar(command, args.grammar, files, stderr)
    constraint = parse_constraint(command, args.constraint, files, grammar, stderr)
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
    )

    num_solutions = args.num_solutions
    i = 0
    while True:
        if 0 < num_solutions <= i:
            break

        result = solver.fuzz()
        if isinstance(result, DerivationTree):
            if not output_dir:
                print(result, flush=True, file=stdout)
            else:
                with open(os.path.join(output_dir, f"{i}.txt"), "wb") as out_file:
                    out_file.write(str(result).encode("utf-8"))
        else:
            assert result == ISLaSolver.TIMEOUT or result == ISLaSolver.UNSAT
            if result == ISLaSolver.UNSAT:
                print("UNSAT", flush=True, file=stderr)
            break

        i += 1


def fuzz(stdout, stderr, parser, args):
    input_ending = "_input.txt"
    stdout_ending = "_stdout.txt"
    stderr_ending = "_stderr.txt"
    status_ending = "_status.txt"

    files = read_files(args)
    ensure_grammar_constraint_present(stderr, parser, args, files)

    command = args.command

    output_dir = args.output_dir
    assert_path_is_dir(stderr, command, output_dir)

    grammar = parse_grammar(command, args.grammar, files, stderr)
    constraint = parse_constraint(command, args.constraint, files, grammar, stderr)
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
    )

    fuzz_command: str = args.test_target
    if "{}" not in fuzz_command:
        print(
            f'isla {command}: warning: the placeholder "{{}}" was not found in '
            f'the fuzz command "{fuzz_command}"; the generated inputs will not be '
            f"accessible for the test target.",
            file=stderr,
        )

    def inst_fuzz_command(inp_file: str) -> str:
        return fuzz_command.replace("{}", inp_file)

    num_solutions = args.num_solutions
    i = 0
    while True:
        if 0 < num_solutions <= i:
            break

        istr = str(i).rjust(4, "0")
        result = solver.fuzz()
        if isinstance(result, DerivationTree):
            # Write input file
            with open(
                os.path.join(output_dir, f"{istr}{input_ending}"), "wb"
            ) as inp_file:
                inp_file.write(str(result).encode("utf-8"))
                inp_file.seek(0)
                inp_file_name = inp_file.name

            try:
                # Execute fuzz target
                result = subprocess.run(
                    inst_fuzz_command(inp_file_name),
                    shell=True,
                    capture_output=True,
                    check=True,
                    text=True,
                )

                standard_output = result.stdout
                error_output = result.stderr
                return_code = result.returncode
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
        else:
            assert result == ISLaSolver.TIMEOUT or result == ISLaSolver.UNSAT
            if result == ISLaSolver.UNSAT:
                print("UNSAT", flush=True, file=stderr)
            break

        i += 1


def check(stdout, stderr, parser, args):
    files = read_files(args)
    ensure_grammar_constraint_present(stderr, parser, args, files)
    command = args.command

    grammar = parse_grammar(command, args.grammar, files, stderr)
    constraint = parse_constraint(command, args.constraint, files, grammar, stderr)

    if args.input_string:
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
        if inp[-1] == "\n":
            inp = inp[:-1]

    parser = EarleyParser(grammar)
    try:
        tree = DerivationTree.from_parse_tree(next(parser.parse(inp)))
    except Exception as exc:
        print(f"input could not be parsed ({type(exc).__name__})", file=stdout)
        sys.exit(1)

    solver = ISLaSolver(grammar, constraint)

    if solver.evaluate(tree):
        print("input satisfies the ISLa constraint", file=stdout)
        sys.exit(0)
    else:
        print("input does not satisfy the ISLa constraint", file=stdout)
        sys.exit(1)


def parse(stdout, stderr, parser, args):
    print(args)


def stub(stdout, stderr, parser, args):
    command = args.command
    out_dir = args.output_dir
    base_name = args.base_name

    assert_path_is_dir(stderr, command, out_dir)

    grammar_1_file = open(os.path.join(out_dir, f"{base_name}_grammar_1.bnf"), "w")
    constraint_1_file = open(
        os.path.join(out_dir, f"{base_name}_constraint_1.isla"), "w"
    )
    constraint_2_file = open(
        os.path.join(out_dir, f"{base_name}_constraint_2.isla"), "w"
    )

    if args.split_grammar:
        grammar_2_file = open(os.path.join(out_dir, f"{base_name}_grammar_2.py"), "w")

        grammar_2_ref = rf""" The remaining nonterminals are defined in the Python
# grammar in file {grammar_2_file.name}."""

        grammar_2_text = r"""
# This partial grammar defines the nonterminals `<rhs>`, `<var>`, and `<digit>`. While
# in general, definitions in BNF might be slightly better readable and have a well-known
# syntax, the Python variant allows creating expansion alternatives programmatically.
# This comes handy, e.g., if you want to include all ASCII lower-case characters, as
# in the example below, without typing them.
#
# Python grammars need to assign a variable `grammar` of type `Dict[str, List[str]]`.
# Be aware that the ISLa CLI *executes* Python grammar files; consequently, make sure
# that no harmful code is included.

import string

grammar = {
    "<rhs>":
        ["<var>", "<digit>"],
    "<var>": list(string.ascii_lowercase),
    "<digit>": list(string.digits)
}
""".strip()
    else:
        grammar_2_ref = ""

    grammar_1_text = rf"""
# This partial grammar defines the nonterminals `<start>`, `<stmt>`, and `<assgn>`
# using standard BNF syntax.{grammar_2_ref}

<start> ::= <stmt>
<stmt> ::= <assgn> " ; " <stmt> | <assgn>
<assgn> ::= <var> " := " <rhs>""".strip()

    if not args.split_grammar:
        grammar_1_text += rf"""
<rhs> ::= <var> | <digit>
<var> ::= {" | ".join(map(lambda c: f'"{c}"', string.ascii_lowercase))}
<digit> ::= {" | ".join(map(lambda c: f'"{c}"', string.digits))}"""

    constraint_1_text = r"""
# This constraint specifies that all variables (in the assignment language declared
# by the grammar files) occurring on the right-hand side of an assignment have to
# appear in the left-hand side of an *earlier* assignment, as in `x := 1 ; y := x`.
# You can pass multiple constraint files to the ISLa solver CLI. In this case, the
# constraints are combined as a *conjunction*.

forall <assgn> assgn_1:
  exists <assgn> assgn_2: (
    before(assgn_2, assgn_1) and
    assgn_1.<rhs>.<var> = assgn_2.<var>)""".strip()

    constraint_2_text = rf"""
# This constraint adds to the basic correctness constraint in file
# {constraint_2_file.name}, which imposes a definition-use requirement, the requirement
# that at least one variable in the generated assignment program must be an `a`. The
# ISLa solver CLI creates a *conjunction* from this constraint and the other one.

exists <var>: <var> = "a"
""".strip()

    if args.split_grammar:
        grammar_expl = rf"""
- `{grammar_1_file.name}` specifies the first half of the assignment grammar using
  a standard [BNF](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form) notation.
- `{grammar_2_file.name}` specifies the remaining grammar nonterminals in a Python
  program. This permits for more concise notations if you need to include many terminal
  values in your grammar. You find more information on this format in the
  [Fuzzing Book](https://www.fuzzingbook.org/html/Grammars.html).
        """.strip()

        bash_command = rf"""
isla solve \
  -s 1 -f 1 -t 10 -n -1 \
  {grammar_1_file.name} \
  {grammar_2_file.name} \
  {constraint_1_file.name} \
  {constraint_2_file.name}""".strip()
    else:
        grammar_expl = rf"""
- `{grammar_1_file.name}` specifies the the assignment grammar using a standard
  [BNF](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form) notation.
            """.strip()

        bash_command = rf"""
isla solve \
  -s 1 -f 1 -t 10 -n -1 \
  {grammar_1_file.name} \
  {constraint_1_file.name} \
  {constraint_2_file.name}""".strip()

    readme_text = rf"""# Inputs to the ISLa Solver CLI

The ISLa solver/checker CLI accepts multiple grammar and constraint files to generate
or check inputs. In the presence of multiple grammar files, they are merged to a single
grammar; multiple constraints are combined to a conjunction.

This stub project defines grammar and constraint files for a simple assignment language,
which comprises words like `x := 1 ; a := x`. We impose one constraint declaring that
each right-hand side variable has been previously declared, and another one imposing
that at least one `a` variable has to occur. Both the grammar and the two constraints
are split across multiple files:

{grammar_expl}
- `{constraint_1_file.name}` contains the definition-use requirement on
  assignment programs.
- `{constraint_2_file.name}` contains the specialized constraint imposing the existence
  of an `a` variable in the generated strings.

By running the command

```bash
{bash_command}
```

you obtain as many solutions to the specified constraints as the solver can come up with
within 10 seconds (because of the `-t 10` argument, which imposes a 10 seconds timeout).
"""

    grammar_1_file.write(grammar_1_text)
    grammar_1_file.close()

    if args.split_grammar:
        grammar_2_file.write(grammar_2_text)
        grammar_2_file.close()

    constraint_1_file.write(constraint_1_text)
    constraint_1_file.close()

    constraint_2_file.write(constraint_2_text)
    constraint_2_file.close()

    with open(os.path.join(out_dir, "README.md"), "w") as readme_file:
        readme_file.write(readme_text)


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
    create_parse_parser(subparsers, stdout, stderr)
    create_stub_parser(subparsers, stdout, stderr)

    return parser


def read_files(args) -> Dict[str, str]:
    return {io_wrapper.name: io_wrapper.read() for io_wrapper in args.files}


def ensure_grammar_constraint_present(
    stderr, parser, args, files: Dict[str, str]
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
    constraint_arg: str,
    files: Dict[str, str],
    grammar: Grammar,
    stderr,
) -> language.Formula:
    constraint = true()

    try:
        if constraint_arg:
            with redirect_stderr(stderr):
                constraint &= parse_isla(
                    constraint_arg,
                    structural_predicates=STANDARD_STRUCTURAL_PREDICATES,
                    semantic_predicates=STANDARD_SEMANTIC_PREDICATES,
                    grammar=grammar,
                )

        for constraint_file_name in filter(lambda f: f.endswith(".isla"), files):
            with open(constraint_file_name, "r") as constraint_file:
                with redirect_stderr(stderr):
                    constraint &= parse_isla(
                        constraint_file.read(),
                        structural_predicates=STANDARD_STRUCTURAL_PREDICATES,
                        semantic_predicates=STANDARD_SEMANTIC_PREDICATES,
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
                            locals_ = {}
                            exec(grammar_file_content, {}, locals_)
                            grammar |= locals_["grammar"]

    except Exception as exc:
        exc_string = str(exc)
        if exc_string == "None":
            exc_string = ""
        print(
            f"isla {subcommand}: error: A {type(exc).__name__} occurred "
            + f"while parsing the grammar{f' ({exc_string})' if exc_string else ''}",
            file=stderr,
        )
        sys.exit(DATA_FORMAT_ERROR)
    return grammar


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
    num_solutions_arg(parser)
    timeout_arg(parser)
    parser.add_argument(
        "--unsat-support",
        action="store_true",
        default=False,
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
    grammar_constraint_files_arg(parser)


def create_fuzz_parser(subparsers, stdout, stderr):
    parser = subparsers.add_parser(
        "fuzz",
        help="pass solutions to an ISLa constraint to a test subject",
        description="""
Create solutions to an ISLa constraint and a reference grammar, and pass these to
a test subject. An output directory must be specified (`-d`). Into this directory,
ISLa writes three files per generated test input: (1) the input (`..._input.txt`),
(2) the standard output of the fuzzed program (`..._stdout.txt`), (3) the standard
error of the fuzzed program (`..._stderr.txt), and (4) the returned status code of
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
        default=".txt",
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
    grammar_constraint_files_arg(parser)


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
    input_file_arg(parser)

    parser.add_argument(
        "-o",
        "--output-file",
        help="""
The file into which to write the (JSON) derivation tree in case that the input
could be successfully parsed and checked. If no file is given, the tree is printed
to stdout""",
    )

    grammar_arg(parser)
    constraint_arg(parser)
    log_level_arg(parser)
    grammar_constraint_files_arg(parser)


def create_stub_parser(subparsers, stdout, stderr):
    parser = subparsers.add_parser(
        "stub",
        help="create grammar and constraint stubs",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
        description="""
Create grammar and constraint stub files to help kickstart a new
specification project.""",
    )
    parser.set_defaults(func=lambda *args: stub(stdout, stderr, parser, *args))

    parser.add_argument(
        "-b",
        "--base-name",
        default="project",
        help="the base name for the created stubs",
    )

    parser.add_argument(
        "-s",
        "--split-grammar",
        type=bool,
        default=True,
        action=argparse.BooleanOptionalAction,
        help="Split the grammar into a BNF and a Python part. If set to False, only "
        + "one complete BNF grammar will be produced.",
    )

    parser.add_argument(
        "output_dir",
        metavar="OUTPUT_DIR",
        help="the directory into which to write the created stubs",
    )


def grammar_constraint_files_arg(parser):
    parser.add_argument(
        "files",
        nargs="*",
        metavar="FILES",
        type=argparse.FileType("r", encoding="UTF-8"),
        help="""
Possibly multiple ISLa constraint (`*.isla`) and BNF grammar (`*.bnf`) or Python
grammar (`*.py`) files. Multiple grammar files will be simply merged; multiple ISLa
constraints will be combined to a disjunction. Python grammar files must declare a
variable `grammar` of type `Dict[str, List[str]]`, including a rule for a nonterminal
named "<start>" that expands to a single other nonterminal. Note that you can _either_
pass a grammar as a file _or_ via the `--grammar` option. For constraints, it is
possible to use both the option and a file input. However, a grammar and a constraint
must be specified somehow.""",
    )


def grammar_constraint_or_input_files_arg(parser):
    parser.add_argument(
        "files",
        nargs="*",
        metavar="FILES",
        type=argparse.FileType("r", encoding="UTF-8"),
        help="""
Possibly multiple ISLa constraint (`*.isla`) and BNF grammar (`*.bnf`) or Python
grammar (`*.py`) files, and/or an input file for checking/parsing. Multiple grammar
files will be simply merged; multiple ISLa constraints will be combined to a
disjunction. Python grammar files must declare a variable `grammar` of type
`Dict[str, List[str]]`, including a rule for a nonterminal named "<start>" that expands
to a single other nonterminal. Note that you can _either_ pass a grammar as a file _or_
via the `--grammar` option. For constraints, it is possible to use both the option and
a file input. However, a grammar and a constraint must be specified somehow.""",
    )


def log_level_arg(parser):
    parser.add_argument(
        "-l",
        "--log-level",
        choices=["ERROR", "WARNING", "INFO", "DEBUG"],
        default="WARNING",
        help="set the logging level",
    )


def weight_vector_arg(parser):
    parser.add_argument(
        "-w",
        "--weight-vector",
        help="""
Set the ISLa weight vector. Expects a comma-separated list of floating point values""",
        default="1,0.3,2,1,18",
    )


def k_arg(parser):
    parser.add_argument(
        "-k",
        type=int,
        help="""
set the length of the k-paths to be considered for coverage computations""",
        default=3,
    )


def unwinding_depth_arg(parser):
    parser.add_argument(
        "--unwinding-depth",
        type=int,
        default=4,
        help="""
Set the depth until which nonregular grammar elements in SMT-LIB expressions are
unwound to make them regular before the SMT solver is queried""",
    )


def unique_trees_arg(parser):
    parser.add_argument(
        "--unique-trees",
        action="store_true",
        help="""
Enforces the uniqueness of derivation trees in the solver queue. This setting can
improve the generator performance, but can also lead to omitted interesting solutions
in certain cases""",
    )


def smt_insts_arg(parser):
    parser.add_argument(
        "-s",
        "--smt-instantiations",
        type=int,
        default=10,
        help="""
the number of solutions obtained from the SMT solver for atomic SMT-LIB formulas""",
    )


def free_insts_arg(parser):
    parser.add_argument(
        "-f",
        "--free-instantiations",
        type=int,
        default=10,
        help="""
the number of times an unconstrained nonterminal should be randomly instantiated
""",
    )


def timeout_arg(parser):
    parser.add_argument(
        "-t",
        "--timeout",
        type=float,
        default=-1,
        help="""
The number of (fractions of) seconds after which the solver should stop finding
solutions. Negative numbers imply that no timeout is set""",
    )


def num_solutions_arg(parser):
    parser.add_argument(
        "-n",
        "--num-solutions",
        type=int,
        default=1,
        help="""
The number of solutions to generate. Negative numbers indicate an infinite number of
solutions (you need ot set a `--timeout` or forcefully stop ISLa)""",
    )


def output_dir_arg(parser, required: bool = False):
    parser.add_argument(
        "-d",
        "--output-dir",
        required=required,
        help="a directory into which to place generated output files",
    )


def constraint_arg(parser):
    parser.add_argument(
        "-c",
        "--constraint",
        help="An ISLa constraint. If constraints are passed as file(s), too, then all "
        + "provided constraints are combined to one conjunction",
    )


def grammar_arg(parser):
    parser.add_argument(
        "-g", "--grammar", help="the grammar in BNF (if not passed as a file)"
    )


def input_file_arg(parser):
    parser.add_argument(
        "input_file",
        metavar="INPUT_FILE",
        help="""
A file containing the input to check. Note that you can _either_ pass an input as a file
_or_ via the `--input-string` option.""",
        nargs="?",
        type=argparse.FileType("r", encoding="UTF-8"),
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


if __name__ == "__main__":
    main()
