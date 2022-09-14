import argparse
import logging
import os
import sys
from contextlib import redirect_stdout, redirect_stderr
from typing import Dict

from grammar_graph import gg

from isla import __version__ as isla_version
from isla.derivation_tree import DerivationTree
from isla.isla_predicates import (
    STANDARD_STRUCTURAL_PREDICATES,
    STANDARD_SEMANTIC_PREDICATES,
)
from isla.isla_shortcuts import true
from isla.language import parse_bnf, parse_isla
from isla.solver import (
    ISLaSolver,
    GrammarBasedBlackboxCostComputer,
    CostSettings,
    CostWeightVector,
)


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
        exit(2)

    if args.version:
        print(f"ISLa version {isla_version}", file=stdout)
        sys.exit(0)

    level_mapping = {
        "ERROR": logging.ERROR,
        "WARNING": logging.WARNING,
        "INFO": logging.INFO,
        "DEBUG": logging.DEBUG,
    }

    logging.basicConfig(stream=stderr, level=level_mapping[args.log_level])

    args.func(args)


def solve(stdout, stderr, parser, args):
    files = read_files(args)
    ensure_grammar_constraint_present(stderr, parser, args, files)

    grammar = {}
    for grammar_file_name in filter(lambda f: f.endswith(".bnf"), files):
        with open(grammar_file_name, "r") as grammar_file:
            grammar |= parse_bnf(grammar_file.read())

    constraint = true()
    for constraint_file_name in filter(lambda f: f.endswith(".isla"), files):
        with open(constraint_file_name, "r") as constraint_file:
            constraint &= parse_isla(
                constraint_file.read(),
                structural_predicates=STANDARD_STRUCTURAL_PREDICATES,
                semantic_predicates=STANDARD_SEMANTIC_PREDICATES,
                grammar=grammar,
            )

    weight_vector = args.weight_vector.split(",")
    assert len(weight_vector) == 5  # TODO: Exit w/ error message
    assert all(w.isnumeric() for w in weight_vector)
    weight_vector = list(map(int, weight_vector))

    cost_computer = GrammarBasedBlackboxCostComputer(
        CostSettings(
            CostWeightVector(
                tree_closing_cost=weight_vector[0],
                constraint_cost=weight_vector[1],
                derivation_depth_penalty=weight_vector[2],
                low_k_coverage_penalty=weight_vector[3],
                low_global_k_path_coverage_penalty=weight_vector[4],
            ),
            k=args.k,
        ),
        gg.GrammarGraph.from_grammar(grammar),
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
            if not args.output_dir:
                print(result, flush=True, file=stdout)
            else:
                with open(os.path.join(args.output_dir, f"{i}.txt"), "wb") as out_file:
                    out_file.write(str(result).encode("utf-8"))
        else:
            assert result == ISLaSolver.TIMEOUT or result == ISLaSolver.UNSAT
            if result == ISLaSolver.UNSAT:
                print("UNSAT", flush=True, file=stderr)
            break

        i += 1


def fuzz(stdout, stderr, parser, args):
    print(args)


def check(stdout, stderr, parser, args):
    print(args)


def parse(stdout, stderr, parser, args):
    print(args)


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

    return parser


def read_files(args) -> Dict[str, str]:
    return {io_wrapper.name: io_wrapper.read() for io_wrapper in args.files}


def ensure_grammar_constraint_present(
    stderr, parser, args, files: Dict[str, str]
) -> None:
    if not args.grammar and all(not file.endswith(".bnf") for file in files):
        parser.print_usage(file=stderr)
        print(
            "isla solve: error: You must specify a grammar by `--grammar` "
            "or FILES arguments with `.bnf` ending.",
            file=stderr,
        )

        exit(2)

    if not args.constraint and all(not file.endswith(".isla") for file in files):
        parser.print_usage(file=stderr)
        print(
            "isla solve: error: You must specify a constraint by `--constraint` "
            "or FILES arguments with `.isla` ending.",
            file=stderr,
        )

        exit(2)


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
    files_arg(parser)


def create_fuzz_parser(subparsers, stdout, stderr):
    parser = subparsers.add_parser(
        "fuzz",
        help="pass solutions to an ISLa constraint to a test subject",
        description="""
Create solutions to an ISLa constraint and a reference grammar, and pass these to
a test subject.""",
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
    output_dir_arg(parser)
    num_solutions_arg(parser)
    timeout_arg(parser)
    free_insts_arg(parser)
    smt_insts_arg(parser)
    unique_trees_arg(parser)
    unwinding_depth_arg(parser)
    weight_vector_arg(parser)
    k_arg(parser)
    log_level_arg(parser)
    files_arg(parser)


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
    input_file_arg(parser)

    grammar_arg(parser)
    constraint_arg(parser)
    log_level_arg(parser)
    files_arg(parser)


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
    files_arg(parser)


def files_arg(parser):
    parser.add_argument(
        "files",
        nargs="*",
        metavar="FILES",
        type=argparse.FileType("r", encoding="UTF-8"),
        help="""
Possibly multiple ISLa constraint (`*.isla`) and BNF grammar (`*.bnf`) files. Multiple
grammar files will be simply merged; multiple ISLa constraints will be combined to a
disjunction. Note that you can _either_ pass a grammar as a file _or_ via the
`--grammar` option; similarly for constraints and the `--constraint` option. Either
way, a grammar and a constraint must be specified""",
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
        default="7,1,4,2,19",
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


def output_dir_arg(parser):
    parser.add_argument(
        "-d",
        "--output-dir",
        help="a directory into which to place generated output files",
    )


def constraint_arg(parser):
    parser.add_argument(
        "-c", "--constraint", help="the ISLa constraint (if not passed as a file)"
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


if __name__ == "__main__":
    main()
