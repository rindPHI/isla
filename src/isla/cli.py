import argparse
import sys
from typing import Dict
from isla import __version__ as isla_version


def main():
    parser = create_parsers()

    args = parser.parse_args()

    if not args.command and not args.version:
        parser.print_usage(file=sys.stderr)
        print(
            "isla: error: You have to choose a global option or one of the commands "
            + "`solve`, `fuzz`, `check`, or `parse`",
            file=sys.stderr,
        )
        exit(2)

    if args.version:
        print(f"ISLa version {isla_version}")
        sys.exit(0)

    args.func(args)


def create_parsers():
    parser = argparse.ArgumentParser(
        prog="isla",
        description="""
The ISLa command line interface.""",
    )

    parser.add_argument(
        "-v", "--version", help="Print the ISLa version number", action="store_true"
    )

    subparsers = parser.add_subparsers(title="Commands", dest="command", required=False)

    create_solve_parser(subparsers)
    create_fuzz_parser(subparsers)
    create_check_parser(subparsers)
    create_parse_parser(subparsers)

    return parser


def solve(parser, args):
    read_files_ensure_grammar_constraint_present(args, parser)


def read_files_ensure_grammar_constraint_present(args, parser) -> Dict[str, str]:
    files = {io_wrapper.name: io_wrapper.read() for io_wrapper in args.files}

    if not args.grammar and all(not file.endswith(".bnf") for file in files):
        parser.print_usage(file=sys.stderr)
        print(
            "isla solve: error: You must specify a grammar by `--grammar` "
            "or FILES arguments with `.bnf` ending.",
            file=sys.stderr,
        )

        exit(2)

    if not args.constraint and all(not file.endswith(".isla") for file in files):
        parser.print_usage(file=sys.stderr)
        print(
            "isla solve: error: You must specify a constraint by `--constraint` "
            "or FILES arguments with `.isla` ending.",
            file=sys.stderr,
        )

        exit(2)

    return files


def fuzz(parser, args):
    print(args)


def check(parser, args):
    print(args)


def parse(parser, args):
    print(args)


def create_solve_parser(subparsers):
    parser = subparsers.add_parser(
        "solve",
        help="create solutions to ISLa constraints or check their unsatisfiability",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
        description="""
Create solutions to an ISLa constraint and a reference grammar.""",
    )
    parser.set_defaults(func=lambda *args: solve(parser, *args))

    grammar_arg(parser)
    constraint_arg(parser)
    output_dir_arg(parser)
    num_solutions_arg(parser)
    timeout_arg(parser)
    parser.add_argument(
        "--unsat-support",
        type=bool,
        action=argparse.BooleanOptionalAction,
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
    log_level_arg(parser)
    files_arg(parser)


def create_fuzz_parser(subparsers):
    parser = subparsers.add_parser(
        "fuzz",
        help="pass solutions to an ISLa constraint to a test subject",
        description="""
Create solutions to an ISLa constraint and a reference grammar, and pass these to
a test subject.""",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.set_defaults(func=lambda *args: fuzz(parser, *args))

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
    log_level_arg(parser)
    files_arg(parser)


def create_check_parser(subparsers):
    parser = subparsers.add_parser(
        "check",
        help="check whether an input satisfies an ISLa constraint",
        description="""
Check whether an input is derivable from a grammar and satisfies and an ISLa
constraint.""",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.set_defaults(func=lambda *args: check(parser, *args))

    input_string_arg(parser)
    input_file_arg(parser)

    grammar_arg(parser)
    constraint_arg(parser)
    log_level_arg(parser)
    files_arg(parser)


def create_parse_parser(subparsers):
    parser = subparsers.add_parser(
        "parse",
        help="parse an input into a derivation tree if it satisfies an ISLa constraint",
        description="""
Parse an input into a derivation tree if it is derivable from a grammar and
satisfies an ISLa constraint.""",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.set_defaults(func=lambda *args: parse(parser, *args))

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
        type=int,
        default=1,
        help="""
Set the logging level; 0 only prints errors, 1 also warnings, 2 noncritical
information, and 3 a debug trace""",
    )


def weight_vector_arg(parser):
    parser.add_argument(
        "-w",
        "--weight-vector",
        help="""
Set the ISLa weight vector. Expects a comma-separated list of floating point values""",
        default="7,1,4,2,19",
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
        type=int,
        default=False,
        action=argparse.BooleanOptionalAction,
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
