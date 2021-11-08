import string
import subprocess
import tempfile
from subprocess import PIPE
from typing import Union

from fuzzingbook.Grammars import srange

from input_constraints import isla
# Based on:
# Kartik Talwar. Tiny-C Compiler. https://gist.github.com/KartikTalwar/3095780.
from input_constraints.isla import parse_isla
from input_constraints.isla_predicates import BEFORE_PREDICATE, SAME_POSITION_PREDICATE, LEVEL_PREDICATE

SCRIPTSIZE_C_GRAMMAR = {
    "<start>": ["<statement>"],
    "<statement>": [
        "<block>",
        "<declaration>",
        "if<paren_expr> <statement> else <statement>",
        "if<paren_expr> <statement>",
        "while<paren_expr> <statement>",
        "do <statement> while<paren_expr>;",
        "<expr>;",
        ";"
    ],
    "<block>": ["{<statements>}"],
    "<statements>": ["<statement><statements>", ""],
    "<declaration>": [
        "int <id> = <expr>;",
        "int <id>;"
    ],
    "<paren_expr>": ["(<expr>)"],
    "<expr>": [
        "<id> = <expr>",
        "<test>",
    ],
    "<test>": [
        "<sum> < <sum>",
        "<sum>",
    ],
    "<sum>": [
        "<sum> + <term>",
        "<sum> - <term>",
        "<term>",
    ],
    "<term>": [
        "<paren_expr>",
        "<id>",
        "<int>",
    ],
    "<id>": srange(string.ascii_lowercase),
    "<int>": [
        "<digit_nonzero><digits>",
        "<digit>",
    ],
    "<digits>": [
        "<digit><int>",
        "<digit>",
    ],
    "<digit>": srange(string.digits),
    "<digit_nonzero>": list(set(srange(string.digits)) - {"0"}),
}

# Forall <id>s use_id in any expression (i.e., only RHSs),
#   there must be a <declaration> decl,
#     which occurs before use_id and on the same or a higher <block> level,
#       that assigns use_id a value.
SCRIPTSIZE_C_DEF_USE_CONSTR_TEXT = """
const start: <start>;

vars {
  expr: <expr>;
  def_id, use_id: <id>;
  decl: <declaration>;
}

constraint {
  forall expr in start:
    forall use_id in expr:
      exists decl="int {def_id}[ = <expr>];" in start:
        (level("GE", "<block>", decl, expr) and 
        (before(decl, expr) and 
        (= use_id def_id)))
}
"""

SCRIPTSIZE_C_DEF_USE_CONSTR = parse_isla(
    SCRIPTSIZE_C_DEF_USE_CONSTR_TEXT, structural_predicates={BEFORE_PREDICATE, LEVEL_PREDICATE})

# TODO: Scoping!
SCRIPTSIZE_C_NO_REDEF_TEXT = """
const start: <start>;

vars {
  declaration, other_declaration: <declaration>;
  def_id, other_def_id: <id>;
}

constraint {
  forall declaration="int {def_id}[ = <expr>];" in start:
     forall other_declaration="int {other_def_id}[ = <expr>];" in start:
       (same_position(declaration, other_declaration) or
        not (= def_id other_def_id))
}
"""

SCRIPTSIZE_C_NO_REDEF_CONSTR = parse_isla(SCRIPTSIZE_C_NO_REDEF_TEXT, structural_predicates={SAME_POSITION_PREDICATE})


def compile_scriptsizec_clang(tree: isla.DerivationTree) -> Union[bool, str]:
    contents = "int main() {\n"
    contents += "\n" + str(tree).replace("\n", "    \t")
    contents += "\n" + "}"

    with tempfile.NamedTemporaryFile(suffix=".c") as tmp:
        tmp.write(contents.encode())
        tmp.flush()
        cmd = ["clang", tmp.name]
        process = subprocess.Popen(cmd, stderr=PIPE)
        (stdout, stderr) = process.communicate()
        exit_code = process.wait()

        return True if exit_code == 0 else stderr.decode("utf-8")
