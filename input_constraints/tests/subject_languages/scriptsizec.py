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
from input_constraints.isla_predicates import BEFORE_PREDICATE, SAME_POSITION_PREDICATE

SCRIPTSIZE_C_GRAMMAR = {
    "<start>": ["<statement>"],
    "<statement>": [
        "{<declarations><statements>}",
        "if<paren_expr> <statement>",
        "if<paren_expr> <statement> else <statement>",
        "while<paren_expr> <statement>",
        "do <statement> while<paren_expr>;",
        "<expr>;",
        ";"
    ],
    "<statements>": ["", "<statement><statements>"],
    "<declarations>": ["", "<declaration><declarations>"],
    "<declaration>": [
        "int <id> = <expr>;",
        "int <id>;"
    ],
    "<paren_expr>": ["(<expr>)"],
    "<expr>": [
        "<test>",
        "<id> = <expr>"
    ],
    "<test>": [
        "<sum>",
        "<sum> < <sum>"
    ],
    "<sum>": [
        "<term>",
        "<sum> + <term>",
        "<sum> - <term>"
    ],
    "<term>": [
        "<id>",
        "<int>",
        "<paren_expr>"
    ],
    "<id>": srange(string.ascii_lowercase),
    "<int>": [
        "<digit>",
        "<digit_nonzero><digits>"
    ],
    "<digits>": [
        "<digit>",
        "<digit><int>"
    ],
    "<digit>": srange(string.digits),
    "<digit_nonzero>": list(set(srange(string.digits)) - {"0"}),
}

SCRIPTSIZE_C_DEF_USE_NO_SCOPING_CONSTR_TEXT = """
const start: <start>;

vars {
  expr: <expr>;
  def_id, use_id: <id>;
  declaration: <declaration>;
}

constraint {
  forall expr in start:
    forall use_id in expr:
      (exists declaration="int {def_id};" in start:
         (before(declaration, expr) and
          (= use_id def_id)) or
       exists declaration="int {def_id} = <expr>;" in start:
         (before(declaration, expr) and
          (= use_id def_id)))
}
"""

SCRIPTSIZE_C_DEF_USE_CONSTR_TEXT = """
const start: <start>;

vars {
  def_id, use_id: <id>;
  decl: <declaration>;
  decls: <declarations>;
  stmts: <statements>;
  stmt: <statement>;
}

constraint {
  forall use_id in start:
    exists stmt="{{{decls}{stmts}}}" in start:
      (exists decl="int {def_id};" in start:
         (before(decl, expr) and
          (= use_id def_id)) or
       exists decl="int {def_id} = <expr>;" in start:
         (before(decl, expr) and
          (= use_id def_id)))
}
"""

# SCRIPTSIZE_C_DEF_USE_CONSTR = parse_isla(SCRIPTSIZE_C_DEF_USE_CONSTR_TEXT, structural_predicates={BEFORE_PREDICATE})
SCRIPTSIZE_C_DEF_USE_CONSTR = parse_isla(SCRIPTSIZE_C_DEF_USE_NO_SCOPING_CONSTR_TEXT, structural_predicates={BEFORE_PREDICATE})

# TODO: Scoping!
SCRIPTSIZE_C_NO_REDEF_TEXT = """
const start: <start>;

vars {
  declaration, other_declaration: <declaration>;
  def_id, other_def_id: <id>;
}

constraint {
  (forall declaration="int {def_id};" in start:
     (forall other_declaration="int {other_def_id};" in start:
       (same_position(declaration, other_declaration) or
        not (= def_id other_def_id)) and
      forall other_declaration="int {other_def_id} = <expr>;" in start:
        (same_position(declaration, other_declaration) or
         not (= def_id other_def_id))) and
   forall declaration="int {def_id} = <expr>;" in start:
     (forall other_declaration="int {other_def_id};" in start:
       (same_position(declaration, other_declaration) or
        not (= def_id other_def_id)) and
      forall other_declaration="int {other_def_id} = <expr>;" in start:
        (same_position(declaration, other_declaration) or
         not (= def_id other_def_id))))
}
"""

SCRIPTSIZE_C_NO_REDEF_CONSTR = parse_isla(SCRIPTSIZE_C_NO_REDEF_TEXT, structural_predicates={SAME_POSITION_PREDICATE})


def compile_scriptsizec_clang(tree: isla.DerivationTree) -> Union[bool, str]:
    contents = "int main() {\n"
    contents += "\n" + str(tree).replace("\n", "    \t")
    contents += "\n" + "}"

    with tempfile.NamedTemporaryFile(suffix=".c") as tmp, tempfile.NamedTemporaryFile(suffix=".out") as outfile:
        tmp.write(contents.encode())
        tmp.flush()
        cmd = ["clang", tmp.name, "-o", outfile.name]
        process = subprocess.Popen(cmd, stderr=PIPE)
        (stdout, stderr) = process.communicate()
        exit_code = process.wait()

        return True if exit_code == 0 else stderr.decode("utf-8")
