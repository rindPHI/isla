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

import string
import subprocess
import tempfile
from subprocess import PIPE
from typing import Union

import isla.derivation_tree

# Based on:
# Kartik Talwar. Tiny-C Compiler. https://gist.github.com/KartikTalwar/3095780.
from isla.helpers import srange
from isla.isla_predicates import (
    BEFORE_PREDICATE,
    SAME_POSITION_PREDICATE,
    LEVEL_PREDICATE,
)
from isla.language import parse_isla

SCRIPTSIZE_C_GRAMMAR = {
    "<start>": ["<statement>"],
    "<statement>": [
        "<block>",
        "if<paren_expr> <statement> else <statement>",
        "if<paren_expr> <statement>",
        "while<paren_expr> <statement>",
        "do <statement> while<paren_expr>;",
        "<expr>;",
        ";",
    ],
    "<block>": ["{<statements>}"],
    "<statements>": ["<block_statement><statements>", ""],
    "<block_statement>": ["<statement>", "<declaration>"],
    "<declaration>": ["int <id> = <expr>;", "int <id>;"],
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
forall <expr> expr in start:
  forall <id> use_id in expr:
    exists <declaration> decl="int {<id> def_id}[ = <expr>];" in start:
      (level("GE", "<block>", decl, expr) and 
      (before(decl, expr) and 
      (= use_id def_id)))
"""

SCRIPTSIZE_C_DEF_USE_CONSTR = parse_isla(
    SCRIPTSIZE_C_DEF_USE_CONSTR_TEXT,
    SCRIPTSIZE_C_GRAMMAR,
    structural_predicates={BEFORE_PREDICATE, LEVEL_PREDICATE},
)

# TODO: Scoping!
SCRIPTSIZE_C_NO_REDEF_TEXT = """
forall <declaration> declaration="int {<id> def_id}[ = <expr>];" in start:
   forall <declaration> other_declaration="int {<id> other_def_id}[ = <expr>];" in start:
     (same_position(declaration, other_declaration) xor not (= def_id other_def_id))"""

SCRIPTSIZE_C_NO_REDEF_CONSTR = parse_isla(
    SCRIPTSIZE_C_NO_REDEF_TEXT,
    SCRIPTSIZE_C_GRAMMAR,
    structural_predicates={SAME_POSITION_PREDICATE},
)


def compile_scriptsizec_clang(
    tree: isla.derivation_tree.DerivationTree,
) -> Union[bool, str]:
    contents = "int main() {\n"
    contents += "\n" + str(tree).replace("\n", "    \t")
    contents += "\n" + "}"

    with tempfile.NamedTemporaryFile(suffix=".c") as tmp, tempfile.NamedTemporaryFile(
        suffix=".o"
    ) as outfile:
        tmp.write(contents.encode())
        tmp.flush()
        cmd = ["clang", tmp.name, "-o", outfile.name]
        process = subprocess.Popen(cmd, stderr=PIPE)
        (stdout, stderr) = process.communicate()
        exit_code = process.wait()

        err_msg = stderr.decode("utf-8")
        has_error = exit_code != 0 or (bool(err_msg) and "error" in err_msg)

        return True if not has_error else err_msg
