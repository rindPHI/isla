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

import copy
import string
from typing import cast, Union, List

import z3
from grammar_graph import gg

import isla.derivation_tree
import isla.isla_shortcuts as sc
from isla import language
from isla.helpers import delete_unreachable, srange
from isla.parser import EarleyParser
from isla.z3_helpers import z3_eq
from .tar import ljust_crop_tar, rjust_crop_tar

SIMPLE_TAR_GRAMMAR = {
    "<start>": ["<entries>"],
    "<entries>": ["<entry>", "<entry><entries>"],
    "<entry>": ["<header><content>"],
    "<header>": ["<file_name>" "<checksum>" "<typeflag>" "<linked_file_name>"],
    "<file_name>": ["<file_name_str><maybe_nuls>"],
    "<file_name_str>": [
        "<file_name_first_char><file_name_chars>",
        "<file_name_first_char>",
    ],
    "<checksum>": ["<octal_digits><NUL><SPACE>"],
    "<typeflag>": ["0", "2"],  # Generalize?  # normal file  # symbolic link
    "<linked_file_name>": ["<file_name_str><maybe_nuls>", "<nuls>"],
    "<content>": ["CONTENT"],
    "<octal_digits>": ["<octal_digit><octal_digits>", "<octal_digit>"],
    "<octal_digit>": srange("01234567"),
    "<file_name_first_char>": srange(string.ascii_letters + string.digits + "_"),
    "<file_name_chars>": ["<file_name_char><file_name_chars>", "<file_name_char>"],
    "<file_name_char>": list(
        set(srange(string.printable)) - set(srange(string.whitespace + "\b\f\v"))
    ),
    "<maybe_nuls>": ["", "<nuls>"],
    "<nuls>": ["<NUL>", "<NUL><nuls>"],
    "<NUL>": ["\x00"],
    "<SPACE>": [" "],
}


def tar_checksum(
    graph: gg.GrammarGraph,
    header: isla.derivation_tree.DerivationTree,
    checksum_tree: isla.derivation_tree.DerivationTree,
) -> language.SemPredEvalResult:
    if not header.is_complete():
        return language.SemPredEvalResult(None)

    current_checksum_path = header.find_node(checksum_tree)

    checksum_grammar = copy.deepcopy(SIMPLE_TAR_GRAMMAR)
    checksum_grammar["<start>"] = ["<checksum>"]
    checksum_grammar["<checksum>"] = [
        "<SPACE><SPACE><SPACE><SPACE><SPACE><SPACE><SPACE><SPACE>"
    ]
    delete_unreachable(checksum_grammar)
    checksum_parser = EarleyParser(checksum_grammar)

    space_checksum = isla.derivation_tree.DerivationTree.from_parse_tree(
        next(checksum_parser.parse("        "))
    ).get_subtree((0,))
    header_wo_checksum = header.replace_path(current_checksum_path, space_checksum)

    header_bytes: List[int] = list(str(header_wo_checksum).encode("ascii"))

    checksum_value = str(oct(sum(header_bytes)))[2:].rjust(6, "0") + "\x00 "

    checksum_grammar = copy.deepcopy(SIMPLE_TAR_GRAMMAR)
    checksum_grammar["<start>"] = ["<checksum>"]
    delete_unreachable(checksum_grammar)
    checksum_parser = EarleyParser(checksum_grammar)

    new_checksum_tree = isla.derivation_tree.DerivationTree.from_parse_tree(
        list(checksum_parser.parse(checksum_value))[0]
    ).get_subtree((0,))

    if str(new_checksum_tree) == str(checksum_tree):
        return language.SemPredEvalResult(True)

    return language.SemPredEvalResult({checksum_tree: new_checksum_tree})


TAR_CHECKSUM_PREDICATE = language.SemanticPredicate(
    "tar_checksum", 2, tar_checksum, binds_tree=False
)


def tar_checksum(
    header: Union[language.Variable, isla.derivation_tree.DerivationTree],
    checksum: Union[language.Variable, isla.derivation_tree.DerivationTree],
) -> language.SemanticPredicateFormula:
    return language.SemanticPredicateFormula(TAR_CHECKSUM_PREDICATE, header, checksum)


mgr = language.VariableManager(SIMPLE_TAR_GRAMMAR)
start = mgr.const("$start", "<start>")

link_constraint = sc.forall(
    mgr.bv("$entry", "<entry>"),
    start,
    sc.forall(
        mgr.bv("$typeflag", "<typeflag>"),
        mgr.bv("$entry"),
        mgr.smt(
            cast(z3.BoolRef, z3_eq(mgr.bv("$typeflag").to_smt(), z3.StringVal("0")))
        )
        | (
            mgr.smt(z3_eq(mgr.bv("$typeflag").to_smt(), z3.StringVal("2")))
            & sc.forall_bind(
                mgr.bv("$linked_file_name_str", "<file_name_str>") + "<maybe_nuls>",
                mgr.bv("$linked_file_name", "<linked_file_name>"),
                mgr.bv("$entry"),
                sc.exists(
                    mgr.bv("$linked_entry", "<entry>"),
                    start,
                    (
                        sc.before(mgr.bv("$entry"), mgr.bv("$linked_entry"))
                        | sc.before(mgr.bv("$linked_entry"), mgr.bv("$entry"))
                    )
                    & sc.forall_bind(
                        mgr.bv("$file_name_str", "<file_name_str>") + "<maybe_nuls>",
                        mgr.bv("$file_name"),
                        mgr.bv("$linked_entry"),
                        mgr.smt(
                            z3_eq(
                                mgr.bv("$file_name_str").to_smt(),
                                mgr.bv("$linked_file_name_str").to_smt(),
                            )
                        ),
                    ),
                ),
            )
        ),
    ),
)

file_name_length_constraint = sc.forall(
    mgr.bv("$file_name", "<file_name>"),
    start,
    ljust_crop_tar(mgr.bv("$file_name"), 100, "\x00"),
)

linked_file_name_length_constraint = sc.forall(
    mgr.bv("$linked_file_name", "<linked_file_name>"),
    start,
    ljust_crop_tar(mgr.bv("$linked_file_name"), 100, "\x00"),
)

checksum_length_constraint = sc.forall(
    mgr.bv("$checksum", "<checksum>"),
    start,
    rjust_crop_tar(mgr.bv("$checksum"), 8, "0"),
)

checksum_constraint = sc.forall(
    mgr.bv("$header", "<header>"),
    start,
    sc.forall(
        mgr.bv("$checksum", "<checksum>"),
        mgr.bv("$header"),
        tar_checksum(mgr.bv("$header"), mgr.bv("$checksum")),
    ),
)

TAR_CONSTRAINTS = mgr.create(
    file_name_length_constraint
    & checksum_constraint
    & checksum_length_constraint
    & linked_file_name_length_constraint
    & link_constraint
    # sc.forall(
    #    mgr.bv("$entry", "<entry>"),
    #    start,
    #    sc.forall(
    #        mgr.bv("$typeflag", "<typeflag>"),
    #        mgr.bv("$entry"),
    #        mgr.smt(cast(z3.BoolRef, mgr.bv("$typeflag").to_smt() == z3.StringVal("0")))
    #        | (mgr.smt(mgr.bv("$typeflag").to_smt() == z3.StringVal("2")) &
    #           sc.forall_bind(
    #               mgr.bv("$linked_file_name_chars", "<characters>") + "<maybe_nuls>",
    #               mgr.bv("$linked_file_name", "<linked_file_name>"),
    #               mgr.bv("$entry"),
    #               sc.exists(
    #                   mgr.bv("$linked_entry", "<entry>"),
    #                   start,
    #                   (sc.before(mgr.bv("$entry"), mgr.bv("$linked_entry"))
    #                    | sc.before(mgr.bv("$linked_entry"), mgr.bv("$entry"))) &
    #                   sc.forall_bind(
    #                       mgr.bv("$file_name_chars", "<characters>") + "<maybe_nuls>",
    #                       mgr.bv("$file_name"),
    #                       mgr.bv("$linked_entry"),
    #                       mgr.smt(mgr.bv("$file_name_chars").to_smt() == mgr.bv("$linked_file_name_chars").to_smt())
    #                   )
    #               )))
    #    ))
)
