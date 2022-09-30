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
import os
import string
import subprocess
import tempfile
from subprocess import PIPE
from typing import Union, List, Optional, Callable

from grammar_graph import gg

import isla.derivation_tree
from isla import language
from isla.helpers import delete_unreachable, roundup, srange, tree_to_string
from isla.isla_predicates import just, OCTAL_TO_DEC_PREDICATE, SAME_POSITION_PREDICATE
from isla.language import parse_isla
from isla.type_defs import ParseTree

TAR_GRAMMAR = {
    "<start>": ["<entries><final_entry>"],
    "<entries>": ["<entry>", "<entry><entries>"],
    "<entry>": ["<header><content>"],
    "<header>": [
        "<file_name>"
        "<file_mode>"
        "<uid>"
        "<gid>"
        "<file_size>"
        "<mod_time>"
        "<checksum>"
        "<typeflag>"
        "<linked_file_name>"
        "ustar<NUL>"
        "00"
        "<uname>"
        "<gname>"
        "<dev_maj_num>"
        "<dev_min_num>"
        "<file_name_prefix>"
        "<header_padding>"
    ],
    "<file_name>": ["<file_name_str><maybe_nuls>"],
    "<file_name_str>": [
        "<file_name_first_char><file_name_chars>",
        "<file_name_first_char>",
    ],
    "<file_mode>": ["<octal_digits><SPACE><NUL>"],
    "<uid>": ["<octal_digits><SPACE><NUL>"],
    "<gid>": ["<octal_digits><SPACE><NUL>"],
    "<file_size>": ["<octal_digits><SPACE>"],
    "<mod_time>": ["<octal_digits><SPACE>"],
    "<checksum>": ["<octal_digits><NUL><SPACE>"],
    "<typeflag>": ["0", "2"],  # Generalize?  # normal file  # symbolic link
    "<linked_file_name>": ["<file_name_str><maybe_nuls>", "<nuls>"],
    # From the useradd manual:
    # Regular expression terms for usernames: [a-z_][a-z0-9_-]*[$]?
    "<uname>": ["<uname_str><maybe_nuls>"],
    "<gname>": ["<uname_str><maybe_nuls>"],
    "<uname_str>": [
        "<uname_first_char><uname_chars><maybe_dollar>",
        "<uname_first_char><maybe_dollar>",
    ],
    "<uname_first_char>": srange(string.ascii_lowercase + "_"),
    "<uname_char>": srange(string.ascii_lowercase + string.digits + "_-"),
    "<uname_chars>": ["<uname_char><uname_chars>", "<uname_char>"],
    "<maybe_dollar>": ["$", ""],
    "<dev_maj_num>": ["<octal_digits><SPACE><NUL>"],
    "<dev_min_num>": ["<octal_digits><SPACE><NUL>"],
    "<file_name_prefix>": ["<nuls>"],  # TODO: Find out how this field is used!
    "<header_padding>": ["<nuls>"],
    "<content>": ["<maybe_characters><maybe_nuls>"],
    "<final_entry>": ["<nuls>"],
    "<octal_digits>": ["<octal_digit><octal_digits>", "<octal_digit>"],
    "<octal_digit>": srange("01234567"),
    "<maybe_characters>": ["<characters>", ""],
    "<characters>": ["<character><characters>", "<character>"],
    "<character>": srange(string.printable),
    "<file_name_first_char>": srange(string.ascii_letters + string.digits + "_"),
    "<file_name_chars>": ["<file_name_char><file_name_chars>", "<file_name_char>"],
    "<file_name_char>": list(
        set(srange(string.printable)) - set(srange(string.whitespace + "\b\f\v"))
    ),
    "<maybe_nuls>": ["<nuls>", ""],
    "<nuls>": ["<NUL><nuls>", "<NUL>"],
    "<NUL>": ["\x00"],
    "<SPACE>": [" "],
}


def tar_checksum(
    _: Optional[gg.GrammarGraph],
    header: isla.derivation_tree.DerivationTree,
    checksum_tree: isla.derivation_tree.DerivationTree,
) -> language.SemPredEvalResult:
    if not header.is_complete():
        return language.SemPredEvalResult(None)

    checksum_parser = TarParser(start_symbol="<checksum>")

    space_checksum = ("<checksum>", [("<SPACE>", [(" ", [])]) for _ in range(8)])

    header_wo_checksum = header.replace_path(
        header.find_node(checksum_tree),
        isla.derivation_tree.DerivationTree.from_parse_tree(space_checksum),
    )

    header_bytes: List[int] = list(str(header_wo_checksum).encode("ascii"))

    checksum_value = str(oct(sum(header_bytes)))[2:].rjust(6, "0") + "\x00 "
    new_checksum_tree = isla.derivation_tree.DerivationTree.from_parse_tree(
        list(checksum_parser.parse(checksum_value))[0]
    ).get_subtree((0,))

    if str(new_checksum_tree) == str(checksum_tree):
        return language.SemPredEvalResult(True)

    return language.SemPredEvalResult({checksum_tree: new_checksum_tree})


TAR_CHECKSUM_PREDICATE = language.SemanticPredicate(
    "tar_checksum", 2, tar_checksum, binds_tree=False
)


def mk_tar_parser(start: str) -> Callable[[str], List[ParseTree]]:
    parser = TarParser(start_symbol=start)
    return lambda inp: parser.parse(inp)


LJUST_CROP_TAR_PREDICATE = language.SemanticPredicate(
    "ljust_crop_tar",
    3,
    lambda graph, tree, width, fillchar: just(
        True, True, mk_tar_parser, tree, width, fillchar
    ),
    binds_tree=False,
)

RJUST_CROP_TAR_PREDICATE = language.SemanticPredicate(
    "rjust_crop_tar",
    3,
    lambda graph, tree, width, fillchar: just(
        False, True, mk_tar_parser, tree, width, fillchar
    ),
    binds_tree=False,
)


def ljust_crop_tar(
    tree: Union[language.Variable, isla.derivation_tree.DerivationTree],
    width: int,
    fillchar: str,
) -> language.SemanticPredicateFormula:
    return language.SemanticPredicateFormula(
        LJUST_CROP_TAR_PREDICATE, tree, width, fillchar
    )


def rjust_crop_tar(
    tree: Union[language.Variable, isla.derivation_tree.DerivationTree],
    width: int,
    fillchar: str,
) -> language.SemanticPredicateFormula:
    return language.SemanticPredicateFormula(
        RJUST_CROP_TAR_PREDICATE, tree, width, fillchar
    )


octal_conv_grammar = copy.deepcopy(TAR_GRAMMAR)
octal_conv_grammar.update(
    {
        "<start>": ["<octal_digits>", "<decimal_digits>"],
        "<decimal_digits>": ["<decimal_digit><decimal_digits>", "<decimal_digit>"],
        "<decimal_digit>": srange(string.digits),
    }
)
delete_unreachable(octal_conv_grammar)

octal_conv_graph = gg.GrammarGraph.from_grammar(octal_conv_grammar)


def octal_to_decimal_tar(
    octal: Union[language.Variable, isla.derivation_tree.DerivationTree],
    decimal: Union[language.Variable, isla.derivation_tree.DerivationTree],
) -> language.SemanticPredicateFormula:
    return language.SemanticPredicateFormula(
        OCTAL_TO_DEC_PREDICATE(octal_conv_graph, "<octal_digits>", "<decimal_digits>"),
        octal,
        decimal,
    )


file_size_constr = parse_isla(
    """
forall <file_size> file_size="{<octal_digits> octal_digits}<SPACE>" in start:
  exists int decimal:
    ((>= (str.to.int decimal) 10) and
    ((<= (str.to.int decimal) 100) and 
    (octal_to_decimal(octal_digits, decimal) and 
     rjust_crop_tar(file_size, 12, "0"))))
""",
    TAR_GRAMMAR,
    semantic_predicates={
        OCTAL_TO_DEC_PREDICATE(octal_conv_graph, "<octal_digits>", "<decimal_digits>"),
        RJUST_CROP_TAR_PREDICATE,
    },
)

file_name_length_constraint = parse_isla(
    """
forall <file_name> file_name in start:
  ((> (str.len file_name) 0) and
   ljust_crop_tar(file_name, 100, "\x00"))
""",
    TAR_GRAMMAR,
    semantic_predicates={LJUST_CROP_TAR_PREDICATE},
)

file_mode_length_constraint = parse_isla(
    """
forall <file_mode> file_mode in start:
  rjust_crop_tar(file_mode, 8, "0")
""",
    TAR_GRAMMAR,
    semantic_predicates={RJUST_CROP_TAR_PREDICATE},
)

uid_length_constraint = parse_isla(
    """
forall <uid> uid in start:
  rjust_crop_tar(uid, 8, "0")
""",
    TAR_GRAMMAR,
    semantic_predicates={RJUST_CROP_TAR_PREDICATE},
)

gid_length_constraint = parse_isla(
    """
forall <gid> gid in start:
  rjust_crop_tar(gid, 8, "0")
""",
    TAR_GRAMMAR,
    semantic_predicates={RJUST_CROP_TAR_PREDICATE},
)

mod_time_length_constraint = parse_isla(
    """
forall <mod_time> mod_time in start:
  rjust_crop_tar(mod_time, 12, "0")
""",
    TAR_GRAMMAR,
    semantic_predicates={RJUST_CROP_TAR_PREDICATE},
)

checksum_constraint = parse_isla(
    """
forall <header> header in start:
  forall <checksum> checksum in header:
    tar_checksum(header, checksum)
""",
    TAR_GRAMMAR,
    semantic_predicates={TAR_CHECKSUM_PREDICATE},
)

linked_file_name_length_constraint = parse_isla(
    """
forall <linked_file_name> linked_file_name in start:
  ljust_crop_tar(linked_file_name, 100, "\x00")
""",
    TAR_GRAMMAR,
    semantic_predicates={LJUST_CROP_TAR_PREDICATE},
)

uname_length_constraint = parse_isla(
    """
forall <uname> uname in start:
  ljust_crop_tar(uname, 32, "\x00")
""",
    TAR_GRAMMAR,
    semantic_predicates={LJUST_CROP_TAR_PREDICATE},
)

gname_length_constraint = parse_isla(
    """
forall <gname> gname in start:
  ljust_crop_tar(gname, 32, "\x00")
""",
    TAR_GRAMMAR,
    semantic_predicates={LJUST_CROP_TAR_PREDICATE},
)

dev_maj_num_length_constraint = parse_isla(
    """
forall <dev_maj_num> dev_maj_num in start:
  rjust_crop_tar(dev_maj_num, 8, "0")
""",
    TAR_GRAMMAR,
    semantic_predicates={RJUST_CROP_TAR_PREDICATE},
)

dev_min_num_length_constraint = parse_isla(
    """
forall <dev_min_num> dev_min_num in start:
  rjust_crop_tar(dev_min_num, 8, "0")
""",
    TAR_GRAMMAR,
    semantic_predicates={RJUST_CROP_TAR_PREDICATE},
)

prefix_length_constraint = parse_isla(
    """
forall <file_name_prefix> prefix in start:
  ljust_crop_tar(prefix, 155, "\x00")
""",
    TAR_GRAMMAR,
    semantic_predicates={LJUST_CROP_TAR_PREDICATE},
)

header_padding_length_constraint = parse_isla(
    """
forall <header_padding> padding in start:
  ljust_crop_tar(padding, 12, "\x00")
""",
    TAR_GRAMMAR,
    semantic_predicates={LJUST_CROP_TAR_PREDICATE},
)

content_length_constraint = parse_isla(
    """
forall <content> content in start:
  ljust_crop_tar(content, 512, "\x00")
""",
    TAR_GRAMMAR,
    semantic_predicates={LJUST_CROP_TAR_PREDICATE},
)

content_size_constr = parse_isla(
    """
forall <entry> entry in start:
  forall <content> content="{<maybe_characters> content_chars}<maybe_nuls>" in entry:
    forall <characters> characters in content_chars:
      forall <file_size> file_size="{<octal_digits> octal_digits}<SPACE>" in entry:
        exists int dec_digits:
          ((>= (str.to.int dec_digits) 10) and 
          ((<= (str.to.int dec_digits) 100) and 
          (octal_to_decimal(octal_digits, dec_digits) and 
           ljust_crop_tar(characters, dec_digits, " "))))
""",
    TAR_GRAMMAR,
    semantic_predicates={
        OCTAL_TO_DEC_PREDICATE(octal_conv_graph, "<octal_digits>", "<decimal_digits>"),
        LJUST_CROP_TAR_PREDICATE,
    },
)

final_entry_length_constraint = parse_isla(
    """
forall <final_entry> final in start:
  ljust_crop_tar(final, 1024, "\x00")
""",
    TAR_GRAMMAR,
    semantic_predicates={LJUST_CROP_TAR_PREDICATE},
)

link_constraint = parse_isla(
    """
forall <entry> entry in start:
  forall <typeflag> typeflag in entry:
    ((= typeflag "0") or 
      ((= typeflag "2") and 
      (forall <linked_file_name> linked_file_name_field_1="<nuls>" in entry:
         false 
       and 
       forall <file_name> linked_file_name_field_2="{<file_name_str> linked_file_name_str}<maybe_nuls>" in entry:
         exists <entry> linked_entry in start:
           (not same_position(entry, linked_entry) and 
            forall <file_name> file_name="{<file_name_str> file_name_str}<maybe_nuls>" in linked_entry:
              ((= linked_file_name_str file_name_str) and
               forall <file_name> entry_file_name="{<file_name_str> entry_file_name_str}<maybe_nuls>" in entry:
                 not (= file_name_str entry_file_name_str))))))
""",
    TAR_GRAMMAR,
    structural_predicates={SAME_POSITION_PREDICATE},
)

TAR_CONSTRAINTS = (
    link_constraint
    & file_name_length_constraint
    & file_mode_length_constraint
    & uid_length_constraint
    & gid_length_constraint
    & file_size_constr
    & mod_time_length_constraint
    & linked_file_name_length_constraint
    & uname_length_constraint
    & gname_length_constraint
    & dev_maj_num_length_constraint
    & dev_min_num_length_constraint
    & prefix_length_constraint
    & header_padding_length_constraint
    & content_length_constraint
    & checksum_constraint
    & content_size_constr
    & final_entry_length_constraint
)


class TarParser:
    def __init__(self, start_symbol="<start>"):
        self.pos = 0
        self.inp = ""
        self.start_symbol = start_symbol

    def parse(self, inp: str) -> List[ParseTree]:
        self.pos = 0
        self.inp = inp

        return [self.parse_start()]

    def parse_start(self) -> ParseTree:
        if self.start_symbol == "<start>":
            children = [self.parse_entries(), self.parse_final_entry()]
        elif self.start_symbol == "<entries>":
            children = [self.parse_entries()]
        elif self.start_symbol == "<entry>":
            children = [self.parse_entry()]
        elif self.start_symbol == "<header>":
            children = [self.parse_header()]
        elif self.start_symbol == "<file_name>":
            children = [self.parse_file_name()]
        elif self.start_symbol == "<file_mode>":
            children = [self.parse_file_mode()]
        elif self.start_symbol == "<uid>":
            children = [self.parse_uid()]
        elif self.start_symbol == "<gid>":
            children = [self.parse_gid()]
        elif self.start_symbol == "<file_size>":
            children = [self.parse_file_size()]
        elif self.start_symbol == "<mod_time>":
            children = [self.parse_mod_time()]
        elif self.start_symbol == "<checksum>":
            children = [self.parse_checksum()]
        elif self.start_symbol == "<typeflag>":
            children = [self.parse_typeflag()]
        elif self.start_symbol == "<linked_file_name>":
            children = [self.parse_linked_file_name()]
        elif self.start_symbol == "<uname>":
            children = [self.parse_uname()]
        elif self.start_symbol == "<gname>":
            children = [self.parse_gname()]
        elif self.start_symbol == "<dev_maj_num>":
            children = [self.parse_dev_maj_num()]
        elif self.start_symbol == "<dev_min_num>":
            children = [self.parse_dev_min_num()]
        elif self.start_symbol == "<file_name_prefix>":
            children = [self.parse_file_name_prefix()]
        elif self.start_symbol == "<header_padding>":
            children = [self.parse_header_padding()]
        elif self.start_symbol == "<content>":
            children = [self.parse_content()]
        elif self.start_symbol == "<final_entry>":
            children = [self.parse_final_entry()]
        elif self.start_symbol == "<characters>":
            children = [self.parse_characters()]
        else:
            raise NotImplementedError(f"Unknown start symbol {self.start_symbol}")

        return "<start>", children

    def parse_entries(self) -> ParseTree:
        entries = []

        block = self.peek(512)

        if block is None:
            raise SyntaxError(
                f"invalid syntax at pos. {self.pos}: premature end of file"
            )

        while not self.is_null(block):
            entries.append(self.parse_entry())

            block = self.peek(512)
            if block is None:
                raise SyntaxError(
                    f"invalid syntax at pos. {self.pos}: premature end of file"
                )

        children = []
        result = ("<entries>", children)
        for idx, entry in enumerate(entries):
            new_children = []
            children.append(entry)

            if idx < len(entries) - 1:
                children.append(("<entries>", new_children))
                children = new_children

        return result

    def parse_entry(self):
        header = self.parse_header()

        content_size_str = tree_to_string(header[1][4])[:-1]
        content_size = 0
        for i in range(len(content_size_str)):
            content_size += int(content_size_str[len(content_size_str) - i - 1]) * (
                8**i
            )

        content = self.parse_content(content_size)

        return "<entry>", [header, content]

    def parse_content(self, content_size: Optional[int] = None) -> ParseTree:
        padded_characters = self.parse_padded_characters(
            self.read(
                roundup(content_size, 512)
                if content_size is not None
                else len(self.inp)
            ),
            parent_nonterminal="<content>",
            characters_optional_nonterminal="<maybe_characters>",
            padding_optional=True,
        )

        # We patch the result, since there are additional (nullable) `<maybe_...>` nonterminals that were
        # not considered before, and the actual characters/nuls nonterminals are no longer nullable.
        first_child = padded_characters[1][0]
        second_child = padded_characters[1][1]

        if first_child[0] == "<characters>":
            first_child = ("<maybe_characters>", [first_child])
        if second_child[0] == "<nuls>":
            second_child = ("<maybe_nuls>", [second_child])

        if first_child[1] and not first_child[1][0][1]:
            first_child = ("<maybe_characters>", [])
        if second_child[1] and not second_child[1][0][1]:
            second_child = ("<maybe_nuls>", [])

        return "<content>", [first_child, second_child]

    def parse_header(self) -> ParseTree:
        file_name = self.parse_file_name()
        file_mode = self.parse_file_mode()
        uid = self.parse_uid()
        gid = self.parse_gid()
        file_size = self.parse_file_size()
        mod_time = self.parse_mod_time()
        checksum = self.parse_checksum()
        typeflag = self.parse_typeflag()
        linked_file_name = self.parse_linked_file_name()

        ustar00_str = self.read(8)
        if ustar00_str != "ustar\x0000":
            raise SyntaxError(
                f"invalid syntax at pos. {self.pos - 8}: {ustar00_str} ('ustar\x0000' expected)"
            )

        uname = self.parse_uname()
        gname = self.parse_gname()
        dev_maj_num = self.parse_dev_maj_num()
        dev_min_num = self.parse_dev_min_num()
        file_name_prefix = (
            self.parse_file_name_prefix()
        )  # TODO: Find out how this field is used!
        padding = self.parse_header_padding()

        return (
            "<header>",
            [
                file_name,
                file_mode,
                uid,
                gid,
                file_size,
                mod_time,
                checksum,
                typeflag,
                linked_file_name,
                ("ustar", []),
                ("<NUL>", [("\x00", [])]),
                ("00", []),
                uname,
                gname,
                dev_maj_num,
                dev_min_num,
                file_name_prefix,
                padding,
            ],
        )

    def parse_header_padding(self):
        padding = ("<header_padding>", [self.parse_nuls(self.read(12))])
        return padding

    def parse_file_name_prefix(self):
        file_name_prefix = ("<file_name_prefix>", [self.parse_nuls(self.read(155))])
        return file_name_prefix

    def parse_dev_min_num(self):
        dev_min_num_padded = self.read(8)
        if dev_min_num_padded[-2:] != " \x00":
            raise SyntaxError(
                f"invalid syntax at pos. {self.pos - 2}: {dev_min_num_padded[-2:]} (' \x00' expected)"
            )
        dev_min_num = (
            "<dev_min_num>",
            [
                self.parse_octal_digits(dev_min_num_padded[:-2]),
                ("<SPACE>", [(" ", [])]),
                ("<NUL>", [("\x00", [])]),
            ],
        )
        return dev_min_num

    def parse_dev_maj_num(self):
        dev_maj_num_padded = self.read(8)
        if dev_maj_num_padded[-2:] != " \x00":
            raise SyntaxError(
                f"invalid syntax at pos. {self.pos - 2}: {dev_maj_num_padded[-2:]} (' \x00' expected)"
            )
        dev_maj_num = (
            "<dev_maj_num>",
            [
                self.parse_octal_digits(dev_maj_num_padded[:-2]),
                ("<SPACE>", [(" ", [])]),
                ("<NUL>", [("\x00", [])]),
            ],
        )
        return dev_maj_num

    def parse_gname(self):
        inp = self.read(32)

        if "\00" in inp:
            nuls_offset = inp.index("\x00")
            uname_str = self.parse_uname_str(inp[:nuls_offset])
            assert not uname_str[1][1][0] == "<uname_chars>" or uname_str[1][1][1]
            nuls = ("<maybe_nuls>", [self.parse_nuls(inp[nuls_offset:])])
            children = [uname_str, nuls]
        else:
            uname_str = self.parse_uname_str(inp)
            assert not uname_str[1][1][0] == "<uname_chars>" or uname_str[1][1][1]
            children = [uname_str, ("<maybe_nuls>", [])]

        return "<gname>", children

    def parse_uname(self):
        inp = self.read(32)

        if "\00" in inp:
            nuls_offset = inp.index("\x00")
            uname_str = self.parse_uname_str(inp[:nuls_offset])
            assert not uname_str[1][1][0] == "<uname_chars>" or uname_str[1][1][1]
            nuls = ("<maybe_nuls>", [self.parse_nuls(inp[nuls_offset:])])
            children = [uname_str, nuls]
        else:
            uname_str = self.parse_uname_str(inp)
            assert not uname_str[1][1][0] == "<uname_chars>" or uname_str[1][1][1]
            children = [uname_str, ("<maybe_nuls>", [])]

        return "<uname>", children

    def parse_uname_str(self, inp: str):
        if "\x00" in inp:
            raise SyntaxError("No NUL characters allowed in <uname_str>")

        uname_first_char = inp[0]

        dollar_index = len(inp) if "$" not in inp else inp.index("$")

        uname_chars = self.parse_characters(
            inp[1:dollar_index],
            characters_nonterminal="<uname_chars>",
            character_nonterminal="<uname_char>",
        )

        if not uname_chars[1]:
            return "<uname_str>", [
                ("<uname_first_char>", [(uname_first_char, [])]),
                ("<maybe_dollar>", [("$", [])] if dollar_index < len(inp) else []),
            ]

        return "<uname_str>", [
            ("<uname_first_char>", [(uname_first_char, [])]),
            uname_chars,
            ("<maybe_dollar>", [("$", [])] if dollar_index < len(inp) else []),
        ]

    def parse_file_name(self):
        inp = self.read(100)

        if "\00" in inp:
            nuls_offset = inp.index("\x00")
            file_name_str = self.parse_file_name_str(inp[:nuls_offset])
            nuls = ("<maybe_nuls>", [self.parse_nuls(inp[nuls_offset:])])
            children = [file_name_str, nuls]
        else:
            file_name_str = self.parse_file_name_str(inp)
            children = [file_name_str, ("<maybe_nuls>", [])]

        return "<file_name>", children

    def parse_file_name_str(self, inp: str):
        if "\x00" in inp:
            raise SyntaxError("No NUL characters allowed in <file_name_str>")

        file_name_first_char = inp[0]

        if len(inp) == 1:
            return "<file_name_str>", [
                ("<file_name_first_char>", [(file_name_first_char, [])])
            ]

        file_name_chars = self.parse_characters(
            inp[1:],
            characters_nonterminal="<file_name_chars>",
            character_nonterminal="<file_name_char>",
        )

        return "<file_name_str>", [
            ("<file_name_first_char>", [(file_name_first_char, [])]),
            file_name_chars,
        ]

    def parse_linked_file_name(self):
        if self.peek() == "\x00":
            return "<linked_file_name>", [self.parse_nuls(self.read(100))]

        return "<linked_file_name>", self.parse_file_name()[1]

    def parse_typeflag(self):
        typeflag = ("<typeflag>", [(self.read(1), [])])
        if typeflag[1][0][0] not in string.digits:
            raise SyntaxError(
                f"invalid syntax at {self.pos - 1}: {str(typeflag)} (digit expected)"
            )
        return typeflag

    def parse_checksum(self):
        checksum_padded = self.read(8)
        if checksum_padded[-2:] != "\x00 ":
            raise SyntaxError(
                f"invalid syntax at pos. {self.pos - 2}: {checksum_padded[-2:]} ('\x00 ' expected)"
            )
        checksum = (
            "<checksum>",
            [
                self.parse_octal_digits(checksum_padded[:-2]),
                ("<NUL>", [("\x00", [])]),
                ("<SPACE>", [(" ", [])]),
            ],
        )
        return checksum

    def parse_mod_time(self):
        mod_time_padded = self.read(12)
        if mod_time_padded[-1] != " ":
            raise SyntaxError(
                f"invalid syntax at pos. {self.pos - 1}: {mod_time_padded[-1]} (' ' expected)"
            )
        mod_time = (
            "<mod_time>",
            [self.parse_octal_digits(mod_time_padded[:-1]), ("<SPACE>", [(" ", [])])],
        )
        return mod_time

    def parse_file_size(self):
        file_size_padded = self.read(12)
        if file_size_padded[-1] != " ":
            raise SyntaxError(
                f"invalid syntax at pos. {self.pos - 1}: {file_size_padded[-1]} (' ' expected)"
            )
        file_size = (
            "<file_size>",
            [self.parse_octal_digits(file_size_padded[:-1]), ("<SPACE>", [(" ", [])])],
        )
        return file_size

    def parse_gid(self):
        gid_padded = self.read(8)
        if gid_padded[-2:] != " \x00":
            raise SyntaxError(
                f"invalid syntax at pos. {self.pos - 2}: {gid_padded[-2:]} (' \x00' expected)"
            )
        gid = (
            "<gid>",
            [
                self.parse_octal_digits(gid_padded[:-2]),
                ("<SPACE>", [(" ", [])]),
                ("<NUL>", [("\x00", [])]),
            ],
        )
        return gid

    def parse_uid(self):
        uid_padded = self.read(8)
        if uid_padded[-2:] != " \x00":
            raise SyntaxError(
                f"invalid syntax at pos. {self.pos - 2}: {uid_padded[-2:]} (' \x00' expected)"
            )
        uid = (
            "<uid>",
            [
                self.parse_octal_digits(uid_padded[:-2]),
                ("<SPACE>", [(" ", [])]),
                ("<NUL>", [("\x00", [])]),
            ],
        )
        return uid

    def parse_file_mode(self):
        file_mode_padded = self.read(8)
        if file_mode_padded[-2:] != " \x00":
            raise SyntaxError(
                f"invalid syntax at pos. {self.pos - 2}: {file_mode_padded[-2:]} (' \x00' expected)"
            )
        file_mode = (
            "<file_mode>",
            [
                self.parse_octal_digits(file_mode_padded[:-2]),
                ("<SPACE>", [(" ", [])]),
                ("<NUL>", [("\x00", [])]),
            ],
        )
        return file_mode

    def parse_padded_characters(
        self,
        inp: str,
        parent_nonterminal: Optional[str] = None,
        padding_optional=True,
        characters_optional_nonterminal: Optional[str] = None,
        characters_nonterminal: str = "<characters>",
        character_nonterminal: str = "<character>",
    ) -> Union[ParseTree, List[ParseTree]]:
        if "\x00" in inp and inp[0] != "\x00":
            nuls_offset = inp.index("\x00")
            children = [
                self.parse_characters(
                    inp=inp[:nuls_offset],
                    characters_nonterminal=characters_nonterminal,
                    character_nonterminal=character_nonterminal,
                ),
                self.parse_nuls(inp[nuls_offset:]),
            ]
        elif "\x00" in inp and inp[0] == "\x00":
            if characters_optional_nonterminal:
                children = [(characters_optional_nonterminal, []), self.parse_nuls(inp)]
            else:
                raise SyntaxError(
                    f"invalid syntax at {self.pos - len(inp)}: {inp} (characters expected)"
                )
        elif padding_optional:
            children = [self.parse_characters(inp=inp), ("<maybe_nuls>", [])]
        else:
            raise SyntaxError(
                f"invalid syntax at {self.pos - len(inp)}: {inp} (padding expected)"
            )

        if parent_nonterminal:
            return parent_nonterminal, children
        else:
            return children

    def parse_octal_digits(self, inp: str) -> ParseTree:
        children = []
        result = ("<octal_digits>", children)
        for idx, char in enumerate(inp):
            if char not in "01234567":
                raise SyntaxError(
                    f"invalid syntax at {self.pos - len(inp) + idx}: {inp[idx:]} (octal digit expected)"
                )
            new_children = []
            children.append(("<octal_digit>", [(char, [])]))

            if idx < len(inp) - 1:
                children.append(("<octal_digits>", new_children))
                children = new_children

        return result

    def parse_characters(
        self,
        inp: Optional[str] = None,
        characters_nonterminal: str = "<characters>",
        character_nonterminal: str = "<character>",
    ) -> ParseTree:
        if inp is None:
            inp = self.inp

        children = []
        result = (characters_nonterminal, children)
        for idx, char in enumerate(inp):
            if char == "\x00":
                raise SyntaxError(
                    f"invalid syntax at {self.pos - len(inp) + idx}: {inp[idx:]} "
                    f"(NUL encountered, character expected)"
                )
            new_children = []
            children.append((character_nonterminal, [(char, [])]))

            if idx < len(inp) - 1:
                children.append((characters_nonterminal, new_children))
                children = new_children

        return result

    def parse_nuls(self, inp: str) -> ParseTree:
        children = []
        result = ("<nuls>", children)
        for idx, char in enumerate(inp):
            if char != "\x00":
                raise SyntaxError(
                    f"invalid syntax at pos. {self.pos - len(inp) + idx}: {inp[idx:]} (NUL expected)"
                )
            new_children = []
            children.append(("<NUL>", [(char, [])]))

            if idx < len(inp) - 1:
                children.append(("<nuls>", new_children))
                children = new_children

        return result

    def parse_final_entry(self) -> ParseTree:
        i = 0
        inp = ""
        while self.peek(512) is not None:
            inp += self.read(512)
            i += 1
        if i < 2 or len(self.inp) != self.pos or not self.is_null(inp):
            raise SyntaxError(
                f"invalid syntax at pos. {self.pos}: {self.inp[self.pos:]} "
                f"(at least two 512 byte blocks of NULs expected"
            )

        return "<final_entry>", [self.parse_nuls(inp)]

    def is_null(self, inp: str) -> bool:
        return all(c == "\x00" for c in inp)

    def peek(self, n=1) -> Optional[str]:
        result = self.inp[self.pos : self.pos + n]
        return result if len(result) == n else None

    def read(self, n=1) -> Optional[str]:
        result = self.inp[self.pos : self.pos + n]
        if len(result) != n:
            raise SyntaxError(
                f"at {self.pos}: {result} (premature end of file, expected {n} bytes left)"
            )
        self.pos += n
        return result


def extract_tar(tree: isla.derivation_tree.DerivationTree) -> Union[bool, str]:
    with tempfile.NamedTemporaryFile(suffix=".tar") as outfile:
        outfile.write(str(tree).encode())
        outfile.flush()
        cmd = ["tar", "tf", outfile.name]
        process = subprocess.Popen(cmd, stdout=PIPE, stderr=PIPE)
        (stdout, stderr) = process.communicate(timeout=2)
        exit_code = process.wait()

        output_msg = stdout.decode("utf-8").strip()
        err_msg = stderr.decode("utf-8").strip()

        # Two sources of a problem:
        # 1) Damaged archive (truncated, invalid fields), and
        # 2) Broken links (i.e., symlinkgs referring to not existing files).
        # In the case of 2, tar might not output an error message, but
        # we consider this an error!

        num_entries = len(tree.filter(lambda t: t.value == "<entry>"))
        entries_in_tar_file = len(
            [line for line in output_msg.split(os.linesep) if line]
        )

        if (entries_in_tar_file != num_entries) and not err_msg:
            err_msg = f"Expected {num_entries} entries in tar file, but found {entries_in_tar_file}"

        has_error = exit_code != 0 or err_msg

        # if err_msg:
        #     print(f"Problem with tar file: '{err_msg}'")

        return True if not has_error else err_msg
