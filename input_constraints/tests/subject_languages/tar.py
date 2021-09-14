import string
from typing import cast

import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import srange

from input_constraints import isla
import input_constraints.isla_shortcuts as sc

TAR_GRAMMAR = {
    "<start>": ["<entries>"],
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
    ],
    "<file_name>": ["<characters><maybe_nuls>"],
    "<file_mode>": ["<padded_octal_digits><SPACE><NUL>"],
    "<uid>": ["<padded_octal_digits><SPACE><NUL>"],
    "<gid>": ["<padded_octal_digits><SPACE><NUL>"],
    "<file_size>": ["<padded_octal_digits><SPACE>"],
    "<mod_time>": ["<padded_octal_digits><SPACE>"],
    "<checksum>": ["<padded_octal_digits><NUL><SPACE>"],
    "<typeflag>": [  # Generalize?
        "0",  # normal file
        "2"  # symbolic link
    ],
    "<linked_file_name>": ["<characters><maybe_nuls>"],
    "<uname>": ["<characters><maybe_nuls>"],
    "<gname>": ["<characters><maybe_nuls>"],
    "<dev_maj_num>": ["<padded_octal_digits><SPACE>"],
    "<dev_min_num>": ["<padded_octal_digits><SPACE>"],
    "<file_name_prefix>": ["<nuls>"],  # TODO: Find out how this field is used!

    "<content>": ["<maybe_characters>"],

    "<padded_octal_digits>": ["<maybe_zeroes><octal_digit_nonzero><maybe_octal_digits>"],
    "<maybe_octal_digits>": ["", "<octal_digits>"],
    "<octal_digits>": ["<octal_digit>", "<octal_digit><octal_digits>"],
    "<octal_digit>": srange("01234567"),
    "<octal_digit_nonzero>": srange("1234567"),
    "<maybe_zeroes>": ["", "<zeroes>"],
    "<zeroes>": ["<ZERO>", "<ZERO><zeroes>"],

    "<maybe_characters>": ["", "<characters>"],
    "<characters>": ["<character>", "<character><characters>"],
    "<character>": srange(string.printable),

    "<maybe_nuls>": ["", "<nuls>"],
    "<nuls>": ["<NUL>", "<NUL><nuls>"],
    "<NUL>": ["\x00"],
    "<SPACE>": [" "],
    "<ZERO>": ["0"]
}

mgr = isla.VariableManager(TAR_GRAMMAR)
start = mgr.const("$start", "<start>")
LENGTH_CONSTRAINTS = mgr.create(
    sc.forall(
        mgr.bv("$file_name", "<file_name>"),
        start,
        sc.ljust_crop(TAR_GRAMMAR, mgr.bv("$file_name"), 100, "\x00")
    ) &
    sc.forall(
        mgr.bv("$file_mode", "<file_mode>"),
        start,
        sc.rjust_crop(TAR_GRAMMAR, mgr.bv("$file_mode"), 8, "0")
    ) &
    sc.forall(
        mgr.bv("$uid", "<uid>"),
        start,
        sc.rjust_crop(TAR_GRAMMAR, mgr.bv("$uid"), 8, "0")
    ) &
    sc.forall(
        mgr.bv("$gid", "<gid>"),
        start,
        sc.rjust_crop(TAR_GRAMMAR, mgr.bv("$gid"), 8, "0")
    ) &
    sc.forall(
        mgr.bv("$file_size", "<file_size>"),
        start,
        sc.rjust_crop(TAR_GRAMMAR, mgr.bv("$file_size"), 12, "0")
    ) &
    sc.forall(
        mgr.bv("$mod_time", "<mod_time>"),
        start,
        sc.rjust_crop(TAR_GRAMMAR, mgr.bv("$mod_time"), 12, "0")
    ) &
    sc.forall(
        mgr.bv("$checksum", "<checksum>"),
        start,
        sc.rjust_crop(TAR_GRAMMAR, mgr.bv("$checksum"), 8, "0")  # TODO: Implement proper checksum
    ) &
    sc.forall(
        mgr.bv("$linked_file_name", "<linked_file_name>"),
        start,
        sc.ljust_crop(TAR_GRAMMAR, mgr.bv("$linked_file_name"), 100, "\x00")
    ) &
    sc.forall(
        mgr.bv("$entry", "<entry>"),
        start,
        sc.forall(
            mgr.bv("$typeflag", "<typeflag>"),
            mgr.bv("$entry"),
            mgr.smt(cast(z3.BoolRef, mgr.bv("$typeflag").to_smt() == z3.StringVal("0")))
            | (mgr.smt(mgr.bv("$typeflag").to_smt() == z3.StringVal("2")) &
               sc.forall_bind(
                   mgr.bv("$linked_file_name_chars", "<characters>") + "<maybe_nuls>",
                   mgr.bv("$linked_file_name", "<linked_file_name>"),
                   mgr.bv("$entry"),
                   sc.exists(
                       mgr.bv("$linked_entry", "<entry>"),
                       start,
                       sc.forall_bind(
                           mgr.bv("$file_name_chars", "<characters>") + "<maybe_nuls>",
                           mgr.bv("$file_name"),
                           mgr.bv("$linked_entry"),
                           mgr.smt(mgr.bv("$file_name_chars").to_smt() == mgr.bv("$linked_file_name_chars").to_smt())
                       )
                   )))
        ))
    # sc.forall(
    #    mgr.bv("$linked_file_name", "<linked_file_name>"),
    #    start,
    #    sc.ljust_crop(TAR_GRAMMAR, mgr.bv("$linked_file_name"), 100, "\x00")
    # )
)
