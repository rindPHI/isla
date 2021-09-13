import string

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
    "<file_mode>": ["<padded_octal_digits><SPACE>"],
    "<uid>": ["<padded_octal_digits><SPACE>"],
    "<gid>": ["<padded_octal_digits><SPACE>"],
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

mgr = isla.VariableManager()
LENGTH_CONSTRAINTS = mgr.create(
    sc.forall(
        mgr.bv("$file_name", "<file_name>"),
        mgr.const("$start", "<start>"),
        mgr.smt(z3.Length(mgr.bv("$file_name").to_smt()) == z3.IntVal(100))
    )
)
