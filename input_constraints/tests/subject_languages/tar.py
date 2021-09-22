import copy
import string
from typing import cast, Union, List

import z3
from fuzzingbook.Grammars import srange
from fuzzingbook.Parser import EarleyParser

import input_constraints.isla_shortcuts as sc
from input_constraints import isla
from input_constraints.helpers import delete_unreachable

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


def tar_checksum(header: isla.DerivationTree, checksum_tree: isla.DerivationTree) -> isla.SemPredEvalResult:
    if not header.is_complete():
        return isla.SemPredEvalResult(None)

    current_checksum_path = header.find_node(checksum_tree)

    checksum_grammar = copy.deepcopy(TAR_GRAMMAR)
    checksum_grammar["<start>"] = ["<checksum>"]
    checksum_grammar["<checksum>"] = ["<SPACE><SPACE><SPACE><SPACE><SPACE><SPACE><SPACE><SPACE>"]
    delete_unreachable(checksum_grammar)
    checksum_parser = EarleyParser(checksum_grammar)

    space_checksum = isla.DerivationTree.from_parse_tree(list(checksum_parser.parse("        "))[0]).get_subtree((0,))
    header_wo_checksum = header.replace_path(current_checksum_path, space_checksum)

    header_bytes: List[int] = list(str(header_wo_checksum).encode("ascii"))

    checksum_value = str(oct(sum(header_bytes)))[2:].rjust(6, "0") + "\x00 "

    checksum_grammar = copy.deepcopy(TAR_GRAMMAR)
    checksum_grammar["<start>"] = ["<checksum>"]
    delete_unreachable(checksum_grammar)
    checksum_parser = EarleyParser(checksum_grammar)

    new_checksum_tree = isla.DerivationTree.from_parse_tree(
        list(checksum_parser.parse(checksum_value))[0]).get_subtree((0,))

    if str(new_checksum_tree) == str(checksum_tree):
        return isla.SemPredEvalResult(True)

    return isla.SemPredEvalResult({checksum_tree: new_checksum_tree})


TAR_CHECKSUM_PREDICATE = isla.SemanticPredicate("tar_checksum", 2, tar_checksum, lambda tree, args: False)


def tar_checksum(
        header: Union[isla.Variable, isla.DerivationTree],
        checksum: Union[isla.Variable, isla.DerivationTree]) -> isla.SemanticPredicateFormula:
    return isla.SemanticPredicateFormula(TAR_CHECKSUM_PREDICATE, header, checksum)


mgr = isla.VariableManager(TAR_GRAMMAR)
start = mgr.const("$start", "<start>")
TAR_CONSTRAINTS = mgr.create(
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
                       (sc.before(mgr.bv("$entry"), mgr.bv("$linked_entry"))
                        | sc.before(mgr.bv("$linked_entry"), mgr.bv("$entry"))) &
                       sc.forall_bind(
                           mgr.bv("$file_name_chars", "<characters>") + "<maybe_nuls>",
                           mgr.bv("$file_name", "<file_name>"),
                           mgr.bv("$linked_entry"),
                           mgr.smt(mgr.bv("$file_name_chars").to_smt() == mgr.bv("$linked_file_name_chars").to_smt()) &
                           mgr.smt(z3.Length(mgr.bv("$file_name_chars").to_smt()) <= z3.IntVal(100))
                       )
                   )))
        )) &
    # sc.forall(
    #     mgr.bv("$file_name", "<file_name>"),
    #     start,
    #     sc.ljust_crop(TAR_GRAMMAR, mgr.bv("$file_name"), 100, "\x00")
    # ) &
    sc.forall(
       mgr.bv("$file_mode", "<file_mode>"),
       start,
       sc.rjust_crop(TAR_GRAMMAR, mgr.bv("$file_mode"), 8, "0")
    ) &
    # sc.forall(
    #    mgr.bv("$uid", "<uid>"),
    #    start,
    #    sc.rjust_crop(TAR_GRAMMAR, mgr.bv("$uid"), 8, "0")
    # ) &
    # sc.forall(
    #    mgr.bv("$gid", "<gid>"),
    #    start,
    #    sc.rjust_crop(TAR_GRAMMAR, mgr.bv("$gid"), 8, "0")
    # ) &
    # sc.forall(
    #     mgr.bv("$file_size", "<file_size>"),
    #     start,
    #     sc.rjust_crop(TAR_GRAMMAR, mgr.bv("$file_size"), 12, "0")
    # ) &
    # sc.forall(
    #     mgr.bv("$mod_time", "<mod_time>"),
    #     start,
    #     sc.rjust_crop(TAR_GRAMMAR, mgr.bv("$mod_time"), 12, "0")
    # ) &
    # sc.forall(
    #     mgr.bv("$linked_file_name", "<linked_file_name>"),
    #     start,
    #     sc.ljust_crop(TAR_GRAMMAR, mgr.bv("$linked_file_name"), 100, "\x00")
    # ) &
    sc.forall(
        mgr.bv("$header", "<header>"),
        start,
        sc.forall(
            mgr.bv("$checksum", "<checksum>"),
            mgr.bv("$header"),
            tar_checksum(mgr.bv("$header"), mgr.bv("$checksum"))
        ))
)
