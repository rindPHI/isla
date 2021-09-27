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
    ],
    "<file_name>": ["<characters><maybe_nuls>"],
    "<file_mode>": ["<octal_digits><SPACE><NUL>"],
    "<uid>": ["<octal_digits><SPACE><NUL>"],
    "<gid>": ["<octal_digits><SPACE><NUL>"],
    "<file_size>": ["<octal_digits><SPACE>"],
    "<mod_time>": ["<octal_digits><SPACE>"],
    "<checksum>": ["<octal_digits><NUL><SPACE>"],
    "<typeflag>": [  # Generalize?
        "0",  # normal file
        "2"  # symbolic link
    ],
    "<linked_file_name>": ["<maybe_characters><maybe_nuls>"],
    "<uname>": ["<characters><maybe_nuls>"],
    "<gname>": ["<characters><maybe_nuls>"],
    "<dev_maj_num>": ["<octal_digits><SPACE><NUL>"],
    "<dev_min_num>": ["<octal_digits><SPACE><NUL>"],
    "<file_name_prefix>": ["<nuls>"],  # TODO: Find out how this field is used!

    "<content>": ["<maybe_characters><maybe_nuls>"],

    "<final_entry>": ["<nuls>"],

    "<octal_digits>": ["<octal_digit><octal_digits>", "<octal_digit>"],
    "<octal_digit>": srange("01234567"),

    "<maybe_characters>": ["<characters>", ""],
    "<characters>": ["<character><characters>", "<character>"],
    "<character>": srange(string.printable),

    "<maybe_nuls>": ["<nuls>", ""],
    "<nuls>": ["<NUL><nuls>", "<NUL>"],
    "<NUL>": ["\x00"],
    "<SPACE>": [" "],
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
    return isla.SemanticPredicateFormula(TAR_CHECKSUM_PREDICATE, header, checksum, order=100)


mgr = isla.VariableManager(TAR_GRAMMAR)
start = mgr.const("$start", "<start>")
TAR_CONSTRAINTS = mgr.create(
    sc.forall(
        mgr.bv("$file_name", "<file_name>"),
        start,
        sc.ljust_crop(TAR_GRAMMAR, mgr.bv("$file_name"), 100, "\x00")
    ) &
    sc.forall(
        mgr.bv("$file_mode", "<file_mode>"),
        start,
        sc.rjust_crop(TAR_GRAMMAR, mgr.bv("$file_mode"), 8, "0")
    )  &
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
    ) # &
    # sc.forall(
    #     mgr.bv("$header", "<header>"),
    #     start,
    #     sc.forall(
    #         mgr.bv("$checksum", "<checksum>"),
    #         mgr.bv("$header"),
    #         tar_checksum(mgr.bv("$header"), mgr.bv("$checksum"))
    #     )) &
    # sc.forall(
    #     mgr.bv("$linked_file_name", "<linked_file_name>"),
    #     start,
    #     sc.ljust_crop(TAR_GRAMMAR, mgr.bv("$linked_file_name"), 100, "\x00")
    # ) &
    # sc.forall(
    #     mgr.bv("$uname", "<uname>"),
    #     start,
    #     sc.ljust_crop(TAR_GRAMMAR, mgr.bv("$uname"), 32, "\x00")
    # ) &
    # sc.forall(
    #     mgr.bv("$gname", "<gname>"),
    #     start,
    #     sc.ljust_crop(TAR_GRAMMAR, mgr.bv("$gname"), 32, "\x00")
    # ) &
    # sc.forall(
    #     mgr.bv("$dev_maj_num", "<dev_maj_num>"),
    #     start,
    #     sc.rjust_crop(TAR_GRAMMAR, mgr.bv("$dev_maj_num"), 8, "0")
    # ) &
    # sc.forall(
    #     mgr.bv("$dev_min_num", "<dev_min_num>"),
    #     start,
    #     sc.rjust_crop(TAR_GRAMMAR, mgr.bv("$dev_min_num"), 8, "0")
    # ) &
    # sc.forall(
    #     mgr.bv("$prefix", "<file_name_prefix>"),
    #     start,
    #     sc.ljust_crop(TAR_GRAMMAR, mgr.bv("$prefix"), 167, "\x00")
    # ) &
    # sc.forall(
    #     mgr.bv("$content", "<content>"),
    #     start,
    #     sc.ljust_crop(TAR_GRAMMAR, mgr.bv("$content"), 512, "\x00")
    # ) &
    # sc.forall(
    #     mgr.bv("$final", "<final_entry>"),
    #     start,
    #     sc.ljust_crop(TAR_GRAMMAR, mgr.bv("$final"), 1024, "\x00")
    # ) &
    # sc.forall(
    #     mgr.bv("$entry", "<entry>"),
    #     start,
    #     sc.forall(
    #         mgr.bv("$typeflag", "<typeflag>"),
    #         mgr.bv("$entry"),
    #         mgr.smt(cast(z3.BoolRef, mgr.bv("$typeflag").to_smt() == z3.StringVal("0")))
    #         | (mgr.smt(mgr.bv("$typeflag").to_smt() == z3.StringVal("2")) &
    #            sc.forall_bind(
    #                mgr.bv("$linked_file_name_chars", "<characters>") + "<maybe_nuls>",
    #                mgr.bv("$linked_file_name", "<linked_file_name>"),
    #                mgr.bv("$entry"),
    #                sc.exists(
    #                    mgr.bv("$linked_entry", "<entry>"),
    #                    start,
    #                    (sc.before(mgr.bv("$entry"), mgr.bv("$linked_entry"))
    #                     | sc.before(mgr.bv("$linked_entry"), mgr.bv("$entry"))) &
    #                    sc.forall_bind(
    #                        mgr.bv("$file_name_chars", "<characters>") + "<maybe_nuls>",
    #                        mgr.bv("$file_name", "<file_name>"),
    #                        mgr.bv("$linked_entry"),
    #                        mgr.smt(mgr.bv("$file_name_chars").to_smt() == mgr.bv("$linked_file_name_chars").to_smt()) &
    #                        mgr.smt(z3.Length(mgr.bv("$file_name_chars").to_smt()) <= z3.IntVal(100))
    #                    )
    #                )))
    #     ))
)
