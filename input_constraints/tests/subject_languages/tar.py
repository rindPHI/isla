import copy
import string
from typing import Union, List, Optional, Tuple, cast

import z3
from fuzzingbook.GrammarFuzzer import tree_to_string
from fuzzingbook.Grammars import srange
from fuzzingbook.Parser import EarleyParser

import input_constraints.isla_shortcuts as sc
from input_constraints import isla
from input_constraints.helpers import delete_unreachable, roundup
from input_constraints.type_defs import ParseTree

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
    "<header_padding>": ["<nuls>"],

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
    )  # &
    # sc.forall(
    #     mgr.bv("$uid", "<uid>"),
    #     start,
    #     sc.rjust_crop(TAR_GRAMMAR, mgr.bv("$uid"), 8, "0")
    # ) &
    # sc.forall(
    #     mgr.bv("$gid", "<gid>"),
    #     start,
    #     sc.rjust_crop(TAR_GRAMMAR, mgr.bv("$gid"), 8, "0")
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
    # )  &
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
    #     sc.ljust_crop(TAR_GRAMMAR, mgr.bv("$prefix"), 155, "\x00")
    # ) &
    # sc.forall(
    #     mgr.bv("$header_padding", "<header_padding>"),
    #     start,
    #     sc.ljust_crop(TAR_GRAMMAR, mgr.bv("$header_padding"), 12, "\x00")
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


class TarParser:
    def __init__(self, start_symbol="<start>"):
        self.pos = 0
        self.inp = ""
        self.start_symbol = "<start>"

    def parse(self, inp: str) -> List[ParseTree]:
        self.pos = 0
        self.inp = inp

        return [self.parse_start()]

    def parse_start(self) -> ParseTree:
        children = []

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
        elif self.start_symbol == "<mode_time>":
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
        # elif self.start_symbol == "<content>":
        #     children = [self.parse_content()]
        elif self.start_symbol == "<final_entry>":
            children = [self.parse_final_entry()]

        return "<start>", children

    def parse_entries(self) -> ParseTree:
        entries = []

        block = self.peek(512)

        if block is None:
            raise SyntaxError(f"at {self.pos}")

        while not self.is_null(block):
            entries.append(self.parse_entry())

            block = self.peek(512)
            if block is None:
                raise SyntaxError(f"at {self.pos}")

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
            content_size += int(content_size_str[len(content_size_str) - i - 1]) * (8 ** i)

        content = self.parse_content(content_size)

        return "<entry>", [header, content]

    def parse_content(self, content_size: int) -> ParseTree:
        return self.parse_padded_characters("<content>", self.read(roundup(content_size, 512)))

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
            raise SyntaxError(f"at {ustar00_str}")

        uname = self.parse_uname()
        gname = self.parse_gname()
        dev_maj_num = self.parse_dev_maj_num()
        dev_min_num = self.parse_dev_min_num()
        file_name_prefix = self.parse_file_name_prefix()  # TODO: Find out how this field is used!
        padding = self.parse_header_padding()

        return ("<header>", [
            file_name, file_mode, uid, gid, file_size, mod_time, checksum, typeflag, linked_file_name,
            ("ustar", []), ("<NUL>", [("\x00", [])]), ("00", []),
            uname, gname, dev_maj_num, dev_min_num, file_name_prefix, padding
        ])

    def parse_header_padding(self):
        padding = ("<header_padding>", [self.parse_nuls(self.read(12))])
        return padding

    def parse_file_name_prefix(self):
        file_name_prefix = ("<file_name_prefix>", [self.parse_nuls(self.read(155))])
        return file_name_prefix

    def parse_dev_min_num(self):
        dev_min_num_padded = self.read(8)
        if dev_min_num_padded[-2:] != " \x00":
            raise SyntaxError(f"at {dev_min_num_padded[-2:]}")
        dev_min_num = ("<dev_maj_num>", [
            self.parse_octal_digits(dev_min_num_padded[:-2]),
            ("<SPACE>", [(" ", [])]),
            ("<NUL>", [("\x00", [])])])
        return dev_min_num

    def parse_dev_maj_num(self):
        dev_maj_num_padded = self.read(8)
        if dev_maj_num_padded[-2:] != " \x00":
            raise SyntaxError(f"at {dev_maj_num_padded[-2:]}")
        dev_maj_num = ("<dev_maj_num>", [
            self.parse_octal_digits(dev_maj_num_padded[:-2]),
            ("<SPACE>", [(" ", [])]),
            ("<NUL>", [("\x00", [])])])
        return dev_maj_num

    def parse_gname(self):
        gname = self.parse_padded_characters("<gname>", self.read(32))
        return gname

    def parse_uname(self):
        uname = self.parse_padded_characters("<uname>", self.read(32))
        return uname

    def parse_file_name(self):
        file_name = self.parse_padded_characters("<file_name>", self.read(100))
        return file_name

    def parse_linked_file_name(self):
        linked_file_name = self.parse_padded_characters("<linked_file_name>", self.read(100))
        return linked_file_name

    def parse_typeflag(self):
        typeflag = ("<typeflag>", [(self.read(1), [])])
        if typeflag[1][0][0] not in string.digits:
            raise SyntaxError(f"at {str(typeflag)}")
        return typeflag

    def parse_checksum(self):
        checksum_padded = self.read(8)
        if checksum_padded[-2:] != "\x00 ":
            raise SyntaxError(f"at {checksum_padded[-2:]}")
        checksum = ("<checksum>", [
            self.parse_octal_digits(checksum_padded[:-2]),
            ("<NUL>", [("\x00", [])]),
            ("<SPACE>", [(" ", [])])])
        return checksum

    def parse_mod_time(self):
        mod_time_padded = self.read(12)
        if mod_time_padded[-1] != " ":
            raise SyntaxError(f"at {mod_time_padded[-1]}")
        mod_time = ("<mod_time>", [
            self.parse_octal_digits(mod_time_padded[:-1]),
            ("<SPACE>", [(" ", [])])])
        return mod_time

    def parse_file_size(self):
        file_size_padded = self.read(12)
        if file_size_padded[-1] != " ":
            raise SyntaxError(f"at {file_size_padded[-1]}")
        file_size = ("<file_size>", [
            self.parse_octal_digits(file_size_padded[:-1]),
            ("<SPACE>", [(" ", [])])])
        return file_size

    def parse_gid(self):
        gid_padded = self.read(8)
        if gid_padded[-2:] != " \x00":
            raise SyntaxError(f"at {gid_padded[-2:]}")
        gid = ("<gid>", [
            self.parse_octal_digits(gid_padded[:-2]),
            ("<SPACE>", [(" ", [])]),
            ("<NUL>", [("\x00", [])])])
        return gid

    def parse_uid(self):
        uid_padded = self.read(8)
        if uid_padded[-2:] != " \x00":
            raise SyntaxError(f"at {uid_padded[-2:]}")
        uid = ("<uid>", [
            self.parse_octal_digits(uid_padded[:-2]),
            ("<SPACE>", [(" ", [])]),
            ("<NUL>", [("\x00", [])])])
        return uid

    def parse_file_mode(self):
        file_mode_padded = self.read(8)
        if file_mode_padded[-2:] != " \x00":
            raise SyntaxError(f"at {file_mode_padded[-2:]}")
        file_mode = ("<file_mode>", [
            self.parse_octal_digits(file_mode_padded[:-2]),
            ("<SPACE>", [(" ", [])]),
            ("<NUL>", [("\x00", [])])])
        return file_mode

    def parse_padded_characters(self, parent_nonterminal: str, inp: str) -> ParseTree:
        nuls_offset = inp.index("\x00")
        return parent_nonterminal, [self.parse_characters(inp[:nuls_offset]), self.parse_nuls(inp[nuls_offset:])]

    def parse_octal_digits(self, inp: str) -> ParseTree:
        children = []
        result = ("<octal_digits>", children)
        for idx, char in enumerate(inp):
            if char not in "01234567":
                raise SyntaxError(f"at {inp[idx:]}")
            new_children = []
            children.append(("<octal_digit>", [(char, [])]))

            if idx < len(inp) - 1:
                children.append(("<octal_digits>", new_children))
                children = new_children

        return result

    def parse_characters(self, inp: str) -> ParseTree:
        children = []
        result = ("<characters>", children)
        for idx, char in enumerate(inp):
            if char == "\x00":
                raise SyntaxError(f"at {inp[idx:]}")
            new_children = []
            children.append(("<character>", [(char, [])]))

            if idx < len(inp) - 1:
                children.append(("<characters>", new_children))
                children = new_children

        return result

    def parse_nuls(self, inp: str) -> ParseTree:
        children = []
        result = ("<nuls>", children)
        for idx, char in enumerate(inp):
            if char != "\x00":
                raise SyntaxError(f"at {inp[idx:]}")
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
        if i < 2 or len(self.inp) != self.pos:
            raise SyntaxError(f"at {self.inp[self.pos:]}")

        return "<final_entry>", [self.parse_nuls(inp)]

    def is_null(self, inp: str) -> bool:
        return all(c == "\x00" for c in inp)

    def peek(self, n=1) -> Optional[str]:
        result = self.inp[self.pos:self.pos + n]
        return result if len(result) == n else None

    def read(self, n=1) -> Optional[str]:
        result = self.inp[self.pos:self.pos + n]
        if len(result) != n:
            raise SyntaxError(f"at {result}")
        self.pos += n
        return result
