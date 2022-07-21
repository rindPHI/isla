import string
from typing import Dict, Callable

from fuzzingbook.GrammarFuzzer import tree_to_string
from fuzzingbook.Parser import EarleyParser

from isla import language
from isla.type_defs import ParseTree, Path

LANG_GRAMMAR = {
    "<start>":
        ["<stmt>"],
    "<stmt>":
        ["<assgn> ; <stmt>", "<assgn>"],
    "<assgn>":
        ["<var> := <rhs>"],
    "<rhs>":
        ["<var>", "<digit>"],
    "<var>": list(string.ascii_lowercase),
    "<digit>": list(string.digits)
}

SIMPLE_CSV_GRAMMAR = {
    "<start>": ["<csv-header><csv-records>"],
    "<csv-header>": ["<csv-field-list>\n"],
    "<csv-records>": ["<csv-record><csv-records>", ""],
    "<csv-record>": ["<csv-field-list>\n"],
    "<csv-field-list>": ["<csv-field>;<csv-field-list>", "<csv-field>"],
    "<csv-field>": list(string.ascii_lowercase),
}
