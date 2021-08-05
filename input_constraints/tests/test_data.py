import string
from typing import Dict, Callable

from fuzzingbook.GrammarFuzzer import tree_to_string
from fuzzingbook.Grammars import convert_ebnf_grammar, srange
from fuzzingbook.Parser import EarleyParser

from input_constraints.type_defs import ParseTree, Path

LANG_GRAMMAR = {
    "<start>":
        ["<stmt>"],
    "<stmt>":
        ["<assgn>", "<assgn> ; <stmt>"],
    "<assgn>":
        ["<var> := <rhs>"],
    "<rhs>":
        ["<var>", "<digit>"],
    "<var>": list(string.ascii_lowercase),
    "<digit>": list(string.digits)
}

CSV_EBNF_GRAMMAR = {
    "<start>": ["<csv-file>"],
    "<csv-file>": ["<csv-header><csv-record>*"],
    "<csv-header>": ["<csv-record>"],
    "<csv-record>": ["<csv-string-list>\n"],
    "<csv-string-list>": ["<raw-string>", "<raw-string>;<csv-string-list>"],
    "<raw-string>": ["<spaces>", "<spaces>?<raw-field><spaces>?"],
    "<raw-field>": ["<simple-field>", "<quoted-field>"],
    "<simple-field>": ["<simple-character>*"],
    "<simple-character>": [c for c in srange(string.printable) if c not in ["\n", ";", '"', " ", "\t", "\r"]],
    "<quoted-field>": ['"<escaped-field>"'],
    "<escaped-field>": ["<escaped-character>*"],
    "<escaped-character>": [c for c in srange(string.printable) if c not in ['"']],
    "<spaces>": [" ", " <spaces>"],
}

CSV_GRAMMAR = convert_ebnf_grammar(CSV_EBNF_GRAMMAR)


def eval_lang(inp: str) -> Dict[str, int]:
    def assgnlhs(assgn: ParseTree):
        return tree_to_string(get_subtree((0,), assgn))

    def assgnrhs(assgn: ParseTree):
        return tree_to_string(get_subtree((2,), assgn))

    valueMap: Dict[str, int] = {}
    tree = list(EarleyParser(LANG_GRAMMAR).parse(inp))[0]

    def evalAssignments(tree):
        node, children = tree
        if node == "<assgn>":
            lhs = assgnlhs(tree)
            rhs = assgnrhs(tree)
            if rhs.isdigit():
                valueMap[lhs] = int(rhs)
            else:
                valueMap[lhs] = valueMap[rhs]

    dfs(tree, evalAssignments)

    return valueMap


def dfs(tree: ParseTree, action: Callable[[ParseTree], None] = print):
    node, children = tree
    action(tree)
    if children is not None:
        for child in children:
            dfs(child, action)


def get_subtree(path: Path, tree: ParseTree) -> ParseTree:
    """Access a subtree based on `path` (a list of children numbers)"""
    node, children = tree

    if not path:
        return tree

    return get_subtree(path[1:], children[path[0]])
