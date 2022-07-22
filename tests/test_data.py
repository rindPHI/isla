import string
from typing import Dict, Callable

from isla import language
from isla.helpers import tree_to_string, srange, crange, convert_ebnf_grammar
from isla.parser import EarleyParser
from isla.type_defs import ParseTree, Path, Grammar

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


def validate_lang(inp: language.DerivationTree) -> bool:
    try:
        eval_lang(str(inp))
        return True
    except Exception:
        return False


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


CHARACTERS_WITHOUT_QUOTE = (
        string.digits
        + string.ascii_letters
        + string.punctuation.replace('"', '').replace('\\', '')
        + ' ')

JSON_EBNF_GRAMMAR: Grammar = {
    "<start>": ["<json>"],
    "<json>": ["<element>"],
    "<element>": ["<ws><value><ws>"],
    "<value>": ["<object>", "<array>", "<string>", "<number>",
                "true", "false", "null", "'; DROP TABLE STUDENTS"],
    "<object>": ["{<ws>}", "{<members>}"],
    "<members>": ["<member>(,<members>)*"],
    "<member>": ["<ws><string><ws>:<element>"],
    "<array>": ["[<ws>]", "[<elements>]"],
    "<elements>": ["<element>(,<elements>)*"],
    "<string>": ['"' + "<characters>" + '"'],
    "<characters>": ["<character>*"],
    "<character>": srange(CHARACTERS_WITHOUT_QUOTE),
    "<number>": ["<int><frac><exp>"],
    "<int>": ["<digit>", "<onenine><digits>", "-<digit>", "-<onenine><digits>"],
    "<digits>": ["<digit>+"],
    "<digit>": ['0', "<onenine>"],
    "<onenine>": crange('1', '9'),
    "<frac>": ["", ".<digits>"],
    "<exp>": ["", "E<sign><digits>", "e<sign><digits>"],
    "<sign>": ["", '+', '-'],
    "<ws>": [" "]
}

JSON_GRAMMAR = convert_ebnf_grammar(JSON_EBNF_GRAMMAR)
