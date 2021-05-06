import string
from typing import Dict

from fuzzingbook.GrammarFuzzer import tree_to_string
from fuzzingbook.Parser import EarleyParser

from input_constraints.helpers import get_subtree, dfs
from input_constraints.type_defs import ParseTree

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