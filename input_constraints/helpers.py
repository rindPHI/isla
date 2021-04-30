from typing import Optional, Set

import z3
from z3 import Symbol

from input_constraints.type_defs import Path, ParseTree


def get_subtree(path: Path, tree: ParseTree) -> ParseTree:
    """Access a subtree based on `path` (a list of children numbers)"""
    node, children = tree

    if not path:
        return tree

    return get_subtree(path[1:], children[path[0]])


def next_path(path: Path, tree: ParseTree) -> Optional[Path]:
    if not path:
        return None

    node, children = get_subtree(path[:-1], tree)
    if len(children) > path[-1] + 1:
        return path[:-1] + (path[-1] + 1,)
    else:
        return next_path(path[:-1], tree)


def get_symbols(formula: z3.BoolRef) -> Set[Symbol]:
    result: Set[Symbol] = set()

    def recurse(elem: z3.ExprRef):
        op = elem.decl()
        if z3.is_const(elem) and op.kind() == z3.Z3_OP_UNINTERPRETED:
            if op.range() != z3.StringSort():
                raise NotImplementedError(
                    f"This class was developed for String symbols only, found {op.range()}")

            result.add(op.name())

        for child in elem.children():
            recurse(child)

    recurse(formula)
    return result
