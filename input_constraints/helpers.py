from typing import Optional, Set, Callable

import z3
from z3 import Symbol

from input_constraints.type_defs import Path, ParseTree


def traverse_tree(tree: ParseTree, action: Callable[[ParseTree], None]) -> None:
    node, children = tree
    action(tree)
    for child in children:
        traverse_tree(child, action)


def get_path_of_subtree(tree: ParseTree, subtree: ParseTree, path: Path = tuple()) -> Optional[Path]:
    current_subtree = get_subtree(path, tree)
    if current_subtree is subtree:
        return path

    node, children = current_subtree
    if not children:
        return None

    for idx in range(len(children)):
        child_result = get_path_of_subtree(tree, subtree, path + (idx,))
        if child_result is not None:
            return child_result

    return None


def is_before(path_1: Path, path_2: Path) -> bool:
    if not path_1 or not path_2:
        # Note: (1,) is not before (1,0), since it's a prefix!
        # Also, (1,) cannot be before ().
        # But (1,0) would be before (1,1).
        return False

    car_1, *cdr_1 = path_1
    car_2, *cdr_2 = path_2

    if car_1 < car_2:
        return True
    elif car_2 < car_1:
        return False
    else:
        return is_before(tuple(cdr_1), tuple(cdr_2))


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
