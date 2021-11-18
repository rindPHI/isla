import itertools
import logging
import random
import math
import re
from typing import Optional, Set, Generator, Tuple, List, Dict, Union, TypeVar, Sequence, cast

import z3
from fuzzingbook.Grammars import unreachable_nonterminals, is_nonterminal, RE_NONTERMINAL

from input_constraints.type_defs import Path, Grammar, ParseTree, ImmutableGrammar

S = TypeVar('S')
T = TypeVar('T')


def pop(l: List[S], default: T = None, index=0) -> Union[S, T]:
    return default if not l else l.pop(index)


def replace_line_breaks(inp: str) -> str:
    return inp.replace("\n", "\\n")


def parent_reflexive(path_1: Path, path_2: Path) -> bool:
    return len(path_1) <= len(path_2) and path_1 == path_2[:len(path_1)]


def parent_or_child(path_1: Path, path_2: Path) -> bool:
    return path_1[:len(path_2)] == path_2 or path_2[:len(path_1)] == path_1


def path_iterator(tree: ParseTree, path: Path = ()) -> Generator[Tuple[Path, ParseTree], None, None]:
    yield path, tree
    if tree[1] is not None:
        for i, child in enumerate(tree[1]):
            yield from path_iterator(child, path + (i,))


def delete_unreachable(grammar: Grammar) -> None:
    for unreachable in unreachable_nonterminals(grammar):
        del grammar[unreachable]


def replace_tree_path(in_tree: ParseTree, path: Path, replacement_tree: ParseTree) -> ParseTree:
    """Returns tree where replacement_tree has been inserted at `path` instead of the original subtree"""
    node, children = in_tree

    if not path:
        return replacement_tree

    head = path[0]
    new_children = (children[:head] +
                    [replace_tree_path(children[head], path[1:], replacement_tree)] +
                    children[head + 1:])

    return node, new_children


def is_prefix(path_1: Path, path_2: Path) -> bool:
    if not path_1:
        return True

    if not path_2:
        return False

    car_1, *cdr_1 = path_1
    car_2, *cdr_2 = path_2

    if car_1 != car_2:
        return False
    else:
        return is_prefix(cdr_1, cdr_2)


def get_symbols(formula: z3.BoolRef) -> Set[z3.Symbol]:
    result: Set[z3.Symbol] = set()

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


def visit_z3_expr(e: Union[z3.ExprRef, z3.QuantifierRef],
                  seen: Optional[Dict[Union[z3.ExprRef, z3.QuantifierRef], bool]] = None) -> \
        Generator[Union[z3.ExprRef, z3.QuantifierRef], None, None]:
    if seen is None:
        seen = {}
    elif e in seen:
        return

    seen[e] = True
    yield e

    if z3.is_app(e):
        for ch in e.children():
            for e in visit_z3_expr(ch, seen):
                yield e
        return

    if z3.is_quantifier(e):
        for e in visit_z3_expr(e.body(), seen):
            yield e
        return


def is_z3_var(expr: z3.ExprRef) -> bool:
    return z3.is_const(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED


def z3_subst(inp: z3.ExprRef, subst_map: Dict[z3.ExprRef, z3.ExprRef]) -> z3.ExprRef:
    return z3.substitute(inp, *tuple(subst_map.items()))


def is_valid(formula: z3.BoolRef, timeout: int = 500) -> bool:
    if z3.is_true(formula):
        return True

    if z3.is_false(formula):
        return False

    solver = z3.Solver()
    solver.set("timeout", timeout)
    solver.add(z3.Not(formula))
    return solver.check() == z3.unsat


def z3_solve(formulas: List[z3.BoolRef], timeout_ms=500) -> Tuple[z3.CheckSatResult, Optional[z3.ModelRef]]:
    logger = logging.getLogger("z3_solve")
    logger.debug("Evaluating formulas %s", ", ".join(map(str, formulas)))

    result = z3.unknown  # To remove IDE warning
    model: Optional[z3.ModelRef] = None
    parallel = False

    for _ in range(20):
        solver = z3.Solver()
        solver.set("timeout", timeout_ms)
        for formula in formulas:
            solver.add(formula)
        result = solver.check()

        if result == z3.sat:
            model = solver.model()

        if result != z3.unknown:
            break

        timeout_ms = int(timeout_ms * .9) + 1
        random.shuffle(formulas)
        parallel = not parallel
        z3.set_param("parallel.enable", parallel)
        z3.set_param("smt.random_seed", random.randint(0, 99999))

    if result == z3.unknown:
        logger.warning("Satisfiability of %s could not be decided", list(map(str, formulas)))

    return result, model


def z3_and(formulas: List[z3.BoolRef]) -> z3.BoolRef:
    if not formulas:
        return z3.BoolRef(True)
    if len(formulas) == 1:
        return formulas[0]
    return z3.And(*formulas)


def z3_or(formulas: List[z3.BoolRef]) -> z3.BoolRef:
    if not formulas:
        return z3.BoolRef(False)
    if len(formulas) == 1:
        return formulas[0]
    return z3.Or(*formulas)


def tree_to_string(tree: ParseTree) -> str:
    result = []
    stack = [tree]

    while stack:
        symbol, children = stack.pop(0)

        if not children:
            result.append('' if is_nonterminal(symbol) else symbol)
            continue

        for child in reversed(children):
            stack.insert(0, child)

    return ''.join(result)


def tree_depth(tree: ParseTree) -> int:
    if not tree[1]:
        return 1

    return 1 + max(tree_depth(child) for child in tree[1])


def tree_size(tree: ParseTree) -> int:
    if not tree[1]:
        return 1

    return 1 + sum(tree_depth(child) for child in tree[1])


def dict_of_lists_to_list_of_dicts(dict_of_lists: Dict[S, List[T]]) -> List[Dict[S, T]]:
    keys = list(dict_of_lists.keys())
    list_of_values = [dict_of_lists[key] for key in keys]
    product = list(itertools.product(*list_of_values))

    return [dict(zip(keys, product_elem)) for product_elem in product]


def roundup(x: int, to: int) -> int:
    return int(math.ceil(x / float(to))) * int(to)


def powerset(iterable):
    """powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"""
    s = list(iterable)
    return itertools.chain.from_iterable(
        itertools.combinations(s, r)
        for r in range(len(s) + 1))


def weighted_geometric_mean(seq: Sequence[float], weights: Sequence[float]) -> float:
    assert len(seq) == len(weights)
    assert all(w >= 0 for w in weights)

    return (math.prod([(n + 1) ** w for n, w in zip(seq, weights) if w > 0]) **
            (1 / sum([w for w in weights if w > 0]))) - 1


def grammar_to_immutable(grammar: Grammar) -> ImmutableGrammar:
    return cast(
        Tuple[Tuple[str, Tuple[str, ...]]],
        tuple({k: tuple(v) for k, v in grammar.items()}.items()))


def immutable_to_grammar(immutable: ImmutableGrammar) -> Grammar:
    return {k: list(v) for k, v in dict(immutable).items()}


def assertions_activated() -> bool:
    result = False

    def set_result_to_true() -> bool:
        nonlocal result
        result = True
        return True

    assert set_result_to_true()
    return result


def split_str_with_nonterminals(expression: str) -> List[str]:
    return [token for token in re.split(
        RE_NONTERMINAL, expression) if token]
