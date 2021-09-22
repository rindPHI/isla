import itertools
import logging
import random
from typing import Optional, Set, Generator, Tuple, List, Dict, Union, TypeVar

import z3
from fuzzingbook.Grammars import unreachable_nonterminals
from grammar_graph.gg import GrammarGraph

from input_constraints.type_defs import Path, Grammar, ParseTree


def replace_line_breaks(inp: str) -> str:
    return inp.replace("\n", "\\n")


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
    logger = logging.getLogger("z3_solve3")
    logger.debug("Evaluating formulas %s", map(str, formulas))

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


def reachable(grammar: Grammar, nonterminal: str, to_nonterminal: str) -> bool:
    graph = GrammarGraph.from_grammar(grammar)
    return graph.get_node(nonterminal).reachable(graph.get_node(to_nonterminal))


def tree_depth(tree: ParseTree) -> int:
    if not tree[1]:
        return 1

    return 1 + max(tree_depth(child) for child in tree[1])


def tree_size(tree: ParseTree) -> int:
    if not tree[1]:
        return 1

    return 1 + sum(tree_depth(child) for child in tree[1])


S = TypeVar('S')
T = TypeVar('T')


def dict_of_lists_to_list_of_dicts(dict_of_lists: Dict[S, List[T]]) -> List[Dict[S, T]]:
    keys = list(dict_of_lists.keys())
    list_of_values = [dict_of_lists[key] for key in keys]
    product = list(itertools.product(*list_of_values))

    return [dict(zip(keys, product_elem)) for product_elem in product]
