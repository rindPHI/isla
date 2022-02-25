import itertools
import logging
import math
import operator
import random
import re
from functools import reduce
from typing import Optional, Set, Generator, Tuple, List, Dict, Union, TypeVar, Sequence, cast, Callable, Iterable

import z3
from fuzzingbook.Grammars import unreachable_nonterminals, is_nonterminal, RE_NONTERMINAL

from isla.type_defs import Path, Grammar, ParseTree, ImmutableGrammar

S = TypeVar('S')
T = TypeVar('T')


class ThreeValuedTruth:
    FALSE = 0
    TRUE = 1
    UNKNOWN = 2

    def __init__(self, val: int):
        assert 0 <= val <= 2
        self.val = val

    def __eq__(self, other):
        return self.val == other.val

    def __hash__(self):
        return self.val

    def to_bool(self) -> bool:
        assert self.val != ThreeValuedTruth.UNKNOWN
        return bool(self.val)

    def __bool__(self):
        return self.to_bool()

    def is_false(self):
        return self.val == ThreeValuedTruth.FALSE

    def is_true(self):
        return self.val == ThreeValuedTruth.TRUE

    def is_unknown(self):
        return self.val == ThreeValuedTruth.UNKNOWN

    @staticmethod
    def from_bool(b: bool) -> 'ThreeValuedTruth':
        return ThreeValuedTruth(int(b))

    @staticmethod
    def all(args: Iterable['ThreeValuedTruth']) -> 'ThreeValuedTruth':
        args = list(args)
        if any(elem.is_false() for elem in args):
            return ThreeValuedTruth.false()
        if any(elem.is_unknown() for elem in args):
            return ThreeValuedTruth.unknown()
        return ThreeValuedTruth.true()

    @staticmethod
    def any(args: Iterable['ThreeValuedTruth']) -> 'ThreeValuedTruth':
        args = list(args)
        if any(elem.is_true() for elem in args):
            return ThreeValuedTruth.true()
        if any(elem.is_unknown() for elem in args):
            return ThreeValuedTruth.unknown()
        return ThreeValuedTruth.false()

    @staticmethod
    def not_(arg: 'ThreeValuedTruth') -> 'ThreeValuedTruth':
        if arg.is_true():
            return ThreeValuedTruth.false()
        if arg.is_false():
            return ThreeValuedTruth.true()
        return ThreeValuedTruth.unknown()

    @staticmethod
    def true():
        return ThreeValuedTruth(ThreeValuedTruth.TRUE)

    @staticmethod
    def false():
        return ThreeValuedTruth(ThreeValuedTruth.FALSE)

    @staticmethod
    def unknown():
        return ThreeValuedTruth(ThreeValuedTruth.UNKNOWN)

    def __neg__(self):
        if self.is_unknown():
            return self

        return ThreeValuedTruth(bool(self))

    def __and__(self, other: 'ThreeValuedTruth') -> 'ThreeValuedTruth':
        if self.is_unknown() or other.is_unknown():
            return ThreeValuedTruth.unknown()

        return ThreeValuedTruth.from_bool(bool(self) and bool(other))

    def __or__(self, other: 'ThreeValuedTruth') -> 'ThreeValuedTruth':
        if self.is_unknown() or other.is_unknown():
            return ThreeValuedTruth.unknown()

        return ThreeValuedTruth.from_bool(bool(self) or bool(other))

    def __repr__(self):
        return f"ThreeValuedTruth({self.val})"

    def __str__(self):
        return ("TRUE" if self.is_true() else
                "FALSE" if self.is_false() else
                "UNKNOWN")


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


def get_symbols(formula: z3.BoolRef) -> Set[z3.SeqRef]:
    result: Set[z3.SeqRef] = set()

    def recurse(elem: z3.ExprRef):
        op = elem.decl()
        if z3.is_const(elem) and op.kind() == z3.Z3_OP_UNINTERPRETED:
            if op.range() != z3.StringSort():
                raise NotImplementedError(
                    f"This class was developed for String symbols only, found {op.range()}")

            assert isinstance(elem, z3.SeqRef)
            result.add(cast(z3.SeqRef, elem))

        for child in elem.children():
            recurse(child)

    recurse(formula)
    return result


TRAVERSE_PREORDER = 0
TRAVERSE_POSTORDER = 1


def traverse(
        tree: ParseTree,
        action: Callable[[Path, ParseTree], None],
        abort_condition: Callable[[Path, ParseTree], bool] = lambda p, n: False,
        kind: int = TRAVERSE_PREORDER,
        reverse: bool = False) -> None:
    stack_1: List[Tuple[Path, ParseTree]] = [((), tree)]
    stack_2: List[Tuple[Path, ParseTree]] = []

    if kind == TRAVERSE_PREORDER:
        reverse = not reverse

    while stack_1:
        path, node = stack_1.pop()
        symbol, children = node

        if abort_condition(path, node):
            return

        if kind == TRAVERSE_POSTORDER:
            stack_2.append((path, node))

        if kind == TRAVERSE_PREORDER:
            action(path, node)

        if children:
            iterator = reversed(children) if reverse else iter(children)

            for idx, child in enumerate(iterator):
                new_path = path + ((len(children) - idx - 1) if reverse else idx,)
                stack_1.append((new_path, child))

    if kind == TRAVERSE_POSTORDER:
        while stack_2:
            action(*stack_2.pop())


def visit_z3_expr(e: z3.ExprRef | z3.QuantifierRef,
                  seen: Optional[Dict[Union[z3.ExprRef, z3.QuantifierRef], bool]] = None) -> \
        Generator[z3.ExprRef | z3.QuantifierRef, None, None]:
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


def z3_push_in_negations(formula: z3.BoolRef, negate=False) -> z3.BoolRef:
    if z3.is_not(formula):
        return z3_push_in_negations(formula.children()[0], negate=not negate)
    elif z3.is_and(formula):
        if negate:
            return z3.Or(*[z3_push_in_negations(child, True) for child in formula.children()])
        else:
            return z3.And(*[z3_push_in_negations(child, False) for child in formula.children()])
    elif z3.is_or(formula):
        if negate:
            return z3.And(*[z3_push_in_negations(child, True) for child in formula.children()])
        else:
            return z3.Or(*[z3_push_in_negations(child, False) for child in formula.children()])

    return z3.simplify(z3.Not(formula) if negate else formula)


def is_valid(formula: z3.BoolRef, timeout: int = 500) -> ThreeValuedTruth:
    if z3.is_true(formula):
        return ThreeValuedTruth.true()

    if z3.is_false(formula):
        return ThreeValuedTruth.false()

    try:
        return ThreeValuedTruth.from_bool(evaluate_z3_expression(formula))
    except NotImplementedError:
        pass

    solver = z3.Solver()
    solver.set("timeout", timeout)
    solver.add(z3.Not(formula))

    if solver.check() == z3.unsat:
        return ThreeValuedTruth.true()
    elif solver.check() == z3.sat:
        return ThreeValuedTruth.false()
    else:
        return ThreeValuedTruth.unknown()


class DomainError(RuntimeError):
    def __init__(self, msg: str, *args):
        super().__init__(msg, *args)
        self.msg = msg

    def __str__(self):
        return f"DomainError({self.msg})"


def evaluate_z3_expression(expr: z3.ExprRef) -> bool | int | str:
    # This can only evaluate concrete expressions: No variables / constants
    if z3.is_var(expr) or is_z3_var(expr):
        raise NotImplementedError("Cannot evaluate expression with variables.")

    if z3.is_quantifier(expr):
        raise NotImplementedError("Cannot evaluate expressions with quantifiers.")

    children = list(map(evaluate_z3_expression, expr.children()))

    # Literals
    if z3.is_string_value(expr):
        expr: z3.StringVal
        return expr.as_string()

    if z3.is_int_value(expr):
        expr: z3.IntVal
        return expr.as_long()

    # NOTE: We convert a float string to int by rounding! This differs from the standard
    #       SMT-LIB/Z3 semantics, where str.to.int returns -1 for all strings that don't
    #       represent positive integers.
    if expr.decl().kind() == z3.Z3_OP_STR_TO_INT:
        if not children[0]:
            raise DomainError("Empty string cannot be converted to int.")
        try:
            return int(children[0])
        except ValueError:
            try:
                return int(float(children[0]))
            except ValueError:
                raise DomainError(f"Expression {children[0]} cannot be converted to int.")

    if z3.is_false(expr):
        return False

    if z3.is_true(expr):
        return True

    # Regular Expressions
    if expr.decl().name() == "re.range":
        return f"[{expr.children()[0].as_string()}-{expr.children()[1].as_string()}]"

    if expr.decl().kind() == z3.Z3_OP_RE_LOOP:
        return f"{evaluate_z3_expression(expr.children()[0])}{{{expr.params()[0]},{expr.params()[1]}}}"

    if expr.decl().kind() == z3.Z3_OP_SEQ_TO_RE:
        return re.escape(expr.children()[0].as_string())

    if expr.decl().kind() == z3.Z3_OP_RE_CONCAT:
        return "".join(map(evaluate_z3_expression, expr.children()))

    if expr.decl().kind() == z3.Z3_OP_SEQ_IN_RE:
        return re.match(f"^{evaluate_z3_expression(expr.children()[1])}$",
                        evaluate_z3_expression(expr.children()[0])) is not None

    if expr.decl().kind() == z3.Z3_OP_RE_STAR:
        return f"({evaluate_z3_expression(expr.children()[0])})*"

    if expr.decl().kind() == z3.Z3_OP_RE_PLUS:
        return f"({evaluate_z3_expression(expr.children()[0])})+"

    if expr.decl().kind() == z3.Z3_OP_RE_UNION:
        return f"(({evaluate_z3_expression(expr.children()[0])}) | ({evaluate_z3_expression(expr.children()[0])}))"

    if expr.decl().name() == "re.comp":
        # The argument must be a union of strings or a range.
        child = expr.children()[0]
        if (child.decl().kind() == z3.Z3_OP_RE_UNION
                and all(grandchild.decl().kind() == z3.Z3_OP_SEQ_TO_RE for grandchild in child.children()) or
                child.decl().name() == "re.range"):
            set_elements = list(map(evaluate_z3_expression, child.children()))
            return "[^" + "".join(set_elements) + "]"

    if expr.decl().kind() == z3.Z3_OP_RE_FULL_SET:
        return ".*?"

    # Boolean Combinations
    if z3.is_not(expr):
        return not children[0]

    if z3.is_and(expr):
        return reduce(operator.and_, children)

    if z3.is_or(expr):
        return reduce(operator.or_, children)

    # Comparisons
    if z3.is_eq(expr):
        return children[0] == children[1]

    if z3.is_lt(expr):
        return children[0] < children[1]

    if z3.is_le(expr):
        return children[0] <= children[1]

    if z3.is_gt(expr):
        return children[0] > children[1]

    if z3.is_ge(expr):
        return children[0] >= children[1]

    # Arithmetic Operations
    if z3.is_add(expr):
        return children[0] + children[1]

    if z3.is_sub(expr):
        return children[0] - children[1]

    if z3.is_mul(expr):
        return children[0] * children[1]

    if z3.is_div(expr):
        return int(children[0] / children[1])

    # String Operations
    if expr.decl().kind() == z3.Z3_OP_SEQ_LENGTH:
        return len(children[0])

    if expr.decl().kind() == z3.Z3_OP_SEQ_CONCAT:
        return cast(str, children[0]) + cast(str, children[1])

    if expr.decl().kind() == z3.Z3_OP_SEQ_AT:
        return cast(str, children[0])[cast(int, children[1])]

    logger = logging.getLogger("Z3 evaluation")
    logger.warning("Evaluation of expression %s not implemented.", expr)
    raise NotImplementedError(f"Evaluation of expression {expr} not implemented.")


def z3_solve(formulas: List[z3.BoolRef], timeout_ms=500) -> Tuple[z3.CheckSatResult, Optional[z3.ModelRef]]:
    logger = logging.getLogger("z3_solve")

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


def dict_of_lists_to_list_of_dicts(dict_of_lists: Dict[S, Iterable[T]]) -> List[Dict[S, T]]:
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


def nested_list_to_tuple(l: List[Union[T, List[T]]]) -> Tuple[Union[T, Tuple[T, ...]], ...]:
    return tuple([tuple(elem) if isinstance(elem, list) else elem for elem in l])


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


def cluster_by_common_elements(l: Sequence[T], f: Callable[[T], Set[S]]) -> List[List[T]]:
    """
    Clusters elements of l by shared elements. Elements of interest are obtained using f.
    For instance, to cluster a list of lists based on common list elements:

    >>> cluster_by_common_elements([[1,2], [2,3], [3,4], [5,6]], lambda l: {e for e in l})

    Gives [[[2, 3], [3, 4], [1, 2]], [[5, 6]]].

    >>> cluster_by_common_elements([1,2,3,4,5,6,7], lambda e: {e, e+3})

    Outputs [[2, 5], [3, 6], [4, 7, 1]].

    :param l: The list to cluster.
    :param f: The function to determine commonality.
    :return: The clusters w.r.t. f.
    """
    clusters = [[e2 for e2 in l if not f(e1).isdisjoint(f(e2))] for e1 in l]

    result = []
    for c in clusters:
        # Merge clusters with common elements...
        clusters_with_common_elements = [c1 for c1 in result if any(not f(e).isdisjoint(f(e1)) for e in c for e1 in c1)]
        for c1 in clusters_with_common_elements:
            result.remove(c1)

        merged_cluster = c + [e for c1 in clusters_with_common_elements for e in c1]

        # ...and remove duplicate elements from the merged cluster.
        no_dupl_cluster = []
        for cluster in merged_cluster:
            if cluster in no_dupl_cluster:
                continue
            no_dupl_cluster.append(cluster)

        result.append(no_dupl_cluster)

    return result


RE_NONTERMINAL = re.compile(r'(<[^<> ]*>)')


def is_nonterminal(s):
    return RE_NONTERMINAL.match(s)


def nonterminals(expansion: str) -> List[str]:
    return RE_NONTERMINAL.findall(expansion)


def smt_expr_to_str(f: z3.ExprRef) -> str:
    op_strings = {
        z3.Z3_OP_SEQ_IN_RE: "str.in_re",
        z3.Z3_OP_SEQ_CONCAT: "str.++",
        z3.Z3_OP_RE_CONCAT: "re.++",
        z3.Z3_OP_STR_TO_INT: "str.to.int",  # <- Different from standard SMT-LIB (Z3 version)
    }

    if z3.is_string_value(f):
        return '"' + cast(str, f.as_string()).replace('"', '""') + '"'
    if z3.is_int_value(f):
        return str(f.as_long())
    if is_z3_var(f):
        return str(f)

    if z3.is_app(f):
        kind = f.decl().kind()

        if kind == z3.Z3_OP_RE_LOOP:
            op = f"(_ re.loop {f.params()[0]} {f.params()[1]})"
        elif kind == z3.Z3_OP_RE_POWER:
            op = f"(_ re.^ {f.params()[0]})"
        elif f.decl().kind() in op_strings:
            op = op_strings[kind]
        else:
            op = f.decl().name()

        return f"({op} {' '.join(map(smt_expr_to_str, f.children()))}".strip() + ")"

    raise NotImplementedError()


def strip_ws(inp: str) -> str:
    inp = inp.strip()
    inp = inp.replace("\n", " ")
    while True:
        new_inp = inp.replace("  ", " ")
        if new_inp == inp:
            break
        inp = new_inp
    return inp
