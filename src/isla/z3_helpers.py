# Copyright © 2022 CISPA Helmholtz Center for Information Security.
# Author: Dominic Steinhöfel.
#
# This file is part of ISLa.
#
# ISLa is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# ISLa is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with ISLa.  If not, see <http://www.gnu.org/licenses/>.

import logging
import operator
import random
import re
import sys
from functools import lru_cache, reduce, partial

from returns.functions import compose
from returns.pipeline import flow
from returns.maybe import Maybe, Some, Nothing
from typing import (
    Callable,
    Tuple,
    cast,
    List,
    Optional,
    Dict,
    Union,
    Generator,
    Set,
    TypeVar,
    Iterable,
    Sequence, Mapping,
)

import z3
from returns.pointfree import lash
from returns.result import Success, Failure, Result
from z3.z3 import _coerce_exprs

from isla.helpers import (
    merge_dict_of_sets,
    merge_intervals,
    HELPERS_LOGGER,
)
from isla.three_valued_truth import ThreeValuedTruth

Z3EvalResult = Tuple[
    Tuple[str, ...], bool | int | str | Callable[[Tuple[str, ...]], bool | int | str]
]


@lru_cache
def evaluate_z3_expression(
    expr: z3.ExprRef,
) -> Result[Z3EvalResult, NotImplementedError]:
    if z3.is_var(expr) or is_z3_var(expr):
        return Success(((str(expr),), lambda args: args[0]))

    if z3.is_quantifier(expr):
        return Failure(
            NotImplementedError("Cannot evaluate expressions with quantifiers.")
        )

    children_results: Tuple[Z3EvalResult, ...] = ()
    for child_expr in expr.children():
        match evaluate_z3_expression(child_expr):
            case Success(child_result):
                children_results += (child_result,)
            case Failure(exc):
                return Failure(exc)

    def not_implemented_failure(_=Nothing) -> Failure[NotImplementedError]:
        logger = logging.getLogger("Z3 evaluation")
        logger.debug("Evaluation of expression %s not implemented.", expr)
        return Failure(
            NotImplementedError(f"Evaluation of expression {expr} not implemented.")
        )

    return (
        flow(
            Nothing,
            *map(
                compose((lambda f: (lambda _: f(expr, children_results))), lash),
                [
                    # Literals
                    evaluate_z3_string_value,
                    evaluate_z3_int_value,
                    evaluate_z3_rat_value,
                    evaluate_z3_str_to_int,
                    evaluate_z3_false_value,
                    evaluate_z3_true_value,
                    # Regular Expressions
                    evaluate_z3_re_range,
                    evaluate_z3_re_loop,
                    evaluate_z3_seq_to_re,
                    evaluate_z3_re_concat,
                    evaluate_z3_seq_in_re,
                    evaluate_z3_re_star,
                    evaluate_z3_re_plus,
                    evaluate_z3_re_option,
                    evaluate_z3_re_union,
                    evaluate_z3_re_comp,
                    evaluate_z3_re_full_set,
                    # Boolean Combinations
                    evaluate_z3_not,
                    evaluate_z3_and,
                    evaluate_z3_or,
                    # Comparisons
                    evaluate_z3_eq,
                    evaluate_z3_lt,
                    evaluate_z3_le,
                    evaluate_z3_gt,
                    evaluate_z3_ge,
                    # Arithmetic Operations
                    evaluate_z3_add,
                    evaluate_z3_sub,
                    evaluate_z3_mul,
                    evaluate_z3_div,
                    evaluate_z3_mod,
                    evaluate_z3_pow,
                    # String Operations
                    evaluate_z3_seq_length,
                    evaluate_z3_seq_concat,
                    evaluate_z3_seq_at,
                    evaluate_z3_seq_extract,
                    evaluate_z3_str_to_code,
                    # Fallback
                    not_implemented_failure,
                ],
            ),
        )
        .bind(lambda result: Success(result))
        .lash(not_implemented_failure)
    )


def evaluate_z3_string_value(expr: z3.ExprRef, _) -> Maybe[Z3EvalResult]:
    if not z3.is_string_value(expr):
        return Nothing
    expr: z3.StringVal
    return Some(((), expr.as_string().replace(r"\u{}", "\x00")))


def evaluate_z3_int_value(expr: z3.ExprRef, _) -> Maybe[Z3EvalResult]:
    if not z3.is_int_value(expr):
        return Nothing

    expr: z3.IntVal
    return Some(((), expr.as_long()))


def evaluate_z3_rat_value(expr: z3.ExprRef, _) -> Maybe[Z3EvalResult]:
    if not z3.is_rational_value(expr):
        return Nothing

    expr: z3.RatVal
    return Some(((), expr.numerator().as_long() / expr.denominator().as_long()))


def evaluate_z3_str_to_int(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    # NOTE: We convert a float string to int by rounding! This differs from the standard
    #       SMT-LIB/Z3 semantics, where str.to.int returns -1 for all strings that don't
    #       represent positive integers.
    if expr.decl().kind() != z3.Z3_OP_STR_TO_INT:
        return Nothing

    if isinstance(children_results[0][1], str) and not children_results[0][1]:
        raise DomainError("Empty string cannot be converted to int.")

    def constructor(args):
        assert len(args) == 1
        c = args[0]
        try:
            return int(c)
        except ValueError:
            try:
                return int(float(c))
            except ValueError:
                raise DomainError(
                    f"Expression {children_results[0]} cannot be converted to int."
                )

    return Some(construct_result(constructor, children_results))


def evaluate_z3_false_value(expr: z3.ExprRef, _) -> Maybe[Z3EvalResult]:
    if not z3.is_false(expr):
        return Nothing
    return Some(((), False))


def evaluate_z3_true_value(expr: z3.ExprRef, _) -> Maybe[Z3EvalResult]:
    if not z3.is_true(expr):
        return Nothing

    return Some(((), True))


# Regular Expressions
def evaluate_z3_re_range(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().name() != "re.range":
        return Nothing

    return Some(
        construct_result(lambda args: f"[{args[0]}-{args[1]}]", children_results)
    )


def evaluate_z3_re_loop(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_RE_LOOP:
        return Nothing

    return Some(
        construct_result(
            lambda args: f"{args[0]}{{{expr.params()[0]},{expr.params()[1]}}}",
            children_results,
        )
    )


def evaluate_z3_seq_to_re(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_SEQ_TO_RE:
        return Nothing

    def constructor(args):
        assert len(args) == 1

        child_string = args[0]
        for symbol, ctrl_character in zip("tnrvf", "\t\n\r\v\f"):
            child_string = child_string.replace("\\" + symbol, ctrl_character)

        return re.escape(child_string)

    return Some(construct_result(constructor, children_results))


def evaluate_z3_re_concat(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_RE_CONCAT:
        return Nothing

    return Some(construct_result(lambda args: "".join(args), children_results))


def evaluate_z3_seq_in_re(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_SEQ_IN_RE:
        return Nothing

    return Some(
        construct_result(
            lambda args: re.match(f"^{args[1]}$", args[0]) is not None,
            children_results,
        )
    )


def evaluate_z3_re_star(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_RE_STAR:
        return Nothing

    return Some(construct_result(lambda args: f"({args[0]})*", children_results))


def evaluate_z3_re_plus(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_RE_PLUS:
        return Nothing

    return Some(construct_result(lambda args: f"({args[0]})+", children_results))


def evaluate_z3_re_option(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_RE_OPTION:
        return Nothing

    return Some(construct_result(lambda args: f"({args[0]})?", children_results))


def evaluate_z3_re_union(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_RE_UNION:
        return Nothing

    return Some(
        construct_result(lambda args: f"(({args[0]})|({args[1]}))", children_results)
    )


def evaluate_z3_re_comp(expr: z3.ExprRef, _) -> Maybe[Z3EvalResult]:
    if expr.decl().name() != "re.comp":
        return Nothing

    # The argument must be a union of strings or a range.
    child = expr.children()[0]
    if (
        child.decl().kind() == z3.Z3_OP_RE_UNION
        and all(
            grandchild.decl().kind() == z3.Z3_OP_SEQ_TO_RE
            for grandchild in child.children()
        )
        or child.decl().name() == "re.range"
    ):
        return Some(
            construct_result(
                lambda args: "[^" + "".join(args) + "]",
                tuple(map(evaluate_z3_expression, child.children())),
            )
        )

    return Nothing


def evaluate_z3_re_full_set(expr: z3.ExprRef, _) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_RE_FULL_SET:
        return Nothing

    return Some(((), ".*?"))


# Boolean Combinations
def evaluate_z3_not(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_not(expr):
        return Nothing

    return Some(construct_result(lambda args: not args[0], children_results))


def evaluate_z3_and(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_and(expr):
        return Nothing

    return Some(
        construct_result(lambda args: reduce(operator.and_, args), children_results)
    )


def evaluate_z3_or(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_or(expr):
        return Nothing

    return Some(
        construct_result(lambda args: reduce(operator.or_, args), children_results)
    )


# Comparisons
def evaluate_z3_eq(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_eq(expr):
        return Nothing

    return Some(construct_result(lambda args: args[0] == args[1], children_results))


def evaluate_z3_lt(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_lt(expr):
        return Nothing

    return Some(construct_result(lambda args: args[0] < args[1], children_results))


def evaluate_z3_le(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_le(expr):
        return Nothing

    return Some(construct_result(lambda args: args[0] <= args[1], children_results))


def evaluate_z3_gt(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_gt(expr):
        return Nothing

    return Some(construct_result(lambda args: args[0] > args[1], children_results))


def evaluate_z3_ge(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_ge(expr):
        return Nothing

    return Some(construct_result(lambda args: args[0] >= args[1], children_results))


# Arithmetic Operations
def evaluate_z3_add(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_add(expr):
        return Nothing

    return Some(construct_result(lambda args: args[0] + args[1], children_results))


def evaluate_z3_sub(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_sub(expr):
        return Nothing

    return Some(construct_result(lambda args: args[0] - args[1], children_results))


def evaluate_z3_mul(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_mul(expr):
        return Nothing

    return Some(construct_result(lambda args: args[0] * args[1], children_results))


def evaluate_z3_div(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_div(expr):
        return Nothing

    return Some(
        construct_result(
            lambda args: int(float(args[0]) / float(args[1])), children_results
        )
    )


def evaluate_z3_mod(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_mod(expr):
        return Nothing

    return Some(construct_result(lambda args: args[0] % args[1], children_results))


def evaluate_z3_pow(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_POWER:
        return Nothing

    return Some(construct_result(lambda args: args[0] ** args[1], children_results))


# String Operations
def evaluate_z3_seq_length(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_SEQ_LENGTH:
        return Nothing

    return Some(construct_result(lambda args: len(args[0]), children_results))


def evaluate_z3_seq_concat(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_SEQ_CONCAT:
        return Nothing

    return Some(
        construct_result(
            lambda args: cast(str, args[0]) + cast(str, args[1]), children_results
        )
    )


def evaluate_z3_seq_at(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_SEQ_AT:
        return Nothing

    return Some(
        construct_result(
            lambda args: cast(str, args[0])[cast(int, args[1])], children_results
        )
    )


def evaluate_z3_seq_extract(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_SEQ_EXTRACT:
        return Nothing

    return Some(
        construct_result(
            lambda args: cast(str, args[0])[
                cast(int, args[1]) : cast(int, args[1]) + cast(int, args[2])
            ],
            children_results,
        )
    )


def evaluate_z3_str_to_code(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_STR_TO_CODE:
        return Nothing

    assert (
        len(children_results) == 1
    ), f"Unexpected argument length {len(children_results)}"

    return Some(
        construct_result(
            lambda args: ord(args[0]),
            children_results,
        )
    )


def construct_result(
    constructor: Callable[[Tuple[bool | int | str, ...]], bool | int | str],
    children_results: Tuple[Z3EvalResult, ...],
) -> Z3EvalResult:
    params: Tuple[str, ...] = tuple(
        set([param for child_params, _ in children_results for param in child_params])
    )

    if not params:
        return (), constructor(
            tuple([child_result for _, child_result in children_results])
        )

    def closure(var_insts: Tuple[str, ...]) -> bool | int | str:
        assert len(var_insts) == len(params)
        instantiated_children_results: Tuple[bool | int | str, ...] = ()
        for child_params, child_result in children_results:
            if not child_params:
                assert type(child_result) in {bool, int, str}
                instantiated_children_results += (cast(bool | int | str, child_result),)
                continue

            instantiated_child_params: Tuple[str] = cast(Tuple[str], ())
            for child_param in child_params:
                instantiated_child_params += (
                    var_insts[params.index(str(child_param))],
                )

            eval_child_result = child_result(instantiated_child_params)
            assert type(eval_child_result) in {bool, int, str}
            instantiated_children_results += (eval_child_result,)

        return constructor(instantiated_children_results)

    return params, closure


def z3_solve(
    formulas: Iterable[z3.BoolRef], timeout_ms=500
) -> Tuple[z3.CheckSatResult, Optional[z3.ModelRef]]:
    logger = logging.getLogger("z3_solve")
    formulas = list(formulas)

    result = z3.unknown  # To remove IDE warning
    model: Optional[z3.ModelRef] = None
    parallel = False

    for _ in range(20):
        solver = z3.Solver()
        if timeout_ms is not None:
            solver.set("timeout", timeout_ms)
        for formula in formulas:
            solver.add(formula)
        result = solver.check()

        if result == z3.sat:
            model = solver.model()

        if result != z3.unknown:
            break

        if timeout_ms is None:
            break

        timeout_ms = int(timeout_ms * 0.9) + 1
        random.shuffle(formulas)
        parallel = not parallel
        z3.set_param("parallel.enable", parallel)
        z3.set_param("smt.random_seed", random.randint(0, 99999))

    if result == z3.unknown:
        logger.warning(
            "Satisfiability of %s could not be decided", list(map(str, formulas))
        )

    return result, model


class DomainError(RuntimeError):
    def __init__(self, msg: str, *args):
        super().__init__(msg, *args)
        self.msg = msg

    def __str__(self):
        return f"DomainError({self.msg})"


def is_valid(formula: z3.BoolRef, timeout: int = 500) -> ThreeValuedTruth:
    if z3.is_true(formula):
        return ThreeValuedTruth.true()

    if z3.is_false(formula):
        return ThreeValuedTruth.false()

    def process_eval_result(eval_result: Z3EvalResult) -> ThreeValuedTruth:
        if eval_result[0]:
            # There must not be any uninstantiated variables left
            return ThreeValuedTruth.false()

        assert isinstance(
            eval_result[1], bool
        ), f"Received {eval_result[1]} (type {type(eval_result[1]).__name__}), not bool"

        return ThreeValuedTruth.from_bool(eval_result[1])

    def solve_using_z3(_=Nothing) -> ThreeValuedTruth:
        z3_result, _ = z3_solve([z3.Not(formula)], timeout_ms=timeout)

        if z3_result == z3.unsat:
            return ThreeValuedTruth.true()
        elif z3_result == z3.sat:
            return ThreeValuedTruth.false()
        else:
            return ThreeValuedTruth.unknown()

    return (
        evaluate_z3_expression(formula)
        .map(process_eval_result)
        .lash(lambda _: Success(solve_using_z3()))
        .unwrap()
    )


def z3_eq(formula_1: z3.ExprRef, formula_2: z3.ExprRef | str | int) -> z3.BoolRef:
    a, b = _coerce_exprs(formula_1, formula_2)
    return z3.BoolRef(
        z3.Z3_mk_eq(formula_1.ctx_ref(), a.as_ast(), b.as_ast()), formula_1.ctx
    )


def z3_and(formulas: Sequence[z3.BoolRef]) -> z3.BoolRef:
    if not formulas:
        return z3.BoolRef(True)
    if len(formulas) == 1:
        return formulas[0]
    return z3.And(*formulas)


def z3_or(formulas: Sequence[z3.BoolRef]) -> z3.BoolRef:
    if not formulas:
        return z3.BoolRef(False)
    if len(formulas) == 1:
        return formulas[0]
    return z3.Or(*formulas)


def z3_push_in_negations(formula: z3.BoolRef, negate=False) -> z3.BoolRef:
    if z3.is_not(formula):
        return z3_push_in_negations(formula.children()[0], negate=not negate)
    elif z3.is_and(formula):
        if negate:
            return z3.Or(
                *[z3_push_in_negations(child, True) for child in formula.children()]
            )
        else:
            return z3.And(
                *[z3_push_in_negations(child, False) for child in formula.children()]
            )
    elif z3.is_or(formula):
        if negate:
            return z3.And(
                *[z3_push_in_negations(child, True) for child in formula.children()]
            )
        else:
            return z3.Or(
                *[z3_push_in_negations(child, False) for child in formula.children()]
            )
    elif isinstance(formula, z3.QuantifierRef):
        vars = [z3.String(formula.var_name(idx)) for idx in range(formula.num_vars())]
        if (negate and formula.is_forall()) or (not negate and formula.is_exists()):
            return z3.Exists(vars, z3_push_in_negations(formula.children()[0], negate))
        else:
            return z3.ForAll(vars, z3_push_in_negations(formula.children()[0], negate))

    return z3.simplify(z3.Not(formula) if negate else formula)


E = TypeVar("E", bound=z3.ExprRef)


def z3_subst(inp: E, subst_map: Mapping[z3.ExprRef, z3.ExprRef]) -> E:
    return z3.substitute(inp, *tuple(subst_map.items()))


def is_z3_var(expr: z3.ExprRef) -> bool:
    return z3.is_const(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED


def replace_in_z3_expr(
    e: z3.ExprRef | z3.QuantifierRef,
    replacement: Callable[
        [z3.ExprRef | z3.QuantifierRef], Optional[z3.ExprRef | z3.QuantifierRef]
    ],
) -> z3.ExprRef | z3.QuantifierRef:
    subst_map: Dict[z3.ExprRef | z3.QuantifierRef, z3.ExprRef | z3.QuantifierRef] = {}

    for sub_expr in visit_z3_expr(e):
        repl = replacement(sub_expr)
        if repl is not None:
            subst_map[sub_expr] = repl

    return z3_subst(e, subst_map)


def visit_z3_expr(
    e: z3.ExprRef | z3.QuantifierRef,
    seen: Optional[Dict[Union[z3.ExprRef, z3.QuantifierRef], bool]] = None,
) -> Generator[z3.ExprRef | z3.QuantifierRef, None, None]:
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


@lru_cache()
def get_symbols(expr: z3.ExprRef) -> Set[z3.SeqRef]:
    if is_z3_var(expr):
        if expr.decl().range() != z3.StringSort():
            raise NotImplementedError(
                f"This class was developed for String symbols only, found {expr.decl().range()}"
            )

        assert isinstance(expr, z3.SeqRef)
        return {expr}

    return reduce(
        lambda acc, elem: acc | elem,
        [get_symbols(child) for child in expr.children()],
        set(),
    )


def smt_expr_to_str(  # noqa: C901
    f: z3.ExprRef, qfd_var_stack: Tuple[str, ...] = ()
) -> str:
    op_strings = {
        z3.Z3_OP_SEQ_IN_RE: "str.in_re",
        z3.Z3_OP_SEQ_CONCAT: "str.++",
        z3.Z3_OP_RE_CONCAT: "re.++",
        z3.Z3_OP_STR_TO_INT: "str.to.int",
        # <- Different from standard SMT-LIB (Z3 version)
    }

    if z3.is_var(f):
        idx = z3.get_var_index(f)
        assert len(qfd_var_stack) > idx
        return qfd_var_stack[idx]
    if z3.is_string_value(f):
        result = '"' + cast(str, f.as_string()).replace('"', r"\"") + '"'
        result = result.replace(r"\u{}", r"\u{0}")
        return result
    if z3.is_int_value(f):
        return str(f.as_long())
    if z3.is_true(f):
        return "true"
    if z3.is_false(f):
        return "false"
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

        if not f.children():
            return op

        return (
            f"({op} {' '.join(map(lambda c: smt_expr_to_str(c, qfd_var_stack), f.children()))}".strip()
            + ")"
        )

    if isinstance(f, z3.QuantifierRef):
        vars = []
        for var_idx in range(f.num_vars()):
            vars.append(f"({f.var_name(var_idx)} {f.var_sort(var_idx)})")
            qfd_var_stack = (f.var_name(var_idx),) + qfd_var_stack

        kind = "forall" if f.is_forall() else "exists"

        return f"({kind} ({' '.join(vars)}) {smt_expr_to_str(f.body(), qfd_var_stack)})"

    raise NotImplementedError(f"{str(f)} ({type(f).__name__})")


def smt_string_val_to_string(smt_val: z3.StringVal) -> str:
    r"""
    Converts `smt_val` to its string representation. Handles the special case of
    null-bytes characters in `smt_val`: Those are represented as `\u{}` by `as_string()`
    and get converted to `\x00`.

    :param smt_val: The `z3.StringVal` to convert to a Python string.
    :return: The Python string representation of `smt_val`.
    """

    return smt_val.as_string().replace(r"\u{}", "\x00")


def parent_relationships_in_z3_expr(
    expr: z3.ExprRef, parent: Optional[z3.ExprRef] = None
) -> Dict[z3.ExprRef, Set[z3.ExprRef]]:
    """
    Returns a dictionary in which each expression in :code:`expr` points to the set of
    parent operators in which it occurs.

    >>> x, y = z3.Strings("x y")
    >>> expr = z3.And(z3_eq(z3.StrToInt(x), z3.IntVal(17)), x > y)
    >>> result = parent_relationships_in_z3_expr(expr)

    >>> result[x]
    {str.<(y, x), StrToInt(x)}
    >>> result[y]
    {str.<(y, x)}
    >>> all(
    ...     child is expr
    ...     or child in parent_relationships_in_z3_expr(expr)
    ...     for child in visit_z3_expr(expr))
    True

    :param expr: The expression from which to extract the parent relationship.
    :param parent: The parent of :code:`expr`.
    :return: A dictionary mapping from all child expressions in :code:`expr` to the set
             of their direct parent expression inside which they occur.
    """
    children_results = reduce(
        merge_dict_of_sets,
        [
            parent_relationships_in_z3_expr(child, expr)
            for child in expr.children()
            if child is not expr
        ],
        {},
    )

    return (
        merge_dict_of_sets(children_results, {expr: {parent}})
        if parent is not None
        else children_results
    )


def z3_split_at_operator(expr: z3.ExprRef, op: int) -> List[z3.ExprRef]:
    """
    Splits an expression constructed from the "op" kind into its constituents.

    >>> z3_split_at_operator(z3.Concat(z3.Re("-"), z3.Range("1", "9"), z3.Plus(z3.Range("0", "9"))), z3.Z3_OP_RE_CONCAT)
    [Re("-"), Range("1", "9"), Plus(Range("0", "9"))]

    :param expr: The expression to split.
    :param op: The operator that should be considered.
    :return: A list of elements that were (recursively) constructed from the operator
        op. Might be a singleton if expr is not constructed from that operator.
    """

    if expr.decl().kind() != op:
        return [expr]

    return reduce(
        lambda acc, child: acc + z3_split_at_operator(child, op), expr.children(), []
    )


ONE_DIGIT_REGEX = re.compile(r"[0-9]")


def seqref_to_int(seqref: z3.SeqRef) -> Maybe[int]:
    """
    TODO
    :param seqref:
    :return:
    """
    assert isinstance(seqref, z3.SeqRef)
    try:
        return Some(int(seqref.as_string()))
    except ValueError:
        return Nothing


def numeric_intervals_from_regex(regex: z3.ReRef) -> Maybe[List[Tuple[int, int]]]:
    r"""
    This function transforms regular expressions representing intervals of integers
    to these intervals. It recognizes regular expressions represented by the following
    context-free grammar (the definition of <sequence> is possibly an
    underapproximation) as long as the ISLa constraint
    :code:`str.to.int(<range>.<digit>[1]) <= str.to.int(<range>.<digit>[2])` is
    satisfied (ranges are ordered)::

        <start> ::= <regex>
        <regex> ::= <single> | <range> | <zeroes> | <full> | <union> | <sequence>
        <single> ::= "z3.Re(\"" <digit> "\")"
        <range> ::= "z3.Range(\"" <digit> "\", \"" <digit> "\")"
        <zeroes> ::= "z3.Star(z3.Re(\"0\"))" | "z3.Plus(z3.Re(\"0\"))"
        <full> ::=
              "z3.Star(z3.Range(\"0\", \"9\"))"
            | "z3.Plus(z3.Range(\"0\", \"9\"))"
        <union> ::= "z3.Union(" <regex> ", " <regex-list> ")"
        <sequence> ::=
              "z3.Concat(" <opt-pm> <maybe-seq-zeroes> <one-or-zero-nine> ", " <zero-nines> ")"
            | "z3.Concat(" <opt-pm> <seq-zeroes> <regex> ")"
            | "z3.Concat(" <seq-first-elems-union> ", " <one-or-zero-nine> ", " <zero-nines> ")"
            | "z3.Concat(" <seq-first-elems-union> ", " <regex> ")"
        <opt-pm> ::= "z3.Option(" <pm> "), " | <pm> ", " | ""
        <pm> ::= "z3.Re(\"+\")" | "z3.Re(\"-\")"
        <maybe-seq-zeroes> ::= <seq-zeroes> | ""
        <seq-zeroes> ::=
              <zeroes> ", " <seq-zeroes> | "z3.Re(\"0\"), " <seq-zeroes>
            | <zeroes> ", " | "z3.Re(\"0\"), "
        <one-or-zero-nine> ::= "z3.Range(\"0\", \"9\")" | "z3.Range(\"1\", \"9\")"
        <zero-nines> ::=
            "z3.Star(z3.Range(\"0\", \"9\"))" | "z3.Plus(z3.Range(\"0\", \"9\"))"
        <seq-first-elems-union> ::= "z3.Union(" <seq-first-elem> ", " <seq-first-elems-list> ")"
        <seq-first-elems-list> ::=
              <seq-first-elem> ", " <seq-first-elems-list>
            | <seq-first-elem>
        <seq-first-elem> ::= <pm> | <zeroes> | "z3.Re(\"0\")"
        <regex-list> ::= <regex> ", " <regex-list> | <regex>
        <digit> ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"

    For expressions outside this grammar, it returns :code:`Nothing`.

    There is no distinction between open and closed intervals. Per default, intervals
    are closed; however, intervals with :code:`-sys.maxsize` as lower or
    :code:`sys.maxsize` as upper bound are open at these bounds.

    Intervals with the same start and end values represent a single number:

    >>> numeric_intervals_from_regex(z3.Re("1"))
    <Some: [(1, 1)]>

    Infinity is represented by (+/-) :code:`sys.maxsize`:

    >>> sys.maxsize
    9223372036854775807

    >>> numeric_intervals_from_regex(z3.Star(z3.Range("0", "9")))
    <Some: [(-9223372036854775807, 9223372036854775807)]>

    We support concatenations of zeroes:

    >>> numeric_intervals_from_regex(z3.Concat(z3.Plus(z3.Re("0")), z3.Re("0"), z3.Star(z3.Range("0", "0"))))
    <Some: [(0, 0)]>

    Neighboring intervals are merged:

    >>> numeric_intervals_from_regex(z3.Union(z3.Range("1", "4"), z3.Re("5")))
    <Some: [(1, 5)]>

    Others kept distinct:

    >>> numeric_intervals_from_regex(z3.Union(z3.Re("6"), z3.Range("1", "4")))
    <Some: [(1, 4), (6, 6)]>

    We recognize + and - signs in unions and options:

    >>> numeric_intervals_from_regex(z3.Concat(z3.Union(z3.Re("+"), z3.Re("-")), z3.Range("0", "9")))
    <Some: [(-9, 9)]>

    >>> numeric_intervals_from_regex(z3.Concat(z3.Option(z3.Re("-")), z3.Range("0", "9")))
    <Some: [(-9, 9)]>

    >>> numeric_intervals_from_regex(z3.Concat(z3.Option(z3.Re("+")), z3.Range("0", "9")))
    <Some: [(0, 9)]>

    Intervals might be split if we add a "-":

    >>> numeric_intervals_from_regex(z3.Concat(z3.Union(z3.Re("+"), z3.Re("-")), z3.Range("2", "9")))
    <Some: [(-9, -2), (2, 9)]>

    The interval of strictly positive numbers if created by enforcing the presence of
    a leading 1:

    >>> numeric_intervals_from_regex(z3.Concat(z3.Star(z3.Re("0")), z3.Range("1", "9"), z3.Star(z3.Range("0", "9"))))
    <Some: [(1, 9223372036854775807)]>

    If the 0-9 interval is inside a Plus, not a Star, we exclude the single-digit
    numbers.

    >>> numeric_intervals_from_regex(z3.Concat(z3.Range("1", "9"), z3.Plus(z3.Range("0", "9"))))
    <Some: [(10, 9223372036854775807)]>

    Also to this interval, we can apply "-":

    >>> numeric_intervals_from_regex(z3.Concat(z3.Re("-"), z3.Range("1", "9"), z3.Plus(z3.Range("0", "9"))))
    <Some: [(-9223372036854775807, -10)]>

    :param regex: The regular expression from which to extract the represented
        intervals.
    :return: An optional list of intervals represented by the regular expression. A
        returned "nothing" signals that either the expressions represent a different
        language than what can be represented by lists of intervals, or that a
        construction is not supported by this function. In intervals, infinity is
        modeled by +/- :code:`sys.maxsize`. With the exception of these special values,
        intervals are closed.
    """

    assert isinstance(regex, z3.ReRef)

    concat = partial(numeric_intervals_from_concat, lambda _: Nothing)
    full_range = partial(
        numeric_intervals_from_full_range,
        concat,
    )
    zeroes = partial(
        numeric_intervals_from_zeroes,
        full_range,
    )
    union = partial(
        numeric_intervals_from_union,
        zeroes,
    )
    seq_to_re = partial(
        numeric_intervals_from_seq_to_re,
        union,
    )
    regex_range = partial(
        numeric_intervals_from_regex_range,
        seq_to_re,
    )

    result: Maybe[List[Tuple[int, int]]] = regex_range(regex)

    if result == Nothing:
        # Note: This is not a problem if we're in a recursive call from the loop
        #       removing 0 padding. In that case, the returned `Nothing`
        #       simply signals that there are no more 0s to remove.
        HELPERS_LOGGER.debug(
            f"Unsupported expression in `numeric_intervals_from_regex`: {regex}"
        )

    return result


def numeric_intervals_from_regex_range(
    fallback: Callable[[z3.ReRef], Maybe[List[Tuple[int, int]]]], regex: z3.ReRef
) -> Maybe[List[Tuple[int, int]]]:
    """
    Handles the :code:`z3.Range(a, b)` case from
    :func:`~isla.z3_helpers.numeric_intervals_from_regex`.

    :param fallback: The function to call if this function is not responsible.
    :param regex: See :func:`~isla.z3_helpers.numeric_intervals_from_regex`
    :return: See :func:`~isla.z3_helpers.numeric_intervals_from_regex`
    """
    if regex.decl().kind() == z3.Z3_OP_RE_RANGE and all(
        ONE_DIGIT_REGEX.match(child.as_string()) for child in regex.children()
    ):
        return (
            seqref_to_int(regex.children()[0])
            .bind(
                lambda low: seqref_to_int(regex.children()[1]).bind(
                    lambda high: (Some((low, high)) if low <= high else Nothing)
                )
            )
            .map(lambda t: [t])
        )
    else:
        return fallback(regex)


def numeric_intervals_from_seq_to_re(
    fallback: Callable[[z3.ReRef], Maybe[List[Tuple[int, int]]]], regex: z3.ReRef
) -> Maybe[List[Tuple[int, int]]]:
    """
    Handles the :code:`z3.Re(c)` case from
    :func:`~isla.z3_helpers.numeric_intervals_from_regex`.

    :param fallback: The function to call if this function is not responsible.
    :param regex: See :func:`~isla.z3_helpers.numeric_intervals_from_regex`
    :return: See :func:`~isla.z3_helpers.numeric_intervals_from_regex`
    """
    if regex.decl().kind() == z3.Z3_OP_SEQ_TO_RE:
        return seqref_to_int(regex.children()[0]).map(lambda n: [(n, n)])
    else:
        return fallback(regex)


def numeric_intervals_from_union(
    fallback: Callable[[z3.ReRef], Maybe[List[Tuple[int, int]]]], regex: z3.ReRef
) -> Maybe[List[Tuple[int, int]]]:
    """
    Handles the :code:`z3.Union(...)` case from
    :func:`~isla.z3_helpers.numeric_intervals_from_regex`.

    :param fallback: The function to call if this function is not responsible.
    :param regex: See :func:`~isla.z3_helpers.numeric_intervals_from_regex`
    :return: See :func:`~isla.z3_helpers.numeric_intervals_from_regex`
    """
    if regex.decl().kind() == z3.Z3_OP_RE_UNION:
        return merge_intervals(*map(numeric_intervals_from_regex, regex.children()))
    else:
        return fallback(regex)


def numeric_intervals_from_zeroes(
    fallback: Callable[[z3.ReRef], Maybe[List[Tuple[int, int]]]], regex: z3.ReRef
) -> Maybe[List[Tuple[int, int]]]:
    """
    Handles the :code:`z3.Star/Plus(...0...)` case from
    :func:`~isla.z3_helpers.numeric_intervals_from_regex`.

    :param fallback: The function to call if this function is not responsible.
    :param regex: See :func:`~isla.z3_helpers.numeric_intervals_from_regex`
    :return: See :func:`~isla.z3_helpers.numeric_intervals_from_regex`
    """
    if regex.decl().kind() in [
        z3.Z3_OP_RE_STAR,
        z3.Z3_OP_RE_PLUS,
    ] and numeric_intervals_from_regex(regex.children()[0]).map(
        lambda intervals: intervals == [(0, 0)]
    ).value_or(
        lambda: False
    ):
        return Some([(0, 0)])
    else:
        return fallback(regex)


def numeric_intervals_from_full_range(
    fallback: Callable[[z3.ReRef], Maybe[List[Tuple[int, int]]]], regex: z3.ReRef
) -> Maybe[List[Tuple[int, int]]]:
    """
    Handles the :code:`z3.Star/Plus(z3.Range("0", "9"))` case from
    :func:`~isla.z3_helpers.numeric_intervals_from_regex`.

    :param fallback: The function to call if this function is not responsible.
    :param regex: See :func:`~isla.z3_helpers.numeric_intervals_from_regex`
    :return: See :func:`~isla.z3_helpers.numeric_intervals_from_regex`
    """
    if regex.decl().kind() in [
        z3.Z3_OP_RE_STAR,
        z3.Z3_OP_RE_PLUS,
    ] and regex.children()[0] == z3.Range("0", "9"):
        return Some([(-sys.maxsize, sys.maxsize)])
    else:
        return fallback(regex)


def numeric_intervals_from_concat(
    fallback: Callable[[z3.ReRef], Maybe[List[Tuple[int, int]]]], regex: z3.ReRef
) -> Maybe[List[Tuple[int, int]]]:
    """
    Handles the concatenation case from
    :func:`~isla.z3_helpers.numeric_intervals_from_regex`.

    :param fallback: The function to call if this function is not responsible.
    :param regex: See :func:`~isla.z3_helpers.numeric_intervals_from_regex`
    :return: See :func:`~isla.z3_helpers.numeric_intervals_from_regex`
    """
    if regex.decl().kind() != z3.Z3_OP_RE_CONCAT:
        return fallback(regex)

    children: List[z3.ReRef] = cast(
        List[z3.ReRef], z3_split_at_operator(regex, z3.Z3_OP_RE_CONCAT)
    )

    first_child = children[0]
    if first_child.decl().kind() == z3.Z3_OP_RE_UNION or first_child == z3.Option(
        z3.Re("-")
    ):
        return merge_intervals(
            *map(
                lambda option_or_union: numeric_intervals_from_regex(
                    z3.Concat(option_or_union, *children[1:])
                ),
                first_child.children()
                if first_child.decl().kind() == z3.Z3_OP_RE_UNION
                else [z3.Re("+"), z3.Re("-")],
            )
        )
    elif first_child in [z3.Re("+"), z3.Option(z3.Re("+"))]:
        return numeric_intervals_from_regex(
            children[1] if len(children) == 2 else z3.Concat(*children[1:])
        )
    elif first_child == z3.Re("-"):
        return numeric_intervals_from_regex(
            children[1] if len(children) == 2 else z3.Concat(*children[1:])
        ).map(
            lambda list_of_intervals: list(
                map(
                    lambda interval: (-interval[1], -interval[0]),
                    reversed(list_of_intervals),
                ),
            )
        )

    # We support the following cases, always with an optional left-padding of
    # 0s that can come in different forms (this comprises the padding of a
    # non-sequence with 0s):
    #
    # - [1-9] [0-9]* -> (1, inf)
    # - [1-9] [0-9]+ -> (10, inf)
    # - [0-9] [0-9]* -> (0, inf)
    # - [0-9] [0-9]+ -> (0, inf)

    idx = 0
    while idx < len(children) and (
        numeric_intervals_from_regex(children[idx])
        .map(lambda intervals: intervals == [(0, 0)])
        .value_or(False)
    ):
        idx += 1

    if idx > 0:
        children = children[idx:]
        return (
            Some([(0, 0)])
            if not children
            else numeric_intervals_from_regex(
                children[0] if len(children) == 1 else z3.Concat(*children)
            )
        )

    if (
        len(children) == 2
        and (
            numeric_intervals_from_regex(children[0])
            .map(lambda first_intervals: first_intervals == [(1, 9)])
            .value_or(False)
        )
        and children[1].decl().kind() == z3.Z3_OP_RE_STAR
        and children[1].children()[0] == z3.Range("0", "9")
    ):
        # - [1-9] [0-9]* -> (1, inf)
        return Some([(1, sys.maxsize)])
    elif (
        len(children) == 2
        and (
            numeric_intervals_from_regex(children[0])
            .map(lambda first_intervals: first_intervals == [(1, 9)])
            .value_or(lambda: False)
        )
        and children[1].decl().kind() == z3.Z3_OP_RE_PLUS
        and children[1].children()[0] == z3.Range("0", "9")
    ):
        # - [1-9] [0-9]+ -> (10, inf)
        return Some([(10, sys.maxsize)])
    elif (
        len(children) == 2
        and (
            numeric_intervals_from_regex(children[0])
            .map(lambda first_intervals: first_intervals == [(0, 9)])
            .value_or(lambda: False)
        )
        and children[1].decl().kind() in [z3.Z3_OP_RE_PLUS, z3.Z3_OP_RE_STAR]
        and children[1].children()[0] == z3.Range("0", "9")
    ):
        # - [0-9] [0-9]* -> (0, inf)
        # - [0-9] [0-9]+ -> (0, inf)
        return Some([(0, sys.maxsize)])
    else:
        return fallback(regex)
