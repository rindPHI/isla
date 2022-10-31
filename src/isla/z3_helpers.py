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
from functools import lru_cache, reduce
from typing import Callable, Tuple, cast, List, Optional, Dict, Union, Generator, Set

import z3
from z3.z3 import _coerce_exprs

from isla.helpers import Maybe, chain_functions
from isla.three_valued_truth import ThreeValuedTruth

Z3EvalResult = Tuple[
    Tuple[str, ...], bool | int | str | Callable[[Tuple[str, ...]], bool | int | str]
]


@lru_cache
def evaluate_z3_expression(expr: z3.ExprRef) -> Z3EvalResult:
    if z3.is_var(expr) or is_z3_var(expr):
        return (str(expr),), lambda args: args[0]

    if z3.is_quantifier(expr):
        raise NotImplementedError("Cannot evaluate expressions with quantifiers.")

    children_results: Tuple[Z3EvalResult, ...] = tuple(
        map(evaluate_z3_expression, expr.children())
    )

    def raise_not_implemented_error(expr: z3.ExprRef, _) -> Maybe[Z3EvalResult]:
        logger = logging.getLogger("Z3 evaluation")
        logger.debug("Evaluation of expression %s not implemented.", expr)
        raise NotImplementedError(f"Evaluation of expression {expr} not implemented.")

    def close(evaluation_function: callable) -> callable:
        return lambda f: evaluation_function(f, children_results)

    return chain_functions(
        map(
            close,
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
                raise_not_implemented_error,
            ],
        ),
        expr,
    ).get()


def evaluate_z3_string_value(expr: z3.ExprRef, _) -> Maybe[Z3EvalResult]:
    if not z3.is_string_value(expr):
        return Maybe.nothing()
    expr: z3.StringVal
    return Maybe(((), expr.as_string().replace(r"\u{}", "\x00")))


def evaluate_z3_int_value(expr: z3.ExprRef, _) -> Maybe[Z3EvalResult]:
    if not z3.is_int_value(expr):
        return Maybe.nothing()

    expr: z3.IntVal
    return Maybe(((), expr.as_long()))


def evaluate_z3_rat_value(expr: z3.ExprRef, _) -> Maybe[Z3EvalResult]:
    if not z3.is_rational_value(expr):
        return Maybe.nothing()

    expr: z3.RatVal
    return Maybe(((), expr.numerator().as_long() / expr.denominator().as_long()))


def evaluate_z3_str_to_int(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    # NOTE: We convert a float string to int by rounding! This differs from the standard
    #       SMT-LIB/Z3 semantics, where str.to.int returns -1 for all strings that don't
    #       represent positive integers.
    if expr.decl().kind() != z3.Z3_OP_STR_TO_INT:
        return Maybe.nothing()

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

    return Maybe(construct_result(constructor, children_results))


def evaluate_z3_false_value(expr: z3.ExprRef, _) -> Maybe[Z3EvalResult]:
    if not z3.is_false(expr):
        return Maybe.nothing()
    return Maybe(((), False))


def evaluate_z3_true_value(expr: z3.ExprRef, _) -> Maybe[Z3EvalResult]:
    if not z3.is_true(expr):
        return Maybe.nothing()

    return Maybe(((), True))


# Regular Expressions
def evaluate_z3_re_range(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().name() != "re.range":
        return Maybe.nothing()

    return Maybe(
        construct_result(lambda args: f"[{args[0]}-{args[1]}]", children_results)
    )


def evaluate_z3_re_loop(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_RE_LOOP:
        return Maybe.nothing()

    return Maybe(
        construct_result(
            lambda args: f"{args[0]}{{{expr.params()[0]},{expr.params()[1]}}}",
            children_results,
        )
    )


def evaluate_z3_seq_to_re(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_SEQ_TO_RE:
        return Maybe.nothing()

    def constructor(args):
        assert len(args) == 1

        child_string = args[0]
        for symbol, ctrl_character in zip("tnrvf", "\t\n\r\v\f"):
            child_string = child_string.replace("\\" + symbol, ctrl_character)

        return re.escape(child_string)

    return Maybe(construct_result(constructor, children_results))


def evaluate_z3_re_concat(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_RE_CONCAT:
        return Maybe.nothing()

    return Maybe(construct_result(lambda args: "".join(args), children_results))


def evaluate_z3_seq_in_re(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_SEQ_IN_RE:
        return Maybe.nothing()

    return Maybe(
        construct_result(
            lambda args: re.match(f"^{args[1]}$", args[0]) is not None,
            children_results,
        )
    )


def evaluate_z3_re_star(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_RE_STAR:
        return Maybe.nothing()

    return Maybe(construct_result(lambda args: f"({args[0]})*", children_results))


def evaluate_z3_re_plus(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_RE_PLUS:
        return Maybe.nothing()

    return Maybe(construct_result(lambda args: f"({args[0]})+", children_results))


def evaluate_z3_re_option(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_RE_OPTION:
        return Maybe.nothing()

    return Maybe(construct_result(lambda args: f"({args[0]})?", children_results))


def evaluate_z3_re_union(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_RE_UNION:
        return Maybe.nothing()

    return Maybe(
        construct_result(lambda args: f"(({args[0]})|({args[1]}))", children_results)
    )


def evaluate_z3_re_comp(expr: z3.ExprRef, _) -> Maybe[Z3EvalResult]:
    if expr.decl().name() != "re.comp":
        return Maybe.nothing()

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
        return Maybe(
            construct_result(
                lambda args: "[^" + "".join(args) + "]",
                tuple(map(evaluate_z3_expression, child.children())),
            )
        )

    return Maybe.nothing()


def evaluate_z3_re_full_set(expr: z3.ExprRef, _) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_RE_FULL_SET:
        return Maybe.nothing()

    return Maybe(((), ".*?"))


# Boolean Combinations
def evaluate_z3_not(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_not(expr):
        return Maybe.nothing()

    return Maybe(construct_result(lambda args: not args[0], children_results))


def evaluate_z3_and(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_and(expr):
        return Maybe.nothing()

    return Maybe(
        construct_result(lambda args: reduce(operator.and_, args), children_results)
    )


def evaluate_z3_or(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_or(expr):
        return Maybe.nothing()

    return Maybe(
        construct_result(lambda args: reduce(operator.or_, args), children_results)
    )


# Comparisons
def evaluate_z3_eq(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_eq(expr):
        return Maybe.nothing()

    return Maybe(construct_result(lambda args: args[0] == args[1], children_results))


def evaluate_z3_lt(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_lt(expr):
        return Maybe.nothing()

    return Maybe(construct_result(lambda args: args[0] < args[1], children_results))


def evaluate_z3_le(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_le(expr):
        return Maybe.nothing()

    return Maybe(construct_result(lambda args: args[0] <= args[1], children_results))


def evaluate_z3_gt(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_gt(expr):
        return Maybe.nothing()

    return Maybe(construct_result(lambda args: args[0] > args[1], children_results))


def evaluate_z3_ge(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_ge(expr):
        return Maybe.nothing()

    return Maybe(construct_result(lambda args: args[0] >= args[1], children_results))


# Arithmetic Operations
def evaluate_z3_add(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_add(expr):
        return Maybe.nothing()

    return Maybe(construct_result(lambda args: args[0] + args[1], children_results))


def evaluate_z3_sub(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_sub(expr):
        return Maybe.nothing()

    return Maybe(construct_result(lambda args: args[0] - args[1], children_results))


def evaluate_z3_mul(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_mul(expr):
        return Maybe.nothing()

    return Maybe(construct_result(lambda args: args[0] * args[1], children_results))


def evaluate_z3_div(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_div(expr):
        return Maybe.nothing()

    return Maybe(
        construct_result(
            lambda args: int(float(args[0]) / float(args[1])), children_results
        )
    )


def evaluate_z3_mod(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if not z3.is_mod(expr):
        return Maybe.nothing()

    return Maybe(construct_result(lambda args: args[0] % args[1], children_results))


def evaluate_z3_pow(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_POWER:
        return Maybe.nothing()

    return Maybe(construct_result(lambda args: args[0] ** args[1], children_results))


# String Operations
def evaluate_z3_seq_length(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_SEQ_LENGTH:
        return Maybe.nothing()

    return Maybe(construct_result(lambda args: len(args[0]), children_results))


def evaluate_z3_seq_concat(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_SEQ_CONCAT:
        return Maybe.nothing()

    return Maybe(
        construct_result(
            lambda args: cast(str, args[0]) + cast(str, args[1]), children_results
        )
    )


def evaluate_z3_seq_at(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_SEQ_AT:
        return Maybe.nothing()

    return Maybe(
        construct_result(
            lambda args: cast(str, args[0])[cast(int, args[1])], children_results
        )
    )


def evaluate_z3_seq_extract(
    expr: z3.ExprRef, children_results: Tuple[Z3EvalResult, ...]
) -> Maybe[Z3EvalResult]:
    if expr.decl().kind() != z3.Z3_OP_SEQ_EXTRACT:
        return Maybe.nothing()

    return Maybe(
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
        return Maybe.nothing()

    assert (
        len(children_results) == 1
    ), f"Unexpected argument length {len(children_results)}"

    return Maybe(
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
    formulas: List[z3.BoolRef], timeout_ms=500
) -> Tuple[z3.CheckSatResult, Optional[z3.ModelRef]]:
    logger = logging.getLogger("z3_solve")

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

    try:
        eval_result = evaluate_z3_expression(formula)
        if eval_result[0]:
            # There must not be any uninstantiated variables left
            return ThreeValuedTruth.false()

        assert isinstance(
            eval_result[1], bool
        ), f"Received {eval_result[1]} (type {type(eval_result[1]).__name__}), not bool"

        return ThreeValuedTruth.from_bool(eval_result[1])
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


def z3_eq(formula_1: z3.ExprRef, formula_2: z3.ExprRef | str | int) -> z3.BoolRef:
    a, b = _coerce_exprs(formula_1, formula_2)
    return z3.BoolRef(
        z3.Z3_mk_eq(formula_1.ctx_ref(), a.as_ast(), b.as_ast()), formula_1.ctx
    )


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


def z3_subst(inp: z3.ExprRef, subst_map: Dict[z3.ExprRef, z3.ExprRef]) -> z3.ExprRef:
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
        return '"' + cast(str, f.as_string()).replace('"', r"\"") + '"'
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
