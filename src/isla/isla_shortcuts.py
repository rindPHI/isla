from typing import Union

import z3

from isla.derivation_tree import DerivationTree
from isla.isla_predicates import (
    BEFORE_PREDICATE,
)
from isla.language import (
    BoundVariable,
    Formula,
    BindExpression,
    Variable,
    ForallFormula,
    ExistsFormula,
    StructuralPredicateFormula,
    SMTFormula,
)


def bexpr(terminal_symbol: str) -> BindExpression:
    return BindExpression(terminal_symbol)


def forall_bind(
    bind_expression: Union[BindExpression, BoundVariable],
    bound_variable: Union[BoundVariable, str],
    in_variable: Union[Variable, DerivationTree],
    inner_formula: Formula,
) -> ForallFormula:
    return ForallFormula(bound_variable, in_variable, inner_formula, bind_expression)


def exists_bind(
    bind_expression: Union[BindExpression, BoundVariable],
    bound_variable: Union[BoundVariable, str],
    in_variable: Union[Variable, DerivationTree],
    inner_formula: Formula,
) -> ExistsFormula:
    return ExistsFormula(bound_variable, in_variable, inner_formula, bind_expression)


def forall(
    bound_variable: BoundVariable,
    in_variable: Union[Variable, DerivationTree],
    inner_formula: Formula,
) -> ForallFormula:
    return ForallFormula(bound_variable, in_variable, inner_formula)


def exists(
    bound_variable: BoundVariable,
    in_variable: Union[Variable, DerivationTree],
    inner_formula: Formula,
) -> ExistsFormula:
    return ExistsFormula(bound_variable, in_variable, inner_formula)


def before(
    var: Union[Variable, DerivationTree], before_var: Union[Variable, DerivationTree]
) -> StructuralPredicateFormula:
    return StructuralPredicateFormula(BEFORE_PREDICATE, var, before_var)


def true():
    return SMTFormula(z3.BoolVal(True))


def false():
    return SMTFormula(z3.BoolVal(False))


def smt_for(formula: z3.BoolRef, *free_variables: Variable) -> SMTFormula:
    return SMTFormula(formula, *free_variables)
