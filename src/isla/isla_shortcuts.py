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
