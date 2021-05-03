from input_constraints.lang import *


def forall_bind(
        bind_expression: BindExpression,
        bound_variable: BoundVariable,
        in_variable: Variable,
        inner_formula: Formula) -> ForallFormula:
    return ForallFormula(bound_variable, in_variable, inner_formula, bind_expression)


def exists_bind(
        bind_expression: BindExpression,
        bound_variable: BoundVariable,
        in_variable: Variable,
        inner_formula: Formula) -> ExistsFormula:
    return ExistsFormula(bound_variable, in_variable, inner_formula, bind_expression)


def forall(
        bound_variable: BoundVariable,
        in_variable: Variable,
        inner_formula: Formula) -> ForallFormula:
    return ForallFormula(bound_variable, in_variable, inner_formula)


def exists(
        bound_variable: BoundVariable,
        in_variable: Variable,
        inner_formula: Formula) -> ExistsFormula:
    return ExistsFormula(bound_variable, in_variable, inner_formula)


def before(
        var: Variable,
        before_var: Variable,
        in_var: Variable) -> PredicateFormula:
    return PredicateFormula(BEFORE_PREDICATE, var, before_var, in_var)


def smt_for(formula: z3.BoolRef, *free_variables: Variable) -> SMTFormula:
    return SMTFormula(formula, *free_variables)
