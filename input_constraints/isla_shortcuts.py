from input_constraints.isla import *


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
        var: Union[Variable, Tuple[Path, DerivationTree]],
        before_var: Union[Variable, Tuple[Path, DerivationTree]]) -> PredicateFormula:
    return PredicateFormula(BEFORE_PREDICATE, var, before_var)


def true():
    return SMTFormula(z3.BoolVal(True))


def false():
    return SMTFormula(z3.BoolVal(False))


def smt_for(formula: z3.BoolRef, *free_variables: Variable) -> SMTFormula:
    return SMTFormula(formula, *free_variables)
