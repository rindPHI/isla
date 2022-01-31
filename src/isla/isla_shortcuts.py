from isla.language import *
from isla.isla_predicates import BEFORE_PREDICATE, COUNT_PREDICATE, LJUST_PREDICATE, LJUST_CROP_PREDICATE, \
    RJUST_CROP_PREDICATE, RJUST_PREDICATE, AFTER_PREDICATE, OCTAL_TO_DEC_PREDICATE, CROP_PREDICATE


def const(bound_variable: BoundVariable, inner_formula: Formula) -> ExistsIntFormula:
    return ExistsIntFormula(bound_variable, inner_formula)


def bexpr(terminal_symbol: str) -> BindExpression:
    return BindExpression(terminal_symbol)


def forall_bind(
        bind_expression: Union[BindExpression, BoundVariable],
        bound_variable: Union[BoundVariable, str],
        in_variable: Union[Variable, DerivationTree],
        inner_formula: Formula) -> ForallFormula:
    return ForallFormula(bound_variable, in_variable, inner_formula, bind_expression)


def exists_bind(
        bind_expression: Union[BindExpression, BoundVariable],
        bound_variable: Union[BoundVariable, str],
        in_variable: Union[Variable, DerivationTree],
        inner_formula: Formula) -> ExistsFormula:
    return ExistsFormula(bound_variable, in_variable, inner_formula, bind_expression)


def forall(
        bound_variable: BoundVariable,
        in_variable: Union[Variable, DerivationTree],
        inner_formula: Formula) -> ForallFormula:
    return ForallFormula(bound_variable, in_variable, inner_formula)


def exists(
        bound_variable: BoundVariable,
        in_variable: Union[Variable, DerivationTree],
        inner_formula: Formula) -> ExistsFormula:
    return ExistsFormula(bound_variable, in_variable, inner_formula)


def before(
        var: Union[Variable, DerivationTree],
        before_var: Union[Variable, DerivationTree]) -> StructuralPredicateFormula:
    return StructuralPredicateFormula(BEFORE_PREDICATE, var, before_var)


def after(
        var: Union[Variable, DerivationTree],
        before_var: Union[Variable, DerivationTree]) -> StructuralPredicateFormula:
    return StructuralPredicateFormula(AFTER_PREDICATE, var, before_var)


def count(
        grammar: Grammar,
        in_tree: Union[Variable, DerivationTree],
        needle: str,
        num: Union[Constant, DerivationTree]) -> SemanticPredicateFormula:
    return SemanticPredicateFormula(COUNT_PREDICATE, in_tree, needle, num)


def crop(
        grammar: Grammar,
        tree: Union[Variable, DerivationTree],
        width: int) -> SemanticPredicateFormula:
    return SemanticPredicateFormula(CROP_PREDICATE, tree, width)


def ljust(
        grammar: Grammar,
        tree: Union[Variable, DerivationTree],
        width: int,
        fillchar: str) -> SemanticPredicateFormula:
    return SemanticPredicateFormula(LJUST_PREDICATE, tree, width, fillchar)


def ljust_crop(
        grammar: Grammar,
        tree: Union[Variable, DerivationTree],
        width: int,
        fillchar: str) -> SemanticPredicateFormula:
    return SemanticPredicateFormula(LJUST_CROP_PREDICATE, tree, width, fillchar)


def rjust(
        grammar: Grammar,
        tree: Union[Variable, DerivationTree],
        width: int,
        fillchar: str) -> SemanticPredicateFormula:
    return SemanticPredicateFormula(RJUST_PREDICATE, tree, width, fillchar)


def rjust_crop(
        grammar: Grammar,
        tree: Union[Variable, DerivationTree],
        width: int,
        fillchar: str) -> SemanticPredicateFormula:
    return SemanticPredicateFormula(RJUST_CROP_PREDICATE, tree, width, fillchar)


def octal_to_decimal(
        grammar: Grammar,
        octal_start: str,
        decimal_start: str,
        octal: Union[Variable, DerivationTree],
        decimal: Union[Variable, DerivationTree]) -> SemanticPredicateFormula:
    return SemanticPredicateFormula(OCTAL_TO_DEC_PREDICATE(grammar, octal_start, decimal_start), octal, decimal)


def true():
    return SMTFormula(z3.BoolVal(True))


def false():
    return SMTFormula(z3.BoolVal(False))


def smt_for(formula: z3.BoolRef, *free_variables: Variable) -> SMTFormula:
    return SMTFormula(formula, *free_variables)
