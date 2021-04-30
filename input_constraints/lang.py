from typing import Union, List, Optional, Iterable, cast, Dict, Tuple

from fuzzingbook.GrammarFuzzer import tree_to_string
from orderedset import OrderedSet
import z3

from input_constraints.helpers import get_subtree, next_path, get_symbols
from input_constraints.type_defs import ParseTree, Path


class Variable:
    def __init__(self, name: str, n_type: str):
        self.name = name
        self.n_type = n_type

    def to_smt(self):
        return z3.String(self.name)

    def __repr__(self):
        return f'{type(self).__name__}("{self.name}", "{self.n_type}")'

    def __str__(self):
        return self.name


class Constant(Variable):
    def __init__(self, name: str, n_type: str):
        """
        A constant is a "free variable" in a formula.

        :param name: The name of the constant.
        :param n_type: The nonterminal type of the constant, e.g., "<var>".
        """
        super().__init__(name, n_type)


class BoundVariable(Variable):
    def __init__(self, name: str, n_type: str):
        """
        A variable bound by a quantifier.

        :param name: The name of the variable.
        :param n_type: The nonterminal type of the variable, e.g., "<var>".
        """
        super().__init__(name, n_type)

    def __add__(self, other: Union[str, 'BoundVariable']) -> 'BindExpression':
        assert type(other) == str or type(other) == BoundVariable
        return BindExpression(self, other)


class BindExpression:
    def __init__(self, *bound_elements: Union[str, BoundVariable]):
        self.bound_elements: List[Union[str, BoundVariable]]
        if bound_elements:
            self.bound_elements = list(bound_elements)
        else:
            self.bound_elements = []

    def __add__(self, other: Union[str, 'BoundVariable']) -> 'BindExpression':
        assert type(other) == str or type(other) == BoundVariable
        result = BindExpression(*self.bound_elements)
        result.bound_elements.append(other)
        return result

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return OrderedSet([var for var in self.bound_elements if type(var) is BoundVariable])

    def match(self, tree: ParseTree) -> Optional[Dict[BoundVariable, ParseTree]]:
        result: Dict[BoundVariable, ParseTree] = {}

        def find(path: Path, elems: List[BoundVariable]) -> bool:
            if not elems:
                return True

            node, children = get_subtree(path, tree)
            if node == elems[0].n_type:
                result[elems[0]] = (node, children)

                if len(elems) == 1:
                    return True

                next_p = next_path(path, tree)
                if next_p is None:
                    return False

                return find(next_p, elems[1:])
            else:
                if not children:
                    next_p = next_path(path, tree)
                    if next_p is None:
                        return False
                    return find(next_p, elems)
                else:
                    return find(path + (0,), elems)

        success = find(tuple(), [elem for elem in self.bound_elements if type(elem) is BoundVariable])
        if success:
            return result
        else:
            return None

    def __repr__(self):
        return f'BindExpression({", ".join(map(repr, self.bound_elements))})'

    def __str__(self):
        return ' '.join(map(lambda e: f'"{e}"' if type(e) is str else str(e), self.bound_elements))


class Formula:
    def bound_variables(self) -> OrderedSet[BoundVariable]:
        pass

    def free_variables(self) -> OrderedSet[Variable]:
        pass

    def __and__(self, other):
        return ConjunctiveFormula(self, other)

    def __or__(self, other):
        return DisjunctiveFormula(self, other)

    def __neg__(self):
        return NegatedFormula(self)


class PropositionalCombinator(Formula):
    def __init__(self, *args: Formula):
        self.args = list(args)

    def free_variables(self) -> OrderedSet[Variable]:
        result: OrderedSet[Variable] = OrderedSet([])
        for arg in self.args:
            result |= arg.free_variables()
        return result

    def __repr__(self):
        return f"{type(self).__name__}({', '.join(map(repr, self.args))})"


class NegatedFormula(PropositionalCombinator):
    def __init__(self, arg: Formula):
        super().__init__(arg)

    def __str__(self):
        return f"¬({self.args[0]})"


class ConjunctiveFormula(PropositionalCombinator):
    def __init__(self, *args: Formula):
        if len(args) < 2:
            raise RuntimeError(f"Conjunction needs at least two arguments, {len(args)} given.")
        super().__init__(*args)

    def __str__(self):
        return f"({' ∧ '.join(map(str, self.args))})"


class DisjunctiveFormula(PropositionalCombinator):
    def __init__(self, *args: Formula):
        if len(args) < 2:
            raise RuntimeError(f"Disjunction needs at least two arguments, {len(args)} given.")
        super().__init__(*args)

    def __str__(self):
        return f"({' ∨ '.join(map(str, self.args))})"


class SMTFormula(Formula):
    def __init__(self, formula: z3.BoolRef, *free_variables: Variable):
        """
        Encapsulates an SMT formula.
        :param formula: The SMT formula.
        :param free_variables: Free varialbes in this formula.
        """

        actual_symbols = get_symbols(formula)
        if len(free_variables) != len(actual_symbols):
            raise RuntimeError(f"Supplied number of {len(free_variables)} symbols does not match "
                               f"actual number of symbols {len(actual_symbols)} in formula '{formula}'")

        self.formula = formula
        self.free_variables_ = OrderedSet(free_variables)

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return OrderedSet([])

    def free_variables(self) -> OrderedSet[Variable]:
        return self.free_variables_

    def __repr__(self):
        return f"SMTFormula({repr(self.formula)}, {', '.join(map(repr, self.free_variables_))})"

    def __str__(self):
        return str(self.formula)


class QuantifiedFormula(Formula):
    def __init__(self,
                 bound_variable: BoundVariable,
                 in_variable: Variable,
                 inner_formula: Formula,
                 bind_expression: Optional[BindExpression] = None):
        self.bound_variable = bound_variable
        self.in_variable = in_variable
        self.inner_formula = inner_formula
        self.bind_expression = bind_expression

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return OrderedSet([self.bound_variable]) | \
               (OrderedSet([]) if self.bind_expression is None else self.bind_expression.bound_variables())

    def free_variables(self) -> OrderedSet[Variable]:
        return (OrderedSet([self.in_variable]) | self.inner_formula.free_variables()) - self.bound_variables()

    def __repr__(self):
        return f'{type(self).__name__}({repr(self.bound_variable)}, {repr(self.in_variable)}, ' \
               f'{repr(self.inner_formula)}{"" if self.bind_expression is None else ", " + repr(self.bind_expression)})'


class ForallFormula(QuantifiedFormula):
    def __init__(self,
                 bound_variable: BoundVariable,
                 in_variable: Variable,
                 inner_formula: Formula,
                 bind_expression: Optional[BindExpression] = None):
        super().__init__(bound_variable, in_variable, inner_formula, bind_expression)

    def __str__(self):
        quote = "'"
        return f'∀ {"" if not self.bind_expression else quote + str(self.bind_expression) + quote + " = "}' \
               f'{str(self.bound_variable)} ∈ {str(self.in_variable)}: ({str(self.inner_formula)})'


class ExistsFormula(QuantifiedFormula):
    def __init__(self,
                 bound_variable: BoundVariable,
                 in_variable: Variable,
                 inner_formula: Formula,
                 bind_expression: Optional[BindExpression] = None):
        super().__init__(bound_variable, in_variable, inner_formula, bind_expression)

    def __str__(self):
        quote = "'"
        return f'∃ {"" if not self.bind_expression else quote + str(self.bind_expression) + quote + " = "}' \
               f'{str(self.bound_variable)} ∈ {str(self.in_variable)}: ({str(self.inner_formula)})'


class ExistsBeforeFormula(ExistsFormula):
    def __init__(self, bound_variable: BoundVariable, before_variable: BoundVariable, in_variable: Variable,
                 inner_formula: Formula, bind_expression: Optional[BindExpression] = None):
        super().__init__(bound_variable, in_variable, inner_formula, bind_expression)
        self.before_variable = before_variable

    def free_variables(self) -> OrderedSet[Variable]:
        return (OrderedSet([self.in_variable, self.before_variable]) |
                self.inner_formula.free_variables()) - self.bound_variables()

    def __repr__(self):
        return f'{type(self).__name__}({repr(self.bound_variable)}, {repr(self.before_variable)}, ' \
               f'{repr(self.in_variable)}, ' \
               f'{repr(self.inner_formula)}{"" if self.bind_expression is None else ", " + repr(self.bind_expression)})'

    def __str__(self):
        quote = "'"
        return f'∃ {"" if not self.bind_expression else quote + str(self.bind_expression) + quote + " = "}' \
               f'{str(self.bound_variable)} before {str(self.before_variable)} ∈ {str(self.in_variable)}: ' \
               f'({str(self.inner_formula)})'


def well_formed(formula: Formula,
                bound_vars: Optional[OrderedSet[BoundVariable]] = None,
                bound_constants: Optional[OrderedSet[Constant]] = None,
                bound_by_smt: Optional[OrderedSet[Variable]] = None) -> bool:
    if bound_vars is None:
        bound_vars = OrderedSet([])
    if bound_constants is None:
        bound_constants = OrderedSet([])
    if bound_by_smt is None:
        bound_by_smt = OrderedSet([])
    t = type(formula)

    if issubclass(t, QuantifiedFormula):
        formula: QuantifiedFormula
        if formula.in_variable in bound_by_smt:
            return False
        if formula.bound_variables().intersection(bound_vars):
            return False
        if type(formula.in_variable) is BoundVariable and formula.in_variable not in bound_vars:
            return False
        if any(free_var not in bound_vars for free_var in formula.free_variables() if type(free_var) is BoundVariable):
            return False

        if type(t) is ExistsBeforeFormula and cast(ExistsBeforeFormula, formula).before_variable not in bound_vars:
            return False

        return well_formed(
            formula.inner_formula,
            bound_vars | formula.bound_variables(),
            bound_constants
            if type(formula.in_variable) is BoundVariable
            else bound_constants | OrderedSet([formula.in_variable]),
            bound_by_smt
        )
    elif t is SMTFormula:
        if any(free_var in bound_constants for free_var in formula.free_variables()):
            return False

        return not any(free_var not in bound_vars
                       for free_var in formula.free_variables()
                       if type(free_var) is BoundVariable)
    elif issubclass(t, PropositionalCombinator):
        formula: PropositionalCombinator

        if t is ConjunctiveFormula:
            smt_formulas = [f for f in formula.args if type(f) is SMTFormula]
            other_formulas = [f for f in formula.args if type(f) is not SMTFormula]

            if any(not well_formed(f, bound_vars, bound_constants, bound_by_smt) for f in smt_formulas):
                return False

            for smt_formula in smt_formulas:
                bound_vars |= [var for var in smt_formula.free_variables() if type(var) is BoundVariable]
                bound_by_smt |= smt_formula.free_variables()

            return all(well_formed(f, bound_vars, bound_constants, bound_by_smt) for f in other_formulas)
        else:
            return all(well_formed(subformula, bound_vars, bound_constants, bound_by_smt)
                       for subformula in formula.args)

    else:
        raise NotImplementedError()


def evaluate(formula: Formula, assignments: Dict[Variable, ParseTree]) -> bool:
    assert well_formed(formula)

    t = type(formula)

    if t is SMTFormula:
        instantiation = z3.substitute(
            formula,
            *tuple({z3.String(symbol.name): z3.StringVal(tree_to_string(symbol_assignment))
                    for symbol, symbol_assignment
                    in assignments.items()}.items()))

        z3.set_param("smt.string_solver", "z3str3")
        solver = z3.Solver()
        solver.add(instantiation)
        return solver.check() == z3.sat  # Set timeout?
    elif t is ForallFormula:
        raise NotImplementedError()  # TODO
    elif t is ExistsFormula:
        raise NotImplementedError()  # TODO
    elif t is ExistsBeforeFormula:
        raise NotImplementedError()  # TODO
    elif t is NegatedFormula:
        raise NotImplementedError()  # TODO
    elif t is ConjunctiveFormula:
        raise NotImplementedError()  # TODO
    elif t is DisjunctiveFormula:
        raise NotImplementedError()  # TODO
    else:
        raise NotImplementedError()
