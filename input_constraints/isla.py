import copy
from typing import Union, List, Optional, Dict, Tuple, Callable

import z3
from fuzzingbook.GrammarFuzzer import tree_to_string
from orderedset import OrderedSet

from input_constraints.helpers import get_subtree, next_path, get_symbols, traverse_tree, is_before, TreeExpander, \
    tree_depth
from input_constraints.type_defs import ParseTree, Path, Grammar


class Variable:
    def __init__(self, name: str, n_type: str):
        self.name = name
        self.n_type = n_type

    def to_smt(self):
        return z3.String(self.name)

    def __eq__(self, other):
        return type(self) is type(other) and (self.name, self.n_type) == (other.name, other.n_type)

    def __hash__(self):
        return hash((type(self).__name__, self.name, self.n_type))

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

    def to_tree_prefix(self, in_nonterminal: str, grammar: Grammar, max_depth=4) -> \
            Tuple[ParseTree, Dict[BoundVariable, Path]]:
        # TODO: Possible optimization which would also allow to check deeper nestings within
        #       reasonable time: Check whether a candidate cannot possibly match. This is the case,
        #       e.g., if the first path is concrete and the first bound variable (non)terminal does
        #       not occur along that path, and similarly for all subsequent paths and variables.

        queue: List[ParseTree] = [(in_nonterminal, None)]
        expander = TreeExpander(grammar)
        while queue:
            expanded = expander.expand_tree_once(queue.pop())

            for tree in expanded:
                if (match_res := self.match(tree)) is not None:
                    match_res: Dict[BoundVariable, Tuple[Path, ParseTree]]
                    return tree, {bv: match_res[bv][0] for bv in match_res}

            queue.extend([tree for tree in expanded if tree_depth(tree) < max_depth])

        assert False, f"Bind expression {str(self)} does does not match with grammar, " \
                      f"or does not occur under scope of nonterminal {in_nonterminal}, " \
                      f"or requires max_depth > {max_depth}"

    def match(self, tree: ParseTree) -> Optional[Dict[BoundVariable, Tuple[Path, ParseTree]]]:
        result: Dict[BoundVariable, Tuple[Path, ParseTree]] = {}

        def find(path: Path, elems: List[BoundVariable]) -> bool:
            if not elems:
                return True if next_path(path, tree) is None else False

            node, children = get_subtree(path, tree)
            if node == elems[0].n_type:
                result[elems[0]] = path, (node, children)

                if len(elems) == 1:
                    return True if next_path(path, tree) is None else False

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
        return result if success else None

    def __repr__(self):
        return f'BindExpression({", ".join(map(repr, self.bound_elements))})'

    def __str__(self):
        return ' '.join(map(lambda e: f'"{e}"' if type(e) is str else str(e), self.bound_elements))


class FormulaVisitor:
    def visit_predicate_formula(self, formula: 'PredicateFormula'):
        pass

    def visit_negated_formula(self, formula: 'NegatedFormula'):
        pass

    def visit_conjunctive_formula(self, formula: 'ConjunctiveFormula'):
        pass

    def visit_disjunctive_formula(self, formula: 'DisjunctiveFormula'):
        pass

    def visit_smt_formula(self, formula: 'SMTFormula'):
        pass

    def visit_exists_formula(self, formula: 'ExistsFormula'):
        pass

    def visit_forall_formula(self, formula: 'ForallFormula'):
        pass


class Formula:
    def bound_variables(self) -> OrderedSet[BoundVariable]:
        """Non-recursive: Only non-empty for quantified formulas"""
        pass

    def free_variables(self) -> OrderedSet[Variable]:
        """Recursive."""
        pass

    def __and__(self, other):
        return ConjunctiveFormula(self, other)

    def __or__(self, other):
        return DisjunctiveFormula(self, other)

    def __neg__(self):
        return NegatedFormula(self)

    def accept(self, visitor: FormulaVisitor):
        raise NotImplementedError()


class Predicate:
    def __init__(self, name: str, arity: int, eval_fun: Callable[..., bool]):
        self.name = name
        self.arity = arity
        self.eval_fun = eval_fun

    def evaluate(self, *instantiations: Tuple[Path, ParseTree]):
        return self.eval_fun(*instantiations)

    def __eq__(self, other):
        return type(other) is Predicate and (self.name, self.arity) == (other.name, other.arity)

    def __repr__(self):
        return f"Predicate({self.name}, {self.arity})"

    def __str__(self):
        return self.name


BEFORE_PREDICATE = Predicate(
    "before", 2, lambda tree, before_tree: is_before(tree[0], before_tree[0])
)


class PredicateFormula(Formula):
    def __init__(self, predicate: Predicate, *args: Variable):
        assert len(args) == predicate.arity
        self.predicate = predicate
        self.args: List[Variable] = list(args)

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return OrderedSet([])

    def free_variables(self) -> OrderedSet[Variable]:
        return OrderedSet(self.args)

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_predicate_formula(self)

    def __str__(self):
        return f"{self.predicate}({', '.join(map(str, self.args))})"

    def __repr__(self):
        return f'PredicateFormula({repr(self.predicate), ", ".join(map(repr, self.args))})'


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

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_negated_formula(self)
        for formula in self.args:
            formula.accept(visitor)

    def __str__(self):
        return f"¬({self.args[0]})"


class ConjunctiveFormula(PropositionalCombinator):
    def __init__(self, *args: Formula):
        if len(args) < 2:
            raise RuntimeError(f"Conjunction needs at least two arguments, {len(args)} given.")
        super().__init__(*args)

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_conjunctive_formula(self)
        for formula in self.args:
            formula.accept(visitor)

    def __str__(self):
        return f"({' ∧ '.join(map(str, self.args))})"


class DisjunctiveFormula(PropositionalCombinator):
    def __init__(self, *args: Formula):
        if len(args) < 2:
            raise RuntimeError(f"Disjunction needs at least two arguments, {len(args)} given.")
        super().__init__(*args)

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_disjunctive_formula(self)
        for formula in self.args:
            formula.accept(visitor)

    def __str__(self):
        return f"({' ∨ '.join(map(str, self.args))})"


class SMTFormula(Formula):
    def __init__(self, formula: z3.BoolRef, *free_variables: Variable):
        """
        Encapsulates an SMT formula.
        :param formula: The SMT formula.
        :param free_variables: Free variables in this formula.
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

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_smt_formula(self)

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

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_forall_formula(self)
        self.inner_formula.accept(visitor)

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

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_exists_formula(self)
        self.inner_formula.accept(visitor)

    def __str__(self):
        quote = "'"
        return f'∃ {"" if not self.bind_expression else quote + str(self.bind_expression) + quote + " = "}' \
               f'{str(self.bound_variable)} ∈ {str(self.in_variable)}: ({str(self.inner_formula)})'


class VariablesCollector(FormulaVisitor):
    def __init__(self, formula: Formula):
        self.formula = formula
        self.result: Optional[OrderedSet[Variable]] = None

    def collect(self) -> OrderedSet[Variable]:
        if self.result is not None:
            return self.result

        self.result = OrderedSet([])
        self.formula.accept(self)
        return self.result

    def visit_exists_formula(self, formula: ExistsFormula):
        self.visit_quantified_formula(formula)

    def visit_forall_formula(self, formula: ForallFormula):
        self.visit_quantified_formula(formula)

    def visit_quantified_formula(self, formula: QuantifiedFormula):
        self.result.add(formula.in_variable)
        self.result.add(formula.bound_variable)
        if formula.bind_expression is not None:
            self.result.update(formula.bind_expression.bound_variables())

    def visit_predicate_formula(self, formula: PredicateFormula):
        self.result.update(formula.args)

    def visit_smt_formula(self, formula: SMTFormula):
        self.result.update(formula.free_variables())


def well_formed(formula: Formula,
                bound_vars: Optional[OrderedSet[BoundVariable]] = None,
                in_expr_vars: Optional[OrderedSet[Variable]] = None,
                bound_by_smt: Optional[OrderedSet[Variable]] = None) -> bool:
    if bound_vars is None:
        bound_vars = OrderedSet([])
    if in_expr_vars is None:
        in_expr_vars = OrderedSet([])
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

        return well_formed(
            formula.inner_formula,
            bound_vars | formula.bound_variables(),
            in_expr_vars | OrderedSet([formula.in_variable]),
            bound_by_smt
        )
    elif t is SMTFormula:
        if any(free_var in in_expr_vars for free_var in formula.free_variables()):
            return False

        return not any(free_var not in bound_vars
                       for free_var in formula.free_variables()
                       if type(free_var) is BoundVariable)
    elif issubclass(t, PropositionalCombinator):
        formula: PropositionalCombinator

        if t is ConjunctiveFormula:
            smt_formulas = [f for f in formula.args if type(f) is SMTFormula]
            other_formulas = [f for f in formula.args if type(f) is not SMTFormula]

            if any(not well_formed(f, bound_vars, in_expr_vars, bound_by_smt) for f in smt_formulas):
                return False

            for smt_formula in smt_formulas:
                bound_vars |= [var for var in smt_formula.free_variables() if type(var) is BoundVariable]
                bound_by_smt |= smt_formula.free_variables()

            return all(well_formed(f, bound_vars, in_expr_vars, bound_by_smt) for f in other_formulas)
        else:
            return all(well_formed(subformula, bound_vars, in_expr_vars, bound_by_smt)
                       for subformula in formula.args)
    elif t is PredicateFormula:
        return all(free_var in bound_vars
                   for free_var in formula.free_variables()
                   if type(free_var) is BoundVariable)
    else:
        raise NotImplementedError()


def evaluate(formula: Formula, assignments: Dict[Variable, Tuple[Path, ParseTree]]) -> bool:
    assert well_formed(formula)

    def evaluate_(formula: Formula, assignments: Dict[Variable, Tuple[Path, ParseTree]]) -> bool:
        q = '"'
        t = type(formula)

        if t is SMTFormula:
            formula: SMTFormula
            instantiation = z3.substitute(
                formula.formula,
                *tuple({z3.String(symbol.name): z3.StringVal(tree_to_string(symbol_assignment[1]))
                        for symbol, symbol_assignment
                        in assignments.items()}.items()))

            z3.set_param("smt.string_solver", "z3str3")
            solver = z3.Solver()
            solver.add(instantiation)
            return solver.check() == z3.sat  # Set timeout?
        elif issubclass(t, QuantifiedFormula):
            formula: QuantifiedFormula
            assert formula.in_variable in assignments
            in_inst: ParseTree = assignments[formula.in_variable][1]
            qfd_var: BoundVariable = formula.bound_variable
            bind_expr: Optional[BindExpression] = formula.bind_expression

            new_assignments: List[Dict[Variable, Tuple[Path, ParseTree]]] = []

            def search_action(path: Path, tree: ParseTree) -> None:
                nonlocal new_assignments
                node, children = tree
                if node == qfd_var.n_type:
                    if bind_expr is not None:
                        maybe_match: Optional[Dict[BoundVariable, Tuple[Path, ParseTree]]] = bind_expr.match(tree)
                        if maybe_match is not None:
                            new_assignment = copy.copy(assignments)
                            new_assignment[qfd_var] = path, tree
                            new_assignment.update(maybe_match)
                            new_assignments.append(new_assignment)
                    else:
                        new_assignment = copy.copy(assignments)
                        new_assignment[qfd_var] = path, tree
                        new_assignments.append(new_assignment)

            traverse_tree(in_inst, search_action)

            if t is ForallFormula:
                formula: ForallFormula
                return all(evaluate_(formula.inner_formula, new_assignment) for new_assignment in new_assignments)
            elif t is ExistsFormula:
                formula: ExistsFormula
                return any(evaluate_(formula.inner_formula, new_assignment) for new_assignment in new_assignments)
        elif t is PredicateFormula:
            formula: PredicateFormula
            arg_insts = [assignments[arg] for arg in formula.args]
            return formula.predicate.evaluate(*arg_insts)
        elif t is NegatedFormula:
            formula: NegatedFormula
            return not evaluate_(formula.args[0], assignments)
        elif t is ConjunctiveFormula:
            formula: ConjunctiveFormula
            return all(evaluate_(sub_formula, assignments) for sub_formula in formula.args)
        elif t is DisjunctiveFormula:
            formula: DisjunctiveFormula
            return any(evaluate_(sub_formula, assignments) for sub_formula in formula.args)
        else:
            raise NotImplementedError()

    return evaluate_(formula, assignments)
