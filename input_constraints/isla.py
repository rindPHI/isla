import copy
import logging
import random
from functools import reduce
from typing import Union, List, Optional, Dict, Tuple, Callable, cast, Generator

import sys
import z3
from fuzzingbook.GrammarFuzzer import tree_to_string, GrammarFuzzer
from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import EarleyParser
from grammar_graph.gg import GrammarGraph
from orderedset import OrderedSet

from input_constraints.helpers import get_subtree, next_path, get_symbols, traverse_tree, is_before, visit_z3_expr, \
    is_z3_var, z3_subst, path_iterator, replace_tree_path
from input_constraints.type_defs import ParseTree, Path, Grammar, AbstractTree

SolutionState = List[Tuple['Constant', 'Formula', AbstractTree]]
Assignment = Tuple['Constant', 'Formula', AbstractTree]

isla_logger = logging.getLogger("isla")


class Variable:
    def __init__(self, name: str, n_type: str):
        self.name = name
        self.n_type = n_type

    def to_smt(self):
        return z3.String(self.name)

    def __eq__(self, other):
        return type(self) is type(other) and (self.name, self.n_type) == (other.name, other.n_type)

    # Comparisons (<, <=, >, >=) implemented s.t. variables can be used, e.g., in priority lists
    def __lt__(self, other):
        return self.name < other.name

    def __le__(self, other):
        return self.name <= other.name

    def __gt__(self, other):
        assert issubclass(type(other), Variable)
        return self.name > other.name

    def __ge__(self, other):
        return self.name >= other.name

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


class DerivationTree:
    def __init__(self, value: Union[str, Variable],
                 children: Optional[List['DerivationTree']] = None,
                 id: Optional[int] = None):
        assert isinstance(value, str) or isinstance(value, Variable)
        assert not isinstance(value, Variable) or not children
        assert children is None or all(isinstance(child, DerivationTree) for child in children)

        self.value = value
        self.children = children
        self.id = id if id is not None else random.randint(0, sys.maxsize)

    def add_child(self, child: 'DerivationTree'):
        self.children.append(child)

    def root_nonterminal(self) -> str:
        if isinstance(self.value, Variable):
            return self.value.n_type

        assert is_nonterminal(self.value)
        return self.value

    def num_children(self) -> int:
        return 0 if self.children is None else len(self.children)

    def is_abstract(self):
        return isinstance(self.value, Variable) or (self.children is not None
                                                    and any(child.is_abstract() for child in self.children))

    def is_open(self):
        return self.children is None or any(child.is_open() for child in self.children)

    def get_subtree(self, path: Path) -> 'DerivationTree':
        """Access a subtree based on `path` (a list of children numbers)"""
        if not path:
            return self

        return self.children[path[0]].get_subtree(path[1:])

    def path_iterator(self, path: Path = ()) -> Generator[Tuple[Path, 'DerivationTree'], None, None]:
        yield path, self
        if self.children is not None:
            for i, child in enumerate(self.children):
                yield from child.path_iterator(path + (i,))

    def find_node(self, node_or_id: Union['DerivationTree', int]) -> Optional[Path]:
        """Finds a node by its (assumed unique) ID. Returns the path relative to this node."""

        if isinstance(node_or_id, DerivationTree):
            node_or_id = node_or_id.id

        for path, node in self.path_iterator():
            if node.id == node_or_id:
                return path

        return None

    def traverse(self, action: Callable[[Path, 'DerivationTree'], None]) -> None:
        for path, subtree in self.path_iterator():
            action(path, subtree)

    def next_path(self, path: Path, skip_children=False) -> Optional[Path]:
        """
        Returns the next path in the tree. Repeated calls result in an iterator over the paths in the tree.
        """

        def num_children(path: Path) -> int:
            _, children = self.get_subtree(path)
            if children is None:
                return 0
            return len(children)

        # Descent towards left-most child leaf
        if not skip_children and num_children(path) > 0:
            return path + (0,)

        # Find next sibling
        for i in range(1, len(path)):
            if path[-i] + 1 < num_children(path[:-i]):
                return path[:-i] + (path[-i] + 1,)

        # Proceed to next root child
        if path[0] + 1 < num_children(tuple()):
            return path[0] + 1,

        # path already is the last path.
        assert skip_children or list(self.path_iterator())[-1][0] == path
        return None

    def replace_path(self, path: Path, replacement_tree: 'DerivationTree') -> 'DerivationTree':
        """Returns tree where replacement_tree has been inserted at `path` instead of the original subtree"""
        node, children = self
        assert isinstance(replacement_tree, DerivationTree)

        if not path:
            return replacement_tree

        head = path[0]
        new_children = (children[:head] +
                        [children[head].replace_path(path[1:], replacement_tree)] +
                        children[head + 1:])

        return DerivationTree(node, new_children, id=self.id)

    def open_concrete_leaves(self) -> Generator[Tuple[Path, 'DerivationTree'], None, None]:
        return ((path, sub_tree)
                for path, sub_tree in self.path_iterator()
                if sub_tree.children is None and not sub_tree.is_abstract())

    def tree_variables(self) -> Generator[Variable, None, None]:
        return (sub_tree.value
                for _, sub_tree in self.path_iterator()
                if isinstance(sub_tree.value, Variable))

    def substitute_variables(self, subst_map: Dict[Variable, 'DerivationTree']) -> 'DerivationTree':
        value, children = self
        if children is None:
            if isinstance(value, Variable) and value in subst_map:
                return subst_map[value]
            else:
                return self

        return DerivationTree(
            value,
            [child.substitute_variables_in_tree(subst_map) for child in children],
            id=self.id)

    @staticmethod
    def from_parse_tree(tree: ParseTree):
        node, children = tree
        return DerivationTree(node,
                              None if children is None
                              else [DerivationTree.from_parse_tree(child) for child in children])

    def to_parse_tree(self) -> ParseTree:
        assert not self.is_abstract()
        return self.value, None if self.children is None else [child.to_parse_tree() for child in self.children]

    def __iter__(self):
        # Allows tuple unpacking: node, children = tree
        yield self.value
        yield self.children

    def __repr__(self):
        return f"DerivationTreeNode({repr(self.value)}, {repr(self.children)})"

    def __hash__(self):
        if self.children is None:
            return hash((self.value, None))

        return hash((self.value,) + tuple(self.children))

    def __eq__(self, other):
        return (isinstance(other, DerivationTree)
                and self.value == other.value
                and self.children == other.children)

    def to_string(self, show_open_leaves: bool = False):
        value, children = self
        if children:
            return ''.join(c.to_string(show_open_leaves) for c in children)
        else:
            if isinstance(value, Variable):
                return value.name

            return value if show_open_leaves or not is_nonterminal(value) else ""

    def __str__(self) -> str:
        return self.to_string(show_open_leaves=True)


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

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return BindExpression(*[elem if elem not in subst_map else subst_map[elem]
                                for elem in self.bound_elements])

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return OrderedSet([var for var in self.bound_elements if type(var) is BoundVariable])

    def to_tree_prefix(self, in_nonterminal: str, grammar: Grammar, to_abstract_tree: bool = True) -> \
            Tuple[DerivationTree, Dict[BoundVariable, Path]]:
        fuzzer = GrammarFuzzer(grammar)

        placeholder_map: Dict[Union[str, BoundVariable], str] = {}
        tree_placeholder_map: Dict[Union[str, BoundVariable], ParseTree] = {}

        for bound_element in self.bound_elements:
            if isinstance(bound_element, str):
                placeholder_map[bound_element] = bound_element
            elif not is_nonterminal(bound_element.n_type):
                placeholder_map[bound_element] = bound_element.n_type
            else:
                ph_candidate = None
                while ph_candidate is None or ph_candidate in tree_placeholder_map.values():
                    ph_candidate = fuzzer.expand_tree((bound_element.n_type, None))

                placeholder_map[bound_element] = tree_to_string(ph_candidate)
                tree_placeholder_map[bound_element] = ph_candidate

        inp = "".join(list(map(lambda elem: placeholder_map[elem], self.bound_elements)))

        graph = GrammarGraph.from_grammar(grammar)
        subgrammar = graph.subgraph(graph.get_node(in_nonterminal)).to_grammar()
        parser = EarleyParser(subgrammar)
        tree = list(parser.parse(inp))[0][1][0]

        positions: Dict[BoundVariable, Path] = {}
        bound_elements = copy.deepcopy(self.bound_elements)
        for path, subtree in path_iterator(tree):
            if not bound_elements:
                break

            if isinstance(bound_elements[0], str):
                if tree_to_string(subtree) == bound_elements[0]:
                    bound_elements = bound_elements[1:]
                continue

            if is_nonterminal(bound_elements[0].n_type):
                if subtree == tree_placeholder_map[bound_elements[0]]:
                    positions[bound_elements[0]] = path
                    tree = replace_tree_path(tree, path, (bound_elements[0] if to_abstract_tree
                                                          else bound_elements[0].n_type,
                                                          None))
                    bound_elements = bound_elements[1:]
                continue

            if tree_to_string(subtree) == bound_elements[0].n_type:
                positions[bound_elements[0]] = path
                tree = replace_tree_path(tree, path, ((bound_elements[0], None) if to_abstract_tree
                                                      else (bound_elements[0].n_type, [])))
                bound_elements = bound_elements[1:]

        assert not bound_elements

        return DerivationTree.from_parse_tree(tree), positions

    def match(self, tree: DerivationTree) -> Optional[Dict[BoundVariable, Tuple[Path, DerivationTree]]]:
        result: Dict[BoundVariable, Tuple[Path, DerivationTree]] = {}

        def find(path: Path, elems: List[BoundVariable]) -> bool:
            if not elems:
                return True if tree.next_path(path) is None else False

            subtree = tree.get_subtree(path)
            node, children = subtree
            if node == elems[0].n_type:
                result[elems[0]] = path, subtree

                if len(elems) == 1:
                    return True if tree.next_path(path, skip_children=True) is None else False

                next_p = tree.next_path(path, skip_children=True)
                if next_p is None:
                    return False

                return find(next_p, elems[1:])
            else:
                if not children:
                    next_p = tree.next_path(path, skip_children=True)
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

    def __hash__(self):
        return hash(self.bound_elements)

    def __eq__(self, other):
        return self.bound_elements == other.bound_elements


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

    def substitute_variables(self, subst_map: Dict[Variable, Variable]) -> 'Formula':
        pass

    def substitute_expressions(self, subst_map: Dict[Variable, Tuple[Path, DerivationTree]]) -> 'Formula':
        pass

    def __and__(self, other):
        if self == other:
            return self

        if isinstance(self, SMTFormula) and z3.is_false(self.formula):
            return self

        if isinstance(other, SMTFormula) and z3.is_false(other.formula):
            return other

        if isinstance(self, SMTFormula) and z3.is_true(self.formula):
            return other

        if isinstance(other, SMTFormula) and z3.is_true(other.formula):
            return self

        return ConjunctiveFormula(self, other)

    def __or__(self, other):
        if self == other:
            return self

        if isinstance(self, SMTFormula) and z3.is_true(self.formula):
            return self

        if isinstance(other, SMTFormula) and z3.is_true(other.formula):
            return other

        if isinstance(self, SMTFormula) and z3.is_false(self.formula):
            return other

        if isinstance(other, SMTFormula) and z3.is_false(other.formula):
            return self

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

    def hash(self):
        return hash((self.name, self.arity))

    def __repr__(self):
        return f"Predicate({self.name}, {self.arity})"

    def __str__(self):
        return self.name


BEFORE_PREDICATE = Predicate(
    "before", 2, lambda inst_1, inst_2: is_before(inst_1[0], inst_2[0])
)


class PredicateFormula(Formula):
    def __init__(self, predicate: Predicate, *args: Union[Variable, Tuple[Path, DerivationTree]]):
        assert len(args) == predicate.arity
        self.predicate = predicate
        self.args: List[Union[Variable, Tuple[Path, DerivationTree]]] = list(args)

    def evaluate(self):
        if any(isinstance(arg, Variable) for arg in self.args):
            raise RuntimeError(f"Cannot evaluate predicate with partially instantiated arguments "
                               f"{self.args}")

        return self.predicate.eval_fun(*self.args)

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return PredicateFormula(self.predicate,
                                *[arg if not isinstance(arg, Variable) or arg not in subst_map
                                  else subst_map[arg] for arg in self.args])

    def substitute_expressions(self, subst_map: Dict[Variable, Tuple[Path, DerivationTree]]) -> Formula:
        new_args = []
        for arg in self.args:
            if isinstance(arg, Variable):
                if arg in subst_map:
                    new_args.append(subst_map[arg])
                else:
                    new_args.append(arg)
                continue

            path, tree = arg[0], arg[1]
            new_args.append((arg[0], tree.substitute_variables({k: v[1] for k, v in subst_map.items()})))

        return PredicateFormula(self.predicate, *new_args)

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return OrderedSet([])

    def free_variables(self) -> OrderedSet[Variable]:
        result = OrderedSet([])
        result.update([arg for arg in self.args if isinstance(arg, Variable)])
        vars_in_concrete_args = [v for arg in self.args if isinstance(arg, tuple) for v in tree_variables(arg[1])]
        result.update(vars_in_concrete_args)
        return result

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_predicate_formula(self)

    def __hash__(self):
        return hash((self.predicate, self.args))

    def __eq__(self, other):
        return type(self) is type(other) and (self.predicate, self.args) == (other.predicate, other.args)

    def __str__(self):
        arg_strings = []
        for arg in self.args:
            if isinstance(arg, Variable):
                arg_strings.append(str(arg))
            else:
                path, tree = arg
                arg_strings.append(f"({path}, {tree})")

        return f"{self.predicate}({', '.join(arg_strings)})"

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

    def __hash__(self):
        return hash(self.args)

    def __eq__(self, other):
        return type(self) == type(other) and self.args == other.args


class NegatedFormula(PropositionalCombinator):
    def __init__(self, arg: Formula):
        super().__init__(arg)

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_negated_formula(self)
        for formula in self.args:
            formula.accept(visitor)

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return NegatedFormula(*[arg.substitute_variables(subst_map) for arg in self.args])

    def substitute_expressions(self, subst_map: Dict[Variable, Tuple[Path, DerivationTree]]) -> Formula:
        return NegatedFormula(*[arg.substitute_expressions(subst_map) for arg in self.args])

    def __str__(self):
        return f"¬({self.args[0]})"


class ConjunctiveFormula(PropositionalCombinator):
    def __init__(self, *args: Formula):
        if len(args) < 2:
            raise RuntimeError(f"Conjunction needs at least two arguments, {len(args)} given.")
        super().__init__(*args)

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return reduce(lambda a, b: a & b, [arg.substitute_variables(subst_map) for arg in self.args])

    def substitute_expressions(self, subst_map: Dict[Variable, Tuple[Path, DerivationTree]]) -> Formula:
        return reduce(lambda a, b: a & b, [arg.substitute_expressions(subst_map) for arg in self.args])

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

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return reduce(lambda a, b: a | b, [arg.substitute_variables(subst_map) for arg in self.args])

    def substitute_expressions(self, subst_map: Dict[Variable, Tuple[Path, DerivationTree]]) -> Formula:
        return reduce(lambda a, b: a | b, [arg.substitute_expressions(subst_map) for arg in self.args])

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

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        new_smt_formula = z3_subst(self.formula, {v1.to_smt(): v2.to_smt() for v1, v2 in subst_map.items()})

        return SMTFormula(cast(z3.BoolRef, new_smt_formula),
                          *[variable if variable not in subst_map else subst_map[variable]
                            for variable in self.free_variables_])

    def substitute_expressions(self, subst_map: Dict[Variable, Tuple[Path, DerivationTree]]) -> Formula:
        subst_map = {k: v for k, v in subst_map.items() if k in self.free_variables_}

        new_free_variables = OrderedSet([variable for variable in self.free_variables_
                                         if variable not in subst_map])

        for key, (path, tree) in subst_map.items():
            if isinstance(tree, DerivationTree) and tree.children is None and tree.is_abstract():
                subst_map[key] = path, tree.value
                new_free_variables.add(tree.value)
                continue

            if isinstance(tree, Variable):
                assert False  # Why should it be a Variable???
                new_free_variables.add(tree)
                continue

            assert not tree.is_abstract()
            subst_map[key] = path, str(tree)

        assert all(isinstance(rhs, str) or isinstance(rhs, Variable) for _, rhs in subst_map.values())

        new_smt_formula = z3_subst(self.formula, {
            variable.to_smt():
                var_or_str.to_smt() if isinstance(var_or_str, Variable)
                else z3.StringVal(var_or_str)
            for variable, (_, var_or_str) in subst_map.items()})

        return SMTFormula(cast(z3.BoolRef, new_smt_formula), *new_free_variables)

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

    def __eq__(self, other):
        return type(self) == type(other) and self.formula == other.formula

    def __hash__(self):
        return hash(self.formula)


class QuantifiedFormula(Formula):
    def __init__(self,
                 bound_variable: BoundVariable,
                 in_variable: Variable,
                 inner_formula: Formula,
                 bind_expression: Optional[BindExpression] = None):
        assert inner_formula is not None

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

    def __eq__(self, other):
        return type(self) == type(other) and \
               (self.bound_variable, self.in_variable, self.inner_formula, self.bind_expression) == \
               (other.bound_variable, other.in_variable, other.inner_formula, other.bind_expression)


class ForallFormula(QuantifiedFormula):
    def __init__(self,
                 bound_variable: BoundVariable,
                 in_variable: Variable,
                 inner_formula: Formula,
                 bind_expression: Optional[BindExpression] = None):
        super().__init__(bound_variable, in_variable, inner_formula, bind_expression)

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return ForallFormula(
            self.bound_variable,
            self.in_variable if self.in_variable not in subst_map else subst_map[self.in_variable],
            self.inner_formula.substitute_variables(subst_map),
            self.bind_expression)

    def substitute_expressions(self, subst_map: Dict[Variable, Tuple[Path, DerivationTree]]) -> Formula:
        if self.in_variable in subst_map:
            # Instantiate quantifier
            matches: List[Dict[Variable, Tuple[Path, DerivationTree]]] = \
                matches_for_quantified_variable(self, subst_map[self.in_variable][1])

            # NOTE: We assume that if there are no matches, the quantified expression is not feasible
            #       also in incomplete parse tree instantiations. Otherwise, it is not correct to remove
            #       the quantified formula!

            if not matches:
                isla_logger.debug(f"Replacing universal formula with True since quantified expression does not "
                                  f"match derivation tree\n"
                                  f"  (tree: {subst_map[self.in_variable][1]}, "
                                  f"formula: {self})")
                return SMTFormula(z3.BoolVal(True))

            result = self.inner_formula.substitute_expressions(subst_map)
            for match in matches:
                result = result.substitute_expressions(match)
            return result

        return ForallFormula(
            self.bound_variable,
            self.in_variable,
            self.inner_formula.substitute_expressions(subst_map),
            self.bind_expression)

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_forall_formula(self)
        self.inner_formula.accept(visitor)

    def __str__(self):
        quote = "'"
        return f'∀ {"" if not self.bind_expression else quote + str(self.bind_expression) + quote + " = "}' \
               f'{str(self.bound_variable)} ∈ {str(self.in_variable)}: ({str(self.inner_formula)})'

    def __eq__(self, other):
        return super.__eq__(self, other)

    def __hash__(self):
        return super.__hash__(self)


class ExistsFormula(QuantifiedFormula):
    def __init__(self,
                 bound_variable: BoundVariable,
                 in_variable: Variable,
                 inner_formula: Formula,
                 bind_expression: Optional[BindExpression] = None):
        super().__init__(bound_variable, in_variable, inner_formula, bind_expression)

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return ExistsFormula(
            self.bound_variable,
            self.in_variable if self.in_variable not in subst_map else subst_map[self.in_variable],
            self.inner_formula.substitute_variables(subst_map),
            self.bind_expression)

    def substitute_expressions(self, subst_map: Dict[Variable, Tuple[Path, DerivationTree]]) -> Formula:
        # Quantification over concrete values (no variables) is not allowed.
        assert self.in_variable not in subst_map

        return ExistsFormula(
            self.bound_variable,
            self.in_variable,
            self.inner_formula.substitute_expressions(subst_map),
            self.bind_expression)

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_exists_formula(self)
        self.inner_formula.accept(visitor)

    def __str__(self):
        quote = "'"
        return f'∃ {"" if not self.bind_expression else quote + str(self.bind_expression) + quote + " = "}' \
               f'{str(self.bound_variable)} ∈ {str(self.in_variable)}: ({str(self.inner_formula)})'

    def __eq__(self, other):
        return super.__eq__(self, other)

    def __hash__(self):
        return super.__hash__(self)


class VariablesCollector(FormulaVisitor):
    def __init__(self):
        self.result: Optional[OrderedSet[Variable]] = None

    def collect(self, formula: Formula) -> OrderedSet[Variable]:
        self.result = OrderedSet([])
        formula.accept(self)
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
        for arg in formula.args:
            if isinstance(arg, Variable):
                self.result.add(arg)
            else:
                _, tree = arg
                self.result.update(tree.tree_variables())

    def visit_smt_formula(self, formula: SMTFormula):
        self.result.update(formula.free_variables())


class FilterVisitor(FormulaVisitor):
    def __init__(self, filter: Callable[[Formula], bool]):
        self.filter = filter
        self.result: List[Formula] = []

    def collect(self, formula: Formula) -> List[Variable]:
        self.result = []
        formula.accept(self)
        return self.result

    def visit_forall_formula(self, formula: ForallFormula):
        if self.filter(formula):
            self.result.append(formula)

    def visit_exists_formula(self, formula: ExistsFormula):
        if self.filter(formula):
            self.result.append(formula)

    def visit_negated_formula(self, formula: NegatedFormula):
        if self.filter(formula):
            self.result.append(formula)

    def visit_smt_formula(self, formula: SMTFormula):
        if self.filter(formula):
            self.result.append(formula)

    def visit_predicate_formula(self, formula: PredicateFormula):
        if self.filter(formula):
            self.result.append(formula)

    def visit_disjunctive_formula(self, formula: DisjunctiveFormula):
        if self.filter(formula):
            self.result.append(formula)

    def visit_conjunctive_formula(self, formula: ConjunctiveFormula):
        if self.filter(formula):
            self.result.append(formula)


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


def evaluate(formula: Formula, assignments: Dict[Variable, Tuple[Path, DerivationTree]]) -> bool:
    assert well_formed(formula)

    def evaluate_(formula: Formula, assignments: Dict[Variable, Tuple[Path, DerivationTree]]) -> bool:
        q = '"'
        t = type(formula)

        if t is SMTFormula:
            formula: SMTFormula
            instantiation = z3.substitute(
                formula.formula,
                *tuple({z3.String(symbol.name): z3.StringVal(str(symbol_assignment[1]))
                        for symbol, symbol_assignment
                        in assignments.items()}.items()))

            z3.set_param("smt.string_solver", "z3str3")
            solver = z3.Solver()
            solver.add(instantiation)
            return solver.check() == z3.sat  # Set timeout?
        elif issubclass(t, QuantifiedFormula):
            formula: QuantifiedFormula
            assert formula.in_variable in assignments
            in_inst: DerivationTree = assignments[formula.in_variable][1]
            new_assignments = matches_for_quantified_variable(formula, in_inst, assignments)

            if t is ForallFormula:
                formula: ForallFormula
                return all(evaluate_(formula.inner_formula, new_assignment) for new_assignment in new_assignments)
            elif t is ExistsFormula:
                formula: ExistsFormula
                return any(evaluate_(formula.inner_formula, new_assignment) for new_assignment in new_assignments)
        elif t is PredicateFormula:
            formula: PredicateFormula
            arg_insts = [arg if not isinstance(arg, Variable) else assignments[arg] for arg in formula.args]
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


def matches_for_quantified_variable(
        formula: QuantifiedFormula,
        in_tree: DerivationTree,
        initial_assignments: Optional[Dict[Variable, Tuple[Path, DerivationTree]]] = None) -> \
        List[Dict[Variable, Tuple[Path, DerivationTree]]]:
    qfd_var: BoundVariable = formula.bound_variable
    bind_expr: Optional[BindExpression] = formula.bind_expression
    new_assignments: List[Dict[Variable, Tuple[Path, DerivationTree]]] = []
    if initial_assignments is None:
        initial_assignments = {}

    def search_action(path: Path, tree: DerivationTree) -> None:
        nonlocal new_assignments
        node, children = tree
        if node == qfd_var.n_type:
            if bind_expr is not None:
                maybe_match: Optional[Dict[BoundVariable, Tuple[Path, DerivationTree]]] = bind_expr.match(tree)
                if maybe_match is not None:
                    new_assignment = copy.copy(initial_assignments)
                    new_assignment[qfd_var] = path, tree
                    new_assignment.update({v: (path + p[0], p[1]) for v, p in maybe_match.items()})
                    new_assignments.append(new_assignment)
            else:
                new_assignment = copy.copy(initial_assignments)
                new_assignment[qfd_var] = path, tree
                new_assignments.append(new_assignment)

    in_tree.traverse(search_action)
    return new_assignments


class NonAtomicVisitor(FormulaVisitor):
    def __init__(self):
        self.non_atomic_variables = OrderedSet([])

    def visit_forall_formula(self, formula: ForallFormula):
        self.non_atomic_variables.add(formula.in_variable)
        if formula.bind_expression is not None:
            self.non_atomic_variables.add(formula.bound_variable)

    def visit_exists_formula(self, formula: ExistsFormula):
        self.non_atomic_variables.add(formula.in_variable)
        if formula.bind_expression is not None:
            self.non_atomic_variables.add(formula.bound_variable)

    def visit_predicate_formula(self, formula: PredicateFormula):
        if formula.predicate != BEFORE_PREDICATE:
            self.non_atomic_variables.update(formula.free_variables())

    def visit_smt_formula(self, formula: SMTFormula):
        # TODO: This is still quite arbitrary and ad-hoc, should be fundamentally investigated and reworked.

        if str(formula.formula.decl()) == "==" and any(not is_z3_var(child)
                                                       for child in formula.formula.children()):
            # In equations like "Var == 'asdf'", it slows down the process to first fuzz Var.
            # Thus, we have to leave Var's type concrete.
            self.non_atomic_variables.update(formula.free_variables())

        for expr in visit_z3_expr(formula.formula):
            # Any non-trivial string expression, e.g., substring computations
            # or regex operations, exclude the involved variables from atomic
            # representations, since their internal structure matters.
            # TODO: Have to more thoroughly test whether this suffices.
            if expr.decl().name() == "str.in_re":
                self.non_atomic_variables.update(formula.free_variables())

            if z3.is_string(expr) and not z3.is_string_value(expr) and not z3.is_const(expr):
                self.non_atomic_variables.update(formula.free_variables())


def abstract_tree_to_string(tree: AbstractTree) -> str:
    symbol, children, *_ = tree
    if children:
        return ''.join(abstract_tree_to_string(c) for c in children)
    else:
        if isinstance(symbol, Variable):
            return symbol.name
        return symbol


def tree_variables(tree: AbstractTree) -> Generator[Variable, None, None]:
    return (sub_tree[0]
            for _, sub_tree in path_iterator(tree)
            if isinstance(sub_tree[0], Variable))


def state_to_string(state: SolutionState) -> str:
    return "{(" + "), (".join(map(str, [f"{constant.name}, {formula}, \"{abstract_tree_to_string(tree)}\""
                                        for constant, formula, tree in state])) + ")}"


def substitute_variables_in_tree(in_tree: AbstractTree, subst_map: Dict[Variable, AbstractTree]) -> AbstractTree:
    node, children = in_tree
    if children is None:
        if isinstance(node, Variable) and node in subst_map:
            return subst_map[node]
        else:
            return in_tree

    return node, [substitute_variables_in_tree(child, subst_map) for child in children]


def inline_var_in_tree(in_tree: AbstractTree, variable: Variable, inst: AbstractTree) -> AbstractTree:
    node, children = in_tree
    if children is None:
        if node == variable:
            return inst
        else:
            return in_tree

    return node, [inline_var_in_tree(child, variable, inst) for child in children]
