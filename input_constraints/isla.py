import copy
import logging
import random
import sys
from functools import reduce
from typing import Union, List, Optional, Dict, Tuple, Callable, cast, Generator, Set, Iterable

import itertools
import z3
from fuzzingbook.GrammarFuzzer import tree_to_string, GrammarFuzzer
from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import EarleyParser
from grammar_graph.gg import GrammarGraph
from orderedset import OrderedSet

from input_constraints.helpers import get_symbols, z3_subst, path_iterator, replace_tree_path, is_valid
from input_constraints.type_defs import ParseTree, Path, Grammar

SolutionState = List[Tuple['Constant', 'Formula', 'DerivationTree']]
Assignment = Tuple['Constant', 'Formula', 'DerivationTree']

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
    NUMERIC_NTYPE = "NUM"

    def __init__(self, name: str, n_type: str):
        """
        A constant is a "free variable" in a formula.

        :param name: The name of the constant.
        :param n_type: The nonterminal type of the constant, e.g., "<var>".
        """
        super().__init__(name, n_type)

    def is_numeric(self):
        return self.n_type == Constant.NUMERIC_NTYPE


class DerivationTree:
    """Derivation trees are immutable!"""

    def __init__(self, value: Union[str, Variable],
                 children: Optional[List['DerivationTree']] = None,
                 id: Optional[int] = None):
        assert isinstance(value, str) or isinstance(value, Variable)
        assert not isinstance(value, Variable) or not children
        assert children is None or all(isinstance(child, DerivationTree) for child in children)

        self.value = value
        self.children = None if children is None else tuple(children)
        self.id = id if id is not None else random.randint(0, sys.maxsize)
        self.__hash = None
        self.__structural_hash = None

        if not children:
            self.__len = 1
        else:
            self.__len = sum([child.__len for child in children]) + 1

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

    def is_complete(self):
        result = not self.is_open()
        assert not result or not self.is_abstract()
        return result

    def get_subtree(self, path: Path) -> 'DerivationTree':
        """Access a subtree based on `path` (a list of children numbers)"""
        if not path:
            return self

        return self.children[path[0]].get_subtree(path[1:])

    def is_valid_path(self, path: Path) -> bool:
        if not path:
            return True

        if not self.children:
            return False

        return self.children[path[0]].is_valid_path(path[1:])

    def path_iterator(self, path: Path = ()) -> Generator[Tuple[Path, 'DerivationTree'], None, None]:
        yield path, self
        if self.children is not None:
            for i, child in enumerate(self.children):
                yield from child.path_iterator(path + (i,))

    def filter(self, f: Callable[['DerivationTree'], bool],
               enforce_unique: bool = False) -> List[Tuple[Path, 'DerivationTree']]:
        result: List[Tuple[Path, 'DerivationTree']] = []

        for path, subtree in self.path_iterator():
            if f(subtree):
                result.append((path, subtree))

                if enforce_unique and len(result) > 1:
                    raise RuntimeError(f"Found searched-for element more than once in {self}")

        return result

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
        if path and path[0] + 1 < num_children(tuple()):
            return path[0] + 1,

        # path already is the last path.
        assert skip_children or list(self.path_iterator())[-1][0] == path
        return None

    def replace_path(self, path: Path, replacement_tree: 'DerivationTree', retain_id=False) -> 'DerivationTree':
        """Returns tree where replacement_tree has been inserted at `path` instead of the original subtree"""
        node, children = self
        assert isinstance(replacement_tree, DerivationTree)

        if not path:
            if retain_id:
                return DerivationTree(replacement_tree.value, replacement_tree.children, id=self.id)

            return replacement_tree

        head = path[0]
        new_children = (children[:head] +
                        (children[head].replace_path(path[1:], replacement_tree, retain_id),) +
                        children[head + 1:])

        return DerivationTree(node, new_children, id=self.id)

    def open_leaves(self) -> Generator[Tuple[Path, 'DerivationTree'], None, None]:
        """
        :return: All open leaves of this tree, including concrete and abstract ones.
        """
        return ((path, sub_tree)
                for path, sub_tree in self.path_iterator()
                if sub_tree.children is None)

    def __len__(self):
        # if self.__len is None:
        #     self.__len = len(list(self.path_iterator()))
        return self.__len

    def __lt__(self, other):
        return len(self) < len(other)

    def __le__(self, other):
        return len(self) <= len(other)

    def __gt__(self, other):
        return len(self) > len(other)

    def __ge__(self, other):
        return len(self) >= len(other)

    def open_concrete_leaves(self) -> Generator[Tuple[Path, 'DerivationTree'], None, None]:
        return ((path, sub_tree)
                for path, sub_tree in self.open_leaves()
                if sub_tree.children is None and not sub_tree.is_abstract())

    def make_concrete(self) -> 'DerivationTree':
        return self.substitute(
            {var: DerivationTree(var.n_type, None) for var in self.tree_variables()})

    def tree_variables(self) -> OrderedSet[Variable]:
        return OrderedSet([
            sub_tree.value
            for _, sub_tree in self.path_iterator()
            if isinstance(sub_tree.value, Variable)])

    def substitute(self, subst_map: Dict[Union[Variable, 'DerivationTree'], 'DerivationTree']) -> 'DerivationTree':
        if self in subst_map:
            return subst_map[self]

        value, children = self
        if children is None:
            if isinstance(value, Variable) and value in subst_map:
                return subst_map[value]
            else:
                return self

        return DerivationTree(
            value,
            [child.substitute(subst_map) for child in children],
            id=self.id)

    def is_prefix(self, other: 'DerivationTree') -> bool:
        if len(self) > len(other):
            return False

        if self.value != other.value:
            return False

        if self.children is None:
            return True

        if not self.children:
            if other.children is None:
                return False
            else:
                return True

        if not other.children:
            return False

        if len(self.children) != len(other.children):
            return False

        return all(self.children[idx].is_prefix(other.children[idx])
                   for idx, _ in enumerate(self.children))

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

    def __compute_hash(self):
        if self.children is None:
            return hash((self.value, self.id))
        else:
            return hash((self.value, self.id) + tuple(self.children))

    def __hash__(self):
        if self.__hash is not None:
            assert self.__hash == self.__compute_hash()
            return self.__hash

        self.__hash = self.__compute_hash()
        return self.__hash

    def __compute_structural_hash(self):
        if self.children is None:
            return hash(self.value)
        else:
            return hash((self.value,) + tuple([child.structural_hash() for child in self.children]))

    def structural_hash(self):
        if self.__structural_hash is not None:
            assert self.__structural_hash == self.__compute_structural_hash()
            return self.__structural_hash

        self.__structural_hash = self.__compute_structural_hash()
        return self.__structural_hash

    def structurally_equal(self, other: 'DerivationTree'):
        return (isinstance(other, DerivationTree)
                and self.value == other.value
                and (self.children is not None or other.children is None)
                and (other.children is not None or self.children is None)
                and (self.children is None or
                     len(self.children) == len(other.children)
                     and all(self.children[idx].structurally_equal(other.children[idx])
                             for idx in range(len(self.children)))))

    def __eq__(self, other):
        """
        Equality takes the randomly assigned ID into account! So trees with the same structure
        might not be equal.
        """
        return (isinstance(other, DerivationTree)
                and self.value == other.value
                and self.children == other.children
                and self.id == other.id)

    def to_string(self, show_open_leaves: bool = False):
        value, children = self
        if children:
            return ''.join(c.to_string(show_open_leaves) for c in children)
        else:
            if isinstance(value, Variable):
                return value.name

            if children is not None:
                return value if not is_nonterminal(value) else ""

            return value if show_open_leaves else ""

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
        return hash(tuple(self.bound_elements))

    def __eq__(self, other):
        return self.bound_elements == other.bound_elements


class FormulaVisitor:
    def visit_predicate_formula(self, formula: 'StructuralPredicateFormula'):
        pass

    def visit_semantic_predicate_formula(self, formula: 'SemanticPredicateFormula'):
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
        raise NotImplementedError()

    def free_variables(self) -> OrderedSet[Variable]:
        """Recursive."""
        raise NotImplementedError()

    def tree_arguments(self) -> OrderedSet[DerivationTree]:
        """Trees that were substituted for variables."""
        raise NotImplementedError()

    def substitute_variables(self, subst_map: Dict[Variable, Variable]) -> 'Formula':
        raise NotImplementedError()

    def substitute_expressions(self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]) -> 'Formula':
        raise NotImplementedError()

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
        if isinstance(self, SMTFormula):
            return SMTFormula(
                z3.Not(self.formula),
                *self.free_variables_,
                instantiated_variables=self.instantiated_variables,
                substitutions=self.substitutions)
        elif isinstance(self, NegatedFormula):
            return self.args[0]
        elif isinstance(self, ConjunctiveFormula):
            return reduce(lambda a, b: a | b, [-arg for arg in self.args])
        elif isinstance(self, DisjunctiveFormula):
            return reduce(lambda a, b: a & b, [-arg for arg in self.args])
        elif isinstance(self, ForallFormula):
            return ExistsFormula(
                self.bound_variable, self.in_variable, -self.inner_formula, self.bind_expression)
        elif isinstance(self, ExistsFormula):
            return ForallFormula(
                self.bound_variable, self.in_variable, -self.inner_formula, self.bind_expression)

        return NegatedFormula(self)

    def accept(self, visitor: FormulaVisitor):
        raise NotImplementedError()


class StructuralPredicate:
    def __init__(self, name: str, arity: int, eval_fun: Callable[[Path, ...], bool]):
        self.name = name
        self.arity = arity
        self.eval_fun = eval_fun

    def evaluate(self, *instantiations: Path):
        return self.eval_fun(*instantiations)

    def __eq__(self, other):
        return type(other) is StructuralPredicate and (self.name, self.arity) == (other.name, other.arity)

    def __hash__(self):
        return hash((self.name, self.arity))

    def __repr__(self):
        return f"Predicate({self.name}, {self.arity})"

    def __str__(self):
        return self.name


class StructuralPredicateFormula(Formula):
    def __init__(self, predicate: StructuralPredicate, *args: Union[Variable, DerivationTree]):
        assert len(args) == predicate.arity
        self.predicate = predicate
        self.args: List[Union[Variable, DerivationTree]] = list(args)

    def evaluate(self, context_tree: DerivationTree) -> bool:
        args_with_paths: List[Tuple[Path, DerivationTree]] = \
            [(context_tree.find_node(tree), tree) if isinstance(tree, DerivationTree)
             else context_tree.filter(
                lambda subtree: subtree.value == tree and subtree.children is None, enforce_unique=True)[0]
             for tree in self.args]

        if any(path is None for path, _ in args_with_paths):
            raise RuntimeError("Could not find paths for all predicate arguments in context tree:\n" +
                               str([str(tree) for path, tree in args_with_paths if path is None]) +
                               f"\nContext tree:\n{context_tree}")

        return self.predicate.eval_fun(*[path for path, _ in args_with_paths])

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return StructuralPredicateFormula(self.predicate,
                                          *[arg if arg not in subst_map
                                            else subst_map[arg] for arg in self.args])

    def substitute_expressions(self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]) -> Formula:
        new_args = []
        for arg in self.args:
            if isinstance(arg, Variable):
                if arg in subst_map:
                    new_args.append(subst_map[arg])
                else:
                    new_args.append(arg)
                continue

            tree: DerivationTree = arg
            if tree in subst_map:
                new_args.append(subst_map[tree])
                continue

            new_args.append(tree.substitute({k: v for k, v in subst_map.items()}))

        return StructuralPredicateFormula(self.predicate, *new_args)

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return OrderedSet([])

    def free_variables(self) -> OrderedSet[Variable]:
        result = OrderedSet([])
        result.update([arg for arg in self.args if isinstance(arg, Variable)])
        vars_in_concrete_args = [v for arg in self.args if isinstance(arg, DerivationTree)
                                 for v in arg.tree_variables()]
        result.update(vars_in_concrete_args)
        return result

    def tree_arguments(self) -> OrderedSet[DerivationTree]:
        return OrderedSet([arg for arg in self.args if isinstance(arg, DerivationTree)])

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_predicate_formula(self)

    def __hash__(self):
        return hash((type(self), self.predicate, tuple(self.args)))

    def __eq__(self, other):
        return type(self) is type(other) and (self.predicate, self.args) == (other.predicate, other.args)

    def __str__(self):
        arg_strings = []
        for arg in self.args:
            arg_strings.append(str(arg))

        return f"{self.predicate}({', '.join(arg_strings)})"

    def __repr__(self):
        return f'PredicateFormula({repr(self.predicate), ", ".join(map(repr, self.args))})'


class SemPredEvalResult:
    def __init__(self, result: Optional[Union[bool, Dict[Union[Constant, DerivationTree], DerivationTree]]]):
        self.result = result

    def true(self):
        return self.result is True

    def false(self):
        return self.result is False

    def ready(self):
        return self.result is not None

    def __eq__(self, other):
        return isinstance(other, SemPredEvalResult) and self.result == other.result

    def __str__(self):
        if self.ready():
            if self.true() or self.false():
                return str(self.result)
            else:
                return "{" + ", ".join([str(key) + ": " + str(value) for key, value in self.result.items()]) + "}"
        else:
            return "UNKNOWN"


class SemanticPredicate:
    def __init__(self, name: str, arity: int,
                 eval_fun: Callable[[Optional[Grammar], ...], SemPredEvalResult],
                 custom_args_equality: Optional[Callable[[Tuple, Tuple], bool]] = None):
        self.name = name
        self.arity = arity
        self.eval_fun = eval_fun
        self.custom_args_equality = custom_args_equality or (lambda t1, t2: t1 == t2)

    def evaluate(self, grammar: Optional[Grammar], *instantiations: Union[DerivationTree, Constant]):
        return self.eval_fun(grammar, *instantiations)

    def __eq__(self, other):
        return type(other) is SemanticPredicate and (self.name, self.arity) == (other.name, other.arity)

    def __hash__(self):
        return hash((self.name, self.arity))

    def __repr__(self):
        return f"SemanticPredicate({self.name}, {self.arity})"

    def __str__(self):
        return self.name


class SemanticPredicateFormula(Formula):
    def __init__(self, predicate: SemanticPredicate, *args: Union[DerivationTree, Constant]):
        assert len(args) == predicate.arity
        self.predicate = predicate
        self.args: List[Union[Variable, DerivationTree]] = list(args)

    def evaluate(self, grammar: Optional[Grammar]) -> SemPredEvalResult:
        return self.predicate.eval_fun(grammar, *self.args)

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return SemanticPredicateFormula(self.predicate,
                                        *[arg if arg not in subst_map
                                          else subst_map[arg] for arg in self.args])

    def substitute_expressions(self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]) -> Formula:
        new_args = []
        for arg in self.args:
            if isinstance(arg, Variable):
                if arg in subst_map:
                    new_args.append(subst_map[arg])
                else:
                    new_args.append(arg)
                continue

            tree: DerivationTree = arg
            if tree in subst_map:
                new_args.append(subst_map[tree])
                continue

            new_args.append(tree.substitute({k: v for k, v in subst_map.items()}))

        return SemanticPredicateFormula(self.predicate, *new_args)

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return OrderedSet([])

    def free_variables(self) -> OrderedSet[Variable]:
        result = OrderedSet([])
        result.update([arg for arg in self.args if isinstance(arg, Variable)])
        vars_in_concrete_args = [v for arg in self.args if isinstance(arg, DerivationTree)
                                 for v in arg.tree_variables()]
        result.update(vars_in_concrete_args)
        return result

    def tree_arguments(self) -> OrderedSet[DerivationTree]:
        return OrderedSet([arg for arg in self.args if isinstance(arg, DerivationTree)])

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_semantic_predicate_formula(self)

    def __hash__(self):
        return hash((type(self), self.predicate, tuple(self.args)))

    def __eq__(self, other):
        return (type(self) is type(other)
                and self.predicate == other.predicate
                and self.predicate.custom_args_equality(self.args, other.args))

    def __str__(self):
        arg_strings = []
        for arg in self.args:
            arg_strings.append(str(arg))

        return f"{self.predicate}({', '.join(arg_strings)})"

    def __repr__(self):
        return f'SemanticPredicateFormula({repr(self.predicate), ", ".join(map(repr, self.args))})'


class PropositionalCombinator(Formula):
    def __init__(self, *args: Formula):
        self.args = args

    def free_variables(self) -> OrderedSet[Variable]:
        result: OrderedSet[Variable] = OrderedSet([])
        for arg in self.args:
            result |= arg.free_variables()
        return result

    def tree_arguments(self) -> OrderedSet[DerivationTree]:
        result: OrderedSet[DerivationTree] = OrderedSet([])
        for arg in self.args:
            result |= arg.tree_arguments()
        return result

    def __repr__(self):
        return f"{type(self).__name__}({', '.join(map(repr, self.args))})"

    def __hash__(self):
        return hash((type(self), self.args))

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

    def substitute_expressions(self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]) -> Formula:
        return NegatedFormula(*[arg.substitute_expressions(subst_map) for arg in self.args])

    def __hash__(self):
        return hash((type(self), self.args))

    def __str__(self):
        return f"¬({self.args[0]})"


class ConjunctiveFormula(PropositionalCombinator):
    def __init__(self, *args: Formula):
        if len(args) < 2:
            raise RuntimeError(f"Conjunction needs at least two arguments, {len(args)} given.")
        super().__init__(*args)

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return reduce(lambda a, b: a & b, [arg.substitute_variables(subst_map) for arg in self.args])

    def substitute_expressions(self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]) -> Formula:
        return reduce(lambda a, b: a & b, [arg.substitute_expressions(subst_map) for arg in self.args])

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_conjunctive_formula(self)
        for formula in self.args:
            formula.accept(visitor)

    def __hash__(self):
        return hash((type(self), self.args))

    def __eq__(self, other):
        return split_conjunction(self) == split_conjunction(other)

    def __str__(self):
        return f"({' ∧ '.join(map(str, self.args))})"


class DisjunctiveFormula(PropositionalCombinator):
    def __init__(self, *args: Formula):
        if len(args) < 2:
            raise RuntimeError(f"Disjunction needs at least two arguments, {len(args)} given.")
        super().__init__(*args)

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return reduce(lambda a, b: a | b, [arg.substitute_variables(subst_map) for arg in self.args])

    def substitute_expressions(self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]) -> Formula:
        return reduce(lambda a, b: a | b, [arg.substitute_expressions(subst_map) for arg in self.args])

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_disjunctive_formula(self)
        for formula in self.args:
            formula.accept(visitor)

    def __hash__(self):
        return hash((type(self), self.args))

    def __eq__(self, other):
        return split_disjunction(self) == split_disjunction(other)

    def __str__(self):
        return f"({' ∨ '.join(map(str, self.args))})"


class SMTFormula(Formula):
    def __init__(self, formula: z3.BoolRef, *free_variables: Variable,
                 instantiated_variables: Optional[OrderedSet[Variable]] = None,
                 substitutions: Optional[Dict[Variable, DerivationTree]] = None):
        """
        Encapsulates an SMT formula.
        :param formula: The SMT formula.
        :param free_variables: Free variables in this formula.
        """
        self.formula = formula
        self.free_variables_ = OrderedSet(free_variables)
        self.instantiated_variables = instantiated_variables or OrderedSet([])
        self.substitutions: Dict[Variable, DerivationTree] = substitutions or {}

        actual_symbols = get_symbols(formula)
        if len(self.free_variables_) + len(self.instantiated_variables) != len(actual_symbols):
            raise RuntimeError(f"Supplied number of {len(free_variables)} symbols does not match "
                               f"actual number of symbols {len(actual_symbols)} in formula '{formula}'")

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        new_smt_formula = z3_subst(self.formula, {v1.to_smt(): v2.to_smt() for v1, v2 in subst_map.items()})

        new_free_variables = [variable if variable not in subst_map
                              else subst_map[variable]
                              for variable in self.free_variables_]

        # This method is only to be used in ensuring the normal form and not thereafter
        assert not self.instantiated_variables
        assert not self.substitutions

        return SMTFormula(cast(z3.BoolRef, new_smt_formula),
                          *new_free_variables,
                          instantiated_variables=self.instantiated_variables,
                          substitutions=self.substitutions)

    def substitute_expressions(self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]) -> Formula:
        tree_subst_map = {k: v for k, v in subst_map.items()
                          if isinstance(k, DerivationTree)
                          and k in self.substitutions.values()}
        var_subst_map: Dict[Variable: DerivationTree] = {
            k: v for k, v in subst_map.items() if k in self.free_variables_}

        updated_substitutions: Dict[Variable, DerivationTree] = {
            var: tree.substitute(tree_subst_map)
            for var, tree in self.substitutions.items()
        }

        new_substitutions: Dict[Variable, DerivationTree] = updated_substitutions | var_subst_map

        complete_substitutions = {k: v for k, v in new_substitutions.items() if v.is_complete()}
        new_substitutions = {k: v for k, v in new_substitutions.items() if not v.is_complete()}

        new_instantiated_variables = OrderedSet([
            var for var in self.instantiated_variables | OrderedSet(new_substitutions.keys())
            if var not in complete_substitutions
        ])

        new_smt_formula: z3.BoolRef = cast(z3.BoolRef, z3_subst(self.formula, {
            variable.to_smt(): z3.StringVal(str(tree))
            for variable, tree in complete_substitutions.items()
        }))

        new_free_variables: OrderedSet[Variable] = OrderedSet([
            variable for variable in self.free_variables_
            if variable not in var_subst_map])

        if len(new_free_variables) + len(new_instantiated_variables) == 0:
            # Formula is ground, we can evaluate it!
            return SMTFormula(z3.BoolVal(is_valid(new_smt_formula)))

        return SMTFormula(cast(z3.BoolRef, new_smt_formula), *new_free_variables,
                          instantiated_variables=new_instantiated_variables,
                          substitutions=new_substitutions)

    def tree_arguments(self) -> OrderedSet[DerivationTree]:
        return OrderedSet(self.substitutions.values())

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return OrderedSet([])

    def free_variables(self) -> OrderedSet[Variable]:
        return self.free_variables_

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_smt_formula(self)

    def __repr__(self):
        return f"SMTFormula({repr(self.formula)}, {', '.join(map(repr, self.free_variables_))}, " \
               f"instantiated_variables={repr(self.instantiated_variables)}, " \
               f"substitutions={repr(self.substitutions)})"

    def __str__(self):
        if not self.substitutions:
            return str(self.formula)
        else:
            subst_string = str({str(var): str(tree) for var, tree in self.substitutions.items()})
            return f"({self.formula}, {subst_string})"

    def __eq__(self, other):
        return type(self) == type(other) and z3.is_true(z3.simplify(self.formula == other.formula))

    def __hash__(self):
        return hash((self.formula, tuple(self.substitutions.items())))


class QuantifiedFormula(Formula):
    def __init__(self,
                 bound_variable: BoundVariable,
                 in_variable: Union[Variable, DerivationTree],
                 inner_formula: Formula,
                 bind_expression: Optional[BindExpression] = None):
        assert inner_formula is not None

        self.bound_variable = bound_variable
        self.in_variable = in_variable
        self.inner_formula = inner_formula
        self.bind_expression = bind_expression

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return (OrderedSet([self.bound_variable])
                | (OrderedSet([]) if self.bind_expression is None else self.bind_expression.bound_variables()))

    def free_variables(self) -> OrderedSet[Variable]:
        return ((OrderedSet([self.in_variable] if isinstance(self.in_variable, Variable) else [])
                 | self.inner_formula.free_variables())
                - self.bound_variables())

    def tree_arguments(self) -> OrderedSet[DerivationTree]:
        result = OrderedSet([])
        if isinstance(self.in_variable, DerivationTree):
            result.add(self.in_variable)
        result.update(self.inner_formula.tree_arguments())
        return result

    def __repr__(self):
        return f'{type(self).__name__}({repr(self.bound_variable)}, {repr(self.in_variable)}, ' \
               f'{repr(self.inner_formula)}{"" if self.bind_expression is None else ", " + repr(self.bind_expression)})'

    def __hash__(self):
        return hash((type(self), self.bound_variable, self.in_variable, self.inner_formula, self.bind_expression))

    def __eq__(self, other):
        return type(self) == type(other) and \
               (self.bound_variable, self.in_variable, self.inner_formula, self.bind_expression) == \
               (other.bound_variable, other.in_variable, other.inner_formula, other.bind_expression)


class ForallFormula(QuantifiedFormula):
    def __init__(self,
                 bound_variable: BoundVariable,
                 in_variable: Union[Variable, DerivationTree],
                 inner_formula: Formula,
                 bind_expression: Optional[BindExpression] = None,
                 already_matched: Optional[Set[int]] = None):
        super().__init__(bound_variable, in_variable, inner_formula, bind_expression)
        self.already_matched: Set[int] = copy.deepcopy(already_matched) or set()

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        assert not self.already_matched

        return ForallFormula(
            self.bound_variable if self.bound_variable not in subst_map else subst_map[self.bound_variable],
            self.in_variable if self.in_variable not in subst_map else subst_map[self.in_variable],
            self.inner_formula.substitute_variables(subst_map),
            None if not self.bind_expression else self.bind_expression.substitute_variables(subst_map),
            self.already_matched
        )

    def substitute_expressions(self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]) -> Formula:
        new_in_variable = self.in_variable
        if self.in_variable in subst_map:
            new_in_variable = subst_map[new_in_variable]
        elif isinstance(new_in_variable, DerivationTree):
            new_in_variable = new_in_variable.substitute(subst_map)

        new_inner_formula = self.inner_formula.substitute_expressions(subst_map)

        if (self.bound_variable not in new_inner_formula.free_variables()
                and (self.bind_expression is None or
                     not any(bv in new_inner_formula.free_variables()
                             for bv in self.bind_expression.bound_variables()))):
            return new_inner_formula

        return ForallFormula(
            self.bound_variable,
            new_in_variable,
            new_inner_formula,
            self.bind_expression,
            self.already_matched)

    def add_already_matched(self, trees: Union[DerivationTree, Iterable[DerivationTree]]) -> 'ForallFormula':
        return ForallFormula(
            self.bound_variable,
            self.in_variable,
            self.inner_formula,
            self.bind_expression,
            self.already_matched | ({trees.id} if isinstance(trees, DerivationTree) else {tree.id for tree in trees}))

    def is_already_matched(self, tree: DerivationTree) -> bool:
        return tree.id in self.already_matched

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
                 in_variable: Union[Variable, DerivationTree],
                 inner_formula: Formula,
                 bind_expression: Optional[BindExpression] = None):
        super().__init__(bound_variable, in_variable, inner_formula, bind_expression)

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return ExistsFormula(
            self.bound_variable if self.bound_variable not in subst_map else subst_map[self.bound_variable],
            self.in_variable if self.in_variable not in subst_map else subst_map[self.in_variable],
            self.inner_formula.substitute_variables(subst_map),
            None if not self.bind_expression else self.bind_expression.substitute_variables(subst_map))

    def substitute_expressions(self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]) -> Formula:
        new_in_variable = self.in_variable
        if self.in_variable in subst_map:
            new_in_variable = subst_map[new_in_variable]
        elif isinstance(new_in_variable, DerivationTree):
            new_in_variable = new_in_variable.substitute(subst_map)

        new_inner_formula = self.inner_formula.substitute_expressions(subst_map)

        if (self.bound_variable not in new_inner_formula.free_variables()
                and (self.bind_expression is None or
                     not any(bv in new_inner_formula.free_variables()
                             for bv in self.bind_expression.bound_variables()))):
            return new_inner_formula

        return ExistsFormula(
            self.bound_variable,
            new_in_variable,
            self.inner_formula.substitute_expressions(subst_map),
            self.bind_expression)

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_exists_formula(self)
        self.inner_formula.accept(visitor)

    def __str__(self):
        quote = "'"
        return f'∃ {"" if not self.bind_expression else quote + str(self.bind_expression) + quote + " = "}' \
               f'{str(self.bound_variable)} ∈ {str(self.in_variable)}: ({str(self.inner_formula)})'


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
        if isinstance(formula.in_variable, Variable):
            self.result.add(formula.in_variable)
        else:
            self.result.update(formula.in_variable.tree_variables())
        self.result.add(formula.bound_variable)
        if formula.bind_expression is not None:
            self.result.update(formula.bind_expression.bound_variables())

    def visit_predicate_formula(self, formula: StructuralPredicateFormula):
        for arg in formula.args:
            if isinstance(arg, Variable):
                self.result.add(arg)
            else:
                _, tree = arg
                self.result.update(tree.tree_variables())

    def visit_semantic_predicate_formula(self, formula: SemanticPredicateFormula):
        for arg in formula.args:
            if isinstance(arg, Variable):
                self.result.add(arg)
            else:
                self.result.update(arg.tree_variables())

    def visit_smt_formula(self, formula: SMTFormula):
        self.result.update(formula.free_variables())


class FilterVisitor(FormulaVisitor):
    def __init__(self, filter: Callable[[Formula], bool]):
        self.filter = filter
        self.result: List[Formula] = []

    def collect(self, formula: Formula) -> List[Formula]:
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

    def visit_predicate_formula(self, formula: StructuralPredicateFormula):
        if self.filter(formula):
            self.result.append(formula)

    def visit_semantic_predicate_formula(self, formula: SemanticPredicateFormula):
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

    if isinstance(formula, QuantifiedFormula):
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
    elif isinstance(formula, SMTFormula):
        if any(free_var in in_expr_vars for free_var in formula.free_variables()):
            return False

        return not any(free_var not in bound_vars
                       for free_var in formula.free_variables()
                       if type(free_var) is BoundVariable)
    elif isinstance(formula, PropositionalCombinator):
        if isinstance(formula, ConjunctiveFormula):
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
    elif isinstance(formula, StructuralPredicateFormula) or isinstance(formula, SemanticPredicateFormula):
        return all(free_var in bound_vars
                   for free_var in formula.free_variables()
                   if type(free_var) is BoundVariable)
    else:
        raise NotImplementedError()


def evaluate(formula: Formula,
             reference_tree: Optional[DerivationTree] = None) -> bool:
    assert well_formed(formula)

    def evaluate_(formula: Formula, assignments: Dict[Variable, Tuple[Path, DerivationTree]]) -> bool:
        if isinstance(formula, SMTFormula):
            instantiation = z3.substitute(
                formula.formula,
                *tuple({z3.String(symbol.name): z3.StringVal(str(symbol_assignment[1]))
                        for symbol, symbol_assignment
                        in assignments.items()}.items()))

            z3.set_param("smt.string_solver", "z3str3")
            solver = z3.Solver()
            solver.add(instantiation)
            return solver.check() == z3.sat  # Set timeout?
        elif isinstance(formula, QuantifiedFormula):
            if isinstance(formula.in_variable, DerivationTree):
                in_inst = formula.in_variable
            else:
                assert formula.in_variable in assignments
                in_inst: DerivationTree = assignments[formula.in_variable][1]

            new_assignments = matches_for_quantified_formula(formula, in_inst, assignments)

            if isinstance(formula, ForallFormula):
                return all(evaluate_(formula.inner_formula, new_assignment) for new_assignment in new_assignments)
            elif isinstance(formula, ExistsFormula):
                return any(evaluate_(formula.inner_formula, new_assignment) for new_assignment in new_assignments)
        elif isinstance(formula, StructuralPredicateFormula):
            assert (not any(isinstance(arg, DerivationTree) for arg in formula.args)
                    or reference_tree is not None)
            arg_insts = [(reference_tree.find_node(arg), arg) if isinstance(arg, DerivationTree)
                         else assignments[arg]
                         for arg in formula.args]
            return formula.predicate.evaluate(*arg_insts)
        elif isinstance(formula, SemanticPredicateFormula):
            arg_insts = [arg if isinstance(arg, DerivationTree) or arg not in assignments
                         else assignments[arg][1]
                         for arg in formula.args]
            eval_res = formula.predicate.evaluate(None, *arg_insts)

            if eval_res.true():
                return True
            elif eval_res.false() or not eval_res.ready():
                return False

            assert isinstance(eval_res.result, dict)
            assert all(isinstance(key, Constant) and key.is_numeric() for key in eval_res.result)

            assignments.update({const: (tuple(), assgn) for const, assgn in eval_res.result.items()})
            return True
        elif isinstance(formula, NegatedFormula):
            return not evaluate_(formula.args[0], assignments)
        elif isinstance(formula, ConjunctiveFormula):
            return all(evaluate_(sub_formula, assignments) for sub_formula in formula.args)
        elif isinstance(formula, DisjunctiveFormula):
            return any(evaluate_(sub_formula, assignments) for sub_formula in formula.args)
        else:
            raise NotImplementedError()

    return evaluate_(formula, {})


def matches_for_quantified_formula(
        formula: QuantifiedFormula,
        in_tree: Optional[DerivationTree] = None,
        initial_assignments: Optional[Dict[Variable, Tuple[Path, DerivationTree]]] = None) -> \
        List[Dict[Variable, Tuple[Path, DerivationTree]]]:
    if in_tree is None:
        in_tree = formula.in_variable
        assert isinstance(in_tree, DerivationTree)

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


def replace_formula(in_formula: Formula,
                    to_replace: Union[Formula, Callable[[Formula], Union[bool, Formula]]],
                    replace_with: Optional[Formula] = None) -> Formula:
    """
    Replaces a formula inside a conjunction or disjunction.
    to_replace is either (1) a formula to replace, or (2) a predicate which holds if the given formula
    should been replaced (if it returns True, replace_with must not be None), or (3) a function returning
    the formula to replace if the subformula should be replaced, or False otherwise. For (3), replace_with
    may be None (it is irrelevant).
    """

    if callable(to_replace):
        result = to_replace(in_formula)
        if isinstance(result, Formula):
            return result

        assert type(result) is bool
        if to_replace(in_formula):
            assert replace_with is not None
            return replace_with
    else:
        if in_formula == to_replace:
            return replace_with

    if isinstance(in_formula, ConjunctiveFormula):
        return reduce(lambda a, b: a & b, [replace_formula(child, to_replace, replace_with)
                                           for child in in_formula.args])
    elif isinstance(in_formula, DisjunctiveFormula):
        return reduce(lambda a, b: a | b, [replace_formula(child, to_replace, replace_with)
                                           for child in in_formula.args])
    elif isinstance(in_formula, NegatedFormula):
        return NegatedFormula(replace_formula(in_formula.args[0], to_replace, replace_with))
    elif isinstance(in_formula, ForallFormula):
        return ForallFormula(
            in_formula.bound_variable,
            in_formula.in_variable,
            replace_formula(in_formula.inner_formula, to_replace, replace_with),
            in_formula.bind_expression,
            in_formula.already_matched
        )
    elif isinstance(in_formula, ExistsFormula):
        return ExistsFormula(
            in_formula.bound_variable,
            in_formula.in_variable,
            replace_formula(in_formula.inner_formula, to_replace, replace_with),
            in_formula.bind_expression)

    return in_formula


def convert_to_nnf(formula: Formula, negate=False) -> Formula:
    """Pushes negations inside the formula."""
    if isinstance(formula, NegatedFormula):
        return convert_to_nnf(formula.args[0], not negate)
    elif isinstance(formula, ConjunctiveFormula):
        args = [convert_to_nnf(arg, negate) for arg in formula.args]
        if negate:
            return reduce(lambda a, b: a | b, args)
        else:
            return reduce(lambda a, b: a & b, args)
    elif isinstance(formula, DisjunctiveFormula):
        args = [convert_to_nnf(arg, negate) for arg in formula.args]
        if negate:
            return reduce(lambda a, b: a & b, args)
        else:
            return reduce(lambda a, b: a | b, args)
    elif isinstance(formula, StructuralPredicateFormula) or isinstance(formula, SemanticPredicateFormula):
        if negate:
            return NegatedFormula(formula)
        else:
            return formula
    elif isinstance(formula, SMTFormula):
        if negate:
            return SMTFormula(
                z3.Not(formula.formula),
                *formula.free_variables(),
                instantiated_variables=formula.instantiated_variables,
                substitutions=formula.substitutions
            )
        else:
            return formula
    elif isinstance(formula, QuantifiedFormula):
        inner_formula = convert_to_nnf(formula.inner_formula, negate) if negate else formula.inner_formula
        already_matched: Set[int] = formula.already_matched if isinstance(formula, ForallFormula) else set()

        if ((isinstance(formula, ForallFormula) and negate)
                or (isinstance(formula, ExistsFormula) and not negate)):
            return ExistsFormula(
                formula.bound_variable, formula.in_variable, inner_formula, formula.bind_expression)
        else:
            return ForallFormula(
                formula.bound_variable, formula.in_variable, inner_formula, formula.bind_expression, already_matched)
    else:
        assert False, f"Unexpected formula type {type(formula).__name__}"


def convert_to_dnf(formula: Formula) -> Formula:
    assert (not isinstance(formula, NegatedFormula)
            or not isinstance(formula.args[0], PropositionalCombinator)), "Convert to NNF before converting to DNF"

    if isinstance(formula, ConjunctiveFormula):
        disjuncts_list = [split_disjunction(convert_to_dnf(arg)) for arg in formula.args]
        return reduce(
            lambda a, b: a | b,
            [left & right for left, right in itertools.product(*disjuncts_list)],
            SMTFormula(z3.BoolVal(False))
        )
    elif isinstance(formula, DisjunctiveFormula):
        return reduce(
            lambda a, b: a | b,
            [convert_to_dnf(subformula) for subformula in formula.args],
            SMTFormula(z3.BoolVal(False))
        )
    elif isinstance(formula, ForallFormula):
        return ForallFormula(
            formula.bound_variable,
            formula.in_variable,
            convert_to_dnf(formula.inner_formula),
            formula.bind_expression,
            formula.already_matched)
    elif isinstance(formula, ExistsFormula):
        return ExistsFormula(
            formula.bound_variable,
            formula.in_variable,
            convert_to_dnf(formula.inner_formula),
            formula.bind_expression)
    else:
        return formula


def ensure_unique_bound_variables(formula: Formula, used_names: Optional[Set[str]] = None) -> Formula:
    used_names: Set[str] = set() if used_names is None else used_names

    def fresh_vars(orig_vars: OrderedSet[BoundVariable]) -> Dict[BoundVariable, BoundVariable]:
        nonlocal used_names
        result: Dict[BoundVariable, BoundVariable] = {}

        for variable in orig_vars:
            if variable.name not in used_names:
                used_names.add(variable.name)
                result[variable] = variable
                continue

            idx = 0
            while f"{variable.name}_{idx}" in used_names:
                idx += 1

            new_name = f"{variable.name}_{idx}"
            used_names.add(new_name)
            result[variable] = BoundVariable(new_name, variable.n_type)

        return result

    if isinstance(formula, ForallFormula):
        formula = cast(ForallFormula, formula.substitute_variables(fresh_vars(formula.bound_variables())))
        return ForallFormula(
            formula.bound_variable,
            formula.in_variable,
            ensure_unique_bound_variables(formula.inner_formula, used_names),
            formula.bind_expression,
            formula.already_matched
        )
    elif isinstance(formula, ExistsFormula):
        formula = cast(ExistsFormula, formula.substitute_variables(fresh_vars(formula.bound_variables())))
        return ExistsFormula(
            formula.bound_variable,
            formula.in_variable,
            ensure_unique_bound_variables(formula.inner_formula, used_names),
            formula.bind_expression,
        )
    elif isinstance(formula, NegatedFormula):
        return NegatedFormula(ensure_unique_bound_variables(formula.args[0], used_names))
    elif isinstance(formula, ConjunctiveFormula):
        return reduce(lambda a, b: a & b, [ensure_unique_bound_variables(arg, used_names) for arg in formula.args])
    elif isinstance(formula, DisjunctiveFormula):
        return reduce(lambda a, b: a | b, [ensure_unique_bound_variables(arg, used_names) for arg in formula.args])
    else:
        return formula


def split_conjunction(formula: Formula) -> List[Formula]:
    if not type(formula) is ConjunctiveFormula:
        return [formula]
    else:
        formula: ConjunctiveFormula
        return [elem for arg in formula.args for elem in split_conjunction(arg)]


def split_disjunction(formula: Formula) -> List[Formula]:
    if not type(formula) is DisjunctiveFormula:
        return [formula]
    else:
        formula: DisjunctiveFormula
        return [elem for arg in formula.args for elem in split_disjunction(arg)]


class VariableManager:
    def __init__(self):
        self.placeholders: Dict[str, Variable] = {}
        self.variables: Dict[str, Variable] = {}

    def __var(self,
              name: str,
              n_type: Optional[str],
              constr: Optional[Callable[[str, Optional[str]], Variable]] = None) -> Variable:
        matching_variables = [var for var_name, var in self.variables.items() if var_name == name]
        if matching_variables:
            return matching_variables[0]

        if constr is not None and n_type:
            return self.variables.setdefault(name, constr(name, n_type))

        matching_placeholders = [var for var_name, var in self.placeholders.items() if var_name == name]
        if matching_placeholders:
            return matching_placeholders[0]

        assert constr is not None
        return self.placeholders.setdefault(name, constr(name, None))

    def const(self, name: str, n_type: Optional[str] = None) -> Constant:
        return cast(Constant, self.__var(name, n_type, Constant))

    def num_const(self, name: str) -> Constant:
        return cast(Constant, self.__var(name, Constant.NUMERIC_NTYPE, Constant))

    def bv(self, name: str, n_type: Optional[str] = None) -> BoundVariable:
        return cast(BoundVariable, self.__var(name, n_type, BoundVariable))

    def smt(self, formula: z3.BoolRef) -> SMTFormula:
        z3_symbols = get_symbols(formula)
        isla_variables = [self.__var(str(z3_symbol), None) for z3_symbol in z3_symbols]
        return SMTFormula(formula, *isla_variables)

    def create(self, formula: Formula) -> Formula:
        assert all(any(var_name == ph_name for var_name in self.variables)
                   for ph_name in self.placeholders)

        return formula.substitute_variables({
            ph_var: next(var for var_name, var in self.variables.items() if var_name == ph_name)
            for ph_name, ph_var in self.placeholders.items()
        })
