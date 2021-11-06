import copy
import itertools
import logging
import pickle
import re
from functools import reduce
from typing import Union, List, Optional, Dict, Tuple, Callable, cast, Generator, Set, Iterable

import z3
from fuzzingbook.GrammarFuzzer import tree_to_string, GrammarFuzzer
from fuzzingbook.Grammars import is_nonterminal, RE_NONTERMINAL
from fuzzingbook.Parser import EarleyParser, PEGParser
from grammar_graph import gg
from orderedset import OrderedSet

from input_constraints.concrete_syntax import ISLA_GRAMMAR
from input_constraints.helpers import get_symbols, z3_subst, is_valid, \
    replace_line_breaks, delete_unreachable, pop, z3_solve, powerset
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

    def is_numeric(self):
        return False

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


class BoundVariable(Variable):
    def __init__(self, name: str, n_type: str):
        """
        A variable bound by a quantifier.

        :param name: The name of the variable.
        :param n_type: The nonterminal type of the variable, e.g., "<var>".
        """
        super().__init__(name, n_type)

    def __add__(self, other: Union[str, 'BoundVariable']) -> 'BindExpression':
        assert isinstance(other, str) or isinstance(other, BoundVariable)
        return BindExpression(self, other)


class DummyVariable(BoundVariable):
    """A variable of which only its nonterminal is of interest (primarily for BindExpressions)."""

    cnt = 0

    def __init__(self, n_type: str):
        super().__init__(f"DUMMY_{DummyVariable.cnt}", n_type)
        DummyVariable.cnt += 1

    def __str__(self):
        return self.n_type


class DerivationTree:
    """Derivation trees are immutable!"""
    next_id: int = 0

    TRAVERSE_PREORDER = 0
    TRAVERSE_POSTORDER = 1

    def __init__(self, value: Union[str, Variable],
                 children: Optional[List['DerivationTree']] = None,
                 id: Optional[int] = None,
                 k_paths: Optional[Dict[int, Set[Tuple[gg.Node, ...]]]] = None):
        assert isinstance(value, str) or isinstance(value, Variable)
        assert not isinstance(value, Variable) or not children
        assert children is None or all(isinstance(child, DerivationTree) for child in children)

        self.value = value
        self.children = None if children is None else tuple(children)

        if id:
            self.id = id
        else:
            self.id = DerivationTree.next_id
            DerivationTree.next_id += 1

        if not children:
            self.__len = 1
        else:
            self.__len = sum([child.__len for child in children]) + 1

        self.__hash = None
        self.__structural_hash = None
        self.__k_paths: Dict[int, Set[Tuple[gg.Node, ...]]] = k_paths or {}

    def k_coverage(self, graph: gg.GrammarGraph, k: int) -> float:
        return len(self.k_paths(graph, k)) / len(graph.k_paths(k))

    def k_paths(self, graph: gg.GrammarGraph, k: int) -> Set[Tuple[gg.Node, ...]]:
        # TODO: Could reuse previously cached k-paths when expanding trees!
        if k not in self.__k_paths:
            self.__k_paths[k] = set(graph.k_paths_in_tree(self.to_parse_tree(), k))

        return self.__k_paths[k]

    def root_nonterminal(self) -> str:
        if isinstance(self.value, Variable):
            return self.value.n_type

        assert is_nonterminal(self.value)
        return self.value

    def num_children(self) -> int:
        return 0 if self.children is None else len(self.children)

    def is_open(self):
        if self.children is None:
            return True

        result = False

        def action(_, node: DerivationTree) -> bool:
            nonlocal result
            if node.children is None:
                result = True
                return True

            return False

        self.traverse(lambda p, n: None, action)

        return result

    def is_complete(self):
        return not self.is_open()

    def get_subtree(self, path: Path) -> 'DerivationTree':
        """Access a subtree based on `path` (a list of children numbers)"""
        if not path:
            return self

        return self.children[path[0]].get_subtree(path[1:])

    def is_valid_path(self, path: Path) -> bool:
        if not path:
            return True

        if not self.children or len(self.children) <= path[0]:
            return False

        return self.children[path[0]].is_valid_path(path[1:])

    def paths(self) -> List[Tuple[Path, 'DerivationTree']]:
        def action(path, node):
            result.append((path, node))

        result: List[Tuple[Path, 'DerivationTree']] = []
        self.traverse(action, kind=DerivationTree.TRAVERSE_PREORDER)
        return result

    def filter(self, f: Callable[['DerivationTree'], bool],
               enforce_unique: bool = False) -> List[Tuple[Path, 'DerivationTree']]:
        result: List[Tuple[Path, 'DerivationTree']] = []

        for path, subtree in self.paths():
            if f(subtree):
                result.append((path, subtree))

                if enforce_unique and len(result) > 1:
                    raise RuntimeError(f"Found searched-for element more than once in {self}")

        return result

    def find_node(self, node_or_id: Union['DerivationTree', int]) -> Optional[Path]:
        """Finds a node by its (assumed unique) ID. Returns the path relative to this node."""

        if isinstance(node_or_id, DerivationTree):
            node_or_id = node_or_id.id

        for path, node in self.paths():
            if node.id == node_or_id:
                return path

        return None

    def traverse(
            self,
            action: Callable[[Path, 'DerivationTree'], None],
            abort_condition: Callable[[Path, 'DerivationTree'], bool] = lambda p, n: False,
            kind: int = TRAVERSE_PREORDER,
            reverse: bool = False
    ) -> None:
        stack_1: List[Tuple[Path, DerivationTree]] = [((), self)]
        stack_2: List[Tuple[Path, DerivationTree]] = []

        if kind == DerivationTree.TRAVERSE_PREORDER:
            reverse = not reverse

        while stack_1:
            path, node = stack_1.pop()

            if abort_condition(path, node):
                return

            if kind == DerivationTree.TRAVERSE_POSTORDER:
                stack_2.append((path, node))

            if kind == DerivationTree.TRAVERSE_PREORDER:
                action(path, node)

            if node.children:
                iterator = reversed(node.children) if reverse else iter(node.children)

                for idx, child in enumerate(iterator):
                    new_path = path + ((len(node.children) - idx - 1) if reverse else idx,)
                    stack_1.append((new_path, child))

        if kind == DerivationTree.TRAVERSE_POSTORDER:
            while stack_2:
                action(*stack_2.pop())

    def nonterminals(self) -> Set[str]:
        result: Set[str] = set()

        def add_if_nonterminal(_: Path, tree: DerivationTree):
            if is_nonterminal(tree.value):
                result.add(tree.value)

        self.traverse(action=add_if_nonterminal)

        return result

    def reachable_symbols(self, grammar: Grammar, is_reachable: Callable[[str, str], bool]) -> Set[str]:
        return self.nonterminals() | {
            nonterminal for nonterminal in grammar
            if any(is_reachable(leaf[1].value, nonterminal)
                   for leaf in self.leaves()
                   if is_nonterminal(leaf[1].value))
        }

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
        assert skip_children or list(self.paths())[-1][0] == path
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

    def leaves(self) -> Generator[Tuple[Path, 'DerivationTree'], None, None]:
        return ((path, sub_tree)
                for path, sub_tree in self.paths()
                if not sub_tree.children)

    def open_leaves(self) -> Generator[Tuple[Path, 'DerivationTree'], None, None]:
        return ((path, sub_tree)
                for path, sub_tree in self.paths()
                if sub_tree.children is None)

    def depth(self) -> int:
        if not self.children:
            return 1
        return 1 + max(child.depth() for child in self.children)

    def new_ids(self) -> 'DerivationTree':
        return DerivationTree(
            self.value,
            None if self.children is None
            else [child.new_ids() for child in self.children])

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

    def substitute(self, subst_map: Dict[Union[Variable, 'DerivationTree'], 'DerivationTree']) -> 'DerivationTree':
        if self in subst_map:
            return subst_map[self]

        if self.children is None:
            return self

        return DerivationTree(
            self.value,
            [child.substitute(subst_map) for child in self.children],
            id=self.id)

    def is_prefix(self, other: 'DerivationTree') -> bool:
        if len(self) > len(other):
            return False

        if self.value != other.value:
            return False

        if not self.children:
            return self.children is None or (not other.children and other.children is not None)

        if not other.children:
            return False

        assert self.children
        assert other.children

        if len(self.children) != len(other.children):
            return False

        return all(self.children[idx].is_prefix(other.children[idx])
                   for idx, _ in enumerate(self.children))

    def is_potential_prefix(self, other: 'DerivationTree') -> bool:
        """Returns `True` iff this the `other` tree can be extended such that this tree
        is a prefix of the `other` tree."""
        if self.value != other.value:
            return False

        if not self.children:
            return self.children is None or (not other.children and other.children is not None)

        if not other.children:
            return other.children is None

        assert self.children
        assert other.children

        if len(self.children) != len(other.children):
            return False

        return all(self.children[idx].is_potential_prefix(other.children[idx])
                   for idx, _ in enumerate(self.children))

    @staticmethod
    def from_parse_tree(tree: ParseTree):
        node, children = tree
        return DerivationTree(node,
                              None if children is None
                              else [DerivationTree.from_parse_tree(child) for child in children])

    def to_parse_tree(self) -> ParseTree:
        return self.value, None if self.children is None else [child.to_parse_tree() for child in self.children]

    def __iter__(self):
        # Allows tuple unpacking: node, children = tree
        yield self.value
        yield self.children

    def compute_hash_iteratively(self, structural=False):
        # We perform an iterative reverse post-order depth-first traversal and use a stack
        # to store intermediate results from lower levels.

        stack: List[int] = []

        def action(_, node: DerivationTree) -> None:
            if node.children is None:
                node_hash = hash(node.value) if structural else hash((node.value, node.id))
            else:
                children_values = []
                for _ in range(len(node.children)):
                    children_values.append(stack.pop())
                node_hash = hash(((node.value,) if structural else (node.value, node.id)) + tuple(children_values))

            stack.append(node_hash)
            if structural:
                node.__structural_hash = node_hash
            else:
                node.__hash = node_hash

        self.traverse(action, kind=DerivationTree.TRAVERSE_POSTORDER, reverse=True)

        assert len(stack) == 1
        return stack.pop()

    def __hash__(self):
        if self.__hash is not None:
            assert self.__hash == self.compute_hash_iteratively()
            return self.__hash

        self.__hash = self.compute_hash_iteratively()
        return self.__hash

    def structural_hash(self):
        if self.__structural_hash is not None:
            assert self.__structural_hash == self.compute_hash_iteratively(structural=True)
            return self.__structural_hash

        self.__structural_hash = self.compute_hash_iteratively(structural=True)
        return self.__structural_hash

    def structurally_equal(self, other: 'DerivationTree'):
        if not isinstance(other, DerivationTree):
            return False

        if (self.value != other.value
                or (self.children is None and other.children is not None)
                or (other.children is None and self.children is not None)):
            return False

        if self.children is None:
            return True

        if len(self.children) != len(other.children):
            return False

        return all(self.children[idx].structurally_equal(other.children[idx])
                   for idx in range(len(self.children)))

    def __eq__(self, other):
        """
        Equality takes the randomly assigned ID into account! So trees with the same structure
        might not be equal.
        """
        return (isinstance(other, DerivationTree)
                and self.value == other.value
                and self.children == other.children
                and self.id == other.id)

    def __repr__(self):
        return f"DerivationTree({repr(self.value)}, {repr(self.children)})"

    def to_string(self, show_open_leaves: bool = False) -> str:
        result = []
        stack = [self]

        while stack:
            node = stack.pop(0)
            symbol = node.value
            children = node.children

            if not children:
                if children is not None:
                    result.append("" if is_nonterminal(symbol) else symbol)
                else:
                    result.append(symbol if show_open_leaves else "")

                continue

            for child in reversed(children):
                stack.insert(0, child)

        return ''.join(result)

    def __str__(self) -> str:
        return self.to_string(show_open_leaves=True)


class BindExpression:
    def __init__(self, *bound_elements: Union[str, BoundVariable, List[str]]):
        self.bound_elements: List[Union[BoundVariable, List[Union[BoundVariable]]]] = []
        for bound_elem in bound_elements:
            if isinstance(bound_elem, BoundVariable):
                self.bound_elements.append(bound_elem)
                continue

            if isinstance(bound_elem, list):
                if len(bound_elem) > 1 or not isinstance(bound_elem[0], str):
                    self.bound_elements.append(bound_elem)
                    continue

                self.bound_elements.append([
                    DummyVariable(token)
                    for token in re.split(RE_NONTERMINAL, bound_elem[0])
                    if token
                ])
                continue

            self.bound_elements.extend([
                DummyVariable(token)
                for token in re.split(RE_NONTERMINAL, bound_elem)
                if token
            ])

        self.prefixes: Dict[str, List[Tuple[DerivationTree, Dict[BoundVariable, Path]]]] = {}

    def __add__(self, other: Union[str, 'BoundVariable']) -> 'BindExpression':
        assert type(other) == str or type(other) == BoundVariable
        result = BindExpression(*self.bound_elements)
        result.bound_elements.append(other)
        return result

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return BindExpression(*[elem if isinstance(elem, list)
                                else subst_map.get(elem, elem)
                                for elem in self.bound_elements])

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        # Not isinstance(var, BoundVariable) since we want to exclude dummy variables
        return OrderedSet([var for var in self.bound_elements if type(var) is BoundVariable])

    def to_tree_prefix(self, in_nonterminal: str, grammar: Grammar) -> \
            List[Tuple[DerivationTree, Dict[BoundVariable, Path]]]:
        if in_nonterminal in self.prefixes:
            cached = self.prefixes[in_nonterminal]
            return [(opt[0].new_ids(), opt[1]) for opt in cached]

        fuzzer = GrammarFuzzer(grammar)

        result: List[Tuple[DerivationTree, Dict[BoundVariable, Path]]] = []

        for bound_elements in self.flatten_bound_elements():
            placeholder_map: Dict[Union[str, BoundVariable], str] = {}

            for bound_element in bound_elements:
                if isinstance(bound_element, str):
                    placeholder_map[bound_element] = bound_element
                elif not is_nonterminal(bound_element.n_type):
                    placeholder_map[bound_element] = bound_element.n_type
                else:
                    ph_candidate = fuzzer.expand_tree((bound_element.n_type, None))
                    placeholder_map[bound_element] = tree_to_string(ph_candidate)

            inp = "".join(list(map(lambda elem: placeholder_map[elem], bound_elements)))

            subgrammar = copy.deepcopy(grammar)
            subgrammar["<start>"] = [in_nonterminal]
            delete_unreachable(subgrammar)

            parser = EarleyParser(subgrammar)
            tree = DerivationTree.from_parse_tree(list(parser.parse(inp))[0][1][0])

            positions: Dict[BoundVariable, Path] = {}
            curr_path = tuple()
            while bound_elements:
                curr_subtree = tree.get_subtree(curr_path)
                curr_bound_elem = bound_elements[0]

                if isinstance(curr_bound_elem, str):
                    if str(curr_subtree) == curr_bound_elem:
                        bound_elements = bound_elements[1:]

                if isinstance(curr_bound_elem, Variable) and curr_bound_elem.n_type == curr_subtree.value:
                    positions[bound_elements[0]] = curr_path
                    tree = tree.replace_path(curr_path, DerivationTree(
                        curr_subtree.value, None if is_nonterminal(curr_bound_elem.n_type) else ()))
                    bound_elements = bound_elements[1:]

                curr_path = tree.next_path(curr_path)
                if curr_path is None:
                    break

            result.append((tree, positions))

        self.prefixes[in_nonterminal] = result
        return result

    def flatten_bound_elements(self):
        """Returns all possible bound elements lists where each contained optional either has
        been chosen or removed. If this BindExpression has no optionals, the returned list is
        a singleton."""
        bound_elements_combinations: List[List[BoundVariable]] = []

        # Consider all possible on/off combinations for optional elements
        optionals = [elem for elem in self.bound_elements if isinstance(elem, list)]
        if optionals:
            for combination in powerset(optionals):
                # Inline all chosen, remove all not chosen optionals
                bound_elements = []
                for bound_element in self.bound_elements:
                    if not isinstance(bound_element, list):
                        bound_elements.append(bound_element)
                        continue

                    if bound_element in combination:
                        bound_elements.extend(bound_element)

                bound_elements_combinations.append(bound_elements)

        return bound_elements_combinations

    def match(self, tree: DerivationTree) -> Optional[Dict[BoundVariable, Tuple[Path, DerivationTree]]]:
        result: Dict[BoundVariable, Tuple[Path, DerivationTree]] = {}

        for bound_variables in reversed(self.flatten_bound_elements()):
            subtrees = list(tree.paths())
            curr_elem = bound_variables.pop(0)

            while subtrees and curr_elem:
                path, subtree = pop(subtrees)

                if subtree.value == curr_elem.n_type:
                    result[curr_elem] = (path, subtree)
                    curr_elem = pop(bound_variables, default=None)

                    subtrees = [(p, s) for p, s in subtrees
                                if not p[:len(path)] == path]

            if not subtrees and not curr_elem:
                return result

        return None

    def __repr__(self):
        return f'BindExpression({", ".join(map(repr, self.bound_elements))})'

    def __str__(self):
        return ''.join(map(
            lambda e: f'{str(e)}'
            if isinstance(e, str)
            else ("[" + "".join(map(str, e)) + "]") if isinstance(e, list)
            else str(e), self.bound_elements))

    def __hash__(self):
        return hash(tuple([tuple(e) if isinstance(e, list) else e for e in self.bound_elements]))

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

    def visit_introduce_numeric_constant_formula(self, formula: 'IntroduceNumericConstantFormula'):
        pass


class Formula:
    # def __getstate__(self):
    #     return {f: pickle.dumps(v) for f, v in self.__dict__.items()} | {"cls": type(self).__name__}
    #
    # def __setstate__(self, state):
    #     pass

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

    def accept(self, visitor: FormulaVisitor):
        raise NotImplementedError()

    def __hash__(self):
        raise NotImplementedError()

    def __eq__(self, other):
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


class StructuralPredicate:
    def __init__(self, name: str, arity: int, eval_fun: Callable[[DerivationTree, Union[Path, str], ...], bool]):
        self.name = name
        self.arity = arity
        self.eval_fun = eval_fun

    def evaluate(self, context_tree: DerivationTree, *instantiations: Union[Path, str]):
        return self.eval_fun(context_tree, *instantiations)

    def __eq__(self, other):
        return type(other) is StructuralPredicate and (self.name, self.arity) == (other.name, other.arity)

    def __hash__(self):
        return hash((self.name, self.arity))

    def __repr__(self):
        return f"Predicate({self.name}, {self.arity})"

    def __str__(self):
        return self.name


class StructuralPredicateFormula(Formula):
    def __init__(self, predicate: StructuralPredicate, *args: Union[str, DerivationTree]):
        assert len(args) == predicate.arity
        self.predicate = predicate
        self.args: List[Union[Variable, DerivationTree]] = list(args)

    def evaluate(self, context_tree: DerivationTree) -> bool:
        args_with_paths: List[Union[str, Tuple[Path, DerivationTree]]] = \
            [arg if isinstance(arg, str) else
             (context_tree.find_node(arg), arg)
             for arg in self.args]

        if any(arg[0] is None for arg in args_with_paths if isinstance(arg, tuple)):
            raise RuntimeError(
                "Could not find paths for all predicate arguments in context tree:\n" +
                str([str(tree) for path, tree in args_with_paths if path is None]) +
                f"\nContext tree:\n{context_tree}")

        return self.predicate.eval_fun(
            context_tree, *[arg if isinstance(arg, str) else arg[0] for arg in args_with_paths])

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return StructuralPredicateFormula(
            self.predicate,
            *[arg if arg not in subst_map else subst_map[arg] for arg in self.args])

    def substitute_expressions(self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]) -> Formula:
        new_args = []
        for arg in self.args:
            if isinstance(arg, Variable):
                if arg in subst_map:
                    new_args.append(subst_map[arg])
                else:
                    new_args.append(arg)
                continue

            if isinstance(arg, str):
                new_args.append(arg)
                continue

            assert isinstance(arg, DerivationTree)
            tree: DerivationTree = arg
            if tree in subst_map:
                new_args.append(subst_map[tree])
                continue

            new_args.append(tree.substitute({k: v for k, v in subst_map.items()}))

        return StructuralPredicateFormula(self.predicate, *new_args)

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return OrderedSet([])

    def free_variables(self) -> OrderedSet[Variable]:
        return OrderedSet([arg for arg in self.args if isinstance(arg, Variable)])

    def tree_arguments(self) -> OrderedSet[DerivationTree]:
        return OrderedSet([arg for arg in self.args if isinstance(arg, DerivationTree)])

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_predicate_formula(self)

    def __hash__(self):
        return hash((type(self).__name__, self.predicate, tuple(self.args)))

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


SemPredArg = Union[DerivationTree, Constant, str, int]


class SemanticPredicate:
    def __init__(
            self, name: str, arity: int,
            eval_fun: Callable[[Union[DerivationTree, Constant, str, int], ...], SemPredEvalResult],
            binds_tree: Optional[Union[Callable[[DerivationTree, Tuple[SemPredArg, ...]], bool], bool]] = None):
        """
        :param name:
        :param arity:
        :param eval_fun:
        :param binds_tree: Given a derivation tree and the arguments for the predicate, this function tests whether
        the tree is bound by the predicate formula. The effect of this is that bound trees cannot be freely expanded,
        similarly to nonterminals bound by a universal quantifier. A semantic predicate may also not bind any of its
        arguments; in that case, we can freely instantiate the arguments and then ask the predicate for a "fix" if
        the instantiation is non-conformant. Most semantic predicates do not bind their arguments. Pass nothing or
        True for this parameter for predicates binding all trees in all their arguments. Pass False for predicates
        binding no trees at all. Pass a custom function for anything special.
        """
        self.name = name
        self.arity = arity
        self.eval_fun = eval_fun

        if binds_tree is not None and binds_tree is not True:
            if binds_tree is False:
                self.binds_tree = lambda tree, args: False
            else:
                self.binds_tree = binds_tree
        else:
            self.binds_tree = (
                lambda tree, args:
                any(tree_arg.find_node(tree) is not None
                    for tree_arg in args
                    if isinstance(tree_arg, DerivationTree)))

    def evaluate(self, *instantiations: SemPredArg):
        return self.eval_fun(*instantiations)

    def __eq__(self, other):
        return type(other) is SemanticPredicate and (self.name, self.arity) == (other.name, other.arity)

    def __hash__(self):
        return hash((self.name, self.arity))

    def __repr__(self):
        return f"SemanticPredicate({self.name}, {self.arity})"

    def __str__(self):
        return self.name


class SemanticPredicateFormula(Formula):
    def __init__(self, predicate: SemanticPredicate, *args: SemPredArg, order: int = 0):
        assert len(args) == predicate.arity
        self.predicate = predicate
        self.args: Tuple[SemPredArg, ...] = args
        self.order = order

    def evaluate(self) -> SemPredEvalResult:
        return self.predicate.eval_fun(*self.args)

    def binds_tree(self, tree: DerivationTree) -> bool:
        return self.predicate.binds_tree(tree, self.args)

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return SemanticPredicateFormula(self.predicate,
                                        *[arg if arg not in subst_map
                                          else subst_map[arg] for arg in self.args], order=self.order)

    def substitute_expressions(self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]) -> Formula:
        new_args = []
        for arg in self.args:
            if isinstance(arg, str) or isinstance(arg, int):
                new_args.append(arg)
                continue

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

        return SemanticPredicateFormula(self.predicate, *new_args, order=self.order)

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return OrderedSet([])

    def free_variables(self) -> OrderedSet[Variable]:
        return OrderedSet([arg for arg in self.args if isinstance(arg, Variable)])

    def tree_arguments(self) -> OrderedSet[DerivationTree]:
        return OrderedSet([arg for arg in self.args if isinstance(arg, DerivationTree)])

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_semantic_predicate_formula(self)

    def __hash__(self):
        return hash((type(self).__name__, self.predicate, self.args))

    def __eq__(self, other):
        return (type(self) is type(other)
                and self.predicate == other.predicate
                and self.args == other.args)

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
        return hash((type(self).__name__, self.args))

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
        return hash((type(self).__name__, self.args))

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
        return hash((type(self).__name__, self.args))

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
        return hash((type(self).__name__, self.args))

    def __eq__(self, other):
        return split_disjunction(self) == split_disjunction(other)

    def __str__(self):
        return f"({' ∨ '.join(map(str, self.args))})"


class SMTFormula(Formula):
    def __init__(self, formula: z3.BoolRef, *free_variables: Variable,
                 instantiated_variables: Optional[OrderedSet[Variable]] = None,
                 substitutions: Optional[Dict[Variable, DerivationTree]] = None,
                 auto_eval: bool = True):
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

        # When substituting expressions, the formula is automatically evaluated if this flag
        # is set to True and all substituted expressions are closed trees, i.e., the formula
        # is ground. Deactivate only for special purposes, e.g., vacuity checking.
        self.auto_eval = auto_eval

    def __getstate__(self) -> Dict[str, bytes]:
        result: Dict[str, bytes] = {f: pickle.dumps(v) for f, v in self.__dict__.items() if f != "formula"}
        result["formula"] = self.formula.sexpr().encode("utf-8")
        return result

    def __setstate__(self, state: Dict[str, bytes]) -> None:
        inst = {f: pickle.loads(v) for f, v in state.items() if f != "formula"}
        free_variables: OrderedSet[Variable] = inst["free_variables_"]
        instantiated_variables: OrderedSet[Variable] = inst["instantiated_variables"]

        z3_constr = z3.parse_smt2_string(
            f"(assert {state['formula'].decode('utf-8')})",
            decls={var.name: z3.String(var.name) for var in free_variables | instantiated_variables})[0]

        self.__dict__ = inst
        self.formula = z3_constr

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        new_smt_formula = z3_subst(self.formula, {v1.to_smt(): v2.to_smt() for v1, v2 in subst_map.items()})

        new_free_variables = [variable if variable not in subst_map
                              else subst_map[variable]
                              for variable in self.free_variables_]

        assert all(inst_var not in subst_map for inst_var in self.instantiated_variables)
        assert all(inst_var not in subst_map for inst_var in self.substitutions.keys())

        return SMTFormula(cast(z3.BoolRef, new_smt_formula),
                          *new_free_variables,
                          instantiated_variables=self.instantiated_variables,
                          substitutions=self.substitutions,
                          auto_eval=self.auto_eval)

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

        if self.auto_eval and len(new_free_variables) + len(new_instantiated_variables) == 0:
            # Formula is ground, we can evaluate it!
            return SMTFormula(z3.BoolVal(is_valid(new_smt_formula)))

        return SMTFormula(cast(z3.BoolRef, new_smt_formula), *new_free_variables,
                          instantiated_variables=new_instantiated_variables,
                          substitutions=new_substitutions,
                          auto_eval=self.auto_eval)

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
        return (type(self) == type(other)
                and z3.is_true(z3.simplify(self.formula == other.formula))
                and self.substitutions == other.substitutions)

    def __hash__(self):
        return hash((self.formula, tuple(self.substitutions.items())))


class IntroduceNumericConstantFormula(Formula):
    def __init__(self, bound_variable: BoundVariable, inner_formula: Formula):
        self.bound_variable = bound_variable
        self.inner_formula = inner_formula

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        """Non-recursive: Only non-empty for quantified formulas"""
        return OrderedSet([self.bound_variable])

    def free_variables(self) -> OrderedSet[Variable]:
        """Recursive."""
        return self.inner_formula.free_variables().difference(self.bound_variables())

    def tree_arguments(self) -> OrderedSet[DerivationTree]:
        return self.inner_formula.tree_arguments()

    def substitute_variables(self, subst_map: Dict[Variable, Variable]) -> 'Formula':
        return IntroduceNumericConstantFormula(
            subst_map.get(self.bound_variable, self.bound_variable),
            self.inner_formula.substitute_variables(subst_map))

    def substitute_expressions(self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]) -> 'Formula':
        assert self.bound_variable not in subst_map
        return IntroduceNumericConstantFormula(
            self.bound_variable,
            self.inner_formula.substitute_expressions(subst_map))

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_introduce_numeric_constant_formula(self)

    def __hash__(self):
        return hash((self.bound_variable, self.inner_formula))

    def __eq__(self, other):
        return (isinstance(other, IntroduceNumericConstantFormula)
                and self.bound_variable == other.bound_variable
                and self.inner_formula == other.inner_formula)

    def __str__(self):
        return f"num {self.bound_variable.name}: {str(self.inner_formula)}"

    def __repr__(self):
        return f"IntroduceNumericConstantFormula({repr(self.bound_variable)}, {repr(self.inner_formula)})"


class QuantifiedFormula(Formula):
    def __init__(self,
                 bound_variable: Union[BoundVariable, str],
                 in_variable: Union[Variable, DerivationTree],
                 inner_formula: Formula,
                 bind_expression: Optional[Union[BindExpression, BoundVariable]] = None):
        assert inner_formula is not None
        assert isinstance(bound_variable, BoundVariable) or bind_expression is not None

        if isinstance(bound_variable, str):
            assert is_nonterminal(bound_variable)
            self.bound_variable = DummyVariable(bound_variable)
        else:
            self.bound_variable = bound_variable

        self.in_variable = in_variable
        self.inner_formula = inner_formula

        if isinstance(bind_expression, BoundVariable):
            self.bind_expression = BindExpression(bind_expression)
        else:
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

    def is_already_matched(self, tree: DerivationTree) -> bool:
        return False

    def __repr__(self):
        return f'{type(self).__name__}({repr(self.bound_variable)}, {repr(self.in_variable)}, ' \
               f'{repr(self.inner_formula)}{"" if self.bind_expression is None else ", " + repr(self.bind_expression)})'

    def __hash__(self):
        return hash((
            type(self).__name__,
            self.bound_variable,
            self.in_variable,
            self.inner_formula,
            self.bind_expression or 0
        ))

    def __eq__(self, other):
        return type(self) == type(other) and \
               (self.bound_variable, self.in_variable, self.inner_formula, self.bind_expression) == \
               (other.bound_variable, other.in_variable, other.inner_formula, other.bind_expression)


class ForallFormula(QuantifiedFormula):
    __next_id = 0

    def __init__(self,
                 bound_variable: Union[BoundVariable, str],
                 in_variable: Union[Variable, DerivationTree],
                 inner_formula: Formula,
                 bind_expression: Optional[BindExpression] = None,
                 already_matched: Optional[Set[int]] = None,
                 id: Optional[int] = None):
        super().__init__(bound_variable, in_variable, inner_formula, bind_expression)
        self.already_matched: Set[int] = copy.deepcopy(already_matched) or set()

        # The id field is used by eliminate_quantifiers to avoid counting universal
        # formulas twice when checking for vacuous satisfaction.
        if id is None:
            self.id = ForallFormula.__next_id
            ForallFormula.__next_id += 1
        else:
            self.id = id

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        assert not self.already_matched

        return ForallFormula(
            self.bound_variable if self.bound_variable not in subst_map else subst_map[self.bound_variable],
            self.in_variable if self.in_variable not in subst_map else subst_map[self.in_variable],
            self.inner_formula.substitute_variables(subst_map),
            None if not self.bind_expression else self.bind_expression.substitute_variables(subst_map),
            self.already_matched,
            id=self.id
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
            self.already_matched,
            id=self.id
        )

    def add_already_matched(self, trees: Union[DerivationTree, Iterable[DerivationTree]]) -> 'ForallFormula':
        return ForallFormula(
            self.bound_variable,
            self.in_variable,
            self.inner_formula,
            self.bind_expression,
            self.already_matched | ({trees.id} if isinstance(trees, DerivationTree) else {tree.id for tree in trees}),
            id=self.id
        )

    def is_already_matched(self, tree: DerivationTree) -> bool:
        return tree.id in self.already_matched

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_forall_formula(self)
        self.inner_formula.accept(visitor)

    def __str__(self):
        quote = '"'
        return f'∀ {"" if not self.bind_expression else quote + str(self.bind_expression) + quote + " = "}' \
               f'{str(self.bound_variable)} ∈ {replace_line_breaks(str(self.in_variable))}: ({str(self.inner_formula)})'


class ExistsFormula(QuantifiedFormula):
    def __init__(self,
                 bound_variable: Union[BoundVariable, str],
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
               f'{str(self.bound_variable)} ∈ {replace_line_breaks(str(self.in_variable))}: ({str(self.inner_formula)})'


class VariablesCollector(FormulaVisitor):
    def __init__(self):
        self.result: OrderedSet[Variable] = OrderedSet()

    @staticmethod
    def collect(formula: Formula) -> OrderedSet[Variable]:
        c = VariablesCollector()
        formula.accept(c)
        return c.result

    def visit_exists_formula(self, formula: ExistsFormula):
        self.visit_quantified_formula(formula)

    def visit_forall_formula(self, formula: ForallFormula):
        self.visit_quantified_formula(formula)

    def visit_quantified_formula(self, formula: QuantifiedFormula):
        if isinstance(formula.in_variable, Variable):
            self.result.add(formula.in_variable)
        self.result.add(formula.bound_variable)
        if formula.bind_expression is not None:
            self.result.update(formula.bind_expression.bound_variables())

    def visit_introduce_numeric_constant_formula(self, formula: IntroduceNumericConstantFormula):
        self.result.add(formula.bound_variable)

    def visit_predicate_formula(self, formula: StructuralPredicateFormula):
        self.result.update([arg for arg in formula.args if isinstance(arg, Variable)])

    def visit_semantic_predicate_formula(self, formula: SemanticPredicateFormula):
        self.result.update([arg for arg in formula.args if isinstance(arg, Variable)])

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

    def visit_introduce_numeric_constant_formula(self, formula: IntroduceNumericConstantFormula):
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

    if isinstance(formula, IntroduceNumericConstantFormula):
        if formula.bound_variables().intersection(bound_vars):
            return False
        if any(free_var not in bound_vars for free_var in formula.free_variables() if type(free_var) is BoundVariable):
            return False

        return well_formed(
            formula.inner_formula,
            bound_vars | formula.bound_variables(),
            in_expr_vars,
            bound_by_smt
        )
    elif isinstance(formula, QuantifiedFormula):
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
        raise NotImplementedError(f"Unsupported formula type {type(formula).__name__}")


class ThreeValuedTruth:
    FALSE = 0
    TRUE = 1
    UNKNOWN = 2

    def __init__(self, val: int):
        assert 0 <= val <= 2
        self.val = val

    def __eq__(self, other):
        return self.val == other.val

    def __hash__(self):
        return self.val

    def to_bool(self) -> bool:
        assert self.val != ThreeValuedTruth.UNKNOWN
        return bool(self.val)

    def __bool__(self):
        return self.to_bool()

    def is_false(self):
        return self.val == ThreeValuedTruth.FALSE

    def is_true(self):
        return self.val == ThreeValuedTruth.TRUE

    def is_unknown(self):
        return self.val == ThreeValuedTruth.UNKNOWN

    @staticmethod
    def from_bool(b: bool) -> 'ThreeValuedTruth':
        return ThreeValuedTruth(int(b))

    @staticmethod
    def all(args: Iterable['ThreeValuedTruth']) -> 'ThreeValuedTruth':
        args = list(args)
        if any(elem.is_false() for elem in args):
            return ThreeValuedTruth.false()
        if any(elem.is_unknown() for elem in args):
            return ThreeValuedTruth.unknown()
        return ThreeValuedTruth.true()

    @staticmethod
    def any(args: Iterable['ThreeValuedTruth']) -> 'ThreeValuedTruth':
        args = list(args)
        if any(elem.is_true() for elem in args):
            return ThreeValuedTruth.true()
        if any(elem.is_unknown() for elem in args):
            return ThreeValuedTruth.unknown()
        return ThreeValuedTruth.false()

    @staticmethod
    def not_(arg: 'ThreeValuedTruth') -> 'ThreeValuedTruth':
        if arg.is_true():
            return ThreeValuedTruth.false()
        if arg.is_false():
            return ThreeValuedTruth.true()
        return ThreeValuedTruth.unknown()

    @staticmethod
    def true():
        return ThreeValuedTruth(ThreeValuedTruth.TRUE)

    @staticmethod
    def false():
        return ThreeValuedTruth(ThreeValuedTruth.FALSE)

    @staticmethod
    def unknown():
        return ThreeValuedTruth(ThreeValuedTruth.UNKNOWN)

    def __repr__(self):
        return f"ThreeValuedTruth({self.val})"

    def __str__(self):
        return ("TRUE" if self.is_true() else
                "FALSE" if self.is_false() else
                "UNKNOWN")


def get_toplevel_quantified_formulas(formula: Formula) -> \
        List[Union[QuantifiedFormula, IntroduceNumericConstantFormula]]:
    if isinstance(formula, QuantifiedFormula) or isinstance(formula, IntroduceNumericConstantFormula):
        return [formula]
    elif isinstance(formula, PropositionalCombinator):
        return [f for arg in formula.args for f in get_toplevel_quantified_formulas(arg)]
    else:
        return []


def eliminate_quantifiers(
        formula: Formula,
        vacuously_satisfied: Optional[Set[ForallFormula]] = None,
        grammar: Optional[Grammar] = None,
        graph: Optional[gg.GrammarGraph] = None,
        reachable: Optional[Callable[[str, str], bool]] = None,
        non_vacuously_satisfied: Optional[Set[ForallFormula]] = None) -> List[Formula]:
    def in_vacuous(formula: ForallFormula) -> bool:
        return any(f.id == formula.id for f in vacuously_satisfied)

    def in_non_vacuous(formula: ForallFormula) -> bool:
        return any(f.id == formula.id for f in non_vacuously_satisfied)

    assert vacuously_satisfied is None or grammar is not None
    if vacuously_satisfied is not None:
        if non_vacuously_satisfied is None:
            non_vacuously_satisfied = set()

        if graph is None:
            graph = gg.GrammarGraph.from_grammar(grammar)

        vacuously_satisfied.difference_update({f for f in vacuously_satisfied if in_non_vacuous(f)})

    if grammar is not None and reachable is None:
        reachable = lambda n1, n2: graph.reachable(graph.get_node(n1), graph.get_node(n2))

    quantified_formulas = get_toplevel_quantified_formulas(formula)
    universal_formulas = [f for f in quantified_formulas if isinstance(f, ForallFormula)]

    if universal_formulas:
        for universal_formula in universal_formulas:
            assert isinstance(universal_formula.in_variable, DerivationTree)
            matches = [
                {var: tree for var, (_, tree) in match.items()}
                for match in matches_for_quantified_formula(universal_formula, universal_formula.in_variable)]
            instantiations = [
                universal_formula.inner_formula.substitute_expressions(match)
                for match in matches]

            if instantiations:
                formula = replace_formula(
                    formula,
                    universal_formula,
                    reduce(lambda f1, f2: f1 & f2, instantiations))

                if vacuously_satisfied is not None:
                    if in_vacuous(universal_formula):
                        vacuously_satisfied.difference_update(
                            {f for f in vacuously_satisfied if f.id == universal_formula.id})
                    if not in_non_vacuous(universal_formula):
                        non_vacuously_satisfied.add(universal_formula)
            else:
                formula = replace_formula(formula, universal_formula, SMTFormula(z3.BoolVal(True)))

                if (vacuously_satisfied is not None and
                        not in_vacuous(universal_formula) and
                        not in_non_vacuous(universal_formula)):

                    # Check if there is still a chance to match the quantifier
                    if any(quantified_formula_might_match(
                            universal_formula,
                            leaf_path,
                            universal_formula.in_variable,
                            grammar,
                            reachable)
                           for leaf_path, leaf_node in universal_formula.in_variable.open_leaves()):
                        continue

                    vacuously_satisfied.add(universal_formula)
                    vacuously_satisfied.update(
                        cast(List[ForallFormula],
                             FilterVisitor(lambda f: isinstance(f, ForallFormula))
                             .collect(universal_formula.inner_formula)))

        return eliminate_quantifiers(formula, vacuously_satisfied, grammar, graph, reachable, non_vacuously_satisfied)

    existential_formulas = [f for f in quantified_formulas if isinstance(f, ExistsFormula)]
    if existential_formulas:
        results: List[Formula] = [formula]
        for existential_formula in existential_formulas:
            assert isinstance(existential_formula.in_variable, DerivationTree)
            matches = [
                {var: tree for var, (_, tree) in match.items()}
                for match in matches_for_quantified_formula(existential_formula, existential_formula.in_variable)]
            instantiations = [
                existential_formula.inner_formula.substitute_expressions(match)
                for match in matches]
            if instantiations:
                results = [
                    replace_formula(result, existential_formula, instantiation)
                    for instantiation in instantiations
                    for result in results]
            else:
                results = [
                    replace_formula(result, existential_formula, SMTFormula(z3.BoolVal(False)))
                    for result in results]

        return list(
            {f for r in results
             for f in eliminate_quantifiers(
                r, vacuously_satisfied, grammar, graph, reachable, non_vacuously_satisfied)})

    intro_const_formulas = [f for f in quantified_formulas if isinstance(f, IntroduceNumericConstantFormula)]
    if intro_const_formulas:
        used_vars = set(VariablesCollector.collect(formula))
        for intro_const_formula in intro_const_formulas:
            fresh = fresh_constant(
                used_vars,
                Constant(intro_const_formula.bound_variable.name, intro_const_formula.bound_variable.n_type))
            formula = replace_formula(
                formula,
                intro_const_formula,
                intro_const_formula.inner_formula.substitute_variables({intro_const_formula.bound_variable: fresh}))

        return eliminate_quantifiers(formula, vacuously_satisfied, grammar, graph, reachable, non_vacuously_satisfied)

    return [formula]


def evaluate_clause(clause: List[Formula], reference_tree: DerivationTree) -> ThreeValuedTruth:
    # Inside the clause, only (possibly negated) predicate formulas and (not negated) SMT formulas should appear.
    assert all(
        isinstance(f, SMTFormula) or
        isinstance(f, SemanticPredicateFormula) or
        isinstance(f, StructuralPredicateFormula) or
        (isinstance(f, NegatedFormula) and
         (isinstance(f.args[0], StructuralPredicateFormula) or
          isinstance(f.args[0], SemanticPredicateFormula)))
        for f in clause)

    # Eliminate structural predicate formulas
    for idx, formula in enumerate(clause):
        if (not isinstance(formula, StructuralPredicateFormula) and
                not (isinstance(formula, NegatedFormula)
                     and isinstance(formula.args[0], StructuralPredicateFormula))):
            continue

        sf: StructuralPredicateFormula = (
            formula if isinstance(formula, StructuralPredicateFormula) else formula.args[0])
        args: List[Union[str, Path]] = [
            reference_tree.find_node(arg)
            if isinstance(arg, DerivationTree)
            else arg
            for arg in sf.args]
        result = sf.predicate.evaluate(reference_tree, *args)

        if ((not result and isinstance(formula, StructuralPredicateFormula)) or
                (result and isinstance(formula, NegatedFormula))):
            return ThreeValuedTruth.false()

        clause[idx] = SMTFormula(z3.BoolVal(True))

    # Eliminate semantic predicate formulas
    for idx, formula in enumerate(clause):
        if (not isinstance(formula, SemanticPredicateFormula) and
                not (isinstance(formula, NegatedFormula)
                     and isinstance(formula.args[0], SemanticPredicateFormula))):
            continue

        sf: SemanticPredicateFormula = (
            formula if isinstance(formula, SemanticPredicateFormula) else formula.args[0])
        result = sf.predicate.evaluate(*sf.args)
        assert result.ready()

        if ((result.false() and isinstance(formula, SemanticPredicateFormula)) or
                (result.true() and isinstance(formula, NegatedFormula))):
            return ThreeValuedTruth.false()

        clause[idx] = SMTFormula(z3.BoolVal(True))

        if result.false() or result.true():
            continue

        # Evaluation returned an assignment
        assignment: Dict[Constant, DerivationTree] = result.result
        assert all(c.is_numeric() for c in assignment.keys())
        for other_idx in range(0, len(clause)):
            if other_idx == idx:
                continue
            clause[other_idx] = clause[other_idx].substitute_expressions(assignment)

    # Evaluate SMT formulas
    smt_formulas: List[SMTFormula] = [f for f in clause if isinstance(f, SMTFormula)]
    if smt_formulas:
        smt_vars: Set[Variable] = {v for f in smt_formulas for v in f.free_variables()}
        assert all(isinstance(v, Constant) and v.is_numeric() for v in smt_vars)
        regex = z3.Union(z3.Re("0"), z3.Concat(z3.Range("1", "9"), z3.Star(z3.Range("0", "9"))))
        smt_formulas.extend([SMTFormula(z3.InRe(v.to_smt(), regex), v) for v in smt_vars])
        smt_result, _ = z3_solve([
            cast(z3.BoolRef, z3_subst(
                f.formula,
                {v.to_smt(): z3.StringVal(str(s))
                 for v, s in f.substitutions.items()}))
            for f in smt_formulas])

        return ThreeValuedTruth.from_bool(smt_result == z3.sat)

    return ThreeValuedTruth.true()


def evaluate_legacy(
        formula: Formula,
        assignments: Dict[Variable, Tuple[Path, DerivationTree]],
        reference_tree: DerivationTree) -> ThreeValuedTruth:
    """
    An evaluation method which is based on tracking assignments in a dictionary.
    This does not work with formulas containing numeric constant introductions,
    but is significantly faster than the more general method based on formula manipulations.

    :param formula: The formula to evaluate.
    :param assignments: The assignments recorded so far.
    :return: A (three-valued) truth value.
    """
    if isinstance(formula, IntroduceNumericConstantFormula):
        raise NotImplementedError("This method cannot evaluate IntroduceNumericConstantFormula formulas.")
    elif isinstance(formula, SMTFormula):
        instantiation = z3.substitute(
            formula.formula,
            *tuple({z3.String(symbol.name): z3.StringVal(str(symbol_assignment[1]))
                    for symbol, symbol_assignment
                    in assignments.items()}.items()))

        # z3.set_param("smt.string_solver", "z3str3")
        solver = z3.Solver()
        solver.add(instantiation)
        return ThreeValuedTruth.from_bool(solver.check() == z3.sat)  # Set timeout?
    elif isinstance(formula, QuantifiedFormula):
        if isinstance(formula.in_variable, DerivationTree):
            in_inst = formula.in_variable
        else:
            assert formula.in_variable in assignments
            in_inst: DerivationTree = assignments[formula.in_variable][1]

        new_assignments = matches_for_quantified_formula(formula, in_inst, assignments)

        if isinstance(formula, ForallFormula):
            return ThreeValuedTruth.all(
                evaluate_legacy(formula.inner_formula, new_assignment, reference_tree)
                for new_assignment in new_assignments)
        elif isinstance(formula, ExistsFormula):
            return ThreeValuedTruth.any(
                evaluate_legacy(formula.inner_formula, new_assignment, reference_tree)
                for new_assignment in new_assignments)
    elif isinstance(formula, StructuralPredicateFormula):
        arg_insts = [
            arg if isinstance(arg, str)
            else reference_tree.find_node(arg)
            if isinstance(arg, DerivationTree)
            else assignments[arg][0]
            for arg in formula.args]
        return ThreeValuedTruth.from_bool(formula.predicate.evaluate(reference_tree, *arg_insts))
    elif isinstance(formula, SemanticPredicateFormula):
        arg_insts = [arg if isinstance(arg, DerivationTree) or arg not in assignments
                     else assignments[arg][1]
                     for arg in formula.args]
        eval_res = formula.predicate.evaluate(*arg_insts)

        if eval_res.true():
            return ThreeValuedTruth.true()
        elif eval_res.false():
            return ThreeValuedTruth.false()

        if not eval_res.ready() or not all(isinstance(key, Constant) for key in eval_res.result):
            # Evaluation resulted in a tree update; that is, the formula is satisfiable, but only
            # after an update of its arguments. This result happens when evaluating formulas during
            # solution search after instantiating variables with concrete trees.
            return ThreeValuedTruth.unknown()

        assignments.update({const: (tuple(), assgn) for const, assgn in eval_res.result.items()})
        return ThreeValuedTruth.true()
    elif isinstance(formula, NegatedFormula):
        return ThreeValuedTruth.not_(evaluate_legacy(formula.args[0], assignments, reference_tree))
    elif isinstance(formula, ConjunctiveFormula):
        return ThreeValuedTruth.all(
            evaluate_legacy(sub_formula, assignments, reference_tree) for sub_formula in formula.args)
    elif isinstance(formula, DisjunctiveFormula):
        return ThreeValuedTruth.any(
            evaluate_legacy(sub_formula, assignments, reference_tree) for sub_formula in formula.args)
    else:
        raise NotImplementedError()


def evaluate(
        formula: Union[Formula, str],
        reference_tree: DerivationTree,
        structural_predicates: Optional[Set[StructuralPredicate]] = None,
        semantic_predicates: Optional[Set[SemanticPredicate]] = None) -> ThreeValuedTruth:
    if isinstance(formula, str):
        formula = parse_isla(formula, structural_predicates, semantic_predicates)

    top_level_constants = {
        c for c in VariablesCollector.collect(formula)
        if isinstance(c, Constant) and not c.is_numeric()}
    assert len(top_level_constants) <= 1
    if len(top_level_constants) > 0:
        assert reference_tree is not None
        formula = formula.substitute_expressions({next(iter(top_level_constants)): reference_tree})

    assert well_formed(formula)

    v = FilterVisitor(lambda f: isinstance(f, IntroduceNumericConstantFormula))
    formula.accept(v)
    if not v.result:
        # The legacy evaluation performs better, but only works w/o IntroduceNumericConstantFormulas.
        return evaluate_legacy(formula, {}, reference_tree)

    qfr_free: List[Formula] = eliminate_quantifiers(formula)
    qfr_free_dnf: List[Formula] = [convert_to_dnf(convert_to_nnf(f)) for f in qfr_free]
    clauses: List[List[Formula]] = [split_conjunction(_f) for f in qfr_free_dnf for _f in split_disjunction(f)]

    return ThreeValuedTruth.any(evaluate_clause(clause, reference_tree) for clause in clauses)


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

                    # The assignment is correct if there is not any non-matched leaf
                    if all(any(len(match_path) <= len(leaf_path) and match_path == leaf_path[:len(match_path)]
                               for match_path, _ in maybe_match.values()) for leaf_path, _ in tree.leaves()):
                        new_assignments.append(new_assignment)
            else:
                new_assignment = copy.copy(initial_assignments)
                new_assignment[qfd_var] = path, tree
                new_assignments.append(new_assignment)

    in_tree.traverse(search_action)
    return new_assignments


def quantified_formula_might_match(
        qfd_formula: QuantifiedFormula,
        path_to_nonterminal: Path,
        tree: DerivationTree,
        grammar: Grammar,
        reachable: Callable[[str, str], bool]) -> bool:
    node = tree.get_subtree(path_to_nonterminal)

    if qfd_formula.in_variable.find_node(node) is None:
        return False

    if qfd_formula.is_already_matched(node):
        # This formula won't match node IFF there is no subtree in node that matches.
        return any(quantified_formula_might_match(qfd_formula, path, node, grammar, reachable)
                   for path, _ in node.paths() if path)

    qfd_nonterminal = qfd_formula.bound_variable.n_type
    if qfd_nonterminal == node.value or reachable(node.value, qfd_nonterminal):
        return True

    if qfd_formula.bind_expression is None:
        return False

    # Is there an extension of some tree `node` is a subtree of, such that the
    # bind expression tree is a prefix tree of that extension?

    maybe_prefix_tree, _ = qfd_formula.bind_expression.to_tree_prefix(
        qfd_formula.bound_variable.n_type, grammar)

    for idx in reversed(range(len(path_to_nonterminal))):
        subtree = tree.get_subtree(path_to_nonterminal[:idx])
        if maybe_prefix_tree.is_potential_prefix(subtree) and not qfd_formula.is_already_matched(subtree):
            return True

    return False


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
            in_formula.already_matched,
            id=in_formula.id
        )
    elif isinstance(in_formula, ExistsFormula):
        return ExistsFormula(
            in_formula.bound_variable,
            in_formula.in_variable,
            replace_formula(in_formula.inner_formula, to_replace, replace_with),
            in_formula.bind_expression)
    elif isinstance(in_formula, IntroduceNumericConstantFormula):
        return IntroduceNumericConstantFormula(
            in_formula.bound_variable,
            replace_formula(in_formula.inner_formula, to_replace, replace_with))

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
    elif isinstance(formula, IntroduceNumericConstantFormula):
        return IntroduceNumericConstantFormula(
            formula.bound_variable, convert_to_nnf(formula.inner_formula, negate))
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
            [reduce(lambda a, b: a & b, OrderedSet(split_conjunction(left & right)), SMTFormula(z3.BoolVal(True)))
             for left, right in itertools.product(*disjuncts_list)],
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
    def __init__(self, grammar: Grammar):
        self.placeholders: Dict[str, Variable] = {}
        self.variables: Dict[str, Variable] = {}
        self.grammar = grammar

    def __var(self,
              name: str,
              n_type: Optional[str],
              constr: Optional[Callable[[str, Optional[str]], Variable]] = None) -> Variable:
        if n_type is not None:
            assert n_type == Constant.NUMERIC_NTYPE or n_type in self.grammar, \
                f"Unknown nonterminal type {n_type} for variable {name}"

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

    def smt(self, formula) -> SMTFormula:
        assert isinstance(formula, z3.BoolRef)
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


def parse_isla(
        inp: str,
        structural_predicates: Optional[Set[StructuralPredicate]] = None,
        semantic_predicates: Optional[Set[SemanticPredicate]] = None) -> Formula:
    structural_predicates_map = {} if not structural_predicates else {p.name: p for p in structural_predicates}
    semantic_predicates_map = {} if not semantic_predicates else {p.name: p for p in semantic_predicates}

    pegparser = PEGParser(ISLA_GRAMMAR)
    tree = DerivationTree.from_parse_tree(pegparser.parse(inp.strip())[0])

    const_decl = tree.filter(lambda n: n.value == "<const>", enforce_unique=True)[0][1]
    const = Constant(str(const_decl.children[2]), str(const_decl.children[-4]))

    var_decls = tree.filter(lambda n: n.value == "<var_decl>")
    variables: List[BoundVariable] = []
    for var_decl in var_decls:
        ids = [str(id) for _, id in var_decl[1].filter(lambda n: n.value == "<id>")]
        ntype = [str(nt) for _, nt in var_decl[1].filter(lambda n: n.value == "<var_type>")][0]
        variables.extend([BoundVariable(id, ntype) for id in ids])

    all_vars = [cast(Variable, const)] + variables

    def check_undeclared_ids(tree: DerivationTree) -> None:
        undeclared_ids = [
            str(var[1]) for var in tree.filter(lambda n: n.value == "<id>")
            if all(decl_var.name != str(var[1]) for decl_var in all_vars)
        ]

        if undeclared_ids:
            raise SyntaxError(f"Undeclared symbols '{', '.join(undeclared_ids)}' in {tree}")

    def parse_constraint(tree: DerivationTree) -> Formula:
        if tree.value == "<constraint>":
            return parse_constraint(tree.children[0])
        if tree.value == "<disjunction>":
            if len(tree.children) == 1:
                return parse_constraint(tree.children[0])
            else:
                return parse_constraint(tree.children[2]) | parse_constraint(tree.children[-3])
        elif tree.value == "<conjunction>":
            if len(tree.children) == 1:
                return parse_constraint(tree.children[0])
            else:
                return parse_constraint(tree.children[2]) & parse_constraint(tree.children[-3])
        elif tree.value == "<negation>":
            if len(tree.children) == 1:
                return parse_constraint(tree.children[0])
            else:
                return -parse_constraint(tree.children[-1])
        elif tree.value == "<num_intro>":
            bvar_sym = str(tree.children[2])

            if all(v.name != bvar_sym for v in all_vars):
                raise SyntaxError(f"Undeclared symbol {bvar_sym} in {str(tree)}")

            bvar = next(v for v in variables if v.name == bvar_sym)

            return IntroduceNumericConstantFormula(bvar, parse_constraint(tree.children[-1]))
        elif tree.value == "<smt_atom>":
            check_undeclared_ids(tree)

            z3_constr = z3.parse_smt2_string(
                f"(assert {str(tree)})",
                decls={var.name: z3.String(var.name) for var in all_vars})[0]
            free_vars = [v for v in [cast(Variable, const)] + variables
                         if v.name in [str(s) for s in get_symbols(z3_constr)]]
            return SMTFormula(z3_constr, *free_vars)
        elif tree.value == "<predicate_atom>":
            check_undeclared_ids(tree)

            predicate_name = str(tree.children[0])
            if predicate_name not in structural_predicates_map and predicate_name not in semantic_predicates_map:
                raise SyntaxError(f"Unknown predicate {predicate_name} in {tree}")

            args = [
                next(var for var in all_vars if var.name == str(arg.children[0]))
                if arg.children[0].value == "<id>"
                else int(str(arg)) if arg.children[0].value == "<number>"
                else str(arg)[1:-1] if arg.children[0].value == "<string>"
                else str(arg)
                for _, arg in tree.filter(lambda n: n.value == "<arg>")]

            is_structural = predicate_name in structural_predicates_map

            predicate = (
                structural_predicates_map[predicate_name] if is_structural
                else semantic_predicates_map[predicate_name])

            if len(args) != predicate.arity:
                raise SyntaxError(
                    f"Unexpected number {len(args)} for predicate {predicate_name} "
                    f"({predicate.arity} expected) in {tree}")

            if is_structural:
                return StructuralPredicateFormula(predicate, *args)
            else:
                return SemanticPredicateFormula(predicate, *args)
        elif tree.value == "<quantified_formula>":
            qfr_sym = str(tree.children[0])
            bvar_sym = str(tree.children[2])
            invar_sym = str(tree.children[-4])

            for sym in [bvar_sym, invar_sym]:
                if all(v.name != sym for v in all_vars):
                    raise SyntaxError(f"Undeclared symbol {sym} in {str(tree)}")

            bvar = next(v for v in variables if v.name == bvar_sym)
            invar = next(v for v in all_vars if v.name == invar_sym)

            bexpr = None
            if tree.children[4].value == "<bind_expr>":
                bexpr = parse_bind_expr(tree.children[4])

            inner_constraint = parse_constraint(tree.children[-1])

            if qfr_sym == "forall":
                return ForallFormula(bvar, invar, inner_constraint, bind_expression=bexpr)
            else:
                return ExistsFormula(bvar, invar, inner_constraint, bind_expression=bexpr)
        else:
            raise NotImplementedError(f"Cannot parse expression {str(tree)}, symbol {tree.value}")

    def parse_bind_expr(tree: DerivationTree) -> BindExpression:
        result_elements: List[Union[str, BoundVariable, List[str]]] = []

        leaves = cast(DerivationTree, tree.children[1]).filter(
            lambda n: n.value == "<bind_expr_element>")

        for _, leaf in leaves:
            leaf = leaf.children[0]
            assert leaf.value in ["<var>", "<optional>", "<esc_chars>"]

            if leaf.value == "<esc_chars>":
                result_elements.append(str(leaf))
            elif leaf.value == "<optional>":
                result_elements.append([str(leaf.children[1])])
            else:
                try:
                    result_elements.append(next(v for v in variables if v.name == str(leaf.children[1])))
                except StopIteration:
                    raise SyntaxError(f"Undeclared symbol {str(leaf.children[1])} in {str(tree)}")

        return BindExpression(*result_elements)

    return parse_constraint(
        tree.filter(lambda n: n.value == "<constraint_decl>", True)[0][1].children[-3])


def get_conjuncts(formula: Formula) -> List[Formula]:
    return [conjunct
            for disjunct in split_disjunction(formula)
            for conjunct in split_conjunction(disjunct)]


def fresh_constant(used: Set[Variable], proposal: Constant, add: bool = True) -> Constant:
    base_name, n_type = proposal.name, proposal.n_type

    name = base_name
    idx = 0
    while any(used_var.name == name for used_var in used):
        name = f"{base_name}_{idx}"
        idx += 1

    result = Constant(name, n_type)
    if add:
        used.add(result)

    return result


def instantiate_top_constant(formula: Formula, tree: DerivationTree) -> Formula:
    top_constant: Constant = next(
        c for c in VariablesCollector.collect(formula)
        if isinstance(c, Constant) and not c.is_numeric())
    return formula.substitute_expressions({top_constant: tree})
