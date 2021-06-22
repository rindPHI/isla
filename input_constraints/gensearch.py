import copy
import heapq
import logging
import operator
from typing import Union, Optional, Dict, Tuple, List, Generator, cast, Set
import z3
from fuzzingbook.GrammarFuzzer import GrammarFuzzer

from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import canonical, non_canonical, EarleyParser
from grammar_to_regex.cfg2regex import RegexConverter
from orderedset import OrderedSet

from input_constraints import isla
from input_constraints.helpers import is_canonical_grammar, compute_numeric_nonterminals, path_iterator, \
    replace_tree_path, delete_unreachable, replace_tree
from input_constraints.isla import compute_atomic_string_nonterminals, VariablesCollector
from input_constraints.type_defs import CanonicalGrammar, Grammar, ParseTree, Path, AbstractTree

SolutionState = List[Tuple[isla.Constant, isla.Formula, AbstractTree]]
SingletonSolutionState = Tuple[isla.Constant, isla.Formula, AbstractTree]


def is_concrete_tree(tree: AbstractTree) -> bool:
    return all(sub_tree[1] is not None for _, sub_tree in path_iterator(tree))


def open_leaves(tree: AbstractTree) -> List[Tuple[Path, AbstractTree]]:
    return [(path, sub_tree)
            for path, sub_tree in path_iterator(tree)
            if type(sub_tree[0]) is str and sub_tree[1] is None]


def inline_state_element(state: SolutionState, state_to_inline: SingletonSolutionState) -> SolutionState:
    result: SolutionState = []
    variable, _, tree = state_to_inline
    for state_element in state:
        other_var, formula, other_tree = state_element
        result.append((other_var, formula, inline_var_in_tree(other_tree, variable, tree)))
    return result


def inline_var_in_tree(in_tree: AbstractTree, variable: isla.Variable, inst: AbstractTree) -> AbstractTree:
    node, children = in_tree
    if node == variable and children is None:
        return inst

    return node, [inline_var_in_tree(child, variable, inst) for child in children]


def merge_state_elements(state: SolutionState) -> SingletonSolutionState:
    # TODO: If we have more than one initial constant, we won't end up in a singleton state
    state_elements: SolutionState = copy.deepcopy(state)

    while len(state_elements) > 1:
        state_elements = inline_state_element(state_elements[:-1], state_elements[-1])

    return state_elements[0]


def fresh_constant(used: Set[isla.Constant], proposal: isla.Constant, add: bool = True) -> isla.Constant:
    base_name, n_type = proposal.name, proposal.n_type

    name = base_name
    idx = 0
    while any(used_var.name == name for used_var in used):
        name = f"{base_name}_{idx}"
        idx += 1

    result = isla.Constant(name, n_type)
    if add:
        used.add(result)

    return result


class ISLaSolver:
    def __init__(self,
                 grammar: Union[Grammar, CanonicalGrammar],
                 formula: isla.Formula,
                 numeric_nonterminals: Optional[OrderedSet[str, Tuple[int, int]]] = None,
                 atomic_string_nonterminals: Optional[OrderedSet[str]] = None
                 ):
        self.grammar = grammar
        if is_canonical_grammar(grammar):
            self.grammar = grammar
        else:
            self.grammar = canonical(grammar)

        self.formula = formula

        self.used_variables: OrderedSet[isla.Variable] = isla.VariablesCollector().collect(formula)

        self.numeric_nonterminals: Dict[str, Tuple[int, int]] = numeric_nonterminals \
            if numeric_nonterminals is not None \
            else compute_numeric_nonterminals(non_canonical(grammar))
        self.atomic_string_nonterminals: OrderedSet[str] = atomic_string_nonterminals \
            if atomic_string_nonterminals is not None \
            else compute_atomic_string_nonterminals(non_canonical(grammar),
                                                    formula,
                                                    self.used_variables,
                                                    self.numeric_nonterminals)

        self.logger = logging.getLogger(type(self).__name__)

    def find_solution(self) -> Generator[Dict[isla.Constant, ParseTree], None, None]:
        # TODO: Use SMT-based generation equipped with regular expressions for atomic formulas
        constant_collector = VariablesCollector()
        constants = [c for c in constant_collector.collect(self.formula) if type(c) is isla.Constant]
        assert len(constants) > 0
        assert len(constants) == 1 or not issubclass(type(self.formula), isla.QuantifiedFormula)

        queue: List[Tuple[int, SolutionStateWrapper]] = []

        heapq.heappush(queue, (0, SolutionStateWrapper(
            [(constant, self.formula, (constant.n_type, None)) for constant in constants])))

        while queue:
            _, state_wrapper = heapq.heappop(queue)
            state = state_wrapper.state

            # 1. Take all state elements with open leaves
            assignments: List[Tuple[Dict[isla.Constant, ParseTree], int]] = []

            for idx, state_element in enumerate(state):
                constant, formula, tree = state_element

                # If formula quantifier-free and does not include syntactic predicates,
                # use SMT-based instantiation to solve it
                pred_for_visitor = isla.FilterVisitor(lambda f: type(f) is isla.PredicateFormula)

                if not issubclass(type(formula), isla.QuantifiedFormula) and not pred_for_visitor.collect(formula):
                    # TODO: Might have to stall such a formula if other, quantified, formulas referring to variables
                    #       in this formula are not yet instantiated. We first process quantifiers, then the atoms.

                    assignments.append((self.solve_quantifier_free_formula(formula), 0))
                else:
                    for open_leaf in open_leaves(tree):
                        path, (leaf_node, _) = open_leaf
                        assert is_nonterminal(leaf_node)

                        # 2. Compute all expansions for all open leaves.
                        #    For existential formulas, compute all trees embedding the
                        #    existentially quantified tree (TODO).

                        for expansion in self.grammar[leaf_node]:
                            expanded_tree = \
                                replace_tree_path(tree, path, (leaf_node, [
                                    (child, None if is_nonterminal(child) else []) for child in expansion
                                ]))

                            # 3. Compute priorities based on greedy completion & length of shortest complete path
                            heuristic_value = 100 - self.compute_heuristic_value(
                                (constant, formula, expanded_tree), expansion)

                            assignments.append(({constant: expanded_tree}, heuristic_value))

            for assgn_w_prio in assignments:
                assignment, prio = assgn_w_prio
                new_state = []
                all_constants = set(constants)

                for state_element in state:
                    constant, formula, tree = state_element

                    # 4. If resulting tree is concrete & valid, inline variable value into all other state elements
                    # TODO: Checking if valid is generally too hard, if constraints are not monotone, i.e., can be
                    #       satisfied later on. Would be nice to formalize that...
                    concretized_tree = tree
                    for assgn_constant, new_tree in assignment.items():
                        if constant == assgn_constant:
                            concretized_tree = new_tree

                            if type(formula) is isla.ForallFormula:
                                formula: isla.ForallFormula
                                matches: List[Dict[isla.Variable, Tuple[Path, ParseTree]]] = \
                                    isla.matches_for_quantified_variable(formula, new_tree)

                                for match in matches:
                                    constant_subst_map = {
                                        variable: fresh_constant(all_constants,
                                                                 isla.Constant(variable.name, variable.n_type))
                                        for variable in match}

                                    inst_formula = formula.inner_formula.substitute_variables(constant_subst_map)

                                    for variable, path_and_tree in match.items():
                                        # TODO: Deal with bind expressions! Have to replace within matched tree
                                        new_constant = constant_subst_map[variable]
                                        new_state.append((new_constant, inst_formula, path_and_tree[1]))
                                        concretized_tree = replace_tree_path(
                                            concretized_tree,
                                            path_and_tree[0],
                                            (new_constant, None))

                        else:
                            concretized_tree = replace_tree(concretized_tree, (assgn_constant, None), new_tree)

                    if constant in constants or not is_concrete_tree(concretized_tree):
                        new_state.append((constant, formula, concretized_tree))

                if len(new_state) == len(constants) and all(is_concrete_tree(tree) for _, _, tree in new_state):
                    # 5. If whole state is concrete, yield result
                    yield {constant: tree for constant, _, tree in new_state}
                else:
                    # 6. Add all resulting non-concrete states w/ priorities to queue
                    heapq.heappush(queue, (prio, SolutionStateWrapper(new_state)))
                    self.logger.debug(f"Pushing new state {new_state}")
                    self.logger.debug(f"Queue length: {len(queue)}")

    def solve_quantifier_free_formula(self, formula: isla.Formula) -> Optional[Dict[isla.Constant, ParseTree]]:
        solver = z3.Solver()
        constant_collector = VariablesCollector()
        constants: List[isla.Constant] = [c for c in constant_collector.collect(formula) if
                                          type(c) is isla.Constant]

        for constant in constants:
            # TODO: Cache regular expressions?
            regex_conv = RegexConverter(non_canonical(self.grammar))
            regex = regex_conv.to_regex(constant.n_type)
            solver.add(z3.InRe(z3.String(constant.name), regex))

        formula: isla.SMTFormula  # TODO: Conjunctions, Disjunctions
        solver.add(formula.formula)

        if solver.check() != z3.sat:
            return None

        # TODO: Make configurable to find more assignments
        return {
            constant: self.parse(constant.n_type, solver.model()[z3.String(constant.name)].as_string())
            for constant in constants
        }

    def parse(self, nonterminal: str, input: str) -> ParseTree:
        grammar = copy.deepcopy(non_canonical(self.grammar))
        grammar["<start>"] = [nonterminal]
        delete_unreachable(grammar)
        parser = EarleyParser(grammar)
        return list(parser.parse(input))[0][1][0]

    def compute_heuristic_value(self, state: SingletonSolutionState, expansion: List[str]) -> int:
        """
        Computes a heuristic value between 0 (worst) and 100 (best) describing the quality of the present solution.
        Criteria are the cost of the expansion, and to what degree the constraint is satisfied (TODO).
        """
        constant, formula, tree = state

        leaf_nonterminals = [leaf[0] if type(leaf[0]) is str else leaf[0].n_type
                             for _, leaf in path_iterator(tree)
                             if leaf[1] is None]

        expansion_cost = GrammarFuzzer(non_canonical(self.grammar)).expansion_cost("".join(expansion))

        # Normalization: We assume a maximum expansion cost of 20, and normalize with respect to that.
        # The result is scaled to the range 0 -- 100 and inverted, since 100 should be a "good" value
        max_value = 20
        normalized_depth_value = 100 - round((min(expansion_cost, max_value) / max_value) * 100)
        assert 0 <= normalized_depth_value <= 100

        # TODO: Add heuristics based on formula

        return normalized_depth_value


class SolutionStateWrapper:
    def __init__(self, state: SolutionState):
        self.state = state

        self.__cmp_state = []
        for constant, formula, tree in state:
            new_tree = tree
            for path, sub_tree in path_iterator(tree):
                node, children = sub_tree
                if children is None:
                    new_tree = replace_tree_path(new_tree, path, (str(node), []))
                else:
                    new_tree = replace_tree_path(new_tree, path, (str(node), children))

            self.__cmp_state.append((constant, formula, new_tree))

    def __lt__(self, other: 'SolutionStateWrapper'):
        return self.__cmp_state < other.__cmp_state

    def __le__(self, other: 'SolutionStateWrapper'):
        return self.__cmp_state <= other.__cmp_state

    def __gt__(self, other: 'SolutionStateWrapper'):
        return self.__cmp_state > other.__cmp_state

    def __ge__(self, other: 'SolutionStateWrapper'):
        return self.__cmp_state >= other.__cmp_state
