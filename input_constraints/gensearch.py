import copy
import heapq
import logging
import random
from typing import Union, Optional, Dict, Tuple, List, Generator, Set

import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.GrammarFuzzer import GrammarFuzzer, tree_to_string
from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import canonical, non_canonical, EarleyParser
from grammar_graph.gg import GrammarGraph
from grammar_to_regex.cfg2regex import RegexConverter
from orderedset import OrderedSet

from input_constraints import isla
from input_constraints.helpers import is_canonical_grammar, compute_numeric_nonterminals, path_iterator, \
    replace_tree_path, delete_unreachable, replace_tree, tree_to_tuples
from input_constraints.isla import compute_atomic_string_nonterminals, VariablesCollector
from input_constraints.type_defs import CanonicalGrammar, Grammar, ParseTree, Path, AbstractTree

SolutionState = List[Tuple[isla.Constant, isla.Formula, AbstractTree]]
Assignment = Tuple[isla.Constant, isla.Formula, AbstractTree]


def is_complete_tree(tree: AbstractTree) -> bool:
    return all(sub_tree[1] is not None for _, sub_tree in path_iterator(tree))


def is_concrete_tree(tree: AbstractTree) -> bool:
    return all(not isinstance(sub_tree[0], isla.Variable) for _, sub_tree in path_iterator(tree))


def open_leaves(tree: AbstractTree) -> Generator[Tuple[Path, AbstractTree], None, None]:
    return ((path, sub_tree)
            for path, sub_tree in path_iterator(tree)
            if type(sub_tree[0]) is str and sub_tree[1] is None)


def substitute_assignment(in_state: SolutionState, assignment: Dict[isla.Constant, ParseTree]) -> SolutionState:
    result: SolutionState = copy.deepcopy(in_state)
    for idx in range(len(in_state)):
        for constant, tree in assignment.items():
            assignment_const, assignment_formula, assignment_tree = result[idx]

            if assignment_const == constant:
                continue

            result[idx] = (assignment_const,
                           assignment_formula.substitute_expressions(
                               {constant: z3.StringVal(tree_to_string(tree))}),
                           inline_var_in_tree(assignment_tree, constant, tree))

    return result


def inline_state_element(state: SolutionState, state_to_inline: Assignment) -> SolutionState:
    result: SolutionState = []
    variable, _, tree = state_to_inline
    for state_element in state:
        other_var, formula, other_tree = state_element
        result.append((other_var, formula, inline_var_in_tree(other_tree, variable, tree)))
    return result


def inline_var_in_tree(in_tree: AbstractTree, variable: isla.Variable, inst: AbstractTree) -> AbstractTree:
    node, children = in_tree
    if children is None:
        if node == variable:
            return inst
        else:
            return in_tree

    return node, [inline_var_in_tree(child, variable, inst) for child in children]


def merge_state_elements(state: SolutionState) -> Assignment:
    # TODO: If we have more than one initial constant, we won't end up in a singleton state
    state_elements: SolutionState = copy.deepcopy(state)

    while len(state_elements) > 1:
        state_elements = inline_state_element(state_elements[:-1], state_elements[-1])

    return state_elements[0]


def is_semantic_formula(formula: isla.Formula) -> bool:
    pred_for_visitor = isla.FilterVisitor(lambda f: type(f) is isla.PredicateFormula)
    return (not isinstance(formula, isla.QuantifiedFormula) and
            not pred_for_visitor.collect(formula))


def fresh_constant(used: Set[isla.Variable], proposal: isla.Constant, add: bool = True) -> isla.Constant:
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


def all_variables(state: SolutionState) -> Set[isla.Variable]:
    result: Set[isla.Variable] = set()
    for constant, formula, _ in state:
        result.add(constant)
        result.update(isla.VariablesCollector().collect(formula))
    return result


def complete_assignment(assignment: Assignment) -> bool:
    _, _, tree = assignment
    return is_concrete_tree(tree) and not any(open_leaves(tree))


def complete_state(state: SolutionState) -> bool:
    return all(complete_assignment(assgn) for assgn in state)


def abstract_tree_to_string(tree: AbstractTree) -> str:
    symbol, children, *_ = tree
    if children:
        return ''.join(abstract_tree_to_string(c) for c in children)
    else:
        if isinstance(symbol, isla.Variable):
            return symbol.name
        return symbol


def state_to_string(state: SolutionState) -> str:
    return "{(" + "), (".join(map(str, [f"{constant.name}, {formula}, \"{abstract_tree_to_string(tree)}\""
                                        for constant, formula, tree in state])) + ")}"


class ISLaSolver:
    def __init__(self,
                 grammar: Union[Grammar, CanonicalGrammar],
                 formula: isla.Formula,
                 max_number_free_instantiations: int = 10
                 ):
        self.grammar = grammar
        if is_canonical_grammar(grammar):
            self.grammar = grammar
        else:
            self.grammar = canonical(grammar)

        self.formula = formula
        self.max_number_free_instantiations = max_number_free_instantiations
        self.used_variables: OrderedSet[isla.Variable] = isla.VariablesCollector().collect(formula)
        self.logger = logging.getLogger(type(self).__name__)

    def find_solution(self) -> Generator[Dict[isla.Constant, ParseTree], None, None]:
        constant_collector = VariablesCollector()
        top_constants = set([c for c in constant_collector.collect(self.formula) if type(c) is isla.Constant])
        assert len(top_constants) > 0
        assert len(top_constants) == 1 or not isinstance(self.formula, isla.QuantifiedFormula)

        queue: List[Tuple[int, SolutionStateWrapper]] = []

        heapq.heappush(queue, (0, SolutionStateWrapper(
            [(constant, self.formula, (constant.n_type, None)) for constant in top_constants])))

        while queue:
            _, state_wrapper = heapq.heappop(queue)
            state = state_wrapper.state
            self.logger.debug(f"Polling new state {state_to_string(state)}")
            self.logger.debug(f"Queue length: {len(queue)}")

            # Choose the first assignment with a non-abstract tree and an open leaf.
            assignment = next((assgn for assgn in state
                               if (tree := assgn[2],
                                   is_concrete_tree(tree) and any(open_leaves(tree)))[1]))
            constant, formula, tree = assignment

            if is_semantic_formula(formula):
                # TODO: Might have to stall such a formula if other, quantified,
                #       formulas referring to variables in this formula are not
                #       yet instantiated. We first process quantifiers, then the atoms.
                # TODO: Check whether this is actually true, find example!

                solution = self.solve_quantifier_free_formula(formula)
                if not solution:
                    # Unsolvable constraint... Nothing more to do here.
                    continue

                new_state: SolutionState = [(c, isla.SMTFormula(z3.BoolVal(True)), solution[c])
                                            for c in solution
                                            if c in top_constants]

                new_state.extend(substitute_assignment([assgn for assgn in state
                                                        if assgn[0] not in solution], solution))

                yield from self.process_new_state(new_state, queue, top_constants)
                continue

            leaf_path, (leaf_node, _) = next(open_leaves(tree))

            if isinstance(formula, isla.ForallFormula):
                open_relevant_leaves = (pair for pair in open_leaves(tree)
                                        if (leaf_node := pair[1][0],
                                            self.reachable(leaf_node, formula.bound_variable.n_type))[1])
                leaf_path, (leaf_node, _) = next(open_relevant_leaves)

                # Expand the leaf, check matching instantiations
                for expansion in self.grammar[leaf_node]:
                    # TODO: Only expand nonterminals from which the nonterminal of the quantified variable
                    #       can be reached. Also inline incomplete trees in that case. Batch-expand later on.
                    expanded_tree = replace_tree_path(tree, leaf_path, (leaf_node, [
                        (child, None if is_nonterminal(child) else []) for child in expansion
                    ]))

                    matches: List[Dict[isla.Variable, Tuple[Path, ParseTree]]] = \
                        isla.matches_for_quantified_variable(formula, expanded_tree)

                    # Only consider open leaves. Others are validly instantiated.
                    matches = [{c: p for c, p in match.items() if p[1][1] is None} for match in matches]

                    new_state = [assgn for assgn in state if assgn is not assignment]

                    for match in matches:
                        constant_subst_map = {}
                        all_vars = all_variables(state)
                        for variable in match:
                            fresh_c = fresh_constant(all_vars, isla.Constant(variable.name, variable.n_type))
                            constant_subst_map[variable] = fresh_c
                            all_vars.add(fresh_c)

                        inst_formula = formula.inner_formula.substitute_variables(constant_subst_map)

                        for variable, (match_path, match_tree) in match.items():
                            # TODO: Deal with bind expressions! Have to replace within matched tree
                            new_constant = constant_subst_map[variable]
                            new_state.append((new_constant, inst_formula, match_tree))
                            expanded_tree = replace_tree_path(expanded_tree, match_path, (new_constant, None))

                    new_state.append((constant, formula, expanded_tree))
                    yield from self.process_new_state(new_state, queue, top_constants)
                    continue

    def process_new_state(self, state, queue, top_constants):
        if complete_state(state):
            yield {c: t for c, _, t in state}
            return

        complete_assignments = [assgn for assgn in state if complete_assignment(assgn)]
        satisfied_assignments = [assgn for assgn in state
                                 if assgn not in complete_assignments and
                                 self.formula_satisfied(assgn)]

        if len(complete_assignments) + len(satisfied_assignments) == len(state):
            fuzzer = GrammarCoverageFuzzer(non_canonical(self.grammar))
            for _ in range(self.max_number_free_instantiations):
                all_complete_assignments = copy.deepcopy(complete_assignments)
                all_complete_assignments.extend([
                    (constant, isla.SMTFormula(z3.BoolVal(True)), fuzzer.expand_tree(copy.deepcopy(tree)))
                    for constant, _, tree in satisfied_assignments
                ])

                yield {c: t for c, _, t in all_complete_assignments}
            return

        top_constant_assignments = [assgn for assgn in state if assgn[0] in top_constants]
        heuristic_value = sum([100 - self.compute_heuristic_value(assgn)
                               for assgn in top_constant_assignments]
                              ) // len(top_constant_assignments)
        heapq.heappush(queue, (heuristic_value, SolutionStateWrapper(state)))

        self.logger.debug(f"Pushing new state {state_to_string(state)}")
        self.logger.debug(f"Queue length: {len(queue)}")

    def reachable(self, nonterminal: str, to_nonterminal: str) -> bool:
        graph = GrammarGraph.from_grammar(non_canonical(self.grammar))
        return graph.get_node(nonterminal).reachable(graph.get_node(to_nonterminal))

    def formula_satisfied(self, assignment: Assignment) -> bool:
        _, formula, tree = assignment

        if not is_concrete_tree(tree):
            # Have to instantiate variables first
            return False

        if is_complete_tree(tree):
            # We assume that all instantiations are valid, therefore
            # the formula is trivially satisfied for all concrete trees
            return True

        if isinstance(formula, isla.ForallFormula):
            nonterminals = set([pair[1][0] for pair in open_leaves(tree)])
            qfd_nonterminal = formula.bound_variable.n_type

            # if qfd_nonterminal is not reachable from any nonterminal, we
            # already know that formula is vacuously satisfied!
            graph = GrammarGraph.from_grammar(non_canonical(self.grammar))
            return not any(graph.get_node(nonterminal).reachable(graph.get_node(qfd_nonterminal))
                           for nonterminal in nonterminals)
        elif isinstance(formula, isla.SMTFormula):
            s = z3.Solver()
            s.add(z3.Not(formula.formula))
            s.set("timeout", 1000)
            return s.check() == z3.unsat

        return False

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

    def compute_heuristic_value(self, state: Assignment) -> int:
        """
        Computes a heuristic value between 0 (worst) and 100 (best) describing the quality of the present solution.
        Criteria are the cost of the expansion, and to what degree the constraint is satisfied (TODO).
        """
        constant, formula, tree = state
        symbols = set([pair[1][0] for pair in open_leaves(tree)])

        if not symbols:
            return 100

        fuzzer = GrammarFuzzer(non_canonical(self.grammar))
        expansion_cost = max([fuzzer.symbol_cost(symbol) for symbol in symbols])

        # Normalization: We assume a maximum expansion cost of 20, and normalize with respect to that.
        # The result is scaled to the range 0 -- 100 and inverted, since 100 should be a "good" value
        max_value = 20
        normalized_depth_value = 100 - round((min(expansion_cost, max_value) / max_value) * 100)
        assert 0 <= normalized_depth_value <= 100

        # TODO: Add heuristics based on formula

        return normalized_depth_value

    def compute_heuristic_value_1(self, state: Assignment, expansion: List[str]) -> int:
        """
        Computes a heuristic value between 0 (worst) and 100 (best) describing the quality of the present solution.
        Criteria are the cost of the expansion, and to what degree the constraint is satisfied (TODO).
        """
        constant, formula, tree = state

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

    def __hash__(self):
        return hash(tuple([(elem[0], elem[1], tree_to_tuples(elem[2])) for elem in self.state]))

    def __str__(self):
        return str(self.state)

    def __repr__(self):
        return f"SolutionStateWrapper({repr(self.state)})"

    def __lt__(self, other: 'SolutionStateWrapper'):
        return random.choice([True, False])

    def __le__(self, other: 'SolutionStateWrapper'):
        return random.choice([True, False])

    def __gt__(self, other: 'SolutionStateWrapper'):
        return random.choice([True, False])

    def __ge__(self, other: 'SolutionStateWrapper'):
        return random.choice([True, False])
