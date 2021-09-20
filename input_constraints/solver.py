import copy
import heapq
import logging
import sys
from functools import reduce, lru_cache
from typing import Generator, Dict, List, Set, Optional, Tuple, Union

import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.GrammarFuzzer import GrammarFuzzer
from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import canonical, EarleyParser
from grammar_graph import gg
from grammar_graph.gg import GrammarGraph
from grammar_to_regex.cfg2regex import RegexConverter
from orderedset import OrderedSet

import input_constraints.isla_shortcuts as sc
from input_constraints import isla
from input_constraints.existential_helpers import insert_tree
from input_constraints.helpers import delete_unreachable, dict_of_lists_to_list_of_dicts, \
    replace_line_breaks
from input_constraints.isla import DerivationTree, VariablesCollector, split_conjunction, split_disjunction, \
    convert_to_dnf, convert_to_nnf, ensure_unique_bound_variables
from input_constraints.type_defs import Grammar, Path


class SolutionState:
    def __init__(self, constraint: isla.Formula, tree: DerivationTree, level: int = 0):
        self.constraint = constraint
        self.tree = tree
        self.level = level
        self.__hash = None

    def formula_satisfied(self) -> isla.ThreeValuedTruth:
        if self.tree.is_open():
            # Have to instantiate variables first
            return isla.ThreeValuedTruth.unknown()

        return isla.evaluate(self.constraint, reference_tree=self.tree)

    def complete(self) -> bool:
        if not self.tree.is_complete():
            return False

        # We assume that any universal quantifier has already been instantiated, if it matches,
        # and is thus satisfied, or another unsatisfied constraint resulted from the instantiation.
        # Existential, predicate, and SMT formulas have to be eliminated first.
        return any(all(not isinstance(conjunct, isla.StructuralPredicateFormula)
                       and (not isinstance(conjunct, isla.SMTFormula) or conjunct == sc.true())
                       and not isinstance(conjunct, isla.SemanticPredicateFormula)
                       and not isinstance(conjunct, isla.ExistsFormula)
                       and (not isinstance(conjunct, isla.ForallFormula) or len(conjunct.already_matched) > 0)
                       for conjunct in split_conjunction(disjunct))
                   for disjunct in split_disjunction(self.constraint))

    def variables(self) -> Set[isla.Variable]:
        return set(isla.VariablesCollector.collect(self.constraint))

    def __iter__(self):
        yield self.constraint
        yield self.tree

    # Numeric comparisons are needed for using solution states in the binary heap queue
    def __lt__(self, other: 'SolutionState'):
        return hash(self) < hash(other)

    def __le__(self, other: 'SolutionState'):
        return hash(self) <= hash(other)

    def __gt__(self, other: 'SolutionState'):
        return hash(self) > hash(other)

    def __ge__(self, other: 'SolutionState'):
        return hash(self) >= hash(other)

    def __hash__(self):
        if self.__hash is None:
            self.__hash = hash((self.constraint, self.tree))
        return self.__hash

    def __eq__(self, other):
        return (isinstance(other, SolutionState)
                and self.constraint == other.constraint
                and self.tree.structurally_equal(other.tree))

    def __repr__(self):
        return f"SolutionState({repr(self.constraint)}, {repr(self.tree)})"

    def __str__(self):
        return f"{{{self.constraint}, {replace_line_breaks(str(self.tree))}}}"


class ISLaSolver:
    def __init__(self,
                 grammar: Grammar,
                 formula: isla.Formula,
                 max_number_free_instantiations: int = 10,
                 max_number_smt_instantiations: int = 10,
                 expand_after_existential_elimination: bool = False,  # Currently not used, might be removed
                 enforce_unique_trees_in_queue: bool = True,
                 precompute_reachability: bool = False,
                 debug: bool = False,
                 # Current cost functions:
                 # 1. "Tree finishing cost" --- Cost computed from the open nonterminals in a tree.
                 # 2. "Univ. qfr. distance cost" --- Distance to satisfying universal quantifiers.
                 # 3. "Constraint cost" --- Cost computed from the constraint. Currently, only counts existential qfrs.
                 # 4. Number of ancestors --- The "derivation depth", increases strictly monotonically. Penalize to
                 #                            prefer items longer in the queue.
                 cost_vectors: Tuple[Tuple[float, float, float], ...] = (
                         # (20, 5, 1, .5), (0, 0, 0, 1), (2, 1, 1, 0)
                         (20, -1, 1, .5), (0, 0, 0, 1), (2, -.5, 1, 0)
                 ),
                 cost_phase_lengths: Tuple[int, ...] = (200, 100, 500),
                 ):
        """
        :param grammar: The underlying grammar.
        :param formula: The formula to solve.
        :param max_number_free_instantiations: Number of times that nonterminals that are not bound by any formula
        should be expanded by a coverage-based fuzzer.
        :param max_number_smt_instantiations: Number of solutions of SMT formulas that should be produced.
        :param expand_after_existential_elimination: Trees are expanded after an existential quantifier elimination
        iff this paramter is set to true. If false, only a finite (potentially small) set of inputs is generated for
        existential constraints. (CURRENTLY NOT USED, MIGHT BE REMOVED)
        :param enforce_unique_trees_in_queue: If true, only one state in the queue containing a tree with the same
        structure can be present at a time. Should be set to false especially if there are top-level SMT formulas
        about numeric constants. TODO: This parameter is awkward, maybe we can find a different solution.
        :param precompute_reachability: If true, the distances between all grammar nodes are pre-computed using
        Floyd-Warshall's algorithm. This makes sense if there are many expensive distance queries, e.g., in a big
        grammar and a constraint with relatively many universal quantifiers.
        :param debug: If true, debug information about the evolution of states is collected, notably in the
        field state_tree. The root of the tree is in the field state_tree_root. The field costs stores the computed
        cost values for all new nodes.
        """
        self.logger = logging.getLogger(type(self).__name__)

        self.grammar = grammar
        self.graph = GrammarGraph.from_grammar(grammar)
        self.canonical_grammar = canonical(grammar)
        self.symbol_costs: Dict[str, int] = self.compute_symbol_costs()
        self.cost_normalizer = CostNormalizer()

        self.formula = ensure_unique_bound_variables(formula)
        top_constants: Set[isla.Constant] = set(
            [c for c in VariablesCollector.collect(self.formula)
             if isinstance(c, isla.Constant)
             and not c.is_numeric()])
        assert len(top_constants) == 1
        self.top_constant = next(iter(top_constants))

        self.max_number_free_instantiations: int = max_number_free_instantiations
        self.max_number_smt_instantiations: int = max_number_smt_instantiations
        # self.expand_after_existential_elimination = expand_after_existential_elimination
        self.enforce_unique_trees_in_queue = enforce_unique_trees_in_queue

        assert len(cost_vectors) == len(cost_phase_lengths)
        # Expected cost_vector length can change if implementation of cost function changes
        # (different number of cost factors).
        assert all(len(cost_vector) == 4 for cost_vector in cost_vectors)
        self.cost_vectors = cost_vectors
        self.cost_phase_lengths = cost_phase_lengths
        self.current_cost_phase: int = 0
        self.current_cost_phase_since: int = 0

        self.precompute_reachability = precompute_reachability
        if precompute_reachability:
            # Pre-compute grammar graph distances for more performant reachability queries
            self.logger.info("Pre-Computing shortest distances between all grammar nodes "
                             "for quicker reachability queries...")
            node_distances: [Dict[gg.Node, Dict[gg.Node, int]]] = self.graph.shortest_distances(infinity=sys.maxsize)
            u: gg.Node
            self.node_distances: [Dict[str, Dict[str, int]]] = {
                u.symbol: {
                    v.symbol: dist
                    for v, dist in node_distances[u].items()
                    if not isinstance(v, gg.ChoiceNode)
                }
                for u in self.graph.all_nodes
                if type(u) is gg.NonterminalNode
            }
            self.logger.info("DONE Pre-Computing shortest distances between all grammar nodes.")

        # Initialize Queue
        initial_tree = DerivationTree(self.top_constant.n_type, None)
        initial_formula = self.formula.substitute_expressions({self.top_constant: initial_tree})
        initial_state = self.establish_invariant(SolutionState(initial_formula, initial_tree))

        self.queue: List[Tuple[float, SolutionState]] = []
        self.tree_hashes_in_queue: Set[int] = {initial_tree.structural_hash()}
        heapq.heappush(self.queue, (0, initial_state))
        self.current_level = 0

        # Debugging stuff
        self.debug = debug
        self.state_tree: Dict[SolutionState, List[SolutionState]] = {}  # is only filled if self.debug
        self.state_tree_root = None
        self.current_state = None
        self.costs: Dict[SolutionState, float] = {}

        if self.debug:
            self.state_tree[initial_state] = []
            self.state_tree_root = initial_state
            self.costs[initial_state] = 0

    def solve(self) -> Generator[DerivationTree, None, None]:
        while self.queue:
            cost: int
            state: SolutionState
            cost, state = heapq.heappop(self.queue)
            self.current_level = state.level
            self.tree_hashes_in_queue.discard(state.tree.structural_hash())

            if self.debug:
                self.current_state = state
                self.state_tree.setdefault(state, [])
            self.logger.debug(f"Polling new state %s (hash %d, cost %f)", state, hash(state), cost)
            self.logger.debug(f"Queue length: %s", len(self.queue))

            # Split disjunctions
            if isinstance(state.constraint, isla.DisjunctiveFormula):
                self.logger.debug("Splitting disjunction %s", state.constraint)
                for disjunct in split_disjunction(state.constraint):
                    new_state = SolutionState(disjunct, state.tree)
                    heapq.heappush(self.queue, (cost, new_state))

                    if self.debug:
                        self.state_tree[self.current_state].append(new_state)
                        self.costs[new_state] = cost

                    self.logger.debug("Pushing new state %s (hash %d, cost %f)", state, hash(new_state), cost)
                    self.logger.debug("Queue length: %d", len(self.queue))
                    if len(self.queue) % 100 == 0:
                        self.logger.info("Queue length: %d", len(self.queue))
                continue

            # Instantiate all top-level structural predicate formulas.
            state = self.instantiate_structural_predicates(state)

            if state.constraint == sc.false():
                continue

            # Match all universal formulas
            result_states = self.match_all_universal_formulas(state)
            if result_states is not None:
                yield from [result for new_state in result_states
                            for result in self.process_new_state(new_state)]
                continue

            # Eliminate all semantic formulas
            result_states = self.eliminate_all_semantic_formulas(state)
            if result_states is not None:
                yield from [result for new_state in result_states
                            for result in self.process_new_state(new_state)]
                continue

            # Eliminate first (ready) semantic predicate formula
            result_state = self.eliminate_first_ready_semantic_predicate_formula(state)
            if result_state is not None:
                yield from self.process_new_state(result_state)
                continue

            # Eliminate first existential formula
            result_states = self.eliminate_first_existential_formula(state)
            if result_states is not None:
                yield from [result for new_state in result_states
                            for result in self.process_new_state(new_state)]
                continue
                # if (not self.expand_after_existential_elimination
                #         or any(result_state.constraint == sc.true() for result_state in result_states)):
                #     continue

            for new_state in self.postprocess_new_state(state):
                if new_state.complete() and new_state.formula_satisfied().is_true():
                    yield new_state.tree
                    continue

                # Expand the tree
                expanded_states = self.expand_tree(new_state)
                assert len(expanded_states) > 0, f"State {new_state} will never leave the queue."

                self.logger.debug("Expanding state %s (%d successors)", new_state, len(expanded_states))
                yield from [result for expanded_state in expanded_states
                            for result in self.process_new_state(expanded_state)]

    def instantiate_structural_predicates(self, state: SolutionState) -> SolutionState:
        predicate_formulas = [
            conjunct for conjunct in get_conjuncts(state.constraint)
            if isinstance(conjunct, isla.StructuralPredicateFormula)]

        formula = state.constraint
        for predicate_formula in predicate_formulas:
            instantiation = isla.SMTFormula(z3.BoolVal(predicate_formula.evaluate(state.tree)))
            self.logger.debug("Eliminating (-> %s) structural predicate formula %s", instantiation, predicate_formula)
            formula = isla.replace_formula(formula, predicate_formula, instantiation)

        return SolutionState(formula, state.tree)

    def eliminate_all_semantic_formulas(self, state: SolutionState) -> Optional[List[SolutionState]]:
        conjuncts = split_conjunction(state.constraint)
        semantic_formulas = [conjunct for conjunct in conjuncts if isinstance(conjunct, isla.SMTFormula)]

        if not semantic_formulas:
            return None

        self.logger.debug("Eliminating semantic formulas [%s]", ", ".join(map(str, semantic_formulas)))

        prefix_conjunction = reduce(lambda a, b: a & b, semantic_formulas, sc.true())
        new_disjunct = (
                prefix_conjunction &
                reduce(lambda a, b: a & b,
                       [conjunct for conjunct in conjuncts if conjunct not in semantic_formulas],
                       sc.true()))

        return self.eliminate_semantic_formula(prefix_conjunction, SolutionState(new_disjunct, state.tree))

    def eliminate_first_ready_semantic_predicate_formula(self, state: SolutionState) -> Optional[SolutionState]:
        semantic_predicate_formulas = [
            conjunct for conjunct in split_conjunction(state.constraint)
            if isinstance(conjunct, isla.SemanticPredicateFormula)]

        if not semantic_predicate_formulas:
            return None

        for semantic_predicate_formula in semantic_predicate_formulas:
            evaluation_result = semantic_predicate_formula.evaluate()
            if not evaluation_result.ready():
                continue

            self.logger.debug("Eliminating semantic predicate formula %s", semantic_predicate_formula)

            if evaluation_result.true() or evaluation_result.false():
                return SolutionState(
                    isla.replace_formula(
                        state.constraint,
                        semantic_predicate_formula,
                        sc.true() if evaluation_result.true() else sc.false()),
                    state.tree)

            new_constraint = (
                isla.replace_formula(state.constraint, semantic_predicate_formula, sc.true())
                    .substitute_expressions(evaluation_result.result))

            return SolutionState(new_constraint, state.tree.substitute(evaluation_result.result))

        return None

    def eliminate_first_existential_formula(self, state: SolutionState) -> Optional[List[SolutionState]]:
        existential_formulas = [
            conjunct for conjunct in split_conjunction(state.constraint)
            if isinstance(conjunct, isla.ExistsFormula)]

        if not existential_formulas:
            return None

        new_states = self.match_existential_formula(existential_formulas[0], state)

        complete_states = [state for state in new_states
                           if state.complete()
                           or state.constraint == sc.true()]
        if complete_states:
            self.logger.debug("Matching existential formula %s", existential_formulas[0])
            new_states = complete_states
        else:
            elimination_result = self.eliminate_existential_formula(existential_formulas[0], state)
            new_states.extend(elimination_result)
            self.logger.debug(
                "Eliminating existential formula %s, %d successors", existential_formulas[0], len(elimination_result))

        return new_states

    def match_all_universal_formulas(self, state: SolutionState) -> Optional[List[SolutionState]]:
        universal_formulas = [
            conjunct for conjunct in split_conjunction(state.constraint)
            if isinstance(conjunct, isla.ForallFormula)]

        if not universal_formulas:
            return None

        result = self.match_universal_formulas(universal_formulas, state)
        if result:
            self.logger.debug("Matched universal formulas [%s]", ", ".join(map(str, universal_formulas)))

        return result or None

    def expand_tree(self, state: SolutionState) -> List[SolutionState]:
        """
        Expands the given tree, but not at nonterminals that can be freely instantiated of those that directly
        correspond to the assignment constant.

        :param state: The current state.
        :return: A (possibly empty) list of expanded trees.
        """

        possible_expansions: List[Dict[Path, List[DerivationTree]]] = dict_of_lists_to_list_of_dicts({
            leaf_path: [
                [DerivationTree(child, None if is_nonterminal(child) else []) for child in expansion]
                for expansion in self.canonical_grammar[leaf_node.value]
            ]
            for leaf_path, leaf_node in state.tree.open_leaves()
            if not self.can_be_freely_instantiated(leaf_path, state)
        })

        if len(possible_expansions) == 1 and not possible_expansions[0]:
            return []

        result: List[SolutionState] = []

        for possible_expansion in possible_expansions:
            expanded_tree = state.tree
            for path, new_children in possible_expansion.items():
                leaf_node = expanded_tree.get_subtree(path)
                expanded_tree = expanded_tree.replace_path(
                    path, DerivationTree(leaf_node.value, new_children, leaf_node.id))

            updated_constraint = state.constraint.substitute_expressions({
                state.tree.get_subtree(path[:idx]): expanded_tree.get_subtree(path[:idx])
                for path in possible_expansion
                for idx in range(len(path) + 1)
            })

            result.append(SolutionState(updated_constraint, expanded_tree))

        return result

    def match_universal_formulas(self,
                                 universal_formulas: List[isla.ForallFormula],
                                 state: SolutionState) -> List[SolutionState]:
        matched = False
        context_formula = state.constraint

        for universal_formula in universal_formulas:
            matches: List[Dict[isla.Variable, Tuple[Path, DerivationTree]]] = \
                [match for match in isla.matches_for_quantified_formula(universal_formula)
                 if not universal_formula.is_already_matched(match[universal_formula.bound_variable][1])]

            universal_formula_with_matches = universal_formula.add_already_matched({
                match_tree
                for match in matches
                for _, match_tree in match.values()
            })

            for match in matches:
                matched = True

                inst_formula = universal_formula_with_matches.inner_formula.substitute_expressions({
                    variable: match_tree for variable, (_, match_tree) in match.items()
                })

                context_formula = inst_formula & isla.replace_formula(
                    context_formula, universal_formula, universal_formula_with_matches
                )

        if matched:
            return [SolutionState(context_formula, state.tree)]
        else:
            return []

    def match_existential_formula(self,
                                  existential_formula: isla.ExistsFormula,
                                  state: SolutionState) -> List[SolutionState]:
        result: List[SolutionState] = []

        matches: List[Dict[isla.Variable, Tuple[Path, DerivationTree]]] = \
            isla.matches_for_quantified_formula(existential_formula)

        context_formula = state.constraint
        for match in matches:
            inst_formula = existential_formula.inner_formula.substitute_expressions({
                variable: match_tree for variable, (_, match_tree) in match.items()
            })
            context_formula = inst_formula & isla.replace_formula(context_formula, existential_formula, sc.true())
            result.append(SolutionState(context_formula, state.tree))

        return result

    def eliminate_existential_formula(self,
                                      existential_formula: isla.ExistsFormula,
                                      state: SolutionState) -> List[SolutionState]:
        bind_expr_paths: Dict[isla.BoundVariable, Path] = {}
        if existential_formula.bind_expression is not None:
            tree_prefix, bind_expr_paths = existential_formula.bind_expression.to_tree_prefix(
                existential_formula.bound_variable.n_type, self.grammar)
            inserted_tree = tree_prefix
        else:
            inserted_tree = DerivationTree(existential_formula.bound_variable.n_type, None)

        insertion_result = insert_tree(self.canonical_grammar, inserted_tree, state.tree, graph=self.graph)

        if not insertion_result:
            return []

        tree_substitutions = [
            {
                original_tree: result_tree.get_subtree(path)
                for path, original_tree in state.tree.path_iterator()
                if result_tree.is_valid_path(path)
            }
            for result_tree in insertion_result]

        variable_substitutions = (
                {existential_formula.bound_variable: inserted_tree} |
                ({} if not bind_expr_paths else {
                    var: inserted_tree.get_subtree(path)
                    for var, path in bind_expr_paths.items()
                    if var in existential_formula.bind_expression.bound_variables()
                }))

        instantiated_formula = existential_formula.inner_formula.substitute_expressions(variable_substitutions)

        return [
            SolutionState(
                (instantiated_formula
                 & self.formula.substitute_expressions({self.top_constant: state.tree.substitute(tree_substitution)})
                 & isla.replace_formula(
                            state.constraint, existential_formula, sc.true()
                        ).substitute_expressions(tree_substitution)),
                state.tree.substitute(tree_substitution))
            for tree_substitution in tree_substitutions]

    def eliminate_semantic_formula(self, semantic_formula: isla.Formula, state: SolutionState) -> List[SolutionState]:
        """
        Solves a semantic formula and, for each solution, substitutes the solution for the respective
        constant in each assignment of the state. Also instantiates all "free" constants in the given
        tree. The SMT solver is passed a regular expression approximating the language of the nonterminal
        of each considered constant. Returns an empty list for unsolvable constraints.

        :param semantic_formula: The semantic (i.e., only containing logical connectors and SMT Formulas)
        formula to solve.
        :param state: The original solution state.
        :return: A list of instantiated SolutionStates.
        """

        solutions: List[Dict[Union[isla.Constant, DerivationTree], DerivationTree]] = \
            self.solve_quantifier_free_formula(semantic_formula)

        results = []
        for solution in solutions:
            if solution:
                new_state = SolutionState(state.constraint.substitute_expressions(solution),
                                          state.tree.substitute(solution))
            else:
                new_state = SolutionState(
                    isla.replace_formula(state.constraint, semantic_formula, sc.true()), state.tree)

            results.append(new_state)

        return results

    def solve_quantifier_free_formula(
            self, formula: isla.Formula) -> List[Dict[Union[isla.Constant, DerivationTree], DerivationTree]]:
        solutions: List[Dict[Union[isla.Constant, DerivationTree], DerivationTree]] = []
        internal_solutions: List[Dict[isla.Constant, z3.StringVal]] = []
        smt_formula = qfr_free_formula_to_z3_formula(formula)

        smt_formulas = [conjunct for conjunct in get_conjuncts(formula)
                        if isinstance(conjunct, isla.SMTFormula)]

        tree_substitutions = reduce(
            lambda d1, d2: d1 | d2,
            [smt_formula.substitutions for smt_formula in smt_formulas],
            {}
        )

        constants = reduce(
            lambda d1, d2: d1 | d2,
            [smt_formula.free_variables() | smt_formula.instantiated_variables
             for smt_formula in smt_formulas],
            set()
        )

        for _ in range(self.max_number_smt_instantiations):
            solver = z3.Solver()
            solver.set("timeout", 1000)

            for constant in constants:
                if constant.is_numeric():
                    regex = z3.Concat(z3.Range("0", "9"), z3.Star(z3.Range("0", "9")))
                else:
                    regex = self.extract_regular_expression(constant.n_type)
                solver.add(z3.InRe(z3.String(constant.name), regex))

            for prev_solution in internal_solutions:
                for constant, string_val in prev_solution.items():
                    solver.add(z3.Not(constant.to_smt() == string_val))

            solver.add(smt_formula)

            solver_result = solver.check()
            if solver_result == z3.unknown:
                self.logger.warning("SMT solver timed out for formula %s", smt_formula)

            if solver_result != z3.sat:
                if not solutions:
                    return []
                else:
                    return solutions

            new_solution = {
                tree_substitutions.get(constant, constant):
                    (
                        val := solver.model()[z3.String(constant.name)].as_string(),
                        DerivationTree(val, []) if constant.is_numeric() else self.parse(constant.n_type, val)
                    )[-1]
                for constant in constants
            }

            new_internal_solution = {
                constant: z3.StringVal(solver.model()[z3.String(constant.name)].as_string())
                for constant in constants}

            if new_solution in solutions:
                # This can happen for trivial solutions, i.e., if the formula is logically valid.
                # Then, the assignment for that constant will always be {}
                return solutions
            else:
                solutions.append(new_solution)
                internal_solutions.append(new_internal_solution)

        return solutions

    def process_new_state(self, new_state: SolutionState) -> List[DerivationTree]:
        return [state.tree for state in self.postprocess_new_state(new_state)
                if self.state_is_valid_or_enqueue(state)]

    def state_is_valid_or_enqueue(self, state: SolutionState) -> bool:
        """
        Returns True if the given state is valid, such that it can be yielded. Returns False and enqueues the state
        if the state is not yet complete, otherwise returns False and discards the state.
        """
        if state.complete():
            assert state.formula_satisfied().is_true()
            return True

        assert all(state.tree.find_node(arg)
                   for predicate_formula in get_conjuncts(state.constraint)
                   if isinstance(predicate_formula, isla.StructuralPredicateFormula)
                   for arg in predicate_formula.args)

        if self.enforce_unique_trees_in_queue and state.tree.structural_hash() in self.tree_hashes_in_queue:
            # Some structures can arise as well from tree insertion (existential quantifier elimination)
            # and expansion; also, tree insertion can yield different trees that have intersecting
            # expansions. We drop those to output more diverse solutions (numbers for SMT solutions
            # and free nonterminals are configurable, so you get more outputs by playing with those!).
            self.logger.debug("Discarding state %s, tree already in queue", str(state))
            return False

        if state.constraint == sc.false():
            self.logger.debug("Discarding state %s", state)
            return False

        state = SolutionState(state.constraint, state.tree, level=self.current_level + 1)

        cost = self.compute_cost(state)
        heapq.heappush(self.queue, (cost, state))
        self.tree_hashes_in_queue.add(state.tree.structural_hash())

        if self.debug:
            self.state_tree[self.current_state].append(state)
            self.costs[state] = cost

        self.logger.debug("Pushing new state %s (hash %d, cost %f)", state, hash(state), cost)
        self.logger.debug("Queue length: %d", len(self.queue))
        if len(self.queue) % 100 == 0:
            self.logger.info("Queue length: %d", len(self.queue))

        # if self.queue_size_limit is not None and len(queue) > self.queue_size_limit:
        #     self.logger.debug(f"Balancing queue")
        #     nlargest = heapq.nlargest(self.queue_no_removed_items, queue)
        #     for elem in nlargest:
        #         queue.remove(elem)
        #     heapq.heapify(queue)

        return False

    def postprocess_new_state(self, new_state: SolutionState) -> List[SolutionState]:
        new_state = self.establish_invariant(new_state)
        new_state = self.remove_nonmatching_universal_quantifiers(new_state)
        new_state = self.remove_infeasible_universal_quantifiers(new_state)

        open_concrete_leaves = list(new_state.tree.open_leaves())
        if (not any(isinstance(conjunct, isla.ExistsFormula) for conjunct in get_conjuncts(new_state.constraint)) and
                open_concrete_leaves and
                all(self.can_be_freely_instantiated(path, new_state)
                    for path, _ in open_concrete_leaves)):
            new_states = [self.remove_nonmatching_universal_quantifiers(state)
                          for state in self.instantiate_free_symbols(new_state)]
        else:
            new_states = [new_state]

        return new_states

    def establish_invariant(self, state: SolutionState) -> SolutionState:
        formula = convert_to_dnf(convert_to_nnf(state.constraint))
        return SolutionState(formula, state.tree)

    def compute_cost(self, state: SolutionState) -> float:
        """Cost of state. Best value: 0, Worst: Unbounded"""

        # How costly is it to finish the tree?
        nonterminals = [leaf.value for _, leaf in state.tree.open_leaves()]
        tree_closing_cost = (
            # len(state.tree) +
            sum([self.symbol_costs[nonterminal]
                 for nonterminal in nonterminals]))

        # Eliminating existential quantifiers (by tree insertion) can be very expensive.
        constraint_cost = len([sub for sub in get_conjuncts(state.constraint)
                               if isinstance(sub, isla.ExistsFormula)])

        # How far are we from matching a universal quantifier?
        match_costs = []
        for universal_formula in [f for f in get_conjuncts(state.constraint) if isinstance(f, isla.ForallFormula)]:
            current_min_cost = sys.maxsize
            for path, leaf_node in state.tree.open_leaves():
                if not universal_formula.in_variable.find_node(leaf_node):
                    continue
                if universal_formula.is_already_matched(leaf_node):
                    continue

                if leaf_node.value == universal_formula.bound_variable.n_type:
                    current_min_cost = 0
                    break

                dist = self.node_distance(leaf_node.value, universal_formula.bound_variable.n_type)
                if dist < current_min_cost:
                    current_min_cost = dist

                if universal_formula.bind_expression is not None:
                    prefix = universal_formula.bind_expression.to_tree_prefix(
                        universal_formula.bound_variable.n_type, self.grammar)

                    i = 1
                    while i < prefix[0].depth() and i < len(path):
                        if state.tree.get_subtree(path[:-i]).is_prefix(prefix[0]):
                            current_min_cost = 0
                            break
                        i += 1
                    else:
                        continue

                    break

            if current_min_cost < sys.maxsize:
                match_costs.append(current_min_cost)

        match_cost = sum(match_costs)

        if len(self.queue) - self.current_cost_phase_since > self.cost_phase_lengths[self.current_cost_phase]:
            self.current_cost_phase_since = len(self.queue)
            self.current_cost_phase = (self.current_cost_phase + 1) % len(self.cost_vectors)
            self.logger.debug(
                "Switching to cost phase %d of %d, vector %s",
                self.current_cost_phase + 1,
                len(self.cost_vectors),
                str(self.cost_vectors[self.current_cost_phase])
            )

        cost_vector = self.cost_vectors[self.current_cost_phase]

        return self.cost_normalizer.compute(
            [tree_closing_cost, match_cost, constraint_cost, state.level],
            cost_vector,
            [True, False, False, False]
        )

    def compute_symbol_costs(self) -> Dict[str, int]:
        self.logger.info("Computing symbol costs")
        result: Dict[str, int] = {}

        for nonterminal in self.grammar:
            fuzzer = GrammarFuzzer(self.grammar)
            tree = fuzzer.expand_tree_with_strategy((nonterminal, None), fuzzer.expand_node_max_cost, 1)
            tree = fuzzer.expand_tree_with_strategy(tree, fuzzer.expand_node_min_cost)
            result[nonterminal] = sum([
                len([expansion for expansion in self.canonical_grammar[tree.value]
                     if any(is_nonterminal(symbol) for symbol in expansion)])
                for _, tree in DerivationTree.from_parse_tree(tree).path_iterator()
                if is_nonterminal(tree.value)
            ]) + 1  # Addition of 1 to avoid 0 cost

        return result

    def remove_nonmatching_universal_quantifiers(self, state: SolutionState) -> SolutionState:
        result = state
        for universal_formula in [conjunct for conjunct in get_conjuncts(state.constraint)
                                  if isinstance(conjunct, isla.ForallFormula)]:
            if (universal_formula.in_variable.is_complete()
                    and not isla.matches_for_quantified_formula(universal_formula)):
                result = SolutionState(
                    isla.replace_formula(result.constraint, universal_formula, sc.true()), result.tree)

        return result

    def remove_infeasible_universal_quantifiers(self, state: SolutionState) -> SolutionState:
        result = state
        for universal_formula in [conjunct for conjunct in get_conjuncts(state.constraint)
                                  if isinstance(conjunct, isla.ForallFormula)]:
            matching_nodes = universal_formula.in_variable.filter(
                lambda sub: sub.value == universal_formula.bound_variable.n_type)

            if any(tree.id not in universal_formula.already_matched for _, tree in matching_nodes):
                continue

            if any(self.reachable(leaf.value, universal_formula.bound_variable.n_type)
                   for _, leaf in universal_formula.in_variable.open_leaves()):
                continue

            result = SolutionState(
                isla.replace_formula(result.constraint, universal_formula, sc.true()), result.tree)

        return result

    def instantiate_free_symbols(self, new_state: SolutionState) -> OrderedSet[SolutionState]:
        """
        Instantiates free nonterminals and constants up to the set bound if the state only consists of top assignments.

        :param new_state: The state to expand
        :return: A new set of states
        """

        result: OrderedSet[SolutionState] = OrderedSet([])
        fuzzer = GrammarCoverageFuzzer(self.grammar)

        for _ in range(self.max_number_free_instantiations):
            substitutions: Dict[DerivationTree, DerivationTree] = {
                subtree: DerivationTree.from_parse_tree(fuzzer.expand_tree((subtree.value, None)))
                for path, subtree in new_state.tree.open_leaves()
                if self.can_be_freely_instantiated(path, new_state)
            }

            if substitutions:
                result.add(
                    SolutionState(new_state.constraint.substitute_expressions(substitutions),
                                  new_state.tree.substitute(substitutions)))

        return result or OrderedSet([new_state])

    def can_be_freely_instantiated(self, path_to_leaf: Path, state: SolutionState) -> bool:
        # An instantiation is only then *not* free if
        # 1) instantiating it might lead to an expression that might match a quantifier
        # 2) the leaf to expand is part of a tree that is an argument to an SMT formula
        # 3) the leaf to expand is bound by a semantic predicate formula.
        conjuncts = get_conjuncts(state.constraint)

        # universal_formulas = [formula for formula in conjuncts
        #                      if (not self.expand_after_existential_elimination
        #                          and isinstance(formula, isla.ForallFormula)
        #                          or self.expand_after_existential_elimination
        #                          and isinstance(formula, isla.QuantifiedFormula))]
        universal_formulas = [formula for formula in conjuncts
                              if isinstance(formula, isla.ForallFormula)]

        smt_formulas = [formula for formula in conjuncts
                        if isinstance(formula, isla.SMTFormula)]
        semantic_predicate_formulas = [formula for formula in conjuncts
                                       if isinstance(formula, isla.SemanticPredicateFormula)]
        leaf_node = state.tree.get_subtree(path_to_leaf)

        return (not any(self.quantified_formula_might_match(qfd_formula, path_to_leaf, state.tree)
                        for qfd_formula in universal_formulas)
                and all(tree_arg.find_node(leaf_node) is None
                        for smt_formula in smt_formulas
                        for tree_arg in smt_formula.tree_arguments())
                and not any(semantic_formula.binds_tree(leaf_node)
                            for semantic_formula in semantic_predicate_formulas)
                )

    def quantified_formula_might_match(
            self, qfd_formula: isla.QuantifiedFormula, path_to_nonterminal: Path, tree: DerivationTree) -> bool:
        node = tree.get_subtree(path_to_nonterminal)

        if qfd_formula.in_variable.find_node(node) is None:
            return False

        if isinstance(qfd_formula, isla.ForallFormula) and qfd_formula.is_already_matched(node):
            return False

        qfd_nonterminal = qfd_formula.bound_variable.n_type
        if qfd_nonterminal == node.value or self.reachable(node.value, qfd_nonterminal):
            return True

        if (qfd_formula.bind_expression is not None
                and node.value in [var.n_type for var in qfd_formula.bind_expression.bound_variables()]):
            prefix_tree, _ = qfd_formula.bind_expression.to_tree_prefix(
                qfd_formula.bound_variable.n_type, self.grammar)

            for idx in reversed(range(len(path_to_nonterminal))):
                subtree = tree.get_subtree(path_to_nonterminal[:idx])
                if subtree.is_prefix(prefix_tree):
                    return True

        return False

    @lru_cache(maxsize=None)
    def node_distance(self, nonterminal: str, to_nonterminal: str) -> int:
        if self.precompute_reachability:
            return self.node_distances[nonterminal][to_nonterminal]
        else:
            to_node = self.graph.get_node(to_nonterminal)
            return self.graph.dijkstra(self.graph.get_node(nonterminal), to_node)[0][to_node]

    def reachable(self, nonterminal: str, to_nonterminal: str) -> bool:
        return self.node_distance(nonterminal, to_nonterminal) < sys.maxsize

    @lru_cache(maxsize=None)
    def extract_regular_expression(self, nonterminal: str) -> z3.ReRef:
        regex_conv = RegexConverter(self.grammar, compress_unions=True)
        return regex_conv.to_regex(nonterminal)

    def parse(self, nonterminal: str, input: str) -> DerivationTree:
        grammar = copy.deepcopy(self.grammar)
        grammar["<start>"] = [nonterminal]
        delete_unreachable(grammar)
        parser = EarleyParser(grammar)
        return DerivationTree.from_parse_tree(list(parser.parse(input))[0][1][0])


class CostNormalizer:
    def __init__(self):
        self.history: List[List[float]] = []

    def compute(self, costs: List[float], weights: List[float], do_average: Optional[List[bool]] = None) -> float:
        if len(self.history) < 100:
            self.add_to_history(costs)
        else:
            self.add_to_history(costs)

        averages = [1 if not do_average or not do_average[idx]
                    else sum(subhistory) / len(subhistory)
                    for idx, subhistory in enumerate(self.history)]
        return sum([a_cost * weights[idx] / averages[idx] for idx, a_cost in enumerate(costs)])

    def add_to_history(self, costs: List[float]):
        if not self.history:
            self.history.extend([[] for _ in costs])

        if len(self.history[0]) > 100:
            self.history = [subhistory[1:] for subhistory in self.history]

        for idx, cost in enumerate(costs):
            self.history[idx].append(cost)


def qfr_free_formula_to_z3_formula(formula: isla.Formula) -> z3.BoolRef:
    if isinstance(formula, isla.SMTFormula):
        return formula.formula
    elif isinstance(formula, isla.NegatedFormula):
        return z3.Not(qfr_free_formula_to_z3_formula(formula.args[0]))
    if isinstance(formula, isla.ConjunctiveFormula):
        return z3.And(*[qfr_free_formula_to_z3_formula(child) for child in formula.args])
    elif isinstance(formula, isla.DisjunctiveFormula):
        return z3.Or(*[qfr_free_formula_to_z3_formula(child) for child in formula.args])

    assert False


def is_semantic_formula(formula: isla.Formula) -> bool:
    pred_qfr_visitor = isla.FilterVisitor(lambda f:
                                          isinstance(f, isla.StructuralPredicateFormula) or
                                          isinstance(f, isla.QuantifiedFormula))
    return not pred_qfr_visitor.collect(formula)


def get_conjuncts(formula: isla.Formula) -> List[isla.Formula]:
    return [conjunct
            for disjunct in split_disjunction(formula)
            for conjunct in split_conjunction(disjunct)]


def quantified_nonterminals_reachable(
        graph: GrammarGraph, formula: isla.QuantifiedFormula, tree: DerivationTree) -> bool:
    if any(formula.bound_variable.n_type == leaf or
           graph.get_node(leaf).reachable(graph.get_node(formula.bound_variable.n_type))
           for _, (leaf, _) in tree.open_leaves()):
        # If the bound variable is reachable from a leaf, we return True also for formulas with bind expression,
        # since we assume that bind expressions yield feasible subtrees.
        return True

    if formula.bind_expression is None:
        return False

    # For formulas with bind expressions, it is possible that we have a subtree with the bound variable nonterminal
    # as inner node and leaves from which the bound nonterminals from the bind expression are reachable.

    subtrees = [subtree for _, subtree in tree.path_iterator()
                if subtree.value == formula.bound_variable.n_type]
    interesting_nonterminals = [variable.n_type for variable in formula.bind_expression.bound_variables()]

    return all(any(any(nonterminal == leaf
                       or graph.get_node(leaf).reachable(graph.get_node(nonterminal))
                       for _, (leaf, _) in subtree.open_leaves())
                   for subtree in subtrees)
               for nonterminal in interesting_nonterminals)


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
