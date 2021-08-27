import copy
import heapq
import logging
from functools import reduce, lru_cache
from typing import Generator, Dict, List, Set, cast, Optional, Tuple, Union

import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import is_nonterminal, nonterminals
from fuzzingbook.Parser import canonical, EarleyParser
from grammar_graph.gg import GrammarGraph
from grammar_to_regex.cfg2regex import RegexConverter
from orderedset import OrderedSet

import input_constraints.isla_shortcuts as sc
from input_constraints import isla
from input_constraints.existential_helpers import insert_tree
from input_constraints.helpers import visit_z3_expr, delete_unreachable, dict_of_lists_to_list_of_dicts, \
    replace_line_breaks
from input_constraints.isla import DerivationTree, VariablesCollector, split_conjunction, split_disjunction, \
    convert_to_dnf, convert_to_nnf, ensure_unique_bound_variables
from input_constraints.type_defs import Grammar, Path


class SolutionState:
    def __init__(self, constraint: isla.Formula, tree: DerivationTree):
        self.constraint = constraint
        self.tree = tree
        self.__hash = None

    def formula_satisfied(self) -> bool:
        if self.tree.is_open():
            # Have to instantiate variables first
            return False

        return isla.evaluate(self.constraint, reference_tree=self.tree)

    def complete(self) -> bool:
        if not self.tree.is_complete():
            return False

        # We assume that any universal quantifier has already been instantiated, if it matches,
        # and is thus satisfied, or another unsatisfied constraint resulted from the instantiation.
        # Existential, predicate, and SMT formulas have to be eliminated first.
        return any(all(not isinstance(conjunct, isla.StructuralPredicateFormula)
                       and (not isinstance(conjunct, isla.SMTFormula) or conjunct == sc.true())
                       and not isinstance(conjunct, isla.ExistsFormula)
                       and (not isinstance(conjunct, isla.ForallFormula) or len(conjunct.already_matched) > 0)
                       for conjunct in split_conjunction(disjunct))
                   for disjunct in split_disjunction(self.constraint))

    def variables(self) -> Set[isla.Variable]:
        result: Set[isla.Variable] = set()
        for constant, formula, tree in self:
            result.update(isla.VariablesCollector().collect(formula))
            result.update(tree.tree_variables())
        return result

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
                 expand_after_existential_elimination: bool = False,
                 enforce_unique_trees_in_queue: bool = True,
                 ):
        """
        :param grammar: The underlying grammar.
        :param formula: The formula to solve.
        :param max_number_free_instantiations: Number of times that nonterminals that are not bound by any formula
        should be expanded by a coverage-based fuzzer.
        :param max_number_smt_instantiations: Number of solutions of SMT formulas that should be produced.
        :param expand_after_existential_elimination: Trees are expanded after an existential quantifier elimination
        iff this paramter is set to true. If false, only a finite (potentially small) set of inputs is generated for
        existential constraints.
        :param enforce_unique_trees_in_queue: If true, only one state in the queue containing a tree with the same
        structure can be present at a time. Should be set to false especially if there are top-level SMT formulas
        about numeric constants. TODO: This parameter is awkward, maybe we can find a different solution.
        """
        self.logger = logging.getLogger(type(self).__name__)

        self.grammar = grammar
        self.canonical_grammar = canonical(grammar)
        self.node_leaf_distances: Dict[str, int] = self.compute_node_leaf_distances()

        self.formula = ensure_unique_bound_variables(formula)
        top_constants: Set[isla.Constant] = set(
            [c for c in VariablesCollector().collect(self.formula)
             if isinstance(c, isla.Constant)
             and not c.is_numeric()])
        assert len(top_constants) == 1
        self.top_constant = next(iter(top_constants))

        self.max_number_free_instantiations: int = max_number_free_instantiations
        self.max_number_smt_instantiations: int = max_number_smt_instantiations
        self.expand_after_existential_elimination = expand_after_existential_elimination
        self.enforce_unique_trees_in_queue = enforce_unique_trees_in_queue

        # Initialize Queue
        initial_tree = DerivationTree(self.top_constant.n_type, None)
        initial_formula = self.formula.substitute_expressions({self.top_constant: initial_tree})
        initial_state = self.establish_invariant(SolutionState(initial_formula, initial_tree))

        self.queue: List[Tuple[float, SolutionState]] = []
        self.tree_hashes_in_queue: Set[int] = {initial_tree.structural_hash()}
        heapq.heappush(self.queue, (0, initial_state))

    def solve(self) -> Generator[DerivationTree, None, None]:
        while self.queue:
            cost: int
            state: SolutionState
            cost, state = heapq.heappop(self.queue)
            self.tree_hashes_in_queue.discard(state.tree.structural_hash())
            self.logger.debug(f"Polling new state %s (hash %d)", state, hash(state))
            self.logger.debug(f"Queue length: %s", len(self.queue))

            # Split disjunctions
            if isinstance(state.constraint, isla.DisjunctiveFormula):
                for disjunct in split_disjunction(state.constraint):
                    heapq.heappush(self.queue, (cost, SolutionState(disjunct, state.tree)))
                continue

            # Instantiate all top-level structural predicate formulas.
            state = instantiate_structural_predicates(state)

            if state.constraint == sc.false():
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
                if (not self.expand_after_existential_elimination
                        or any(result_state.constraint == sc.true() for result_state in result_states)):
                    continue

            # Match all universal formulas
            result_states = self.match_all_universal_formulas(state)
            if result_states is not None:
                yield from [result for new_state in result_states
                            for result in self.process_new_state(new_state)]
                continue

            for new_state in self.postprocess_new_state(state):
                if new_state.complete() and new_state.formula_satisfied():
                    yield new_state.tree
                    continue

                # Expand the tree
                expanded_states = self.expand_tree(new_state)
                assert len(expanded_states) > 0, f"State {new_state} will never leave the queue."
                yield from [result for expanded_state in expanded_states
                            for result in self.process_new_state(expanded_state)]

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
            evaluation_result = semantic_predicate_formula.evaluate(self.grammar)
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

            return SolutionState(
                state.constraint.substitute_expressions(evaluation_result.result),
                state.tree.substitute(evaluation_result.result),
            )

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
            self.logger.debug("Eliminating existential formula %s", existential_formulas[0])
            new_states.extend(self.eliminate_existential_formula(existential_formulas[0], state))

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
            for leaf_path, leaf_node in state.tree.open_concrete_leaves()
            if not self.can_be_freely_instantiated(leaf_path, state)
        })

        if len(possible_expansions) == 1 and not possible_expansions[0]:
            return []

        result: List[SolutionState] = []

        for possible_expansion in possible_expansions:
            expanded_tree = state.tree
            for path, new_children in possible_expansion.items():
                leaf_node = expanded_tree.get_subtree(path)
                expanded_tree = expanded_tree.replace_path(path, DerivationTree(leaf_node.value, new_children))

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
                isla.matches_for_quantified_formula(universal_formula)

            for match in matches:
                bound_var_match_tree = match[universal_formula.bound_variable][1]

                if universal_formula.is_already_matched(bound_var_match_tree):
                    continue

                matched = True

                inst_formula = universal_formula.inner_formula.substitute_expressions({
                    variable: match_tree for variable, (_, match_tree) in match.items()
                })

                context_formula = inst_formula & isla.replace_formula(
                    context_formula,
                    universal_formula,
                    universal_formula.add_already_matched({match_tree for _, match_tree in match.values()})
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
                existential_formula.bound_variable.n_type, self.grammar, to_abstract_tree=False)
            inserted_tree = tree_prefix
        else:
            inserted_tree = DerivationTree(existential_formula.bound_variable.n_type, None)

        insertion_result = insert_tree(self.canonical_grammar, inserted_tree, state.tree)

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

            if solver.check() != z3.sat:
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

    def process_new_state(
            self, new_state: SolutionState,
            cost_reduction: Optional[float] = None,
    ) -> List[DerivationTree]:
        return [state.tree for state in self.postprocess_new_state(new_state)
                if self.state_is_valid_or_enqueue(state, cost_reduction)]

    def state_is_valid_or_enqueue(self,
                                  state: SolutionState,
                                  cost_reduction: Optional[float] = None) -> bool:
        """
        Returns True if the given state is valid, such that it can be yielded. Returns False and enqueues the state
        if the state is not yet complete, otherwise returns False and discards the state.
        """
        if state.complete():
            if state.formula_satisfied():
                return True

            # In certain occasions, it can happen that a complete state does not satisfy the constraint.
            # A typical (maybe the only) case is when an existential quantifier is eliminated and the
            # original constraint is re-attached. Then, the there might be several options for matching
            # the existential quantifier again, some of which will be unsuccessful.
            #
            # Complete, but invalid states are discarded and not enqueued
            self.logger.debug(f"Discarding state %s (unsatisfied constraint)", state)
            return False

        assert all(all(state.tree.find_node(arg) for arg in predicate_formula.args)
                   for predicate_formula in get_conjuncts(state.constraint)
                   if isinstance(predicate_formula, isla.StructuralPredicateFormula))

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

        heapq.heappush(self.queue, (self.compute_cost(state, cost_reduction or 1.0), state))
        self.tree_hashes_in_queue.add(state.tree.structural_hash())

        self.logger.debug(f"Pushing new state %s (hash %d)", state, hash(state))
        self.logger.debug(f"Queue length: %d", len(self.queue))
        if len(self.queue) % 100 == 0:
            self.logger.info(f"Queue length: %d", len(self.queue))

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

        open_concrete_leaves = list(new_state.tree.open_concrete_leaves())
        if (not any(isinstance(conjunct, isla.ExistsFormula) for conjunct in get_conjuncts(new_state.constraint))
                and open_concrete_leaves
                and all(self.can_be_freely_instantiated(path, new_state)
                        for path, _ in open_concrete_leaves)):
            new_states = [self.remove_nonmatching_universal_quantifiers(state)
                          for state in self.instantiate_free_symbols(new_state)]
        else:
            new_states = [new_state]

        return new_states

    def establish_invariant(self, state: SolutionState) -> SolutionState:
        formula = convert_to_dnf(convert_to_nnf(state.constraint))
        return SolutionState(formula, state.tree)

    def compute_cost(self, state: SolutionState, cost_reduction: float = 1.0) -> float:
        """Cost of state. Best value: 0, Worst: Unbounded"""
        # return cost_reduction * len(state.tree)

        nonterminals = [leaf.value for _, leaf in state.tree.open_leaves()]
        return cost_reduction * (
                len(state.tree) +
                sum([self.node_leaf_distances[nonterminal] for nonterminal in nonterminals])
        )

    def compute_node_leaf_distances(self) -> Dict[str, int]:
        self.logger.info("Computing node-to-leaf distances")
        result: Dict[str, int] = {}
        graph = GrammarGraph.from_grammar(self.grammar)
        leaves = [graph.get_node(nonterminal) for nonterminal in self.grammar
                  if any(len(nonterminals(expansion)) == 0
                         for expansion in self.grammar[nonterminal])]

        for nonterminal in self.grammar:
            dist, _ = graph.dijkstra(graph.get_node(nonterminal))
            result[nonterminal] = min([dist[leaf] for leaf in leaves])

        return result

    def remove_nonmatching_universal_quantifiers(self, state: SolutionState) -> SolutionState:
        conjuncts = get_conjuncts(state.constraint)
        if any(isinstance(conjunct, isla.ExistsFormula) for conjunct in conjuncts):
            return state

        result = state
        for universal_formula in [conjunct for conjunct in conjuncts if isinstance(conjunct, isla.ForallFormula)]:
            if (universal_formula.in_variable.is_complete()
                    and not isla.matches_for_quantified_formula(universal_formula)):
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
        # 2) the nonterminal to instantiate is part of a tree that is an argument
        #    to an SMT formula or semantic predicate formula
        conjuncts = get_conjuncts(state.constraint)

        universal_formulas = [formula for formula in conjuncts
                              if (not self.expand_after_existential_elimination
                                  and isinstance(formula, isla.ForallFormula)
                                  or self.expand_after_existential_elimination
                                  and isinstance(formula, isla.QuantifiedFormula))]

        semantic_formulas = [formula for formula in conjuncts
                             if isinstance(formula, isla.SMTFormula)
                             or isinstance(formula, isla.SemanticPredicateFormula)]
        leaf_node = state.tree.get_subtree(path_to_leaf)

        return (not any(self.quantified_formula_might_match(qfd_formula, path_to_leaf, state)
                        for qfd_formula in universal_formulas)
                and all(all(tree_arg.find_node(leaf_node) is None
                            for tree_arg in semantic_formula.tree_arguments())
                        for semantic_formula in semantic_formulas)
                )

    def quantified_formula_might_match(
            self, qfd_formula: isla.QuantifiedFormula, path_to_nonterminal: Path, state: SolutionState) -> bool:
        node = state.tree.get_subtree(path_to_nonterminal)

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
                qfd_formula.bound_variable.n_type, self.grammar, to_abstract_tree=False)

            for idx in reversed(range(len(path_to_nonterminal))):
                subtree = state.tree.get_subtree(path_to_nonterminal[:idx])
                if subtree.is_prefix(prefix_tree):
                    return True

        return False

    @lru_cache()
    def reachable(self, nonterminal: str, to_nonterminal: str) -> bool:
        graph = GrammarGraph.from_grammar(self.grammar)
        return graph.get_node(nonterminal).reachable(graph.get_node(to_nonterminal))

    @lru_cache()
    def extract_regular_expression(self, nonterminal: str) -> z3.ReRef:
        regex_conv = RegexConverter(self.grammar, compress_unions=True)
        return regex_conv.to_regex(nonterminal)

    def parse(self, nonterminal: str, input: str) -> DerivationTree:
        grammar = copy.deepcopy(self.grammar)
        grammar["<start>"] = [nonterminal]
        delete_unreachable(grammar)
        parser = EarleyParser(grammar)
        return DerivationTree.from_parse_tree(list(parser.parse(input))[0][1][0])


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


def instantiate_structural_predicates(state: SolutionState) -> SolutionState:
    # Note: The current interpretation of these Python (non-SMT) predicates is that they are *structural* predicate,
    #       i.e., they are only concerned about positions / paths and not about actual parse trees.
    #       This means that we can already evaluate them when they still contain constants, as long as the constants
    #       occur in the derivation tree.
    predicate_formulas = [
        conjunct for conjunct in get_conjuncts(state.constraint)
        if isinstance(conjunct, isla.StructuralPredicateFormula)]

    formula = state.constraint
    for predicate_formula in predicate_formulas:
        instantiation = isla.SMTFormula(z3.BoolVal(predicate_formula.evaluate(state.tree)))
        formula = isla.replace_formula(formula, predicate_formula, instantiation)

    return SolutionState(formula, state.tree)


def get_conjuncts(formula: isla.Formula) -> List[isla.Formula]:
    return [conjunct
            for disjunct in split_disjunction(formula)
            for conjunct in split_conjunction(disjunct)]


def quantified_nonterminals_reachable(
        grammar: Grammar, formula: isla.QuantifiedFormula, tree: DerivationTree) -> bool:
    graph = GrammarGraph.from_grammar(grammar)

    if any(formula.bound_variable.n_type == leaf or
           graph.get_node(leaf).reachable(graph.get_node(formula.bound_variable.n_type))
           for _, (leaf, _) in tree.open_concrete_leaves()):
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
                       for _, (leaf, _) in subtree.open_concrete_leaves())
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
