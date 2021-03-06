import copy
import functools
import heapq
import itertools
import logging
import operator
import random
import sys
import time
from abc import ABC
from dataclasses import dataclass
from functools import reduce, lru_cache

import math
import pkg_resources
import z3
from grammar_graph import gg
from grammar_graph.gg import GrammarGraph
from grammar_to_regex.cfg2regex import RegexConverter
from grammar_to_regex.regex import regex_to_z3
from orderedset import OrderedSet
from packaging import version
from typing import Generator, Dict, List, Set, Optional, Tuple, Union, cast, Callable

import isla.evaluator
import isla.helpers
import isla.isla_shortcuts as sc
import isla.three_valued_truth
from isla import language
from isla.existential_helpers import insert_tree, DIRECT_EMBEDDING, SELF_EMBEDDING, CONTEXT_ADDITION
from isla.fuzzer import GrammarFuzzer, GrammarCoverageFuzzer
from isla.helpers import delete_unreachable, dict_of_lists_to_list_of_dicts, \
    replace_line_breaks, weighted_geometric_mean, assertions_activated, \
    split_str_with_nonterminals, cluster_by_common_elements, is_nonterminal, canonical, lazyjoin, lazystr, is_prefix
from isla.isla_predicates import STANDARD_STRUCTURAL_PREDICATES, STANDARD_SEMANTIC_PREDICATES, COUNT_PREDICATE
from isla.language import VariablesCollector, split_conjunction, split_disjunction, \
    convert_to_dnf, convert_to_nnf, ensure_unique_bound_variables, parse_isla, get_conjuncts, QuantifiedFormula
from isla.derivation_tree import DerivationTree
from isla.parser import EarleyParser
from isla.type_defs import Grammar, Path
from isla.z3_helpers import z3_solve, z3_subst, z3_eq


class SolutionState:
    def __init__(self, constraint: language.Formula, tree: DerivationTree, level: int = 0):
        self.constraint = constraint
        self.tree = tree
        self.level = level
        self.__hash = None

    def formula_satisfied(self, grammar: Grammar) -> isla.three_valued_truth.ThreeValuedTruth:
        if self.tree.is_open():
            # Have to instantiate variables first
            return isla.three_valued_truth.ThreeValuedTruth.unknown()

        return isla.evaluator.evaluate(self.constraint, self.tree, grammar)

    def complete(self) -> bool:
        if not self.tree.is_complete():
            return False

        # We assume that any universal quantifier has already been instantiated, if it matches,
        # and is thus satisfied, or another unsatisfied constraint resulted from the instantiation.
        # Existential, predicate, and SMT formulas have to be eliminated first.

        # return any(all(not isinstance(conjunct, language.StructuralPredicateFormula)
        #                and (not isinstance(conjunct, language.SMTFormula) or conjunct == sc.true())
        #                and not isinstance(conjunct, language.SemanticPredicateFormula)
        #                and not isinstance(conjunct, language.ExistsFormula)
        #                and (not isinstance(conjunct, language.ForallFormula) or len(conjunct.already_matched) > 0)
        #                for conjunct in split_conjunction(disjunct))
        #            for disjunct in split_disjunction(self.constraint))

        return self.constraint == sc.true()

    def variables(self) -> Set[language.Variable]:
        return set(language.VariablesCollector.collect(self.constraint))

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


@dataclass
class CostWeightVector:
    tree_closing_cost: float = 0,
    constraint_cost: float = 0,
    derivation_depth_penalty: float = 0,
    low_k_coverage_penalty: float = 0,
    low_global_k_path_coverage_penalty: float = 0

    def __iter__(self):
        return iter([
            self.tree_closing_cost,
            self.constraint_cost,
            self.derivation_depth_penalty,
            self.low_k_coverage_penalty,
            self.low_global_k_path_coverage_penalty
        ])

    def __getitem__(self, item):
        assert isinstance(item, int)
        return [
            self.tree_closing_cost,
            self.constraint_cost,
            self.derivation_depth_penalty,
            self.low_k_coverage_penalty,
            self.low_global_k_path_coverage_penalty
        ][item]


@dataclass(frozen=True)
class CostSettings:
    weight_vector: CostWeightVector
    k: int = 3

    def __init__(self, weight_vector: CostWeightVector, k: int = 3):
        assert isinstance(weight_vector, CostWeightVector)
        assert isinstance(k, int)
        object.__setattr__(self, 'weight_vector', weight_vector)
        object.__setattr__(self, 'k', k)


STD_COST_SETTINGS = CostSettings(
    CostWeightVector(
        tree_closing_cost=7,
        constraint_cost=3,
        derivation_depth_penalty=5,
        low_k_coverage_penalty=20,
        low_global_k_path_coverage_penalty=12),
    k=3)


class ISLaSolver:
    def __init__(self,
                 grammar: Grammar,
                 formula: Union[language.Formula, str],
                 structural_predicates: Set[language.StructuralPredicate] = STANDARD_STRUCTURAL_PREDICATES,
                 semantic_predicates: Set[language.SemanticPredicate] = STANDARD_SEMANTIC_PREDICATES,
                 max_number_free_instantiations: int = 10,
                 max_number_smt_instantiations: int = 10,
                 max_number_tree_insertion_results: int = 5,
                 enforce_unique_trees_in_queue: bool = True,
                 precompute_reachability: bool = False,
                 debug: bool = False,
                 cost_computer: Optional['CostComputer'] = None,
                 timeout_seconds: Optional[int] = None,
                 global_fuzzer: bool = False,
                 predicates_unique_in_int_arg: Tuple[language.SemanticPredicate, ...] = (COUNT_PREDICATE,),
                 fuzzer_factory: Callable[[Grammar], GrammarFuzzer] = lambda grammar: GrammarCoverageFuzzer(grammar),
                 tree_insertion_methods=DIRECT_EMBEDDING + SELF_EMBEDDING + CONTEXT_ADDITION):
        """
        :param grammar: The underlying grammar.
        :param formula: The formula to solve.
        :param max_number_free_instantiations: Number of times that nonterminals that are not bound by any formula
        should be expanded by a coverage-based fuzzer.
        :param max_number_smt_instantiations: Number of solutions of SMT formulas that should be produced.
        :param precompute_reachability: If true, the distances between all grammar nodes are pre-computed using
        Floyd-Warshall's algorithm. This makes sense if there are many expensive distance queries, e.g., in a big
        grammar and a constraint with relatively many universal quantifiers.
        :param debug: If true, debug information about the evolution of states is collected, notably in the
        field state_tree. The root of the tree is in the field state_tree_root. The field costs stores the computed
        cost values for all new nodes.
        :param global_fuzzer: If set to True, only one coverage-guided grammar fuzzer object is used to finish
        off unconstrained open derivation trees throughout the whole generation time. This may be beneficial for
        some targets; e.g., we experienced that CSV works significantly faster. However, the achieved k-path coverage
        can be lower with that setting.
        :param predicates_unique_in_int_arg: This is needed in certain cases for instantiating universal
        integer quantifiers. The supplied predicates should have exactly one integer argument, and hold
        for exactly one integer value once all other parameters are fixed.
        :param fuzzer_factory: Constructor of the fuzzer to use for instantiating "free" nonterminals.
        :param tree_insertion_methods: Combination of methods to use for existential quantifier elimination by
        tree insertion. Full selection: `DIRECT_EMBEDDING & SELF_EMBEDDING & CONTEXT_ADDITION`.
        """
        self.logger = logging.getLogger(type(self).__name__)

        # We require at least z3 4.8.13.0. ISLa might work for some older versions, but
        # at least for 4.8.8.0, we have witnessed that certain rather easy constraints,
        # like equations, don't work since z3 cannot handle the restrictions to more
        # complicated regular expressions. This happened in the XML case study with
        # constraints of the kind <id> == <id_no_prefix>. At least with 4.8.13.0, this
        # works flawlessly, but times out for 4.8.8.0.
        #
        # This should be solved using Python requirements, which however cannot be done
        # currently since the fuzzingbook library inflexibly binds z3 to 4.8.8.0. Thus,
        # one has to manually install a newer version and ignore the warning.

        z3_version = pkg_resources.get_distribution("z3-solver").version
        assert version.parse(z3_version) >= version.parse("4.8.13.0"), \
            f"ISLa requires at least z3 4.8.13.0, present: {z3_version}. " \
            f"Please install a newer z3 version, e.g., using 'pip install z3-solver==4.8.14.0'."

        self.grammar = grammar
        self.graph = GrammarGraph.from_grammar(grammar)
        self.canonical_grammar = canonical(grammar)
        self.timeout_seconds = timeout_seconds
        self.global_fuzzer = global_fuzzer
        self.fuzzer_factory = fuzzer_factory
        self.predicates_unique_in_int_arg: Set[language.SemanticPredicate] = set(predicates_unique_in_int_arg)
        self.tree_insertion_methods = tree_insertion_methods

        self.cost_computer = (
            cost_computer if cost_computer is not None
            else GrammarBasedBlackboxCostComputer(STD_COST_SETTINGS, self.graph))

        if isinstance(formula, str):
            formula = parse_isla(formula, grammar, structural_predicates, semantic_predicates)

        self.formula = ensure_unique_bound_variables(formula)
        top_constants: Set[language.Constant] = set(
            [c for c in VariablesCollector.collect(self.formula)
             if isinstance(c, language.Constant)
             and not c.is_numeric()])
        assert len(top_constants) == 1
        self.top_constant = next(iter(top_constants))

        quantifier_chains: List[Tuple[language.ForallFormula, ...]] = [
            tuple([f for f in c if isinstance(f, language.ForallFormula)])
            for c in get_quantifier_chains(formula)]
        # TODO: Remove?
        self.quantifier_chains: List[Tuple[language.ForallFormula, ...]] = [c for c in quantifier_chains if c]

        self.max_number_free_instantiations: int = max_number_free_instantiations
        self.max_number_smt_instantiations: int = max_number_smt_instantiations
        self.max_number_tree_insertion_results = max_number_tree_insertion_results
        self.enforce_unique_trees_in_queue = enforce_unique_trees_in_queue

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
        initial_state = SolutionState(initial_formula, initial_tree)
        initial_states = self.establish_invariant(initial_state)

        self.queue: List[Tuple[float, SolutionState]] = []
        self.tree_hashes_in_queue: Set[int] = {initial_tree.structural_hash()}
        self.state_hashes_in_queue: Set[int] = {hash(state) for state in initial_states}
        for state in initial_states:
            heapq.heappush(self.queue, (self.compute_cost(state), state))
        self.current_level = 0

        # Debugging stuff
        self.debug = debug
        self.state_tree: Dict[SolutionState, List[SolutionState]] = {}  # is only filled if self.debug
        self.state_tree_root = None
        self.current_state = None
        self.costs: Dict[SolutionState, float] = {}

        if self.debug:
            self.state_tree[initial_state] = initial_states
            self.state_tree_root = initial_state
            self.costs[initial_state] = 0
            for state in initial_states:
                self.costs[state] = self.compute_cost(state)

    def solve(self) -> Generator[DerivationTree, None, None]:
        start_time = int(time.time())
        fuzzer = self.fuzzer_factory(self.grammar)

        while self.queue:
            if self.timeout_seconds is not None:
                if int(time.time()) - start_time > self.timeout_seconds:
                    return

            # import dill as pickle
            # state_hash = 7615739788910218270
            # out_file = "/tmp/saved_debug_state"
            # if hash(self.queue[0][1]) == state_hash:
            #     with open(out_file, 'wb') as debug_state_file:
            #         pickle.dump(self, debug_state_file)
            #     print(f"Dumping state to {out_file}")
            #     exit()

            cost: int
            state: SolutionState
            cost, state = heapq.heappop(self.queue)

            self.current_level = state.level
            self.tree_hashes_in_queue.discard(state.tree.structural_hash())
            self.state_hashes_in_queue.discard(hash(state))

            if self.debug:
                self.current_state = state
                self.state_tree.setdefault(state, [])
            self.logger.debug(f"Polling new state %s (hash %d, cost %f)", state, hash(state), cost)
            self.logger.debug(f"Queue length: %s", len(self.queue))

            assert not isinstance(state.constraint, language.DisjunctiveFormula)

            # Instantiate all top-level structural predicate formulas.
            state = self.instantiate_structural_predicates(state)

            if state.constraint == sc.false():
                continue

            # Eliminate existential quantifiers over integers -> replace by constants
            result_state = self.eliminate_existential_integer_quantifiers(state)
            if result_state is not None:
                yield from self.process_new_state(result_state)
                continue

            # Eliminate universal quantifiers over integers -> random choice up to max_number_free_instantiations times
            result_states = self.instantiate_universal_integer_quantifiers(state)
            if result_states is not None:
                yield from self.process_new_states(result_states)
                continue

            # Match all universal formulas
            result_states = self.match_all_universal_formulas(state)
            if result_states is not None:
                yield from self.process_new_states(result_states)
                continue

            # Expand if there are any not yet eliminated / matched universal quantifiers
            if any(isinstance(conjunct, language.ForallFormula) for conjunct in get_conjuncts(state.constraint)):
                expanded_states = self.expand_tree(state)
                assert len(expanded_states) > 0, f"State {state} will never leave the queue."

                self.logger.debug("Expanding state %s (%d successors)", state, len(expanded_states))
                yield from self.process_new_states(expanded_states)
                continue

            # Eliminate all semantic formulas
            result_states = self.eliminate_all_semantic_formulas(state)
            if result_states is not None:
                yield from self.process_new_states(result_states)
                continue

            # Eliminate all ready semantic predicate formulas
            result_state = self.eliminate_all_ready_semantic_predicate_formulas(state)
            if result_state is not None:
                yield from self.process_new_state(result_state)
                continue

            # Eliminate first existential formula
            result_states = self.eliminate_first_match_all_existential_formulas(state)
            if result_states is not None:
                yield from self.process_new_states(result_states)
                # Also add some expansions of the original state, to create a larger
                # solution stream (otherwise, it might be possible that only a small
                # finite number of solutions are generated for existential formulas).
                yield from self.process_new_states(self.expand_tree(state, limit=2, only_universal=False))
                continue

            # semantic predicate formulas can remain if they bind lazily. In that case, we can choose a random
            # instantiation and let the predicate "fix" the resulting tree.
            assert (state.constraint == sc.true() or
                    all(isinstance(conjunct, language.SemanticPredicateFormula)
                        or (isinstance(conjunct, language.NegatedFormula) and
                            isinstance(conjunct.args[0], language.SemanticPredicateFormula))
                        for conjunct in get_conjuncts(state.constraint))), \
                f"Constraint is not true and contains formulas " \
                f"other than semantic predicate formulas: {state.constraint}"
            assert (state.constraint == sc.true() or
                    all(not pred_formula.binds_tree(leaf)
                        for pred_formula in get_conjuncts(state.constraint)
                        if isinstance(pred_formula, language.SemanticPredicateFormula)
                        for _, leaf in state.tree.open_leaves()) or
                    all(not cast(language.SemanticPredicateFormula, pred_formula.args[0]).binds_tree(leaf)
                        for pred_formula in get_conjuncts(state.constraint)
                        if isinstance(pred_formula, language.NegatedFormula) and
                        isinstance(pred_formula.args[0], language.SemanticPredicateFormula))
                    for _, leaf in state.tree.open_leaves()
                    ), \
                f"Constraint is not true and contains semantic predicate formulas which bind open leaves in the tree: " \
                f"{state.constraint}, leaves: {', '.join(list(map(str, [leaf for _, leaf in state.tree.open_leaves()])))}"

            if not self.global_fuzzer:
                fuzzer = self.fuzzer_factory(self.grammar)
            if state.constraint == sc.true():
                for _ in range(self.max_number_free_instantiations):
                    result = state.tree
                    for path, leaf in state.tree.open_leaves():
                        leaf_inst = fuzzer.expand_tree(DerivationTree(leaf.value, None))
                        result = result.replace_path(path, leaf_inst)
                    yield from self.process_new_states([SolutionState(state.constraint, result)])
            else:
                # noinspection PyTypeChecker
                yield from self.process_new_states(self.expand_state(state, fuzzer))

    def expand_state(self, state: SolutionState, fuzzer: GrammarCoverageFuzzer) -> List[SolutionState]:
        result: List[SolutionState] = []
        for _ in range(self.max_number_free_instantiations):
            substitutions: Dict[DerivationTree, DerivationTree] = {
                subtree: fuzzer.expand_tree(DerivationTree(subtree.value, None))
                for path, subtree in state.tree.open_leaves()
            }

            if substitutions:
                result.append(SolutionState(
                    state.constraint.substitute_expressions(substitutions),
                    state.tree.substitute(substitutions)))

        return result

    def instantiate_structural_predicates(self, state: SolutionState) -> SolutionState:
        predicate_formulas = [
            pred_formula for pred_formula in language.FilterVisitor(
                lambda f: isinstance(f, language.StructuralPredicateFormula)).collect(state.constraint)
            if (isinstance(pred_formula, language.StructuralPredicateFormula)
                and all(not isinstance(arg, language.Variable) for arg in pred_formula.args))
        ]

        formula = state.constraint
        for predicate_formula in predicate_formulas:
            instantiation = language.SMTFormula(z3.BoolVal(predicate_formula.evaluate(state.tree)))
            self.logger.debug("Eliminating (-> %s) structural predicate formula %s", instantiation, predicate_formula)
            formula = language.replace_formula(formula, predicate_formula, instantiation)

        return SolutionState(formula, state.tree)

    def eliminate_existential_integer_quantifiers(self, state: SolutionState) -> Optional[SolutionState]:
        existential_int_formulas = [
            conjunct for conjunct in get_conjuncts(state.constraint)
            if isinstance(conjunct, language.ExistsIntFormula)]

        if not existential_int_formulas:
            return None

        formula = state.constraint
        for existential_int_formula in existential_int_formulas:
            # The following check for validity is not only a performance measure, but required
            # when existential integer formulas are re-inserted. Otherwise, new constants get
            # introduced, and the solver won't terminate.
            if isla.evaluator.evaluate(
                    existential_int_formula,
                    state.tree,
                    self.grammar,
                    assumptions={f for f in split_conjunction(state.constraint) if f != existential_int_formula}
            ).is_true():
                self.logger.debug("Removing existential integer quantifier '%.30s', already implied "
                                  "by tree and existing constraints", existential_int_formula)
                # This should simplify the process after quantifier re-insertion.
                return SolutionState(
                    language.replace_formula(state.constraint, existential_int_formula, sc.true()),
                    state.tree)

            self.logger.debug("Eliminating existential integer quantifier %s", existential_int_formula)
            used_vars = set(VariablesCollector.collect(formula))
            fresh = language.fresh_constant(
                used_vars,
                language.Constant(
                    existential_int_formula.bound_variable.name,
                    existential_int_formula.bound_variable.n_type))
            instantiation = existential_int_formula.inner_formula.substitute_variables(
                {existential_int_formula.bound_variable: fresh})
            formula = language.replace_formula(formula, existential_int_formula, instantiation)

        return SolutionState(formula, state.tree)

    def instantiate_universal_integer_quantifiers(self, state: SolutionState) -> Optional[List[SolutionState]]:
        universal_int_formulas = [
            conjunct for conjunct in get_conjuncts(state.constraint)
            if isinstance(conjunct, language.ForallIntFormula)]

        if not universal_int_formulas:
            return None

        results: List[SolutionState] = [state]
        for universal_int_formula in universal_int_formulas:
            results = [
                result for formula_list in [
                    self.instantiate_universal_integer_quantifier(
                        previous_result, universal_int_formula)
                    for previous_result in results]
                for result in formula_list]

        return results

    def instantiate_universal_integer_quantifier(
            self,
            state: SolutionState,
            universal_int_formula: language.ForallIntFormula) -> List[SolutionState]:
        constant = language.Constant(universal_int_formula.bound_variable.name,
                                     universal_int_formula.bound_variable.n_type)
        # noinspection PyTypeChecker
        inner_formula = universal_int_formula.inner_formula.substitute_variables({
            universal_int_formula.bound_variable: constant})

        def infer_satisfying_assignments(smt_formula: language.SMTFormula) -> Set[int | language.Constant]:
            free_variables = smt_formula.free_variables()
            max_instantiations = self.max_number_free_instantiations if len(free_variables) == 1 else 1

            try:
                solver_result = self.solve_quantifier_free_formula(
                    [smt_formula], max_instantiations=max_instantiations
                )

                solutions: Dict[language.Constant, Set[int]] = {
                    c: {int(solution[cast(language.Constant, c)].value)
                        for solution in solver_result}
                    for c in free_variables
                }
            except ValueError:
                assert False, "Expected numeric solution."

            if solutions:
                if len(free_variables) == 1:
                    return solutions[constant]
                else:
                    assert all(len(solution) == 1 for solution in solutions.values())
                    # In situations with multiple variables, we might have to abstract from concrete values.
                    # Currently, we only support simple equality inference (based on one sample...). Note that
                    # for supporting *more complex* terms (e.g., additions), we would have to extend the whole
                    # infrastructure: Substitutions with complex terms, and complex terms in semantic predicate
                    # arguments, are unsupported as of now.
                    candidates = {
                        c for c in solutions
                        if c != constant and next(iter(solutions[c])) == next(iter(solutions[constant]))}

                    # Filter working candidates
                    return {
                        c for c in candidates
                        if self.solve_quantifier_free_formula(
                            [cast(language.SMTFormula, smt_formula.substitute_variables({constant: c}))],
                            max_instantiations=1)}

        instantiations: List[Dict[language.Constant | DerivationTree,
                                  int | language.Constant | DerivationTree]] = []

        if isinstance(universal_int_formula.inner_formula, language.DisjunctiveFormula):
            # In the disjunctive case, we attempt to falsify all SMT formulas in the inner formula
            # (on top level) that contain the bound variable as argument.
            smt_disjuncts = [
                formula for formula in language.split_disjunction(inner_formula)
                if isinstance(formula, language.SMTFormula) and constant in formula.free_variables()
            ]

            if smt_disjuncts and len(smt_disjuncts) < len(language.split_disjunction(inner_formula)):
                instantiation_values = infer_satisfying_assignments(
                    -reduce(language.SMTFormula.disjunction, smt_disjuncts))

                # We also try to falsify (negated) semantic predicate formulas, if present,
                # if there exist any remaining disjuncts.
                semantic_predicate_formulas: List[Tuple[language.SemanticPredicateFormula, bool]] = [
                    (pred_formula, False) if isinstance(pred_formula, language.SemanticPredicateFormula)
                    else (cast(language.NegatedFormula, pred_formula).args[0], True)
                    for pred_formula in language.FilterVisitor(
                        lambda f: (constant in f.free_variables() and
                                   (isinstance(f, language.SemanticPredicateFormula) or
                                    isinstance(f, language.NegatedFormula) and
                                    isinstance(f.args[0], language.SemanticPredicateFormula))),
                        do_continue=lambda f: isinstance(f, language.DisjunctiveFormula)
                    ).collect(inner_formula)
                    if all(not isinstance(var, language.BoundVariable) for var in pred_formula.free_variables())
                ]

                if (semantic_predicate_formulas and
                        len(semantic_predicate_formulas) + len(smt_disjuncts) <
                        len(language.split_disjunction(inner_formula))):
                    for value in instantiation_values:
                        instantiation: Dict[language.Constant | DerivationTree,
                                            int | language.Constant | DerivationTree] = {constant: value}
                        for semantic_predicate_formula, negated in semantic_predicate_formulas:
                            eval_result = cast(
                                language.SemanticPredicateFormula,
                                language.substitute(semantic_predicate_formula, {constant: value})
                            ).evaluate(self.graph, negate=not negated)
                            if eval_result.ready() and not eval_result.is_boolean():
                                instantiation.update(eval_result.result)
                        instantiations.append(instantiation)
                else:
                    instantiations.extend([{constant: value} for value in instantiation_values])

        results: List[SolutionState] = []
        for instantiation in instantiations:
            self.logger.debug(
                "Instantiating universal integer quantifier (%s -> %s) %s",
                universal_int_formula.bound_variable,
                instantiation[constant],
                universal_int_formula)

            formula = language.replace_formula(
                state.constraint,
                universal_int_formula,
                language.substitute(inner_formula, instantiation))
            formula = language.substitute(formula, instantiation)

            tree = state.tree.substitute({
                tree: subst for tree, subst in instantiation.items()
                if isinstance(tree, DerivationTree)})

            results.append(SolutionState(formula, tree))

        if results:
            return results

        # If the above approach was not successful, we con transform the universal int
        # quantifier to an existential one in a particular situation:
        #
        # Let phi(elem, i) be such that phi(elem) (for fixed first argument) is a unary
        # relation that holds for exactly one argument:
        #
        # forall <A> elem:
        #   exists int i:
        #     phi(elem, i) and
        #     forall int i':
        #       phi(elem, i) <==> i = i'
        #
        # Then, the following transformations are equivalence-preserving:
        #
        # forall int i:
        #   exists <A> elem:
        #     not phi(elem, i)
        #
        # <==> (*)
        #
        # exists int i:
        #   exists <A> elem':
        #     phi(elem', i) &
        #   exists <A> elem:
        #     not phi(elem, i) &
        #   forall int i':
        #     i != i' ->
        #     exists <A> elem'':
        #       not phi(elem'', i')
        #
        # <==> (+)
        #
        # exists int i:
        #   exists <A> elem':
        #     phi(elem', i) &
        #   exists <A> elem:
        #     not phi(elem, i)
        #
        # (*)
        # Problematic is only the first inner conjunct. However, for every elem, there
        # has to be an i such that phi(elem, i) holds. If there is no no in the first
        # place, also the original formula would be unsatisfiable. Without this conjunct,
        # the transformation is a simple "quantifier unwinding."
        #
        # (+)
        # Let i' != i. Choose elem'' := elem': Since phi(elem', i) holds and i != i',
        # "not phi(elem', i')" has to hold.

        if (isinstance(universal_int_formula.inner_formula, language.ExistsFormula) and
                isinstance(universal_int_formula.inner_formula.inner_formula, language.NegatedFormula) and
                isinstance(
                    universal_int_formula.inner_formula.inner_formula.args[0],
                    language.SemanticPredicateFormula) and
                cast(language.SemanticPredicateFormula,
                     universal_int_formula.inner_formula.inner_formula.args[0]).predicate
                in self.predicates_unique_in_int_arg):
            inner_formula: language.ExistsFormula = universal_int_formula.inner_formula
            predicate_formula: language.SemanticPredicateFormula = cast(
                language.SemanticPredicateFormula,
                cast(language.NegatedFormula, inner_formula.inner_formula).args[0])

            fresh_var = language.fresh_bound_variable(
                language.VariablesCollector().collect(state.constraint),
                inner_formula.bound_variable, add=False)

            new_formula = language.ExistsIntFormula(
                universal_int_formula.bound_variable,
                language.ExistsFormula(
                    fresh_var,
                    inner_formula.in_variable,
                    predicate_formula.substitute_variables({inner_formula.bound_variable: fresh_var})) &
                inner_formula)

            self.logger.debug(
                "Transforming universal integer quantifier "
                "(special case, see code comments for explanation):\n%s ==> %s",
                universal_int_formula,
                new_formula)

            return [SolutionState(
                language.replace_formula(state.constraint, universal_int_formula, new_formula),
                state.tree)]

        self.logger.warning(
            "Did not find a way to instantiate formula %s!\n" +
            "Discarding this state. Please report this to your nearest ISLa developer.",
            universal_int_formula)
        return []

    def eliminate_all_semantic_formulas(self, state: SolutionState) -> Optional[List[SolutionState]]:
        conjuncts = split_conjunction(state.constraint)
        semantic_formulas = [conjunct for conjunct in conjuncts
                             if isinstance(conjunct, language.SMTFormula)
                             and not z3.is_true(conjunct.formula)]

        if not semantic_formulas:
            return None

        self.logger.debug("Eliminating semantic formulas [%s]", lazyjoin(", ", semantic_formulas))

        prefix_conjunction = reduce(lambda a, b: a & b, semantic_formulas, sc.true())
        new_disjunct = (
                prefix_conjunction &
                reduce(lambda a, b: a & b,
                       [conjunct for conjunct in conjuncts if conjunct not in semantic_formulas],
                       sc.true()))

        return self.eliminate_semantic_formula(
            prefix_conjunction,
            SolutionState(new_disjunct, state.tree))

    def eliminate_all_ready_semantic_predicate_formulas(self, state: SolutionState) -> Optional[SolutionState]:
        semantic_predicate_formulas: List[language.NegatedFormula | language.SemanticPredicateFormula] = [
            cast(language.NegatedFormula | language.SemanticPredicateFormula, pred_formula)
            for pred_formula in language.FilterVisitor(
                lambda f: (isinstance(f, language.SemanticPredicateFormula) or
                           isinstance(f, language.NegatedFormula) and
                           isinstance(f.args[0], language.SemanticPredicateFormula)),
                do_continue=lambda f: (not isinstance(f, language.NegatedFormula) or
                                       not isinstance(f.args[0], language.SemanticPredicateFormula))
            ).collect(state.constraint)
            if all(not isinstance(var, language.BoundVariable) for var in pred_formula.free_variables())
        ]

        semantic_predicate_formulas = sorted(
            semantic_predicate_formulas,
            key=lambda f: (2 * cast(language.SemanticPredicateFormula, f.args[0]).order + 100
                           if isinstance(f, language.NegatedFormula)
                           else f.order))

        if not semantic_predicate_formulas:
            return None

        result = state

        changed = False
        for idx, possibly_negated_semantic_predicate_formula in enumerate(semantic_predicate_formulas):
            negated = isinstance(possibly_negated_semantic_predicate_formula, language.NegatedFormula)
            semantic_predicate_formula: language.SemanticPredicateFormula = (
                cast(language.NegatedFormula, possibly_negated_semantic_predicate_formula).args[0] if negated
                else possibly_negated_semantic_predicate_formula)

            evaluation_result = semantic_predicate_formula.evaluate(self.graph, negate=negated)
            if not evaluation_result.ready():
                continue

            self.logger.debug("Eliminating semantic predicate formula %s", semantic_predicate_formula)
            changed = True

            if evaluation_result.is_boolean():
                result = SolutionState(
                    language.replace_formula(
                        result.constraint,
                        semantic_predicate_formula,
                        language.SMTFormula(z3.BoolVal(evaluation_result.true()))),
                    result.tree)
                continue

            new_constraint = (
                language.replace_formula(
                    result.constraint, semantic_predicate_formula,
                    sc.false() if negated else sc.true()
                ).substitute_expressions(evaluation_result.result))

            for k in range(idx + 1, len(semantic_predicate_formulas)):
                semantic_predicate_formulas[k] = cast(
                    language.SemanticPredicateFormula,
                    semantic_predicate_formulas[k].substitute_expressions(evaluation_result.result))

            result = SolutionState(
                new_constraint,
                result.tree.substitute(evaluation_result.result))

        return result if changed else None

    def eliminate_first_match_all_existential_formulas(self, state: SolutionState) -> Optional[List[SolutionState]]:
        # We produce up to three output states: One where all existential formulas that can be matched
        # are matched, one where only the first existential formula is matched, and one where only the
        # first existential formula is eliminated by tree insertion. The reason is that for re-inserted
        # existential formulas, eager matching is the best strategy; in other cases, however, it is not
        # clear whether matching or insertion are the best strategies.
        existential_formulas = [
            conjunct for conjunct in split_conjunction(state.constraint)
            if isinstance(conjunct, language.ExistsFormula)]

        if not existential_formulas:
            return None

        # 1. Match all existential formulas.
        # NOTE: Deactivated; seems to be more beneficial to only match the first formula...
        all_matched = OrderedSet()
        # stack = [(state, [])]
        # while stack:
        #     curr_state, already_matched = stack.pop()
        #     try:
        #         next_existential_formula = next(
        #             conjunct for conjunct in split_conjunction(curr_state.constraint)
        #             if isinstance(conjunct, language.ExistsFormula) and conjunct not in already_matched)
        #     except StopIteration:
        #         all_matched.add(curr_state)
        #         continue
        #
        #     match_result = self.match_existential_formula(next_existential_formula, curr_state)
        #     if not match_result:
        #         stack.append((curr_state, already_matched + [next_existential_formula]))
        #     else:
        #         stack.extend([(result, list(already_matched)) for result in match_result])
        #
        # if all_matched:
        #     self.logger.debug(
        #         "Matched all matchable existential formulas, result: [%s]",
        #         ", ".join([f"{s} (hash={hash(s)})" for s in all_matched])
        #     )
        #
        #     if all(result.complete() for result in all_matched):
        #         return list(all_matched)

        # 2. Match first existential formula.
        first_matched = OrderedSet(self.match_existential_formula(existential_formulas[0], state))

        if first_matched:
            self.logger.debug(
                "Matched first existential formulas, result: [%s]",
                lazyjoin(", ", [lazystr(lambda: f"{s} (hash={hash(s)})") for s in first_matched]))

        # 3. Eliminate first existential formula by tree insertion.
        elimination_result = OrderedSet(self.eliminate_existential_formula(existential_formulas[0], state))
        elimination_result = OrderedSet([
            result for result in elimination_result
            if not any(
                other_result.tree == result.tree
                and self.propositionally_unsatisfiable(result.constraint & -other_result.constraint)
                for other_result in all_matched | first_matched)
        ])

        if not elimination_result and not first_matched and not all_matched:
            self.logger.warning(
                "Existential qfr elimination: Could not eliminate existential formula %s "
                "by matching or tree insertion", existential_formulas[0])

        if elimination_result:
            self.logger.debug(
                "Eliminated existential formula %s by tree insertion, %d successors",
                existential_formulas[0],
                len(elimination_result))

        return [result for result in all_matched | first_matched | elimination_result if result != state]

    def match_all_universal_formulas(self, state: SolutionState) -> Optional[List[SolutionState]]:
        universal_formulas = [
            conjunct for conjunct in split_conjunction(state.constraint)
            if isinstance(conjunct, language.ForallFormula)]

        if not universal_formulas:
            return None

        result = self.match_universal_formulas(universal_formulas, state)
        if result:
            self.logger.debug("Matched universal formulas [%s]", lazyjoin(", ", universal_formulas))

        return result or None

    def expand_tree(
            self,
            state: SolutionState,
            only_universal: bool = True,
            limit: Optional[int] = None) -> List[SolutionState]:
        """
        Expands the given tree, but not at nonterminals that can be freely instantiated of those that directly
        correspond to the assignment constant.

        :param state: The current state.
        :param only_universal: If set to True, only nonterminals that might match universal quantifiers are
        expanded. If set to false, also nonterminals matching to existential quantifiers are expanded.
        :param limit: If set to a value, this will return only up to limit expansions.
        :return: A (possibly empty) list of expanded trees.
        """

        nonterminal_expansions: Dict[Path, List[List[DerivationTree]]] = {
            leaf_path: [
                [DerivationTree(child, None if is_nonterminal(child) else [])
                 for child in expansion]
                for expansion in self.canonical_grammar[leaf_node.value]
            ]
            for leaf_path, leaf_node in state.tree.open_leaves()
            if any(
                self.quantified_formula_might_match(formula, leaf_path, state.tree)
                for formula in get_conjuncts(state.constraint)
                if (only_universal and isinstance(formula, language.ForallFormula))
                or (not only_universal and isinstance(formula, language.QuantifiedFormula))
            )}

        possible_expansions: List[Dict[Path, List[DerivationTree]]] = []
        if not limit:
            possible_expansions = dict_of_lists_to_list_of_dicts(nonterminal_expansions)
            assert len(possible_expansions) == math.prod(len(values) for values in nonterminal_expansions.values())
        else:
            for _ in range(limit):
                curr_expansion = {}
                for path, expansions in nonterminal_expansions.items():
                    if not expansions:
                        continue

                    curr_expansion[path] = random.choice(expansions)
                possible_expansions.append(curr_expansion)

        if len(possible_expansions) == 1 and not possible_expansions[0]:
            return []

        result: List[SolutionState] = []
        for possible_expansion in possible_expansions:
            expanded_tree = state.tree
            for path, new_children in possible_expansion.items():
                leaf_node = expanded_tree.get_subtree(path)
                expanded_tree = expanded_tree.replace_path(
                    path, DerivationTree(leaf_node.value, new_children, leaf_node.id))

                assert expanded_tree is not state.tree
                assert expanded_tree != state.tree
                assert expanded_tree.structural_hash() != state.tree.structural_hash()

            updated_constraint = state.constraint.substitute_expressions({
                state.tree.get_subtree(path[:idx]): expanded_tree.get_subtree(path[:idx])
                for path in possible_expansion
                for idx in range(len(path) + 1)
            })

            result.append(SolutionState(updated_constraint, expanded_tree))

        assert not limit or len(result) <= limit
        return result

    def match_universal_formulas(
            self, universal_formulas: List[language.ForallFormula], state: SolutionState) -> List[SolutionState]:
        number_matches = 0
        context_formula = state.constraint

        for universal_formula in universal_formulas:
            matches: List[Dict[language.Variable, Tuple[Path, DerivationTree]]] = \
                [match for match in isla.evaluator.matches_for_quantified_formula(universal_formula, self.grammar)
                 if not universal_formula.is_already_matched(match[universal_formula.bound_variable][1])]

            universal_formula_with_matches = universal_formula.add_already_matched({
                match[universal_formula.bound_variable][1]
                for match in matches
            })

            for match in matches:
                number_matches += 1

                inst_formula = universal_formula_with_matches.inner_formula.substitute_expressions({
                    variable: match_tree for variable, (_, match_tree) in match.items()
                })

                context_formula = inst_formula & language.replace_formula(
                    context_formula, universal_formula, universal_formula_with_matches
                )

        if number_matches:
            return [SolutionState(context_formula, state.tree)]
        else:
            return []

    def match_existential_formula(
            self, existential_formula: language.ExistsFormula, state: SolutionState) -> List[SolutionState]:
        result: List[SolutionState] = []

        matches: List[Dict[language.Variable, Tuple[Path, DerivationTree]]] = \
            isla.evaluator.matches_for_quantified_formula(existential_formula, self.grammar)

        for match in matches:
            inst_formula = existential_formula.inner_formula.substitute_expressions({
                variable: match_tree for variable, (_, match_tree) in match.items()
            })
            constraint = inst_formula & language.replace_formula(state.constraint, existential_formula, sc.true())
            result.append(SolutionState(constraint, state.tree))

        return result

    def eliminate_existential_formula(
            self, existential_formula: language.ExistsFormula, state: SolutionState) -> List[SolutionState]:
        if existential_formula.bind_expression is not None:
            inserted_trees_and_bind_paths = existential_formula.bind_expression.to_tree_prefix(
                existential_formula.bound_variable.n_type, self.grammar)
        else:
            inserted_trees_and_bind_paths = [(DerivationTree(existential_formula.bound_variable.n_type, None), {})]

        result: List[SolutionState] = []

        inserted_tree: DerivationTree
        bind_expr_paths: Dict[language.BoundVariable, Path]
        for inserted_tree, bind_expr_paths in inserted_trees_and_bind_paths:
            self.logger.debug(
                "insert_tree(self.canonical_grammar, %s, %s, self.graph, %s)",
                lazystr(lambda: repr(inserted_tree)),
                lazystr(lambda: repr(existential_formula.in_variable)),
                self.max_number_tree_insertion_results)

            insertion_results = insert_tree(
                self.canonical_grammar,
                inserted_tree,
                existential_formula.in_variable,
                graph=self.graph,
                max_num_solutions=self.max_number_tree_insertion_results * 2,
                methods=self.tree_insertion_methods
            )

            insertion_results = sorted(insertion_results, key=lambda t: compute_tree_closing_cost(t, self.graph))
            insertion_results = insertion_results[:self.max_number_tree_insertion_results]

            for insertion_result in insertion_results:
                # actual_inserted_tree = insertion_result.get_subtree(insertion_result.find_node(inserted_tree))
                replaced_path = state.tree.find_node(existential_formula.in_variable)
                resulting_tree = state.tree.replace_path(replaced_path, insertion_result)

                tree_substitution: Dict[DerivationTree, DerivationTree] = {}
                for idx in range(len(replaced_path) + 1):
                    original_path = replaced_path[:idx - 1]
                    original_tree = state.tree.get_subtree(original_path)
                    if (resulting_tree.is_valid_path(original_path) and
                            original_tree.value == resulting_tree.get_subtree(original_path).value
                            and resulting_tree.get_subtree(original_path) != original_tree):
                        tree_substitution[original_tree] = resulting_tree.get_subtree(original_path)

                # tree_substitution: Dict[DerivationTree, DerivationTree] = {
                #     original_tree: resulting_tree.get_subtree(original_path)
                #     for original_path, original_tree in state.tree.paths()
                #     if (resulting_tree.is_valid_path(original_path) and
                #         original_tree.value == resulting_tree.get_subtree(original_path).value
                #         and resulting_tree.get_subtree(original_path) != original_tree)}

                assert insertion_result.find_node(inserted_tree) is not None
                variable_substitutions = {existential_formula.bound_variable: inserted_tree}

                if bind_expr_paths:
                    if assertions_activated():
                        dangling_bind_expr_vars = [
                            (var, path)
                            for var, path in bind_expr_paths.items()
                            if (var in existential_formula.bind_expression.bound_variables() and
                                insertion_result.find_node(inserted_tree.get_subtree(path)) is None)]
                        assert not dangling_bind_expr_vars, \
                            f"Bound variables from match expression not found in tree: " \
                            f"[{' ,'.join(map(repr, dangling_bind_expr_vars))}]"

                    variable_substitutions.update({
                        var: inserted_tree.get_subtree(path)
                        for var, path in bind_expr_paths.items()
                        if var in existential_formula.bind_expression.bound_variables()
                    })

                instantiated_formula = (
                    existential_formula.inner_formula
                        .substitute_expressions(variable_substitutions)
                        .substitute_expressions(tree_substitution)
                )

                instantiated_original_constraint = language.replace_formula(
                    state.constraint, existential_formula, sc.true()
                ).substitute_expressions(tree_substitution)

                new_tree = resulting_tree.substitute(tree_substitution)

                new_formula = (
                        instantiated_formula &
                        self.formula.substitute_expressions(
                            {self.top_constant: new_tree}) &
                        instantiated_original_constraint)

                new_state = SolutionState(new_formula, new_tree)

                assert all(
                    new_state.tree.find_node(tree) is not None
                    for quantified_formula in split_conjunction(new_state.constraint)
                    if isinstance(quantified_formula, language.QuantifiedFormula)
                    for _, tree in quantified_formula.in_variable.filter(lambda t: True))

                if assertions_activated() or self.debug:
                    lost_tree_predicate_arguments: List[DerivationTree] = [
                        arg
                        for invstate in self.establish_invariant(new_state)
                        for predicate_formula in get_conjuncts(invstate.constraint)
                        if isinstance(predicate_formula, language.StructuralPredicateFormula)
                        for arg in predicate_formula.args
                        if isinstance(arg, DerivationTree) and
                           invstate.tree.find_node(arg) is None]

                    if lost_tree_predicate_arguments:
                        previous_posititions = [state.tree.find_node(t) for t in lost_tree_predicate_arguments]
                        assert False, f"Dangling subtrees [{', '.join(map(repr, lost_tree_predicate_arguments))}], " \
                                      f"previously at positions [{', '.join(map(str, previous_posititions))}] " \
                                      f"in tree {repr(state.tree)} (hash: {hash(state)})."

                    lost_semantic_formula_arguments = [
                        arg
                        for invstate in self.establish_invariant(new_state)
                        for semantic_formula in get_conjuncts(new_state.constraint)
                        if isinstance(semantic_formula, language.SMTFormula)
                        for arg in semantic_formula.substitutions.values()
                        if invstate.tree.find_node(arg) is None]

                    if lost_semantic_formula_arguments:
                        previous_posititions = [state.tree.find_node(t) for t in lost_semantic_formula_arguments]
                        previous_posititions = [p for p in previous_posititions if p is not None]
                        assert False, f"Dangling subtrees [{', '.join(map(repr, lost_semantic_formula_arguments))}], " \
                                      f"previously at positions [{', '.join(map(str, previous_posititions))}] " \
                                      f"in tree {repr(state.tree)} (hash: {hash(state)})."

                result.append(new_state)

        return result

    def eliminate_semantic_formula(
            self, semantic_formula: language.Formula, state: SolutionState) -> List[SolutionState]:
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

        assert all(isinstance(conjunct, language.SMTFormula) for conjunct in get_conjuncts(semantic_formula))

        # NODE: We need to cluster SMT formulas by tree substitutions. If there are two formulas
        # with a variable $var which is instantiated to different trees, we need two separate
        # solutions. If, however, $var is instantiated with the *same* tree, we need one solution
        # to both formulas together.

        smt_formulas = self.rename_instantiated_variables_in_smt_formulas(
            [smt_formula for smt_formula in get_conjuncts(semantic_formula) if
             isinstance(smt_formula, language.SMTFormula)])

        # Now, we also cluster formulas by common variables (and instantiated subtrees: One formula
        # might yield an instantiation of a subtree of the instantiation of another formula. They
        # need to appear in the same cluster). The solver can better handle smaller constraints,
        # and those which do not have variables in common can be handled independently.

        def cluster_keys(smt_formula: language.SMTFormula):
            return (smt_formula.free_variables() |
                    smt_formula.instantiated_variables |
                    set([subtree for tree in smt_formula.substitutions.values() for _, subtree in tree.paths()]))

        formula_clusters: List[List[language.SMTFormula]] = cluster_by_common_elements(smt_formulas, cluster_keys)

        assert all(not cluster_keys(smt_formula) or
                   any(smt_formula in cluster for cluster in formula_clusters)
                   for smt_formula in smt_formulas)

        formula_clusters = [cluster for cluster in formula_clusters if cluster]
        remaining_clusters = [smt_formula for smt_formula in smt_formulas if not cluster_keys(smt_formula)]
        if remaining_clusters:
            formula_clusters.append(remaining_clusters)

        all_solutions: List[List[Dict[Union[language.Constant, DerivationTree], DerivationTree]]] = [
            self.solve_quantifier_free_formula(cluster) for cluster in formula_clusters
        ]

        # These solutions are all independent, such that we can combine each solution with all others.
        solutions: List[Dict[Union[language.Constant, DerivationTree], DerivationTree]] = [
            functools.reduce(operator.or_, dicts) for dicts in itertools.product(*all_solutions)]

        solutions_with_subtrees: List[Dict[Union[language.Constant, DerivationTree], DerivationTree]] = []
        for solution in solutions:
            # We also have to instantiate all subtrees of the substituted element.

            solution_with_subtrees: Dict[Union[language.Constant, DerivationTree], DerivationTree] = {}
            for orig, subst in solution.items():
                if isinstance(orig, language.Constant):
                    solution_with_subtrees[orig] = subst
                    continue

                assert isinstance(orig, DerivationTree), f'Expected a DerivationTree, given: {type(orig).__name__}'
                for path, tree in [(p, t) for p, t in orig.paths() if t not in solution_with_subtrees]:
                    assert subst.is_valid_path(path), \
                        f"SMT Solution {subst} does not have " \
                        f"orig path {path} from tree {orig} (state {hash(state)})"
                    solution_with_subtrees[tree] = subst.get_subtree(path)

            solutions_with_subtrees.append(solution_with_subtrees)

        results = []
        for solution in solutions_with_subtrees:
            if solution:
                new_state = SolutionState(
                    state.constraint.substitute_expressions(solution),
                    state.tree.substitute(solution))
            else:
                new_state = SolutionState(
                    language.replace_formula(state.constraint, semantic_formula, sc.true()),
                    state.tree)

            results.append(new_state)

        return results

    def solve_quantifier_free_formula(
            self,
            smt_formulas: List[language.SMTFormula],
            max_instantiations: Optional[int] = None) -> \
            List[Dict[language.Constant | DerivationTree, DerivationTree]]:
        # If any SMT formula refers to subtrees in the instantiations of other SMT formulas,
        # we have to instantiate those first.
        def get_conflicts(smt_formulas):
            return [
                f for fidx, f in enumerate(smt_formulas)
                if any(
                    ot != t and ot.find_node(t) is not None
                    for t in f.substitutions.values()
                    for ofidx, of in enumerate(smt_formulas)
                    if fidx != ofidx
                    for ot in of.substitutions.values())]

        conflicts = get_conflicts(smt_formulas)

        if conflicts:
            smt_formulas = conflicts
            assert not get_conflicts(smt_formulas)

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

        solutions: List[Dict[Union[language.Constant, DerivationTree], DerivationTree]] = []
        internal_solutions: List[Dict[language.Constant, z3.StringVal]] = []

        num_instantiations = max_instantiations or self.max_number_smt_instantiations
        for _ in range(num_instantiations):
            formulas: List[z3.BoolRef] = []

            for constant in constants:
                if constant.is_numeric():
                    regex = z3.Union(z3.Re("0"), z3.Concat(z3.Range("1", "9"), z3.Star(z3.Range("0", "9"))))
                elif constant in tree_substitutions:
                    # We have a more concrete shape of the desired instantiation available
                    regexes = [
                        self.extract_regular_expression(t) if is_nonterminal(t)
                        else z3.Re(t)
                        for t in split_str_with_nonterminals(str(tree_substitutions[constant]))]
                    assert regexes
                    regex = z3.Concat(*regexes) if len(regexes) > 1 else regexes[0]
                else:
                    regex = self.extract_regular_expression(constant.n_type)

                formulas.append(z3.InRe(z3.String(constant.name), regex))

            for prev_solution in internal_solutions:
                formulas.extend([
                    # "str.to_int(constant) == 42" has been shown to be more efficiently
                    # solvable than "x == '17'"---fewer timeouts!
                    z3.Not(z3.StrToInt(constant.to_smt()) == z3.IntVal(int(string_val.as_string())))
                    if constant.is_numeric()
                    else z3.Not(z3_eq(constant.to_smt(), string_val))
                    for constant, string_val in prev_solution.items()])

            for smt_formula in smt_formulas:
                formulas.append(smt_formula.formula)

            solver_result, maybe_model = z3_solve(formulas)

            if solver_result != z3.sat:
                if not solutions:
                    return []
                else:
                    return solutions

            assert maybe_model is not None

            new_solution = {
                tree_substitutions.get(constant, constant):
                    (
                        val := maybe_model[z3.String(constant.name)].as_string(),
                        DerivationTree(val, []) if constant.is_numeric() else self.parse(constant.n_type, val)
                    )[-1]
                for constant in constants
            }

            new_internal_solution = {
                constant: z3.StringVal(maybe_model[z3.String(constant.name)].as_string())
                for constant in constants}

            if new_solution in solutions:
                # This can happen for trivial solutions, i.e., if the formula is logically valid.
                # Then, the assignment for that constant will always be {}
                return solutions
            else:
                solutions.append(new_solution)
                if new_internal_solution:
                    internal_solutions.append(new_internal_solution)
                else:
                    # Again, for a trivial solution (e.g., True), the assignment can be empty
                    break

        return solutions

    def rename_instantiated_variables_in_smt_formulas(self, smt_formulas):
        old_smt_formulas = smt_formulas
        smt_formulas = []
        for subformula in old_smt_formulas:
            subst_var: language.Variable
            subst_tree: DerivationTree

            new_smt_formula: z3.BoolRef = subformula.formula
            new_substitutions = subformula.substitutions
            new_instantiated_variables = subformula.instantiated_variables

            for subst_var, subst_tree in subformula.substitutions.items():
                new_name = f"{subst_tree.value}_{subst_tree.id}"
                new_var = language.BoundVariable(new_name, subst_var.n_type)

                new_smt_formula = cast(z3.BoolRef, z3_subst(new_smt_formula, {subst_var.to_smt(): new_var.to_smt()}))
                new_substitutions = {new_var if k == subst_var else k: v for k, v in new_substitutions.items()}
                new_instantiated_variables = {new_var if v == subst_var else v for v in new_instantiated_variables}

            smt_formulas.append(
                language.SMTFormula(
                    new_smt_formula,
                    *subformula.free_variables_,
                    instantiated_variables=new_instantiated_variables,
                    substitutions=new_substitutions))

        return smt_formulas

    def process_new_states(self, new_states: List[SolutionState]) -> List[DerivationTree]:
        return [tree for new_state in new_states for tree in self.process_new_state(new_state)]

    def process_new_state(self, new_state: SolutionState) -> List[DerivationTree]:
        new_state = self.instantiate_structural_predicates(new_state)
        new_states = self.establish_invariant(new_state)
        new_states = [self.remove_nonmatching_universal_quantifiers(new_state) for new_state in new_states]
        new_states = [self.remove_infeasible_universal_quantifiers(new_state) for new_state in new_states]

        assert all(
            state.tree.find_node(tree) is not None
            for state in new_states
            for quantified_formula in split_conjunction(state.constraint)
            if isinstance(quantified_formula, language.QuantifiedFormula)
            for _, tree in quantified_formula.in_variable.filter(lambda t: True))

        solution_trees = [new_state.tree for new_state in new_states if self.state_is_valid_or_enqueue(new_state)]

        for tree in solution_trees:
            self.cost_computer.signal_tree_output(tree)

        return solution_trees

    def state_is_valid_or_enqueue(self, state: SolutionState) -> bool:
        """
        Returns True if the given state is valid, such that it can be yielded. Returns False and enqueues the state
        if the state is not yet complete, otherwise returns False and discards the state.
        """

        if state.complete():
            assert state.formula_satisfied(self.grammar).is_true()
            return True

        # Helps in debugging below assertion:
        # [(predicate_formula, [
        #     arg for arg in predicate_formula.args
        #     if isinstance(arg, DerivationTree) and not state.tree.find_node(arg)])
        #  for predicate_formula in get_conjuncts(state.constraint)
        #  if isinstance(predicate_formula, language.StructuralPredicateFormula)]

        if assertions_activated() or self.debug:
            dangling_predicate_argument_trees = [
                (predicate_formula, arg)
                for predicate_formula in language.FilterVisitor(
                    lambda f: isinstance(f, language.StructuralPredicateFormula)).collect(state.constraint)
                for arg in cast(language.StructuralPredicateFormula, predicate_formula).args
                if isinstance(arg, DerivationTree) and state.tree.find_node(arg) is None
            ]

            if dangling_predicate_argument_trees:
                assert False, \
                    "Dangling predicate arguments: [" + \
                    ", ".join([str(f) + ", " + repr(a) for f, a in dangling_predicate_argument_trees]) + "]"

            dangling_smt_formula_argument_trees = [
                (smt_formula, arg)
                for smt_formula in language.FilterVisitor(
                    lambda f: isinstance(f, language.SMTFormula)).collect(state.constraint)
                for arg in cast(language.SMTFormula, smt_formula).substitutions.values()
                if isinstance(arg, DerivationTree) and state.tree.find_node(arg) is None
            ]

            if dangling_smt_formula_argument_trees:
                assert False, \
                    "Dangling SMT formula arguments: [" + \
                    ", ".join([str(f) + ", " + repr(a) for f, a in dangling_smt_formula_argument_trees]) + "]"

        if self.enforce_unique_trees_in_queue and state.tree.structural_hash() in self.tree_hashes_in_queue:
            # Some structures can arise as well from tree insertion (existential quantifier elimination)
            # and expansion; also, tree insertion can yield different trees that have intersecting
            # expansions. We drop those to output more diverse solutions (numbers for SMT solutions
            # and free nonterminals are configurable, so you get more outputs by playing with those!).
            self.logger.debug("Discarding state %s, tree already in queue", state)
            return False

        if hash(state) in self.state_hashes_in_queue:
            self.logger.debug("Discarding state %s, already in queue", state)
            return False

        # if state.constraint == sc.false():
        if self.propositionally_unsatisfiable(state.constraint):
            self.logger.debug("Discarding state %s", state)
            return False

        state = SolutionState(state.constraint, state.tree, level=self.current_level + 1)

        cost = self.compute_cost(state)
        heapq.heappush(self.queue, (cost, state))
        self.tree_hashes_in_queue.add(state.tree.structural_hash())
        self.state_hashes_in_queue.add(hash(state))

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

    def propositionally_unsatisfiable(self, formula: language.Formula) -> bool:
        return formula == sc.false()

        # NOTE: Deactivated propositional check for performance reasons
        # z3_formula = language.isla_to_smt_formula(formula, replace_untranslatable_with_predicate=True)
        # solver = z3.Solver()
        # solver.add(z3_formula)
        # return solver.check() == z3.unsat

    def establish_invariant(self, state: SolutionState) -> List[SolutionState]:
        formula = convert_to_dnf(convert_to_nnf(state.constraint))
        return [
            SolutionState(disjunct, state.tree)
            for disjunct in split_disjunction(formula)]

    def compute_cost(self, state: SolutionState) -> float:
        if state.constraint == sc.true():
            return 0

        return self.cost_computer.compute_cost(state)

    def remove_nonmatching_universal_quantifiers(self, state: SolutionState) -> SolutionState:
        result = state
        for universal_formula in [conjunct for conjunct in get_conjuncts(state.constraint)
                                  if isinstance(conjunct, language.ForallFormula)]:
            if (universal_formula.in_variable.is_complete()
                    and not isla.evaluator.matches_for_quantified_formula(universal_formula, self.grammar)):
                result = SolutionState(
                    language.replace_formula(result.constraint, universal_formula, sc.true()),
                    result.tree)

        return result

    def remove_infeasible_universal_quantifiers(self, state: SolutionState) -> SolutionState:
        result = state
        for universal_formula in get_conjuncts(state.constraint):
            if not isinstance(universal_formula, language.ForallFormula):
                continue

            if not (any(self.quantified_formula_might_match(universal_formula, leaf_path, universal_formula.in_variable)
                        for leaf_path, leaf_node in universal_formula.in_variable.open_leaves())
                    or [match for match in
                        isla.evaluator.matches_for_quantified_formula(universal_formula, self.grammar)
                        if not universal_formula.is_already_matched(match[universal_formula.bound_variable][1])]):
                result = SolutionState(
                    language.replace_formula(result.constraint, universal_formula, sc.true()),
                    result.tree)

        return result

    def quantified_formula_might_match(
            self, qfd_formula: language.QuantifiedFormula, path_to_nonterminal: Path, tree: DerivationTree) -> bool:
        return quantified_formula_might_match(
            qfd_formula,
            path_to_nonterminal,
            tree,
            self.grammar,
            self.reachable_reflexively)

    @lru_cache(maxsize=None)
    def node_distance(self, nonterminal: str, to_nonterminal: str) -> int:
        if self.precompute_reachability:
            return self.node_distances[nonterminal][to_nonterminal]
        else:
            from_node = self.graph.get_node(nonterminal)
            to_node = self.graph.get_node(to_nonterminal)

            assert from_node is not None, f"Node {nonterminal} not found in graph"
            assert to_node is not None, f"Node {to_nonterminal} not found in graph"

            return self.graph.dijkstra(from_node, to_node)[0][to_node]

    def reachable_reflexively(self, from_nonterminal: str, to_nonterminal: str) -> bool:
        return self.node_distance(from_nonterminal, to_nonterminal) < sys.maxsize

    @lru_cache(maxsize=None)
    def extract_regular_expression(self, nonterminal: str) -> z3.ReRef:
        regex_conv = RegexConverter(self.grammar, compress_unions=True)
        regex = regex_conv.to_regex(nonterminal, convert_to_z3=False)
        self.logger.debug(f"Computed regular expression for nonterminal {nonterminal}:\n{regex}")
        z3_regex = regex_to_z3(regex)

        if assertions_activated():
            # Check correctness of regular expression
            grammar = self.graph.subgraph(nonterminal).to_grammar()

            # 1. L(grammar) \subseteq L(regex)
            # NOTE: Removed this check. If unwinding is required, it will fail!
            # self.logger.debug(
            #     "Checking L(grammar) \\subseteq L(regex) for nonterminal '%s' and regex '%s'",
            #     nonterminal,
            #     regex)
            # fuzzer = GrammarCoverageFuzzer(grammar)
            # for _ in range(400):
            #     inp = fuzzer.fuzz()
            #     s = z3.Solver()
            #     s.add(z3.InRe(z3.StringVal(inp), z3_regex))
            #     assert s.check() == z3.sat, f"Input '{inp}' from grammar language is not in regex language"

            # 2. L(regex) \subseteq L(grammar)
            self.logger.debug(
                "Checking L(regex) \\subseteq L(grammar) for nonterminal '%s' and regex '%s'",
                nonterminal,
                regex)
            parser = EarleyParser(grammar)
            c = z3.String("c")
            prev: Set[str] = set()
            for _ in range(100):
                s = z3.Solver()
                s.add(z3.InRe(c, z3_regex))
                for inp in prev:
                    s.add(z3.Not(c == z3.StringVal(inp)))
                if s.check() != z3.sat:
                    self.logger.debug(
                        "Cannot find the %d-th solution for regex %s (timeout).\nThis is *not* a problem "
                        "if there not that many solutions (for regexes with finite language), or if we "
                        "are facing a meaningless timeout of the solver.",
                        len(prev) + 1, regex)
                    break
                new_inp = s.model()[c].as_string()
                try:
                    next(parser.parse(new_inp))
                except SyntaxError:
                    assert False, f"Input '{new_inp}' from regex language is not in grammar language."
                prev.add(new_inp)

        return z3_regex

    def parse(self, nonterminal: str, input: str) -> DerivationTree:
        grammar = copy.deepcopy(self.grammar)
        grammar["<start>"] = [nonterminal]
        delete_unreachable(grammar)
        parser = EarleyParser(grammar)
        return DerivationTree.from_parse_tree(list(parser.parse(input))[0][1][0])


class CostComputer(ABC):
    def compute_cost(self, state: SolutionState) -> float:
        """
        Computes a cost value for the given state. States with lower cost
        will be preferred in the analysis.

        :param state: The state for which to compute a cost.
        :return: The cost value.
        """
        raise NotImplementedError()

    def signal_tree_output(self, tree: DerivationTree) -> None:
        """
        Should be called when a tree is output as a solution. Used to
        update internal information for cost computation.

        :param tree The tree that is output as a solution.
        :return: Nothing.
        """
        raise NotImplementedError()


class GrammarBasedBlackboxCostComputer(CostComputer):
    def __init__(
            self,
            cost_settings: CostSettings,
            graph: gg.GrammarGraph,
            reset_coverage_after_n_round_with_no_coverage: int = 100):
        self.cost_settings = cost_settings
        self.graph = graph

        self.covered_k_paths: Set[Tuple[gg.Node, ...]] = set()
        self.rounds_with_no_new_coverage = 0
        self.reset_coverage_after_n_round_with_no_coverage = reset_coverage_after_n_round_with_no_coverage
        self.symbol_costs: Optional[Dict[str, int]] = None

        self.logger = logging.getLogger(type(self).__name__)

    def compute_cost(self, state: SolutionState) -> float:
        # How costly is it to finish the tree?
        tree_closing_cost = compute_tree_closing_cost(state.tree, self.graph)

        # Quantifiers are expensive (universal formulas have to be matched, tree insertion for existential
        # formulas is even more costly). TODO: Penalize nested quantifiers more.
        constraint_cost = sum(
            [idx * (2 if isinstance(f, language.ExistsFormula) else 1) + 1
             for c in get_quantifier_chains(state.constraint)
             for idx, f in enumerate(c)])

        # k-Path coverage: Fewer covered -> higher penalty
        k_cov_cost = self._compute_k_coverage_cost(state)

        # Covered k-paths: Fewer contributed -> higher penalty
        global_k_path_cost = self._compute_global_k_coverage_cost(state)

        costs = [tree_closing_cost, constraint_cost, state.level, k_cov_cost, global_k_path_cost]
        assert all(c >= 0 for c in costs)

        # Compute geometric mean
        result = weighted_geometric_mean(costs, list(self.cost_settings.weight_vector))

        self.logger.debug(
            "Computed cost for state %s:\n%f, individual costs: %s, weights: %s",
            lazystr(lambda: f"({(str(state.constraint)[:50] + '...')}, {state.tree})"),
            result, costs, self.cost_settings.weight_vector)

        return result

    def signal_tree_output(self, tree: DerivationTree) -> None:
        self._update_covered_k_paths(tree)

    def _symbol_costs(self):
        if self.symbol_costs is None:
            self.symbol_costs = compute_symbol_costs(self.graph)
        return self.symbol_costs

    def _update_covered_k_paths(self, tree: DerivationTree):
        if self.cost_settings.weight_vector.low_global_k_path_coverage_penalty > 0:
            old_covered_k_paths = copy.copy(self.covered_k_paths)

            self.covered_k_paths.update(tree.k_paths(self.graph, self.cost_settings.k))

            if old_covered_k_paths == self.covered_k_paths:
                self.rounds_with_no_new_coverage += 1

            graph_paths = self.graph.k_paths(self.cost_settings.k)
            if (self.rounds_with_no_new_coverage >= self.reset_coverage_after_n_round_with_no_coverage or
                    self.covered_k_paths == graph_paths):
                if self.covered_k_paths == graph_paths:
                    self.logger.debug("ALL PATHS COVERED")
                else:
                    self.logger.debug(
                        "COVERAGE RESET SINCE NO CHANGE IN COVERED PATHS SINCE %d ROUNDS (%d path(s) uncovered)",
                        self.reset_coverage_after_n_round_with_no_coverage,
                        len(graph_paths) - len(self.covered_k_paths))

                    # uncovered_paths = self.graph.k_paths(self.cost_settings.k) - self.covered_k_paths
                    # self.logger.info("\n".join([", ".join(f"'{n.symbol}'" for n in p) for p in uncovered_paths]))

                self.covered_k_paths = set()
            else:
                pass
                # uncovered_paths = self.graph.k_paths(self.cost_settings.k) - self.covered_k_paths
                # self.logger.info("\n".join([", ".join(f"'{n.symbol}'" for n in p) for p in uncovered_paths]))

            if self.rounds_with_no_new_coverage >= self.reset_coverage_after_n_round_with_no_coverage:
                self.rounds_with_no_new_coverage = 0

    def _compute_global_k_coverage_cost(self, state: SolutionState):
        num_contributed_k_paths = len(
            {path for path in self.graph.k_paths(self.cost_settings.k)
             if path in state.tree.k_paths(self.graph, self.cost_settings.k) and
             path not in self.covered_k_paths})
        num_missing_k_paths = len(self.graph.k_paths(self.cost_settings.k)) - len(self.covered_k_paths)

        return 1 - (num_contributed_k_paths / num_missing_k_paths)

    def _compute_k_coverage_cost(self, state: SolutionState) -> float:
        return math.prod([
            1 - state.tree.k_coverage(self.graph, k) for k in range(1, self.cost_settings.k + 1)]
        ) ** (1 / float(self.cost_settings.k))


def compute_tree_closing_cost(tree: DerivationTree, graph: GrammarGraph) -> float:
    nonterminals = [leaf.value for _, leaf in tree.open_leaves()]
    return sum([compute_symbol_costs(graph)[nonterminal] for nonterminal in nonterminals])


def get_quantifier_chains(formula: language.Formula) -> \
        List[Tuple[Union[language.QuantifiedFormula, language.ExistsIntFormula], ...]]:
    univ_toplevel_formulas = isla.evaluator.get_toplevel_quantified_formulas(formula)
    return [(f,) + c for f in univ_toplevel_formulas for c in (get_quantifier_chains(f.inner_formula) or [()])]


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
    # bind expression tree is a prefix tree of that extension, and extending
    # the nonterminal might approach a match?
    # Note that the prefix tree must not *already* be a match.

    maybe_prefix_tree: DerivationTree
    for maybe_prefix_tree, var_map in qfd_formula.bind_expression.to_tree_prefix(
            qfd_formula.bound_variable.n_type, grammar):
        reverse_var_map = {path: var for var, path in var_map.items()}

        for idx in reversed(range(len(path_to_nonterminal))):
            subtree = tree.get_subtree(path_to_nonterminal[:idx])
            if (maybe_prefix_tree.is_potential_prefix(subtree) and
                    not qfd_formula.is_already_matched(subtree)):
                # If the current nonterminal does not need to be further expanded to match
                # the prefix tree, we need to return false; otherwise, we would needlessly
                # expand nonterminals that could actually be freely instantiated.

                path_to_node_in_prefix_tree = path_to_nonterminal[idx:]

                while not maybe_prefix_tree.is_valid_path(path_to_node_in_prefix_tree):
                    path_to_node_in_prefix_tree = path_to_node_in_prefix_tree[:-1]

                # If this path in the prefix tree is sub-path of a path associated with a dummy
                # variable, we do not resport a possible match; such an element can be freely instantiated.
                mapping_paths = [path for path in reverse_var_map if is_prefix(path_to_node_in_prefix_tree, path)]
                assert mapping_paths
                if all(isinstance(reverse_var_map[mapping_path], language.DummyVariable)
                       for mapping_path in mapping_paths):
                    continue

                node_in_prefix_tree = maybe_prefix_tree.get_subtree(path_to_node_in_prefix_tree)

                if reachable(node.value, node_in_prefix_tree.value):
                    return True

    return False


@lru_cache()
def compute_symbol_costs(graph: GrammarGraph) -> Dict[str, int]:
    grammar = graph.to_grammar()
    canonical_grammar = canonical(grammar)

    result: Dict[str, int] = {}

    for nonterminal in grammar:
        fuzzer = GrammarFuzzer(grammar)
        tree = fuzzer.expand_tree_with_strategy(DerivationTree(nonterminal, None), fuzzer.expand_node_max_cost, 1)
        tree = fuzzer.expand_tree_with_strategy(tree, fuzzer.expand_node_min_cost)
        result[nonterminal] = sum([
            len([expansion for expansion in canonical_grammar[tree.value]
                 if any(is_nonterminal(symbol) for symbol in expansion)])
            for _, tree in tree.paths()
            if is_nonterminal(tree.value)
        ])

    def all_paths(
            from_node: gg.NonterminalNode,
            to_node: gg.NonterminalNode, cycles_allowed: int = 1) -> List[List[gg.NonterminalNode]]:
        """Compute all paths between two nodes. Note: We allow to visit each nonterminal twice.
        This is not really allowing up to `cycles_allowed` cycles (which was the original intention
        of the parameter), since then we would have to check per path; yet, the number of paths would
        explode then and the current implementation provides reasonably good results."""
        result: List[List[gg.NonterminalNode]] = []
        visited: Dict[gg.NonterminalNode, int] = {n: 0 for n in graph.all_nodes}

        queue: List[List[gg.NonterminalNode]] = [[from_node]]
        while queue:
            p = queue.pop(0)
            if p[-1] == to_node:
                result.append(p)
                continue

            for child in p[-1].children:
                if not isinstance(child, gg.NonterminalNode) or visited[child] > cycles_allowed + 1:
                    continue

                visited[child] += 1
                queue.append(p + [child])

        return [[n for n in p if not isinstance(n, gg.ChoiceNode)] for p in result]

    nonterminal_parents = [
        nonterminal for nonterminal in canonical_grammar
        if any(
            is_nonterminal(symbol)
            for expansion in canonical_grammar[nonterminal]
            for symbol in expansion)]

    # Sometimes this computation results in some nonterminals having lower cost values
    # than nonterminals that are reachable from those (but not vice versa), which is
    # undesired. We counteract this by assuring that on paths with at most one cycle
    # from the root to any nonterminal parent, the costs are strictly monotonically
    # decreasing.
    for nonterminal_parent in nonterminal_parents:
        # noinspection PyTypeChecker
        for path in all_paths(graph.root, graph.get_node(nonterminal_parent)):
            for idx in reversed(range(1, len(path))):
                source: gg.Node = path[idx - 1]
                target: gg.Node = path[idx]

                if result[source.symbol] <= result[target.symbol]:
                    result[source.symbol] = result[target.symbol] + 1

    return result
