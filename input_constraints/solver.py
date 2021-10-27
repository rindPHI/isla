import copy
import heapq
import logging
import sys
from functools import reduce, lru_cache
from typing import Generator, Dict, List, Set, Optional, Tuple, Union, cast

import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.GrammarFuzzer import GrammarFuzzer
from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import canonical, EarleyParser
from grammar_graph import gg
from grammar_graph.gg import GrammarGraph
from grammar_to_regex.cfg2regex import RegexConverter

import input_constraints.isla_shortcuts as sc
from input_constraints import isla
from input_constraints.existential_helpers import insert_tree
from input_constraints.helpers import delete_unreachable, dict_of_lists_to_list_of_dicts, \
    replace_line_breaks, z3_subst, z3_solve
from input_constraints.isla import DerivationTree, VariablesCollector, split_conjunction, split_disjunction, \
    convert_to_dnf, convert_to_nnf, ensure_unique_bound_variables, parse_isla, get_conjuncts
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

        return isla.evaluate(self.constraint, self.tree)

    def complete(self) -> bool:
        if not self.tree.is_complete():
            return False

        # We assume that any universal quantifier has already been instantiated, if it matches,
        # and is thus satisfied, or another unsatisfied constraint resulted from the instantiation.
        # Existential, predicate, and SMT formulas have to be eliminated first.

        # return any(all(not isinstance(conjunct, isla.StructuralPredicateFormula)
        #                and (not isinstance(conjunct, isla.SMTFormula) or conjunct == sc.true())
        #                and not isinstance(conjunct, isla.SemanticPredicateFormula)
        #                and not isinstance(conjunct, isla.ExistsFormula)
        #                and (not isinstance(conjunct, isla.ForallFormula) or len(conjunct.already_matched) > 0)
        #                for conjunct in split_conjunction(disjunct))
        #            for disjunct in split_disjunction(self.constraint))

        return self.constraint == sc.true()

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
                 formula: Union[isla.Formula, str],
                 structural_predicates: Optional[Dict[str, isla.StructuralPredicate]] = None,
                 semantic_predicates: Optional[Dict[str, isla.SemanticPredicate]] = None,
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

        if isinstance(formula, str):
            formula = parse_isla(formula, structural_predicates, semantic_predicates)

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
        initial_state = SolutionState(initial_formula, initial_tree)
        initial_states = self.establish_invariant(initial_state)

        self.queue: List[Tuple[float, SolutionState]] = []
        self.tree_hashes_in_queue: Set[int] = {initial_tree.structural_hash()}
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
        fuzzer = GrammarCoverageFuzzer(self.grammar)

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

            assert not isinstance(state.constraint, isla.DisjunctiveFormula)

            # Instantiate all top-level structural predicate formulas.
            state = self.instantiate_structural_predicates(state)

            if state.constraint == sc.false():
                continue

            # Match all universal formulas
            result_states = self.match_all_universal_formulas(state)
            if result_states is not None:
                yield from self.process_new_states(result_states)
                continue

            # Expand if there are any not yet eliminated / matched universal quantifiers
            if any(isinstance(conjunct, isla.ForallFormula) for conjunct in get_conjuncts(state.constraint)):
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
            result_states = self.eliminate_first_existential_formula(state)
            if result_states is not None:
                yield from self.process_new_states(result_states)
                continue
                # if (not self.expand_after_existential_elimination
                #         or any(result_state.constraint == sc.true() for result_state in result_states)):
                #     continue

            # semantic predicate formulas can remain if they bind lazily. In that case, we can choose a random
            # instantiation and let the predicate "fix" the resulting tree.
            assert (state.constraint == sc.true() or
                    all(isinstance(conjunct, isla.SemanticPredicateFormula)
                        for conjunct in get_conjuncts(state.constraint))), \
                f"Constraint is not true and contains formulas " \
                f"other than semantic predicate formulas: {state.constraint}"
            assert (state.constraint == sc.true() or
                    all(not pred_formula.binds_tree(leaf)
                        for pred_formula in get_conjuncts(state.constraint)
                        if isinstance(pred_formula, isla.SemanticPredicateFormula)
                        for _, leaf in state.tree.open_leaves())), \
                f"Constraint is not true and contains semantic predicate formulas which bind open leaves in the tree: " \
                f"{state.constraint}, leaves: {', '.join(list(map(str, [leaf for _, leaf in state.tree.open_leaves()])))}"

            if state.constraint == sc.true():
                for _ in range(self.max_number_free_instantiations):
                    yield DerivationTree.from_parse_tree(fuzzer.expand_tree(state.tree.to_parse_tree()))
            else:
                for _ in range(self.max_number_free_instantiations):
                    substitutions: Dict[DerivationTree, DerivationTree] = {
                        subtree: DerivationTree.from_parse_tree(fuzzer.expand_tree((subtree.value, None)))
                        for path, subtree in state.tree.open_leaves()
                    }

                    if substitutions:
                        yield from self.process_new_state(
                            SolutionState(state.constraint.substitute_expressions(substitutions),
                                          state.tree.substitute(substitutions)))

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
        semantic_formulas = [conjunct for conjunct in conjuncts
                             if isinstance(conjunct, isla.SMTFormula)
                             and not z3.is_true(conjunct.formula)]

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

    def eliminate_all_ready_semantic_predicate_formulas(self, state: SolutionState) -> Optional[SolutionState]:
        semantic_predicate_formulas = [
            conjunct for conjunct in split_conjunction(state.constraint)
            if isinstance(conjunct, isla.SemanticPredicateFormula)]

        semantic_predicate_formulas = sorted(semantic_predicate_formulas, key=lambda f: f.order)

        if not semantic_predicate_formulas:
            return None

        result = state

        changed = False
        for idx, semantic_predicate_formula in enumerate(semantic_predicate_formulas):
            evaluation_result = semantic_predicate_formula.evaluate()
            if not evaluation_result.ready():
                continue

            self.logger.debug("Eliminating semantic predicate formula %s", semantic_predicate_formula)
            changed = True

            if evaluation_result.false():
                return SolutionState(sc.false(), result.tree)

            if evaluation_result.true():
                result = SolutionState(
                    isla.replace_formula(
                        result.constraint,
                        semantic_predicate_formula,
                        sc.true()),
                    result.tree)
                continue

            new_constraint = (
                isla.replace_formula(result.constraint, semantic_predicate_formula, sc.true())
                    .substitute_expressions(evaluation_result.result))

            for k in range(idx + 1, len(semantic_predicate_formulas)):
                semantic_predicate_formulas[k] = cast(
                    isla.SemanticPredicateFormula,
                    semantic_predicate_formulas[k].substitute_expressions(evaluation_result.result))

            result = SolutionState(new_constraint, result.tree.substitute(evaluation_result.result))

        return result if changed else None

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
            if any(self.quantified_formula_might_match(formula, leaf_path, state.tree)
                   for formula in get_conjuncts(state.constraint)
                   if isinstance(formula, isla.ForallFormula))
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

                assert expanded_tree is not state.tree
                assert expanded_tree != state.tree
                assert expanded_tree.structural_hash() != state.tree.structural_hash()

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
                match[universal_formula.bound_variable][1]
                for match in matches
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

        for match in matches:
            inst_formula = existential_formula.inner_formula.substitute_expressions({
                variable: match_tree for variable, (_, match_tree) in match.items()
            })
            constraint = inst_formula & isla.replace_formula(state.constraint, existential_formula, sc.true())
            result.append(SolutionState(constraint, state.tree))

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
                for path, original_tree in state.tree.paths()
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

        # smt_formula = qfr_free_formula_to_z3_formula(formula)

        assert all(isinstance(conjunct, isla.SMTFormula) for conjunct in get_conjuncts(formula))

        smt_formulas = [conjunct for conjunct in get_conjuncts(formula)
                        if isinstance(conjunct, isla.SMTFormula)]

        # NODE: We need to cluster SMT formulas by tree substitutions! If there are two formulas
        # with a variable $var which is instantiated to different trees, we need two separate
        # solution. If, however, $var is instantiated with the *same* tree, we need one solution
        # to both formulas together.

        old_smt_formulas = smt_formulas
        smt_formulas = []

        for subformula in old_smt_formulas:
            subst_var: isla.Variable
            subst_tree: DerivationTree

            new_smt_formula: z3.BoolRef = subformula.formula
            new_substitutions = subformula.substitutions
            new_instantiated_variables = subformula.instantiated_variables

            for subst_var, subst_tree in subformula.substitutions.items():
                new_name = f"{subst_var.name}_{subst_tree.value}_{subst_tree.id}"
                new_var = isla.BoundVariable(new_name, subst_var.n_type)

                new_smt_formula = cast(z3.BoolRef, z3_subst(new_smt_formula, {subst_var.to_smt(): new_var.to_smt()}))
                new_substitutions = {new_var if k is subst_var else k: v for k, v in new_substitutions.items()}
                new_instantiated_variables = {new_var if v is subst_var else v for v in new_instantiated_variables}

            smt_formulas.append(
                isla.SMTFormula(
                    new_smt_formula,
                    *subformula.free_variables_,
                    instantiated_variables=new_instantiated_variables,
                    substitutions=new_substitutions))

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
            formulas: List[z3.BoolRef] = []

            for constant in constants:
                if constant.is_numeric():
                    regex = z3.Union(z3.Re("0"), z3.Concat(z3.Range("1", "9"), z3.Star(z3.Range("0", "9"))))
                else:
                    regex = self.extract_regular_expression(constant.n_type)
                formulas.append(z3.InRe(z3.String(constant.name), regex))

            for prev_solution in internal_solutions:
                for constant, string_val in prev_solution.items():
                    formulas.append(z3.Not(constant.to_smt() == string_val))

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
                internal_solutions.append(new_internal_solution)

        return solutions

    def process_new_states(self, new_states: List[SolutionState]) -> List[DerivationTree]:
        return [tree for new_state in new_states for tree in self.process_new_state(new_state)]

    def process_new_state(self, new_state: SolutionState) -> List[DerivationTree]:
        new_states = self.establish_invariant(new_state)
        new_states = [self.remove_nonmatching_universal_quantifiers(new_state) for new_state in new_states]
        new_states = [self.remove_infeasible_universal_quantifiers(new_state) for new_state in new_states]

        return [new_state.tree for new_state in new_states if self.state_is_valid_or_enqueue(new_state)]

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

        assert all(state.tree.find_node(arg)
                   for semantic_formula in get_conjuncts(state.constraint)
                   if isinstance(semantic_formula, isla.SMTFormula)
                   for arg in semantic_formula.substitutions.values())

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

    def establish_invariant(self, state: SolutionState) -> List[SolutionState]:
        formula = convert_to_dnf(convert_to_nnf(state.constraint))
        return [SolutionState(disjunct, state.tree) for disjunct in split_disjunction(formula)]

    def compute_cost(self, state: SolutionState) -> float:
        """Cost of state. Best value: 0, Worst: Unbounded"""

        # How costly is it to finish the tree?
        nonterminals = [leaf.value for _, leaf in state.tree.open_leaves()]
        tree_closing_cost = (
            # len(state.tree) +
            sum([self.symbol_costs[nonterminal]
                 for nonterminal in nonterminals]))

        # Quantifiers are expensive (universal formulas have to be matched, tree insertion for existential
        # formulas is even more costly).
        constraint_cost = len([sub for sub in get_conjuncts(state.constraint)
                               if isinstance(sub, isla.QuantifiedFormula)])

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
                for _, tree in DerivationTree.from_parse_tree(tree).paths()
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
        for universal_formula in get_conjuncts(state.constraint):
            if not isinstance(universal_formula, isla.ForallFormula):
                continue

            if not (any(self.quantified_formula_might_match(universal_formula, leaf_path, universal_formula.in_variable)
                        for leaf_path, leaf_node in universal_formula.in_variable.open_leaves())
                    or [match for match in isla.matches_for_quantified_formula(universal_formula)
                        if not universal_formula.is_already_matched(match[universal_formula.bound_variable][1])]):
                result = SolutionState(
                    isla.replace_formula(result.constraint, universal_formula, sc.true()), result.tree)

        return result

    def quantified_formula_might_match(
            self, qfd_formula: isla.QuantifiedFormula, path_to_nonterminal: Path, tree: DerivationTree) -> bool:
        node = tree.get_subtree(path_to_nonterminal)

        if qfd_formula.in_variable.find_node(node) is None:
            return False

        if qfd_formula.is_already_matched(node):
            # This formula won't match node IFF there is no subtree in node that matches.
            return any(self.quantified_formula_might_match(qfd_formula, path, node)
                       for path, _ in node.paths() if path)

        qfd_nonterminal = qfd_formula.bound_variable.n_type
        if qfd_nonterminal == node.value or self.reachable(node.value, qfd_nonterminal):
            return True

        if qfd_formula.bind_expression is None:
            return False

        # Is there an extension of some tree `node` is a subtree of, such that the
        # bind expression tree is a prefix tree of that extension?

        maybe_prefix_tree, _ = qfd_formula.bind_expression.to_tree_prefix(
            qfd_formula.bound_variable.n_type, self.grammar)

        for idx in reversed(range(len(path_to_nonterminal))):
            subtree = tree.get_subtree(path_to_nonterminal[:idx])
            if maybe_prefix_tree.is_potential_prefix(subtree) and not qfd_formula.is_already_matched(subtree):
                return True

        return False

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
        return max(0, sum([a_cost * weights[idx] / averages[idx] for idx, a_cost in enumerate(costs)]))

    def add_to_history(self, costs: List[float]):
        if not self.history:
            self.history.extend([[] for _ in costs])

        if len(self.history[0]) > 100:
            self.history = [subhistory[1:] for subhistory in self.history]

        for idx, cost in enumerate(costs):
            self.history[idx].append(cost)
