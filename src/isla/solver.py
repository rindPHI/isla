# Copyright © 2022 CISPA Helmholtz Center for Information Security.
# Author: Dominic Steinhöfel.
#
# This file is part of ISLa.
#
# ISLa is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# ISLa is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with ISLa.  If not, see <http://www.gnu.org/licenses/>.

import copy
import functools
import heapq
import itertools
import logging
import math
import operator
import random
import sys
import time
from abc import ABC
from dataclasses import dataclass
from functools import reduce, lru_cache, partial
from typing import (
    Dict,
    List,
    Set,
    Optional,
    Tuple,
    Union,
    cast,
    Callable,
    Iterable,
    Sequence,
)

import pkg_resources
import z3
from grammar_graph import gg
from grammar_graph.gg import GrammarGraph
from grammar_to_regex.cfg2regex import RegexConverter
from grammar_to_regex.regex import regex_to_z3
from orderedset import OrderedSet
from packaging import version
from returns.converters import result_to_maybe
from returns.functions import compose, tap
from returns.maybe import Nothing, Some
from returns.pipeline import flow, is_successful
from returns.pointfree import lash
from returns.result import safe, Success

import isla.isla_shortcuts as sc
import isla.three_valued_truth
from isla import language
from isla.derivation_tree import DerivationTree
from isla.evaluator import (
    evaluate,
    quantified_formula_might_match,
    get_toplevel_quantified_formulas,
    eliminate_quantifiers,
)
from isla.evaluator import matches_for_quantified_formula
from isla.existential_helpers import (
    insert_tree,
    DIRECT_EMBEDDING,
    SELF_EMBEDDING,
    CONTEXT_ADDITION,
)
from isla.fuzzer import GrammarFuzzer, GrammarCoverageFuzzer, expansion_key
from isla.helpers import (
    delete_unreachable,
    shuffle,
    dict_of_lists_to_list_of_dicts,
    weighted_geometric_mean,
    assertions_activated,
    split_str_with_nonterminals,
    cluster_by_common_elements,
    is_nonterminal,
    canonical,
    lazyjoin,
    lazystr,
    Maybe,
    eliminate_suffixes,
    get_elem_by_equivalence,
    get_expansions,
    list_del,
    compute_nullable_nonterminals,
    eassert,
    merge_dict_of_sets,
)
from isla.isla_predicates import (
    STANDARD_STRUCTURAL_PREDICATES,
    STANDARD_SEMANTIC_PREDICATES,
    COUNT_PREDICATE,
)
from isla.language import (
    VariablesCollector,
    split_conjunction,
    split_disjunction,
    convert_to_dnf,
    convert_to_nnf,
    ensure_unique_bound_variables,
    parse_isla,
    get_conjuncts,
    parse_bnf,
    ForallIntFormula,
    set_smt_auto_eval,
    NoopFormulaTransformer,
    set_smt_auto_subst,
    fresh_constant,
)
from isla.mutator import Mutator
from isla.parser import EarleyParser
from isla.type_defs import Grammar, Path, ImmutableList, CanonicalGrammar
from isla.z3_helpers import (
    z3_solve,
    z3_subst,
    z3_eq,
    z3_and,
    visit_z3_expr,
    smt_string_val_to_string,
    parent_relationships_in_z3_expr,
    numeric_intervals_from_regex,
    z3_or,
)


@dataclass(frozen=True)
class SolutionState:
    constraint: language.Formula
    tree: DerivationTree
    level: int = 0
    __hash: Optional[int] = None

    def formula_satisfied(
        self, grammar: Grammar
    ) -> isla.three_valued_truth.ThreeValuedTruth:
        if self.tree.is_open():
            # Have to instantiate variables first
            return isla.three_valued_truth.ThreeValuedTruth.unknown()

        return evaluate(self.constraint, self.tree, grammar)

    def complete(self) -> bool:
        if not self.tree.is_complete():
            return False

        # We assume that any universal quantifier has already been instantiated, if it
        # matches, and is thus satisfied, or another unsatisfied constraint resulted
        # from the instantiation. Existential, predicate, and SMT formulas have to be
        # eliminated first.

        return self.constraint == sc.true()

    # Less-than comparisons are needed for usage in the binary heap queue
    def __lt__(self, other: "SolutionState"):
        return hash(self) < hash(other)

    def __hash__(self):
        if self.__hash is None:
            result = hash((self.constraint, self.tree))
            object.__setattr__(self, "__hash", result)
            return result

        return self.__hash

    def __eq__(self, other):
        return (
            isinstance(other, SolutionState)
            and self.constraint == other.constraint
            and self.tree.structurally_equal(other.tree)
        )


@dataclass(frozen=True)
class CostWeightVector:
    """
    Collection of weights for the
    :class:`~isla.solver.GrammarBasedBlackboxCostComputer`.
    """

    tree_closing_cost: float = 0
    constraint_cost: float = 0
    derivation_depth_penalty: float = 0
    low_k_coverage_penalty: float = 0
    low_global_k_path_coverage_penalty: float = 0

    def __iter__(self):
        """
        Use tuple assignment for objects of this type:

        >>> v = CostWeightVector(1, 2, 3, 4, 5)
        >>> a, b, c, d, e = v
        >>> (a, b, c, d, e)
        (1, 2, 3, 4, 5)

        :return: An iterator of the fixed-size list of elements of the weight vector.
        """
        return iter(
            [
                self.tree_closing_cost,
                self.constraint_cost,
                self.derivation_depth_penalty,
                self.low_k_coverage_penalty,
                self.low_global_k_path_coverage_penalty,
            ]
        )

    def __getitem__(self, item: int) -> float:
        """
        Tuple-like access of elements of the vector.

        >>> v = CostWeightVector(1, 2, 3, 4, 5)
        >>> v[3]
        4

        :param item: A numeric index.
        :return: The element at index :code:`item`.
        """
        assert isinstance(item, int)
        return [
            self.tree_closing_cost,
            self.constraint_cost,
            self.derivation_depth_penalty,
            self.low_k_coverage_penalty,
            self.low_global_k_path_coverage_penalty,
        ][item]


@dataclass(frozen=True)
class CostSettings:
    weight_vector: CostWeightVector
    k: int = 3

    def __init__(self, weight_vector: CostWeightVector, k: int = 3):
        assert isinstance(weight_vector, CostWeightVector)
        assert isinstance(k, int)
        object.__setattr__(self, "weight_vector", weight_vector)
        object.__setattr__(self, "k", k)


STD_COST_SETTINGS = CostSettings(
    CostWeightVector(
        tree_closing_cost=6.5,
        constraint_cost=1,
        derivation_depth_penalty=4,
        low_k_coverage_penalty=2,
        low_global_k_path_coverage_penalty=19,
    ),
    k=3,
)


@dataclass(frozen=True)
class UnknownResultError(Exception):
    pass


@dataclass(frozen=True)
class SemanticError(Exception):
    pass


@dataclass(frozen=True)
class SolverDefaults:
    formula: Optional[language.Formula | str] = None
    structural_predicates: frozenset[
        language.StructuralPredicate
    ] = STANDARD_STRUCTURAL_PREDICATES
    semantic_predicates: frozenset[
        language.SemanticPredicate
    ] = STANDARD_SEMANTIC_PREDICATES
    max_number_free_instantiations: int = 10
    max_number_smt_instantiations: int = 10
    max_number_tree_insertion_results: int = 5
    enforce_unique_trees_in_queue: bool = False
    debug: bool = False
    cost_computer: Optional["CostComputer"] = None
    timeout_seconds: Optional[int] = None
    global_fuzzer: bool = False
    predicates_unique_in_int_arg: Tuple[language.SemanticPredicate, ...] = (
        COUNT_PREDICATE,
    )
    fuzzer_factory: Callable[
        [Grammar], GrammarFuzzer
    ] = lambda grammar: GrammarCoverageFuzzer(grammar)
    tree_insertion_methods: Optional[int] = None
    activate_unsat_support: bool = False
    grammar_unwinding_threshold: int = 4
    initial_tree: Maybe[DerivationTree] = Nothing
    enable_optimized_z3_queries: bool = True
    start_symbol: Optional[str] = None


_DEFAULTS = SolverDefaults()


class ISLaSolver:
    """
    The solver class for ISLa formulas/constraints. Its top-level methods are

    :meth:`~isla.solver.ISLaSolver.solve`
      Use to generate solutions for an ISLa constraint.

    :meth:`~isla.solver.ISLaSolver.check`
      Use to check if an ISLa constraint is satisfied for a given input.

    :meth:`~isla.solver.ISLaSolver.parse`
      Use to parse and validate an input.

    :meth:`~isla.solver.ISLaSolver.repair`
      Use to repair an input such that it satisfies a constraint.

    :meth:`~isla.solver.ISLaSolver.mutate`
      Use to mutate an input such that the result satisfies a constraint.
    """

    def __init__(
        self,
        grammar: Grammar | str,
        formula: Optional[language.Formula | str] = _DEFAULTS.formula,
        structural_predicates: Set[
            language.StructuralPredicate
        ] = _DEFAULTS.structural_predicates,
        semantic_predicates: Set[
            language.SemanticPredicate
        ] = _DEFAULTS.semantic_predicates,
        max_number_free_instantiations: int = _DEFAULTS.max_number_free_instantiations,
        max_number_smt_instantiations: int = _DEFAULTS.max_number_smt_instantiations,
        max_number_tree_insertion_results: int = _DEFAULTS.max_number_tree_insertion_results,
        enforce_unique_trees_in_queue: bool = _DEFAULTS.enforce_unique_trees_in_queue,
        debug: bool = _DEFAULTS.debug,
        cost_computer: Optional["CostComputer"] = _DEFAULTS.cost_computer,
        timeout_seconds: Optional[int] = _DEFAULTS.timeout_seconds,
        global_fuzzer: bool = _DEFAULTS.global_fuzzer,
        predicates_unique_in_int_arg: Tuple[
            language.SemanticPredicate, ...
        ] = _DEFAULTS.predicates_unique_in_int_arg,
        fuzzer_factory: Callable[[Grammar], GrammarFuzzer] = _DEFAULTS.fuzzer_factory,
        tree_insertion_methods: Optional[int] = _DEFAULTS.tree_insertion_methods,
        activate_unsat_support: bool = _DEFAULTS.activate_unsat_support,
        grammar_unwinding_threshold: int = _DEFAULTS.grammar_unwinding_threshold,
        initial_tree: Maybe[DerivationTree] = _DEFAULTS.initial_tree,
        enable_optimized_z3_queries: bool = _DEFAULTS.enable_optimized_z3_queries,
        start_symbol: Optional[str] = _DEFAULTS.start_symbol,
    ):
        """
        The constructor of :class:`~isla.solver.ISLaSolver` accepts a large number of
        parameters. However, all but the first one, :code:`grammar`, are *optional.*

        The simplest way to construct an ISLa solver is by only providing it with a
        grammar only; it then works like a grammar fuzzer.

        >>> import random
        >>> random.seed(1)

        >>> import string
        >>> LANG_GRAMMAR = {
        ...     "<start>":
        ...         ["<stmt>"],
        ...     "<stmt>":
        ...         ["<assgn> ; <stmt>", "<assgn>"],
        ...     "<assgn>":
        ...         ["<var> := <rhs>"],
        ...     "<rhs>":
        ...         ["<var>", "<digit>"],
        ...     "<var>": list(string.ascii_lowercase),
        ...     "<digit>": list(string.digits)
        ... }
        >>>
        >>> from isla.solver import ISLaSolver
        >>> solver = ISLaSolver(LANG_GRAMMAR)
        >>>
        >>> str(solver.solve())
        'd := 9'
        >>> str(solver.solve())
        'v := n ; s := r'

        :param grammar: The underlying grammar; either, as a "Fuzzing Book" dictionary
          or in BNF syntax.
        :param formula: The formula to solve; either a string or a readily parsed
          formula. If no formula is given, a default `true` constraint is assumed, and
          the solver falls back to a grammar fuzzer. The number of produced solutions
          will then be bound by `max_number_free_instantiations`.
        :param structural_predicates: Structural predicates to use when parsing a
          formula.
        :param semantic_predicates: Semantic predicates to use when parsing a formula.
        :param max_number_free_instantiations: Number of times that nonterminals that
          are not bound by any formula should be expanded by a coverage-based fuzzer.
        :param max_number_smt_instantiations: Number of solutions of SMT formulas that
          should be produced.
        :param max_number_tree_insertion_results: The maximum number of results when
          solving existential quantifiers by tree insertion.
        :param enforce_unique_trees_in_queue: If true, states with the same tree as an
          already existing tree in the queue are discarded, irrespectively of the
          constraint.
        :param debug: If true, debug information about the evolution of states is
          collected, notably in the field state_tree. The root of the tree is in the
          field state_tree_root. The field costs stores the computed cost values for
          all new nodes.
        :param cost_computer: The `CostComputer` class for computing the cost relevant
          to placing states in ISLa's queue.
        :param timeout_seconds: Number of seconds after which the solver will terminate.
        :param global_fuzzer: If set to True, only one coverage-guided grammar fuzzer
          object is used to finish off unconstrained open derivation trees throughout
          the whole generation time. This may be beneficial for some targets; e.g., we
          experienced that CSV works significantly faster. However, the achieved k-path
          coverage can be lower with that setting.
        :param predicates_unique_in_int_arg: This is needed in certain cases for
          instantiating universal integer quantifiers. The supplied predicates should
          have exactly one integer argument, and hold for exactly one integer value
          once all other parameters are fixed.
        :param fuzzer_factory: Constructor of the fuzzer to use for instantiating
          "free" nonterminals.
        :param tree_insertion_methods: Combination of methods to use for existential
          quantifier elimination by tree insertion. Full selection: `DIRECT_EMBEDDING &
          SELF_EMBEDDING & CONTEXT_ADDITION`.
        :param activate_unsat_support: Set to True if you assume that a formula might
          be unsatisfiable. This triggers additional tests for unsatisfiability that
          reduce input generation performance, but might ensure termination (with a
          negative solver result) for unsatisfiable problems for which the solver could
          otherwise diverge.
        :param grammar_unwinding_threshold: When querying the SMT solver, ISLa passes a
          regular expression for the syntax of the involved nonterminals. If this
          syntax is not regular, we unwind the respective part in the reference grammar
          up to a depth of `grammar_unwinding_threshold`. If this is too shallow, it can
          happen that an equation etc. cannot be solved; if it is too deep, it can
          negatively impact performance (and quite tremendously so).
        :param initial_tree: An initial input tree for the queue, if the solver shall
          not start from the tree `(<start>, None)`.
        :param enable_optimized_z3_queries: Enables preprocessing of Z3 queries (mainly
          numeric problems concerning things like length). This can improve performance
          significantly; however, it might happen that certain problems cannot be solved
          anymore. In that case, this option can/should be deactivated.
        :param start_symbol: This is an alternative to `initial_tree` for starting with
          a start symbol different form `<start>`. If `start_symbol` is provided, a tree
          consisting of a single root node with the value of `start_symbol` is chosen as
          initial tree.
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
        assert version.parse(z3_version) >= version.parse("4.8.13.0"), (
            f"ISLa requires at least z3 4.8.13.0, present: {z3_version}. "
            "Please install a newer z3 version, e.g., using 'pip install z3-solver==4.8.14.0'."
        )

        if isinstance(grammar, str):
            self.grammar = parse_bnf(grammar)
        else:
            self.grammar = copy.deepcopy(grammar)

        assert start_symbol is None or not is_successful(
            initial_tree
        ), "You cannot supply a start symbol *and* an initial tree."

        if start_symbol is not None:
            self.grammar |= {"<start>": [start_symbol]}
            self.grammar = delete_unreachable(self.grammar)

        self.graph = GrammarGraph.from_grammar(self.grammar)
        self.canonical_grammar = canonical(self.grammar)
        self.timeout_seconds = timeout_seconds
        self.start_time: Optional[int] = None
        self.global_fuzzer = global_fuzzer
        self.fuzzer = fuzzer_factory(self.grammar)
        self.fuzzer_factory = fuzzer_factory
        self.predicates_unique_in_int_arg: Set[language.SemanticPredicate] = set(
            predicates_unique_in_int_arg
        )
        self.grammar_unwinding_threshold = grammar_unwinding_threshold
        self.enable_optimized_z3_queries = enable_optimized_z3_queries

        if activate_unsat_support and tree_insertion_methods is None:
            self.tree_insertion_methods = 0
        else:
            if activate_unsat_support:
                assert tree_insertion_methods is not None
                print(
                    "With activate_unsat_support set, a 0 value for tree_insertion_methods is recommended, "
                    f"the current value is: {tree_insertion_methods}",
                    file=sys.stderr,
                )

            self.tree_insertion_methods = (
                DIRECT_EMBEDDING + SELF_EMBEDDING + CONTEXT_ADDITION
            )
            if tree_insertion_methods is not None:
                self.tree_insertion_methods = tree_insertion_methods

        self.activate_unsat_support = activate_unsat_support
        self.currently_unsat_checking: bool = False

        self.cost_computer = (
            cost_computer
            if cost_computer is not None
            else GrammarBasedBlackboxCostComputer(STD_COST_SETTINGS, self.graph)
        )

        formula = (
            sc.true()
            if formula is None
            else (
                parse_isla(
                    formula, self.grammar, structural_predicates, semantic_predicates
                )
                if isinstance(formula, str)
                else formula
            )
        )

        self.formula = ensure_unique_bound_variables(formula)

        top_constants: Set[language.Constant] = set(
            [
                c
                for c in VariablesCollector.collect(self.formula)
                if isinstance(c, language.Constant) and not c.is_numeric()
            ]
        )

        assert len(top_constants) <= 1, (
            "ISLa only accepts up to one constant (free variable), "
            + f'found {len(top_constants)}: {", ".join(map(str, top_constants))}'
        )

        self.top_constant = result_to_maybe(safe(lambda: next(iter(top_constants)))())

        quantifier_chains: List[Tuple[language.ForallFormula, ...]] = [
            tuple([f for f in c if isinstance(f, language.ForallFormula)])
            for c in get_quantifier_chains(formula)
        ]
        # TODO: Remove?
        self.quantifier_chains: List[Tuple[language.ForallFormula, ...]] = [
            c for c in quantifier_chains if c
        ]

        self.max_number_free_instantiations: int = max_number_free_instantiations
        self.max_number_smt_instantiations: int = max_number_smt_instantiations
        self.max_number_tree_insertion_results = max_number_tree_insertion_results
        self.enforce_unique_trees_in_queue = enforce_unique_trees_in_queue

        # Initialize Queue
        self.initial_tree = (
            initial_tree.lash(
                lambda _: Maybe.from_optional(start_symbol)
                .map(lambda s: eassert(s, s in self.grammar))
                .map(lambda s: DerivationTree(s, None))
            ).lash(
                lambda _: Some(
                    DerivationTree(
                        self.top_constant.map(lambda c: c.n_type).value_or("<start>"),
                        None,
                    )
                )
            )
        ).unwrap()

        initial_formula = self.top_constant.map(
            lambda c: self.formula.substitute_expressions({c: self.initial_tree})
        ).value_or(self.formula)
        initial_state = SolutionState(initial_formula, self.initial_tree)
        initial_states = self.establish_invariant(initial_state)

        self.queue: List[Tuple[float, SolutionState]] = []
        self.tree_hashes_in_queue: Set[int] = {self.initial_tree.structural_hash()}
        self.state_hashes_in_queue: Set[int] = {hash(state) for state in initial_states}
        for state in initial_states:
            heapq.heappush(self.queue, (self.compute_cost(state), state))

        self.seen_coverages: Set[str] = set()
        self.current_level: int = 0
        self.step_cnt: int = 0
        self.last_cost_recomputation: int = 0

        self.regex_cache = {}

        self.solutions: List[DerivationTree] = []

        # Debugging stuff
        self.debug = debug
        self.state_tree: Dict[
            SolutionState, List[SolutionState]
        ] = {}  # is only filled if self.debug
        self.state_tree_root = None
        self.current_state = None
        self.costs: Dict[SolutionState, float] = {}

        if self.debug:
            self.state_tree[initial_state] = initial_states
            self.state_tree_root = initial_state
            self.costs[initial_state] = 0
            for state in initial_states:
                self.costs[state] = self.compute_cost(state)

    def solve(self) -> DerivationTree:
        """
        Attempts to compute a solution to the given ISLa formula. Returns that solution,
        if any. This function can be called repeatedly to obtain more solutions until
        one of two exception types is raised: A :class:`StopIteration` indicates that
        no more solution can be found; a :class:`TimeoutError` is raised if a timeout
        occurred. After that, an exception will be raised every time.

        The timeout can be controlled by the :code:`timeout_seconds`
        :meth:`constructor <isla.solver.ISLaSolver.__init__>` parameter.

        :return: A solution for the ISLa formula passed to the
          :class:`isla.solver.ISLaSolver`.
        """
        if self.timeout_seconds is not None and self.start_time is None:
            self.start_time = int(time.time())

        while self.queue:
            self.step_cnt += 1

            # import dill as pickle
            # state_hash = 9107154106757938105
            # out_file = "/tmp/saved_debug_state"
            # if hash(self.queue[0][1]) == state_hash:
            #     with open(out_file, 'wb') as debug_state_file:
            #         pickle.dump(self, debug_state_file)
            #     print(f"Dumping state to {out_file}")
            #     exit()

            if self.timeout_seconds is not None:
                if int(time.time()) - self.start_time > self.timeout_seconds:
                    self.logger.debug("TIMEOUT")
                    raise TimeoutError(self.timeout_seconds)

            if self.solutions:
                solution = self.solutions.pop(0)
                self.logger.debug('Found solution "%s"', solution)
                return solution

            cost: int
            state: SolutionState
            cost, state = heapq.heappop(self.queue)

            self.current_level = state.level
            self.tree_hashes_in_queue.discard(state.tree.structural_hash())
            self.state_hashes_in_queue.discard(hash(state))

            if self.debug:
                self.current_state = state
                self.state_tree.setdefault(state, [])
            self.logger.debug(
                "Polling new state (%s, %s) (hash %d, cost %f)",
                state.constraint,
                state.tree.to_string(show_open_leaves=True, show_ids=True),
                hash(state),
                cost,
            )
            self.logger.debug("Queue length: %s", len(self.queue))

            assert not isinstance(state.constraint, language.DisjunctiveFormula)

            # Instantiate all top-level structural predicate formulas.
            state = self.instantiate_structural_predicates(state)

            # Apply the first elimination function that is applicable.
            # The later ones are ignored.
            def process_and_extend_solutions(
                result_states: List[SolutionState],
            ) -> Nothing:
                assert result_states is not None
                self.solutions.extend(self.process_new_states(result_states))
                return Nothing

            flow(
                Nothing,
                *map(
                    compose(lambda f: (lambda _: f(state)), lash),
                    [
                        self.noop_on_false_constraint,
                        self.eliminate_existential_integer_quantifiers,
                        self.instantiate_universal_integer_quantifiers,
                        self.match_all_universal_formulas,
                        self.expand_to_match_quantifiers,
                        self.eliminate_all_semantic_formulas,
                        self.eliminate_all_ready_semantic_predicate_formulas,
                        self.eliminate_and_match_first_existential_formula_and_expand,
                        self.assert_remaining_formulas_are_lazy_binding_semantic,
                        self.finish_unconstrained_trees,
                        self.expand,
                    ],
                ),
            ).bind(process_and_extend_solutions)

        if self.solutions:
            solution = self.solutions.pop(0)
            self.logger.debug('Found solution "%s"', solution)
            return solution
        else:
            self.logger.debug("UNSAT")
            raise StopIteration()

    def check(self, inp: DerivationTree | str) -> bool:
        """
        Evaluates whether the given derivation tree satisfies the constraint passed to
        the solver. Raises an `UnknownResultError` if this could not be evaluated
        (e.g., because of a solver timeout or a semantic predicate that cannot be
        evaluated).

        :param inp: The input to evaluate, either readily parsed or as a string.
        :return: A truth value.
        """
        if isinstance(inp, str):
            try:
                self.parse(inp)
                return True
            except (SyntaxError, SemanticError):
                return False

        assert isinstance(inp, DerivationTree)

        result = evaluate(self.formula, inp, self.grammar)

        if result.is_unknown():
            raise UnknownResultError()
        else:
            return bool(result)

    def parse(
        self,
        inp: str,
        nonterminal: str = "<start>",
        skip_check: bool = False,
        silent: bool = False,
    ) -> DerivationTree:
        """
        Parses the given input `inp`. Raises a `SyntaxError` if the input does not
        satisfy the grammar, a `SemanticError` if it does not satisfy the constraint
        (this is only checked if `nonterminal` is "<start>"), and returns the parsed
        `DerivationTree` otherwise.

        :param inp: The input to parse.
        :param nonterminal: The nonterminal to start parsing with, if a string
          corresponding to a sub-grammar shall be parsed. We don't check semantic
          correctness in that case.
        :param skip_check: If True, the semantic check is left out.
        :param silent: If True, no error is sent to the log stream in case of a
            failed parse.
        :return: A parsed `DerivationTree`.
        """
        grammar = copy.deepcopy(self.grammar)
        if nonterminal != "<start>":
            grammar |= {"<start>": [nonterminal]}
            grammar = delete_unreachable(grammar)

        parser = EarleyParser(grammar)
        try:
            parse_tree = next(parser.parse(inp))
            if nonterminal != "<start>":
                parse_tree = parse_tree[1][0]
            tree = DerivationTree.from_parse_tree(parse_tree)
        except SyntaxError as err:
            if not silent:
                self.logger.error(
                    f'Error parsing "{inp}" starting with "{nonterminal}"'
                )
            raise err

        if not skip_check and nonterminal == "<start>" and not self.check(tree):
            raise SemanticError()

        return tree

    def repair(
        self, inp: DerivationTree | str, fix_timeout_seconds: float = 3
    ) -> Maybe[DerivationTree]:
        """
        Attempts to repair the given input. The input must not violate syntactic
        (grammar) constraints. If semantic constraints are violated, this method
        gradually abstracts the input and tries to turn it into a valid one.
        Note that intensive structural manipulations are not performed; we merely
        try to satisfy SMT-LIB and semantic predicate constraints.

        :param inp: The input to fix.
        :param fix_timeout_seconds: A timeout used when calling the solver for an
          abstracted input. Usually, a low timeout suffices.
        :return: A fixed input (or the original, if it was not broken) or nothing.
        """

        inp = self.parse(inp, skip_check=True) if isinstance(inp, str) else inp

        try:
            if self.check(inp) or not is_successful(self.top_constant):
                return Some(inp)
        except UnknownResultError:
            pass

        formula = self.top_constant.map(
            lambda c: self.formula.substitute_expressions({c: inp})
        ).unwrap()

        set_smt_auto_eval(formula, False)
        set_smt_auto_subst(formula, False)

        qfr_free = eliminate_quantifiers(
            formula,
            grammar=self.grammar,
            numeric_constants={
                c
                for c in VariablesCollector.collect(formula)
                if isinstance(c, language.Constant) and c.is_numeric()
            },
        )

        # We first evaluate all structural predicates; for now, we do not interfere
        # with structure.
        semantic_only = qfr_free.transform(EvaluatePredicateFormulasTransformer(inp))

        if semantic_only == sc.false():
            # This cannot be repaired while preserving structure; for existential
            # problems, we could try tree insertion. We leave this for future work.
            return Nothing

        # We try to satisfy any of the remaining disjunctive elements, in random order
        for formula_to_satisfy in shuffle(split_disjunction(semantic_only)):
            # Now, we consider all combinations of 1, 2, ... of the derivation trees
            # participating in the formula. We successively prune deeper and deeper
            # subtrees until the resulting input evaluates to "unknown" for the given
            # formula.

            participating_paths = {
                inp.find_node(arg) for arg in formula_to_satisfy.tree_arguments()
            }

            def do_complete(tree: DerivationTree) -> Maybe[DerivationTree]:
                return result_to_maybe(
                    safe(
                        self.copy_without_queue(
                            initial_tree=Some(tree),
                            timeout_seconds=Some(fix_timeout_seconds),
                        ).solve,
                        (UnknownResultError, TimeoutError, StopIteration),
                    )()
                )

            # If p1, p2 are in participating_paths, then we consider the following
            # path combinations (roughly) in the listed order:
            # {p1}, {p2}, {p1, p2}, {p1[:-1]}, {p2[:-1]}, {p1[:-1], p2}, {p1, p2[:-1]},
            # {p1[:-1], p2[:-1]}, ...
            for abstracted_tree in generate_abstracted_trees(inp, participating_paths):
                match (
                    safe(lambda: self.check(abstracted_tree))()
                    .bind(lambda _: Nothing)
                    .lash(
                        lambda exc: Some(abstracted_tree)
                        if isinstance(exc, UnknownResultError)
                        else Nothing
                    )
                    .bind(do_complete)
                ):
                    case Some(completed):
                        return Some(completed)
                    case _:
                        pass

        return Nothing

    def mutate(
        self,
        inp: DerivationTree | str,
        min_mutations: int = 2,
        max_mutations: int = 5,
        fix_timeout_seconds: float = 1,
    ) -> DerivationTree:
        """
        Mutates `inp` such that the result satisfies the constraint.

        :param inp: The input to mutate.
        :param min_mutations: The minimum number of mutation steps to perform.
        :param max_mutations: The maximum number of mutation steps to perform.
        :param fix_timeout_seconds: A timeout used when calling the solver for fixing
          an abstracted input. Usually, a low timeout suffices.
        :return: A mutated input.
        """

        inp = self.parse(inp, skip_check=True) if isinstance(inp, str) else inp
        mutator = Mutator(
            self.grammar,
            min_mutations=min_mutations,
            max_mutations=max_mutations,
            graph=self.graph,
        )

        while True:
            mutated = mutator.mutate(inp)
            if mutated.structurally_equal(inp):
                continue
            maybe_fixed = self.repair(mutated, fix_timeout_seconds)
            if is_successful(maybe_fixed):
                return maybe_fixed.unwrap()

    def copy_without_queue(
        self,
        grammar: Maybe[Grammar | str] = Nothing,
        formula: Maybe[language.Formula | str] = Nothing,
        max_number_free_instantiations: Maybe[int] = Nothing,
        max_number_smt_instantiations: Maybe[int] = Nothing,
        max_number_tree_insertion_results: Maybe[int] = Nothing,
        enforce_unique_trees_in_queue: Maybe[bool] = Nothing,
        debug: Maybe[bool] = Nothing,
        cost_computer: Maybe["CostComputer"] = Nothing,
        timeout_seconds: Maybe[int] = Nothing,
        global_fuzzer: Maybe[bool] = Nothing,
        predicates_unique_in_int_arg: Maybe[
            Tuple[language.SemanticPredicate, ...]
        ] = Nothing,
        fuzzer_factory: Maybe[Callable[[Grammar], GrammarFuzzer]] = Nothing,
        tree_insertion_methods: Maybe[int] = Nothing,
        activate_unsat_support: Maybe[bool] = Nothing,
        grammar_unwinding_threshold: Maybe[int] = Nothing,
        initial_tree: Maybe[DerivationTree] = Nothing,
        enable_optimized_z3_queries: Maybe[bool] = Nothing,
        start_symbol: Optional[str] = None,
    ):
        result = ISLaSolver(
            grammar=grammar.value_or(self.grammar),
            formula=formula.value_or(self.formula),
            max_number_free_instantiations=max_number_free_instantiations.value_or(
                self.max_number_free_instantiations
            ),
            max_number_smt_instantiations=max_number_smt_instantiations.value_or(
                self.max_number_smt_instantiations
            ),
            max_number_tree_insertion_results=max_number_tree_insertion_results.value_or(
                self.max_number_tree_insertion_results
            ),
            enforce_unique_trees_in_queue=enforce_unique_trees_in_queue.value_or(
                self.enforce_unique_trees_in_queue
            ),
            debug=debug.value_or(self.debug),
            cost_computer=cost_computer.value_or(self.cost_computer),
            timeout_seconds=timeout_seconds.value_or(self.timeout_seconds),
            global_fuzzer=global_fuzzer.value_or(self.global_fuzzer),
            predicates_unique_in_int_arg=predicates_unique_in_int_arg.value_or(
                self.predicates_unique_in_int_arg
            ),
            fuzzer_factory=fuzzer_factory.value_or(self.fuzzer_factory),
            tree_insertion_methods=tree_insertion_methods.value_or(
                self.tree_insertion_methods
            ),
            activate_unsat_support=activate_unsat_support.value_or(
                self.activate_unsat_support
            ),
            grammar_unwinding_threshold=grammar_unwinding_threshold.value_or(
                self.grammar_unwinding_threshold
            ),
            initial_tree=initial_tree,
            enable_optimized_z3_queries=enable_optimized_z3_queries.value_or(
                self.enable_optimized_z3_queries
            ),
            start_symbol=start_symbol,
        )

        result.regex_cache = self.regex_cache

        return result

    @staticmethod
    def noop_on_false_constraint(
        state: SolutionState,
    ) -> Maybe[List[SolutionState]]:
        if state.constraint == sc.false():
            # This state can be silently discarded.
            return Some([state])

        return Nothing

    def expand_to_match_quantifiers(
        self,
        state: SolutionState,
    ) -> Maybe[List[SolutionState]]:
        if all(
            not isinstance(conjunct, language.ForallFormula)
            for conjunct in get_conjuncts(state.constraint)
        ):
            return Nothing

        expansion_result = self.expand_tree(state)

        assert len(expansion_result) > 0, f"State {state} will never leave the queue."
        self.logger.debug(
            "Expanding state %s (%d successors)", state, len(expansion_result)
        )

        return Some(expansion_result)

    def eliminate_and_match_first_existential_formula_and_expand(
        self,
        state: SolutionState,
    ) -> Maybe[List[SolutionState]]:
        elim_result = self.eliminate_and_match_first_existential_formula(state)
        if elim_result is None:
            return Nothing

        # Also add some expansions of the original state, to create a larger
        # solution stream (otherwise, it might be possible that only a small
        # finite number of solutions are generated for existential formulas).
        return Some(
            elim_result + self.expand_tree(state, limit=2, only_universal=False)
        )

    def assert_remaining_formulas_are_lazy_binding_semantic(
        self,
        state: SolutionState,
    ) -> Maybe[List[SolutionState]]:
        # SEMANTIC PREDICATE FORMULAS can remain if they bind lazily. In that case, we can choose a random
        # instantiation and let the predicate "fix" the resulting tree.
        assert state.constraint == sc.true() or all(
            isinstance(conjunct, language.SemanticPredicateFormula)
            or (
                isinstance(conjunct, language.NegatedFormula)
                and isinstance(conjunct.args[0], language.SemanticPredicateFormula)
            )
            for conjunct in get_conjuncts(state.constraint)
        ), (
            "Constraint is not true and contains formulas "
            f"other than semantic predicate formulas: {state.constraint}"
        )

        assert (
            state.constraint == sc.true()
            or all(
                not pred_formula.binds_tree(leaf)
                for pred_formula in get_conjuncts(state.constraint)
                if isinstance(pred_formula, language.SemanticPredicateFormula)
                for _, leaf in state.tree.open_leaves()
            )
            or all(
                not cast(
                    language.SemanticPredicateFormula, pred_formula.args[0]
                ).binds_tree(leaf)
                for pred_formula in get_conjuncts(state.constraint)
                if isinstance(pred_formula, language.NegatedFormula)
                and isinstance(pred_formula.args[0], language.SemanticPredicateFormula)
            )
            for _, leaf in state.tree.open_leaves()
        ), (
            "Constraint is not true and contains semantic predicate formulas binding open tree leaves: "
            f"{state.constraint}, leaves: "
            + ", ".join(
                [str(leaf) for _, leaf in state.tree.open_leaves()],
            )
        )

        return Nothing

    def finish_unconstrained_trees(
        self,
        state: SolutionState,
    ) -> Maybe[List[SolutionState]]:
        fuzzer = (
            self.fuzzer if self.global_fuzzer else self.fuzzer_factory(self.grammar)
        )

        if isinstance(fuzzer, GrammarCoverageFuzzer):
            fuzzer.covered_expansions.update(self.seen_coverages)

        if state.constraint != sc.true():
            return Nothing

        closed_results: List[SolutionState] = []
        for _ in range(self.max_number_free_instantiations):
            result = state.tree
            for path, leaf in state.tree.open_leaves():
                leaf_inst = fuzzer.expand_tree(DerivationTree(leaf.value, None))
                result = result.replace_path(path, leaf_inst)

            closed_results.append(SolutionState(state.constraint, result))

        return Some(closed_results)

    def expand(
        self,
        state: SolutionState,
    ) -> Maybe[List[SolutionState]]:
        fuzzer = (
            self.fuzzer if self.global_fuzzer else self.fuzzer_factory(self.grammar)
        )

        if isinstance(fuzzer, GrammarCoverageFuzzer):
            fuzzer.covered_expansions.update(self.seen_coverages)

        result: List[SolutionState] = []
        for _ in range(self.max_number_free_instantiations):
            substitutions: Dict[DerivationTree, DerivationTree] = {
                subtree: fuzzer.expand_tree(DerivationTree(subtree.value, None))
                for path, subtree in state.tree.open_leaves()
            }

            if substitutions:
                result.append(
                    SolutionState(
                        state.constraint.substitute_expressions(substitutions),
                        state.tree.substitute(substitutions),
                    )
                )

        return Some(result)

    def instantiate_structural_predicates(self, state: SolutionState) -> SolutionState:
        predicate_formulas = [
            pred_formula
            for pred_formula in language.FilterVisitor(
                lambda f: isinstance(f, language.StructuralPredicateFormula)
            ).collect(state.constraint)
            if (
                isinstance(pred_formula, language.StructuralPredicateFormula)
                and all(
                    not isinstance(arg, language.Variable) for arg in pred_formula.args
                )
            )
        ]

        formula = state.constraint
        for predicate_formula in predicate_formulas:
            instantiation = language.SMTFormula(
                z3.BoolVal(predicate_formula.evaluate(state.tree))
            )
            self.logger.debug(
                "Eliminating (-> %s) structural predicate formula %s",
                instantiation,
                predicate_formula,
            )
            formula = language.replace_formula(
                formula, predicate_formula, instantiation
            )

        return SolutionState(formula, state.tree)

    def eliminate_existential_integer_quantifiers(
        self, state: SolutionState
    ) -> Maybe[List[SolutionState]]:
        existential_int_formulas = [
            conjunct
            for conjunct in get_conjuncts(state.constraint)
            if isinstance(conjunct, language.ExistsIntFormula)
        ]

        if not existential_int_formulas:
            return Nothing

        formula = state.constraint
        for existential_int_formula in existential_int_formulas:
            # The following check for validity is not only a performance measure, but required
            # when existential integer formulas are re-inserted. Otherwise, new constants get
            # introduced, and the solver won't terminate.
            if evaluate(
                existential_int_formula,
                state.tree,
                self.grammar,
                assumptions={
                    f
                    for f in split_conjunction(state.constraint)
                    if f != existential_int_formula
                },
            ).is_true():
                self.logger.debug(
                    "Removing existential integer quantifier '%.30s', already implied "
                    "by tree and existing constraints",
                    existential_int_formula,
                )
                # This should simplify the process after quantifier re-insertion.
                return Some(
                    [
                        SolutionState(
                            language.replace_formula(
                                state.constraint, existential_int_formula, sc.true()
                            ),
                            state.tree,
                        )
                    ]
                )

            self.logger.debug(
                "Eliminating existential integer quantifier %s", existential_int_formula
            )
            used_vars = set(VariablesCollector.collect(formula))
            fresh = language.fresh_constant(
                used_vars,
                language.Constant(
                    existential_int_formula.bound_variable.name,
                    existential_int_formula.bound_variable.n_type,
                ),
            )
            instantiation = existential_int_formula.inner_formula.substitute_variables(
                {existential_int_formula.bound_variable: fresh}
            )
            formula = language.replace_formula(
                formula, existential_int_formula, instantiation
            )

        return Some([SolutionState(formula, state.tree)])

    def instantiate_universal_integer_quantifiers(
        self, state: SolutionState
    ) -> Maybe[List[SolutionState]]:
        universal_int_formulas = [
            conjunct
            for conjunct in get_conjuncts(state.constraint)
            if isinstance(conjunct, language.ForallIntFormula)
        ]

        if not universal_int_formulas:
            return Nothing

        results: List[SolutionState] = [state]
        for universal_int_formula in universal_int_formulas:
            results = [
                result
                for formula_list in [
                    self.instantiate_universal_integer_quantifier(
                        previous_result, universal_int_formula
                    )
                    for previous_result in results
                ]
                for result in formula_list
            ]

        return Some(results)

    def instantiate_universal_integer_quantifier(
        self, state: SolutionState, universal_int_formula: language.ForallIntFormula
    ) -> List[SolutionState]:
        results = self.instantiate_universal_integer_quantifier_by_enumeration(
            state, universal_int_formula
        )

        if results:
            return results

        return self.instantiate_universal_integer_quantifier_by_transformation(
            state, universal_int_formula
        )

    def instantiate_universal_integer_quantifier_by_transformation(
        self, state: SolutionState, universal_int_formula: language.ForallIntFormula
    ) -> List[SolutionState]:
        # If the enumeration approach was not successful, we con transform the universal int
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

        if (
            isinstance(universal_int_formula.inner_formula, language.ExistsFormula)
            and isinstance(
                universal_int_formula.inner_formula.inner_formula,
                language.NegatedFormula,
            )
            and isinstance(
                universal_int_formula.inner_formula.inner_formula.args[0],
                language.SemanticPredicateFormula,
            )
            and cast(
                language.SemanticPredicateFormula,
                universal_int_formula.inner_formula.inner_formula.args[0],
            ).predicate
            in self.predicates_unique_in_int_arg
        ):
            inner_formula: language.ExistsFormula = universal_int_formula.inner_formula
            predicate_formula: language.SemanticPredicateFormula = cast(
                language.SemanticPredicateFormula,
                cast(language.NegatedFormula, inner_formula.inner_formula).args[0],
            )

            fresh_var = language.fresh_bound_variable(
                language.VariablesCollector().collect(state.constraint),
                inner_formula.bound_variable,
                add=False,
            )

            new_formula = language.ExistsIntFormula(
                universal_int_formula.bound_variable,
                language.ExistsFormula(
                    fresh_var,
                    inner_formula.in_variable,
                    predicate_formula.substitute_variables(
                        {inner_formula.bound_variable: fresh_var}
                    ),
                )
                & inner_formula,
            )

            self.logger.debug(
                "Transforming universal integer quantifier "
                "(special case, see code comments for explanation):\n%s ==> %s",
                universal_int_formula,
                new_formula,
            )

            return [
                SolutionState(
                    language.replace_formula(
                        state.constraint, universal_int_formula, new_formula
                    ),
                    state.tree,
                )
            ]

        self.logger.warning(
            "Did not find a way to instantiate formula %s!\n"
            + "Discarding this state. Please report this to your nearest ISLa developer.",
            universal_int_formula,
        )

        return []

    def instantiate_universal_integer_quantifier_by_enumeration(
        self, state: SolutionState, universal_int_formula: ForallIntFormula
    ) -> Optional[List[SolutionState]]:
        constant = language.Constant(
            universal_int_formula.bound_variable.name,
            universal_int_formula.bound_variable.n_type,
        )

        # noinspection PyTypeChecker
        inner_formula = universal_int_formula.inner_formula.substitute_variables(
            {universal_int_formula.bound_variable: constant}
        )

        instantiations: List[
            Dict[
                language.Constant | DerivationTree,
                int | language.Constant | DerivationTree,
            ]
        ] = []

        if isinstance(universal_int_formula.inner_formula, language.DisjunctiveFormula):
            # In the disjunctive case, we attempt to falsify all SMT formulas in the inner formula
            # (on top level) that contain the bound variable as argument.
            smt_disjuncts = [
                formula
                for formula in language.split_disjunction(inner_formula)
                if isinstance(formula, language.SMTFormula)
                and constant in formula.free_variables()
            ]

            if smt_disjuncts and len(smt_disjuncts) < len(
                language.split_disjunction(inner_formula)
            ):
                instantiation_values = (
                    self.infer_satisfying_assignments_for_smt_formula(
                        -reduce(language.SMTFormula.disjunction, smt_disjuncts),
                        constant,
                    )
                )

                # We also try to falsify (negated) semantic predicate formulas, if present,
                # if there exist any remaining disjuncts.
                semantic_predicate_formulas: List[
                    Tuple[language.SemanticPredicateFormula, bool]
                ] = [
                    (pred_formula, False)
                    if isinstance(pred_formula, language.SemanticPredicateFormula)
                    else (cast(language.NegatedFormula, pred_formula).args[0], True)
                    for pred_formula in language.FilterVisitor(
                        lambda f: (
                            constant in f.free_variables()
                            and (
                                isinstance(f, language.SemanticPredicateFormula)
                                or isinstance(f, language.NegatedFormula)
                                and isinstance(
                                    f.args[0], language.SemanticPredicateFormula
                                )
                            )
                        ),
                        do_continue=lambda f: isinstance(
                            f, language.DisjunctiveFormula
                        ),
                    ).collect(inner_formula)
                    if all(
                        not isinstance(var, language.BoundVariable)
                        for var in pred_formula.free_variables()
                    )
                ]

                if semantic_predicate_formulas and len(
                    semantic_predicate_formulas
                ) + len(smt_disjuncts) < len(language.split_disjunction(inner_formula)):
                    for value in instantiation_values:
                        instantiation: Dict[
                            language.Constant | DerivationTree,
                            int | language.Constant | DerivationTree,
                        ] = {constant: value}
                        for (
                            semantic_predicate_formula,
                            negated,
                        ) in semantic_predicate_formulas:
                            eval_result = cast(
                                language.SemanticPredicateFormula,
                                language.substitute(
                                    semantic_predicate_formula, {constant: value}
                                ),
                            ).evaluate(self.graph, negate=not negated)
                            if eval_result.ready() and not eval_result.is_boolean():
                                instantiation.update(eval_result.result)
                        instantiations.append(instantiation)
                else:
                    instantiations.extend(
                        [{constant: value} for value in instantiation_values]
                    )

        results: List[SolutionState] = []
        for instantiation in instantiations:
            self.logger.debug(
                "Instantiating universal integer quantifier (%s -> %s) %s",
                universal_int_formula.bound_variable,
                instantiation[constant],
                universal_int_formula,
            )

            formula = language.replace_formula(
                state.constraint,
                universal_int_formula,
                language.substitute(inner_formula, instantiation),
            )
            formula = language.substitute(formula, instantiation)

            tree = state.tree.substitute(
                {
                    tree: subst
                    for tree, subst in instantiation.items()
                    if isinstance(tree, DerivationTree)
                }
            )

            results.append(SolutionState(formula, tree))

        return results

    def infer_satisfying_assignments_for_smt_formula(
        self, smt_formula: language.SMTFormula, constant: language.Constant
    ) -> Set[int | language.Constant]:
        """
        This method returns `self.max_number_free_instantiations` many solutions for
        the given :class:`~isla.language.SMTFormula` if `constant` is the only free
        variable in `smt_formula`. The given formula must be a numeric formula, i.e.,
        all free variables must be numeric. If more than one free variables are
        present, at most one solution is returned (see example below).

        :param smt_formula: The :class:`~isla.language.SMTFormula` to solve. Must
          only contain numeric free variables.
        :param constant: One free variable in `smt_formula`.
        :return: A set of solutions (see explanation above & comment below).

        We create a solver with a dummy grammar (it's not needed for this example),
        choosing a value of 5 for `max_number_free_instantiations`.

        >>> solver = ISLaSolver(
        ...     '<start> ::= "x"',  # dummy grammar
        ...     max_number_free_instantiations=5,
        ... )

        The formula we're considering is `x > 10`.

        >>> from isla.language import Constant, SMTFormula, Variable, unparse_isla
        >>> x = Constant("x", Variable.NUMERIC_NTYPE)

        >>> formula = SMTFormula(z3.StrToInt(x.to_smt()) > z3.IntVal(10), x)
        >>> unparse_isla(formula)
        '(< 10 (str.to.int x))'

        We obtain five results (due to our choice of `max_number_free_instantiations`).

        >>> results = solver.infer_satisfying_assignments_for_smt_formula(formula, x)
        >>> len(results)
        5

        All results are `int`s...

        >>> all(isinstance(result, int) for result in results)
        True

        ...and all are strictly greater than 10.

        >>> all(result > 10 for result in results)
        True

        Now, lets consider `x == y`. This formula contains *two* free variables, `x`
        and `y`. It is the only type of formula with more than one variable for which
        this method will return a solution in the current state.

        >>> y = Constant("y", Variable.NUMERIC_NTYPE)
        >>> formula = SMTFormula(
        ...     z3_eq(z3.StrToInt(x.to_smt()), z3.StrToInt(y.to_smt())), x, y)
        >>> unparse_isla(formula)
        '(= (str.to.int x) (str.to.int y))'

        The solution is the singleton set with the variable `y`, which is an
        instantiation of the constant `x` solving the equation.

        >>> solver.infer_satisfying_assignments_for_smt_formula(formula, x)
        {Constant("y", "NUM")}

        If we choose a different type of formula (a greater-than relation), we obtain
        an empty solution set.

        >>> formula = SMTFormula(
        ...     z3.StrToInt(x.to_smt()) > z3.StrToInt(y.to_smt()), x, y)
        >>> unparse_isla(formula)
        '(> (str.to.int x) (str.to.int y))'
        >>> solver.infer_satisfying_assignments_for_smt_formula(formula, x)
        set()

        With a non-numeric formula, we obtain an AssertionError (if assertions are
        enabled). This method expects to be called only internally, so this should
        not happen (with or without activated assertions).

        >>> z = Constant("x", "<start>")
        >>> formula = SMTFormula(z3_eq(z.to_smt(), z3.StringVal("x")), z)
        >>> print(unparse_isla(formula))
        const x: <start>;
        <BLANKLINE>
        (= x "x")
        >>> results = solver.infer_satisfying_assignments_for_smt_formula(formula, z)
        Traceback (most recent call last):
        ...
        AssertionError: Expected numeric solution.
        """

        free_variables = smt_formula.free_variables()
        max_instantiations = (
            self.max_number_free_instantiations if len(free_variables) == 1 else 1
        )

        try:
            solver_result = self.solve_quantifier_free_formula(
                (smt_formula,), max_instantiations=max_instantiations
            )

            solutions: Dict[language.Constant, Set[int]] = {
                c: {
                    int(solution[cast(language.Constant, c)].value)
                    for solution in solver_result
                }
                for c in free_variables
            }
        except ValueError:
            assert False, "Expected numeric solution."

        if solutions:
            if len(free_variables) == 1:
                return solutions[constant]
            else:
                assert all(len(solution) == 1 for solution in solutions.values())
                # In situations with multiple variables, we might have to abstract from
                # concrete values. Currently, we only support simple equality inference
                # (based on one sample...). Note that for supporting *more complex*
                # terms (e.g., additions), we would have to extend the whole
                # infrastructure: Substitutions with complex terms, and complex terms
                # in semantic predicate arguments, are unsupported as of now.
                candidates = {
                    c
                    for c in solutions
                    if c != constant
                    and next(iter(solutions[c])) == next(iter(solutions[constant]))
                }

                # Filter working candidates
                return {
                    c
                    for c in candidates
                    if self.solve_quantifier_free_formula(
                        (
                            cast(
                                language.SMTFormula,
                                smt_formula.substitute_variables({constant: c}),
                            ),
                        ),
                        max_instantiations=1,
                    )
                }

    def eliminate_all_semantic_formulas(
        self, state: SolutionState, max_instantiations: Optional[int] = None
    ) -> Maybe[List[SolutionState]]:
        """
        Eliminates all SMT-LIB formulas that appear in `state`'s constraint as conjunctive elements.
        If, e.g., an SMT-LIB formula occurs as a disjunction, no solution is computed.

        :param state: The state in which to solve all SMT-LIB formulas.
        :param max_instantiations: The number of solutions the SMT solver should be asked for.
        :return: The discovered solutions.
        """

        conjuncts = split_conjunction(state.constraint)
        semantic_formulas = [
            conjunct
            for conjunct in conjuncts
            if isinstance(conjunct, language.SMTFormula)
            and not z3.is_true(conjunct.formula)
        ]

        if not semantic_formulas:
            return Nothing

        self.logger.debug(
            "Eliminating semantic formulas [%s]", lazyjoin(", ", semantic_formulas)
        )

        prefix_conjunction = reduce(lambda a, b: a & b, semantic_formulas, sc.true())
        new_disjunct = prefix_conjunction & reduce(
            lambda a, b: a & b,
            [conjunct for conjunct in conjuncts if conjunct not in semantic_formulas],
            sc.true(),
        )

        return Some(
            self.eliminate_semantic_formula(
                prefix_conjunction,
                SolutionState(new_disjunct, state.tree),
                max_instantiations,
            )
        )

    def eliminate_all_ready_semantic_predicate_formulas(
        self, state: SolutionState
    ) -> Maybe[List[SolutionState]]:
        semantic_predicate_formulas: List[
            language.NegatedFormula | language.SemanticPredicateFormula
        ] = [
            cast(
                language.NegatedFormula | language.SemanticPredicateFormula,
                pred_formula,
            )
            for pred_formula in language.FilterVisitor(
                lambda f: (
                    isinstance(f, language.SemanticPredicateFormula)
                    or isinstance(f, language.NegatedFormula)
                    and isinstance(f.args[0], language.SemanticPredicateFormula)
                ),
                do_continue=lambda f: (
                    not isinstance(f, language.NegatedFormula)
                    or not isinstance(f.args[0], language.SemanticPredicateFormula)
                ),
            ).collect(state.constraint)
            if all(
                not isinstance(var, language.BoundVariable)
                for var in pred_formula.free_variables()
            )
        ]

        semantic_predicate_formulas = sorted(
            semantic_predicate_formulas,
            key=lambda f: (
                2 * cast(language.SemanticPredicateFormula, f.args[0]).predicate.order
                + 100
                if isinstance(f, language.NegatedFormula)
                else f.predicate.order
            ),
        )

        if not semantic_predicate_formulas:
            return Nothing

        result = state

        changed = False
        for idx, possibly_negated_semantic_predicate_formula in enumerate(
            semantic_predicate_formulas
        ):
            negated = isinstance(
                possibly_negated_semantic_predicate_formula, language.NegatedFormula
            )
            semantic_predicate_formula: language.SemanticPredicateFormula = (
                cast(
                    language.NegatedFormula, possibly_negated_semantic_predicate_formula
                ).args[0]
                if negated
                else possibly_negated_semantic_predicate_formula
            )

            evaluation_result = semantic_predicate_formula.evaluate(
                self.graph, negate=negated
            )
            if not evaluation_result.ready():
                continue

            self.logger.debug(
                "Eliminating semantic predicate formula %s", semantic_predicate_formula
            )
            changed = True

            if evaluation_result.is_boolean():
                result = SolutionState(
                    language.replace_formula(
                        result.constraint,
                        semantic_predicate_formula,
                        language.smt_atom(evaluation_result.true()),
                    ),
                    result.tree,
                )
                continue

            substitution = subtree_solutions(evaluation_result.result)

            new_constraint = language.replace_formula(
                result.constraint,
                semantic_predicate_formula,
                sc.false() if negated else sc.true(),
            ).substitute_expressions(substitution)

            for k in range(idx + 1, len(semantic_predicate_formulas)):
                semantic_predicate_formulas[k] = cast(
                    language.SemanticPredicateFormula,
                    semantic_predicate_formulas[k].substitute_expressions(substitution),
                )

            result = SolutionState(new_constraint, result.tree.substitute(substitution))
            assert self.graph.tree_is_valid(result.tree)

        return Maybe.from_optional([result] if changed else None)

    def eliminate_and_match_first_existential_formula(
        self, state: SolutionState
    ) -> Optional[List[SolutionState]]:
        # We produce up to two groups of output states: One where the first existential
        # formula, if it can be matched, is matched, and one where the first existential
        # formula is eliminated by tree insertion.

        def do_eliminate(
            first_existential_formula_with_idx: Tuple[int, language.ExistsFormula]
        ) -> List[SolutionState]:
            first_matched = OrderedSet(
                self.match_existential_formula(
                    first_existential_formula_with_idx[0], state
                )
            )

            # Tree insertion can be deactivated by setting `self.tree_insertion_methods`
            # to 0.
            if not self.tree_insertion_methods:
                return list(first_matched)

            if first_matched:
                self.logger.debug(
                    "Matched first existential formulas, result: [%s]",
                    lazyjoin(
                        ", ",
                        [
                            lazystr(lambda: f"{s} (hash={hash(s)})")
                            for s in first_matched
                        ],
                    ),
                )

            # 3. Eliminate first existential formula by tree insertion.
            elimination_result = OrderedSet(
                self.eliminate_existential_formula(
                    first_existential_formula_with_idx[0], state
                )
            )
            elimination_result = OrderedSet(
                [
                    result
                    for result in elimination_result
                    if not any(
                        other_result.tree == result.tree
                        and self.propositionally_unsatisfiable(
                            result.constraint & -other_result.constraint
                        )
                        for other_result in first_matched
                    )
                ]
            )

            if not elimination_result and not first_matched:
                self.logger.warning(
                    "Existential qfr elimination: Could not eliminate existential formula %s "
                    "by matching or tree insertion",
                    first_existential_formula_with_idx[1],
                )

            if elimination_result:
                self.logger.debug(
                    "Eliminated existential formula %s by tree insertion, %d successors",
                    first_existential_formula_with_idx[1],
                    len(elimination_result),
                )

            return [
                result
                for result in first_matched | elimination_result
                if result != state
            ]

        return (
            result_to_maybe(
                safe(
                    lambda: next(
                        (idx, conjunct)
                        for idx, conjunct in enumerate(
                            split_conjunction(state.constraint)
                        )
                        if isinstance(conjunct, language.ExistsFormula)
                    )
                )()
            )
            .map(do_eliminate)
            .value_or(None)
        )

    def match_all_universal_formulas(
        self, state: SolutionState
    ) -> Maybe[List[SolutionState]]:
        universal_formulas = [
            conjunct
            for conjunct in split_conjunction(state.constraint)
            if isinstance(conjunct, language.ForallFormula)
        ]

        if not universal_formulas:
            return Nothing

        result = self.match_universal_formulas(state)
        if not result:
            return Nothing

        self.logger.debug(
            "Matched universal formulas [%s]", lazyjoin(", ", universal_formulas)
        )

        return Some(result)

    def expand_tree(
        self,
        state: SolutionState,
        only_universal: bool = True,
        limit: Optional[int] = None,
    ) -> List[SolutionState]:
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
                [
                    DerivationTree(child, None if is_nonterminal(child) else [])
                    for child in expansion
                ]
                for expansion in self.canonical_grammar[leaf_node.value]
            ]
            for leaf_path, leaf_node in state.tree.open_leaves()
            if any(
                self.quantified_formula_might_match(formula, leaf_path, state.tree)
                for formula in get_conjuncts(state.constraint)
                if (only_universal and isinstance(formula, language.ForallFormula))
                or (
                    not only_universal
                    and isinstance(formula, language.QuantifiedFormula)
                )
            )
        }

        if not nonterminal_expansions:
            return []

        possible_expansions: List[Dict[Path, List[DerivationTree]]] = []
        if not limit:
            possible_expansions = dict_of_lists_to_list_of_dicts(nonterminal_expansions)
            assert len(possible_expansions) == math.prod(
                len(values) for values in nonterminal_expansions.values()
            )
        else:
            for _ in range(limit):
                curr_expansion = {}
                for path, expansions in nonterminal_expansions.items():
                    if not expansions:
                        continue

                    curr_expansion[path] = random.choice(expansions)
                possible_expansions.append(curr_expansion)

        # This replaces a previous `if` statement with the negated condition as guard,
        # which seems to be dead code (the guard can never hold true due to the check
        # of emptiness of `nonterminal_expansions` above). We keep this assertion here
        # to be sure.
        assert (
            len(possible_expansions) > 1
            or len(possible_expansions) == 1
            and possible_expansions[0]
        )

        result: List[SolutionState] = []
        for possible_expansion in possible_expansions:
            expanded_tree = state.tree
            for path, new_children in possible_expansion.items():
                leaf_node = expanded_tree.get_subtree(path)
                expanded_tree = expanded_tree.replace_path(
                    path, DerivationTree(leaf_node.value, new_children, leaf_node.id)
                )

                assert expanded_tree is not state.tree
                assert expanded_tree != state.tree
                assert expanded_tree.structural_hash() != state.tree.structural_hash()

            updated_constraint = state.constraint.substitute_expressions(
                {
                    state.tree.get_subtree(path[:idx]): expanded_tree.get_subtree(
                        path[:idx]
                    )
                    for path in possible_expansion
                    for idx in range(len(path) + 1)
                }
            )

            result.append(SolutionState(updated_constraint, expanded_tree))

        assert not limit or len(result) <= limit
        return result

    def match_universal_formulas(self, state: SolutionState) -> List[SolutionState]:
        instantiated_formulas: List[language.Formula] = []
        conjuncts = split_conjunction(state.constraint)

        for idx, universal_formula in enumerate(conjuncts):
            if not isinstance(universal_formula, language.ForallFormula):
                continue

            matches: List[Dict[language.Variable, Tuple[Path, DerivationTree]]] = [
                match
                for match in matches_for_quantified_formula(
                    universal_formula, self.grammar
                )
                if not universal_formula.is_already_matched(
                    match[universal_formula.bound_variable][1]
                )
            ]

            universal_formula_with_matches = universal_formula.add_already_matched(
                {match[universal_formula.bound_variable][1] for match in matches}
            )

            for match in matches:
                inst_formula = (
                    universal_formula_with_matches.inner_formula.substitute_expressions(
                        {
                            variable: match_tree
                            for variable, (_, match_tree) in match.items()
                        }
                    )
                )

                instantiated_formulas.append(inst_formula)
                conjuncts[idx] = universal_formula_with_matches

        if instantiated_formulas:
            return [
                SolutionState(
                    sc.conjunction(*instantiated_formulas) & sc.conjunction(*conjuncts),
                    state.tree,
                )
            ]
        else:
            return []

    def match_existential_formula(
        self, existential_formula_idx: int, state: SolutionState
    ) -> List[SolutionState]:
        result: List[SolutionState] = []

        conjuncts: ImmutableList[language.Formula] = tuple(
            split_conjunction(state.constraint)
        )
        existential_formula = cast(
            language.ExistsFormula, conjuncts[existential_formula_idx]
        )

        matches: List[
            Dict[language.Variable, Tuple[Path, DerivationTree]]
        ] = matches_for_quantified_formula(existential_formula, self.grammar)

        for match in matches:
            inst_formula = existential_formula.inner_formula.substitute_expressions(
                {variable: match_tree for variable, (_, match_tree) in match.items()}
            )
            constraint = inst_formula & sc.conjunction(
                *list_del(conjuncts, existential_formula_idx)
            )
            result.append(SolutionState(constraint, state.tree))

        return result

    def eliminate_existential_formula(
        self, existential_formula_idx: int, state: SolutionState
    ) -> List[SolutionState]:
        conjuncts: ImmutableList[language.Formula] = tuple(
            split_conjunction(state.constraint)
        )
        existential_formula = cast(
            language.ExistsFormula, conjuncts[existential_formula_idx]
        )

        inserted_trees_and_bind_paths = (
            [(DerivationTree(existential_formula.bound_variable.n_type, None), {})]
            if existential_formula.bind_expression is None
            else (
                existential_formula.bind_expression.to_tree_prefix(
                    existential_formula.bound_variable.n_type, self.grammar
                )
            )
        )

        result: List[SolutionState] = []

        inserted_tree: DerivationTree
        bind_expr_paths: Dict[language.BoundVariable, Path]
        for inserted_tree, bind_expr_paths in inserted_trees_and_bind_paths:
            self.logger.debug(
                "insert_tree(self.canonical_grammar, %s, %s, self.graph, %s)",
                lazystr(lambda: repr(inserted_tree)),
                lazystr(lambda: repr(existential_formula.in_variable)),
                self.max_number_tree_insertion_results,
            )

            insertion_results = insert_tree(
                self.canonical_grammar,
                inserted_tree,
                existential_formula.in_variable,
                graph=self.graph,
                max_num_solutions=self.max_number_tree_insertion_results * 2,
                methods=self.tree_insertion_methods,
            )

            insertion_results = sorted(
                insertion_results,
                key=lambda t: compute_tree_closing_cost(t, self.graph),
            )
            insertion_results = insertion_results[
                : self.max_number_tree_insertion_results
            ]

            for insertion_result in insertion_results:
                replaced_path = state.tree.find_node(existential_formula.in_variable)
                resulting_tree = state.tree.replace_path(
                    replaced_path, insertion_result
                )

                tree_substitution: Dict[DerivationTree, DerivationTree] = {}
                for idx in range(len(replaced_path) + 1):
                    original_path = replaced_path[: idx - 1]
                    original_tree = state.tree.get_subtree(original_path)
                    if (
                        resulting_tree.is_valid_path(original_path)
                        and original_tree.value
                        == resulting_tree.get_subtree(original_path).value
                        and resulting_tree.get_subtree(original_path) != original_tree
                    ):
                        tree_substitution[original_tree] = resulting_tree.get_subtree(
                            original_path
                        )

                assert insertion_result.find_node(inserted_tree) is not None
                variable_substitutions = {
                    existential_formula.bound_variable: inserted_tree
                }

                if bind_expr_paths:
                    if assertions_activated():
                        dangling_bind_expr_vars = [
                            (var, path)
                            for var, path in bind_expr_paths.items()
                            if (
                                var
                                in existential_formula.bind_expression.bound_variables()
                                and insertion_result.find_node(
                                    inserted_tree.get_subtree(path)
                                )
                                is None
                            )
                        ]
                        assert not dangling_bind_expr_vars, (
                            f"Bound variables from match expression not found in tree: "
                            f"[{' ,'.join(map(repr, dangling_bind_expr_vars))}]"
                        )

                    variable_substitutions.update(
                        {
                            var: inserted_tree.get_subtree(path)
                            for var, path in bind_expr_paths.items()
                            if var
                            in existential_formula.bind_expression.bound_variables()
                        }
                    )

                instantiated_formula = (
                    existential_formula.inner_formula.substitute_expressions(
                        variable_substitutions
                    ).substitute_expressions(tree_substitution)
                )

                instantiated_original_constraint = sc.conjunction(
                    *list_del(conjuncts, existential_formula_idx)
                ).substitute_expressions(tree_substitution)

                new_tree = resulting_tree.substitute(tree_substitution)

                new_formula = (
                    instantiated_formula
                    & self.formula.substitute_expressions(
                        {self.top_constant.unwrap(): new_tree}
                    )
                    & instantiated_original_constraint
                )

                new_state = SolutionState(new_formula, new_tree)

                assert all(
                    new_state.tree.find_node(tree) is not None
                    for quantified_formula in split_conjunction(new_state.constraint)
                    if isinstance(quantified_formula, language.QuantifiedFormula)
                    for _, tree in quantified_formula.in_variable.filter(lambda t: True)
                )

                if assertions_activated() or self.debug:
                    lost_tree_predicate_arguments: List[DerivationTree] = [
                        arg
                        for invstate in self.establish_invariant(new_state)
                        for predicate_formula in get_conjuncts(invstate.constraint)
                        if isinstance(
                            predicate_formula, language.StructuralPredicateFormula
                        )
                        for arg in predicate_formula.args
                        if isinstance(arg, DerivationTree)
                        and invstate.tree.find_node(arg) is None
                    ]

                    if lost_tree_predicate_arguments:
                        previous_posititions = [
                            state.tree.find_node(t)
                            for t in lost_tree_predicate_arguments
                        ]
                        assert False, (
                            f"Dangling subtrees [{', '.join(map(repr, lost_tree_predicate_arguments))}], "
                            f"previously at positions [{', '.join(map(str, previous_posititions))}] "
                            f"in tree {repr(state.tree)} (hash: {hash(state)})."
                        )

                    lost_semantic_formula_arguments = [
                        arg
                        for invstate in self.establish_invariant(new_state)
                        for semantic_formula in get_conjuncts(new_state.constraint)
                        if isinstance(semantic_formula, language.SMTFormula)
                        for arg in semantic_formula.substitutions.values()
                        if invstate.tree.find_node(arg) is None
                    ]

                    if lost_semantic_formula_arguments:
                        previous_posititions = [
                            state.tree.find_node(t)
                            for t in lost_semantic_formula_arguments
                        ]
                        previous_posititions = [
                            p for p in previous_posititions if p is not None
                        ]
                        assert False, (
                            f"Dangling subtrees [{', '.join(map(repr, lost_semantic_formula_arguments))}], "
                            f"previously at positions [{', '.join(map(str, previous_posititions))}] "
                            f"in tree {repr(state.tree)} (hash: {hash(state)})."
                        )

                result.append(new_state)

        return result

    def eliminate_semantic_formula(
        self,
        semantic_formula: language.Formula,
        state: SolutionState,
        max_instantiations: Optional[int] = None,
    ) -> Optional[List[SolutionState]]:
        """
        Solves a semantic formula and, for each solution, substitutes the solution for
        the respective constant in each assignment of the state. Also instantiates all
        "free" constants in the given tree. The SMT solver is passed a regular
        expression approximating the language of the nonterminal of each considered
        constant. Returns an empty list for unsolvable constraints.

        :param semantic_formula: The semantic (i.e., only containing logical connectors and SMT Formulas)
        formula to solve.
        :param state: The original solution state.
        :param max_instantiations: The maximum number of solutions to ask the SMT solver for.
        :return: A list of instantiated SolutionStates.
        """

        assert all(
            isinstance(conjunct, language.SMTFormula)
            for conjunct in get_conjuncts(semantic_formula)
        )

        # NOTE: We need to cluster SMT formulas by tree substitutions. If there are two
        # formulas with a variable $var which is instantiated to different trees, we
        # need two separate solutions. If, however, $var is instantiated with the
        # *same* tree, we need one solution to both formulas together.

        smt_formulas = self.rename_instantiated_variables_in_smt_formulas(
            [
                smt_formula
                for smt_formula in get_conjuncts(semantic_formula)
                if isinstance(smt_formula, language.SMTFormula)
            ]
        )

        # Now, we also cluster formulas by common variables (and instantiated subtrees:
        # One formula might yield an instantiation of a subtree of the instantiation of
        # another formula. They need to appear in the same cluster). The solver can
        # better handle smaller constraints, and those which do not have variables in
        # common can be handled independently.

        def cluster_keys(smt_formula: language.SMTFormula):
            return (
                smt_formula.free_variables()
                | smt_formula.instantiated_variables
                | set(
                    [
                        subtree
                        for tree in smt_formula.substitutions.values()
                        for _, subtree in tree.paths()
                    ]
                )
            )

        formula_clusters: List[List[language.SMTFormula]] = cluster_by_common_elements(
            smt_formulas, cluster_keys
        )

        assert all(
            not cluster_keys(smt_formula)
            or any(smt_formula in cluster for cluster in formula_clusters)
            for smt_formula in smt_formulas
        )

        formula_clusters = [cluster for cluster in formula_clusters if cluster]
        remaining_clusters = [
            smt_formula for smt_formula in smt_formulas if not cluster_keys(smt_formula)
        ]
        if remaining_clusters:
            formula_clusters.append(remaining_clusters)

        # Note: We cannot ask for `max_instantiations` solutions for *each cluster;*
        #       this would imply that we get 10^4 solutions if `max_instantiations`
        #       is 10 and we have 4 clusters (we combine all these solutions to a
        #       product). Instead, we want 10 solutions; thus, we compute the
        #       #numCluster'th root of `max_instantiations` and ceil.
        #       For example, the ceil of the 4-root of 10 is 2, and 2^10 is 16. This
        #       is still within an acceptable range.

        solutions_per_cluster = math.ceil(
            (max_instantiations or self.max_number_smt_instantiations)
            ** (1 / len(formula_clusters))
        )

        all_solutions: List[
            List[Dict[Union[language.Constant, DerivationTree], DerivationTree]]
        ] = [
            self.solve_quantifier_free_formula(
                tuple(cluster),
                solutions_per_cluster,
            )
            for cluster in formula_clusters
        ]

        # These solutions are all independent, such that we can combine each solution
        # with all others.
        solutions: List[
            Dict[Union[language.Constant, DerivationTree], DerivationTree]
        ] = [
            functools.reduce(operator.or_, dicts)
            for dicts in itertools.product(*all_solutions)
        ]

        results = []
        # We also have to instantiate all subtrees of the substituted element.
        for solution in map(subtree_solutions, solutions):
            if solution:
                new_state = SolutionState(
                    state.constraint.substitute_expressions(solution),
                    state.tree.substitute(solution),
                )
            else:
                new_state = SolutionState(
                    language.replace_formula(
                        state.constraint, semantic_formula, sc.true()
                    ),
                    state.tree,
                )

            results.append(new_state)

        return results

    @lru_cache(100)
    def solve_quantifier_free_formula(
        self,
        smt_formulas: ImmutableList[language.SMTFormula],
        max_instantiations: Optional[int] = None,
    ) -> List[Dict[language.Constant | DerivationTree, DerivationTree]]:
        """
        Attempts to solve the given SMT-LIB formulas by calling Z3.

        Note that this function does not unify variables pointing to the same derivation
        trees. E.g., a solution may be returned for the formula `var_1 = "a" and
        var_2 = "b"`, though `var_1` and `var_2` point to the same `<var>` tree as
        defined by their substitutions maps. Unification is performed in
        `eliminate_all_semantic_formulas`.

        :param smt_formulas: The SMT-LIB formulas to solve.
        :param max_instantiations: The maximum number of instantiations to produce.
        :return: A (possibly empty) list of solutions.
        """

        # If any SMT formula refers to *sub*trees in the instantiations of other SMT
        # formulas, we have to instantiate those first.
        priority_formulas = smt_formulas_referring_to_subtrees(smt_formulas)

        if priority_formulas:
            smt_formulas = priority_formulas
            assert not smt_formulas_referring_to_subtrees(smt_formulas)

        tree_substitutions = reduce(
            lambda d1, d2: d1 | d2,
            [smt_formula.substitutions for smt_formula in smt_formulas],
            {},
        )

        constants = reduce(
            lambda d1, d2: d1 | d2,
            [
                smt_formula.free_variables() | smt_formula.instantiated_variables
                for smt_formula in smt_formulas
            ],
            set(),
        )

        solutions: List[
            Dict[Union[language.Constant, DerivationTree], DerivationTree]
        ] = []
        internal_solutions: List[Dict[language.Constant, z3.StringVal]] = []

        num_instantiations = max_instantiations or self.max_number_smt_instantiations
        for _ in range(num_instantiations):
            (
                solver_result,
                maybe_model,
            ) = self.solve_smt_formulas_with_language_constraints(
                constants,
                tuple([smt_formula.formula for smt_formula in smt_formulas]),
                tree_substitutions,
                internal_solutions,
            )

            if solver_result != z3.sat:
                if not solutions:
                    return []
                else:
                    return solutions

            assert maybe_model is not None

            new_solution = {
                tree_substitutions.get(constant, constant): maybe_model[constant]
                for constant in constants
            }

            new_internal_solution = {
                constant: z3.StringVal(str(maybe_model[constant]))
                for constant in constants
            }

            if new_solution in solutions:
                # This can happen for trivial solutions, i.e., if the formula is
                # logically valid. Then, the assignment for that constant will
                # always be {}
                return solutions
            else:
                solutions.append(new_solution)
                if new_internal_solution:
                    internal_solutions.append(new_internal_solution)
                else:
                    # Again, for a trivial solution (e.g., True), the assignment
                    # can be empty.
                    break

        return solutions

    def solve_smt_formulas_with_language_constraints(
        self,
        variables: Set[language.Variable],
        smt_formulas: ImmutableList[z3.BoolRef],
        tree_substitutions: Dict[language.Variable, DerivationTree],
        solutions_to_exclude: List[Dict[language.Variable, z3.StringVal]],
    ) -> Tuple[z3.CheckSatResult, Dict[language.Variable, DerivationTree]]:
        # We disable optimized Z3 queries if the SMT formulas contain "too concrete"
        # substitutions, that is, substitutions with a tree that is not merely an
        # open leaf. Example: we have a constrained `str.len(<chars>) < 10` and a
        # tree `<char><char>`; only the concrete length "10" is possible then. In fact,
        # we could simply finish of the tree and check the constraint, or restrict the
        # custom tree generation to admissible lengths, but we stay general here. The
        # SMT solution is more robust.

        if self.enable_optimized_z3_queries and not any(
            substitution.children for substitution in tree_substitutions.values()
        ):
            vars_in_context = self.infer_variable_contexts(variables, smt_formulas)
            length_vars = vars_in_context["length"]
            int_vars = vars_in_context["int"]
            flexible_vars = vars_in_context["flexible"]
        else:
            length_vars = set()
            int_vars = set()
            flexible_vars = set(variables)

        # Add language constraints for "flexible" variables
        formulas: List[z3.BoolRef] = self.generate_language_constraints(
            flexible_vars, tree_substitutions
        )

        # Create fresh variables for `str.len` and `str.to.int` variables.
        all_variables = set(variables)
        fresh_var_map: Dict[language.Variable, z3.ExprRef] = {}
        for var in length_vars | int_vars:
            fresh = fresh_constant(
                all_variables,
                language.Constant(var.name, "NOT-NEEDED"),
            )
            fresh_var_map[var] = z3.Int(fresh.name)

        # In `smt_formulas`, we replace all `length(...)` terms for "length variables"
        # with the corresponding fresh variable.
        replacement_map: Dict[z3.ExprRef, z3.ExprRef] = {
            expr: fresh_var_map[
                get_elem_by_equivalence(
                    expr.children()[0],
                    length_vars | int_vars,
                    lambda e1, e2: e1 == e2.to_smt(),
                )
            ]
            for formula in smt_formulas
            for expr in visit_z3_expr(formula)
            if expr.decl().kind() in {z3.Z3_OP_SEQ_LENGTH, z3.Z3_OP_STR_TO_INT}
            and expr.children()[0] in {var.to_smt() for var in length_vars | int_vars}
        }

        # Perform substitution, add formulas
        formulas.extend(
            [
                cast(z3.BoolRef, z3_subst(formula, replacement_map))
                for formula in smt_formulas
            ]
        )

        # Lengths must be positive
        formulas.extend(
            [
                cast(
                    z3.BoolRef,
                    replacement_map[z3.Length(length_var.to_smt())] >= z3.IntVal(0),
                )
                for length_var in length_vars
            ]
        )

        # Add custom intervals for int variables
        for int_var in int_vars:
            if int_var.n_type == language.Variable.NUMERIC_NTYPE:
                # "NUM" variables range over the full int domain
                continue

            regex = self.extract_regular_expression(int_var.n_type)
            maybe_intervals = numeric_intervals_from_regex(regex)
            repl_var = replacement_map[z3.StrToInt(int_var.to_smt())]
            maybe_intervals.map(
                tap(
                    lambda intervals: formulas.append(
                        z3_or(
                            [
                                z3.And(
                                    repl_var >= z3.IntVal(interval[0])
                                    if interval[0] > -sys.maxsize
                                    else z3.BoolVal(True),
                                    repl_var <= z3.IntVal(interval[1])
                                    if interval[1] < sys.maxsize
                                    else z3.BoolVal(True),
                                )
                                for interval in intervals
                            ]
                        )
                    )
                )
            )

        for prev_solution in solutions_to_exclude:
            prev_solution_formula = z3_and(
                [
                    self.previous_solution_formula(
                        var, string_val, fresh_var_map, length_vars, int_vars
                    )
                    for var, string_val in prev_solution.items()
                ]
            )

            formulas.append(z3.Not(prev_solution_formula))

        sat_result, maybe_model = z3_solve(formulas)

        if sat_result != z3.sat:
            return sat_result, {}

        assert maybe_model is not None

        return sat_result, {
            var: self.extract_model_value(
                var, maybe_model, fresh_var_map, length_vars, int_vars
            )
            for var in variables
        }

    @staticmethod
    def previous_solution_formula(
        var: language.Variable,
        string_val: z3.StringVal,
        fresh_var_map: Dict[language.Variable, z3.ExprRef],
        length_vars: Set[language.Variable],
        int_vars: Set[language.Variable],
    ) -> z3.BoolRef:
        """
        Computes a formula describing the previously found solution
        :code:`var == string_val` for an :class:`~isla.language.SMTFormula`.
        Considers the special cases that :code:`var` is a "length" or "int"
        variable, i.e., occurred only in these contexts in the formula this
        solution is about.

        >>> x = language.Variable("x", "<X>")
        >>> ISLaSolver.previous_solution_formula(
        ...     x, z3.StringVal("val"), {}, set(), set())
        x == "val"

        >>> ISLaSolver.previous_solution_formula(
        ...     x, z3.StringVal("val"), {x: z3.Int("x_0")}, {x}, set())
        x_0 == 3

        >>> ISLaSolver.previous_solution_formula(
        ...     x, z3.StringVal("10"), {x: z3.Int("x_0")}, set(), {x})
        x_0 == 10

        >>> x = language.Variable("x", language.Variable.NUMERIC_NTYPE)
        >>> ISLaSolver.previous_solution_formula(
        ...     x, z3.StringVal("10"), {x: z3.Int("x_0")}, set(), {x})
        x_0 == 10

        A "numeric" variable (of "NUM" type) is expected to always be an int variable,
        which also needs to be reflected in its inclusion in :code:`fresh_var_map`.

        >>> x = language.Variable("x", language.Variable.NUMERIC_NTYPE)
        >>> ISLaSolver.previous_solution_formula(
        ...     x, z3.StringVal("10"), {}, set(), set())
        Traceback (most recent call last):
        ...
        AssertionError

        :param var: The variable the solution is for.
        :param string_val: The solution for :code:`var`.
        :param fresh_var_map: A map from variables to fresh variables for "length" or
                              "int" variables.
        :param length_vars: The "length" variables.
        :param int_vars: The "int" variables.
        :return: An equation describing the previous solution.
        """

        if var in int_vars:
            return z3_eq(
                fresh_var_map[var],
                z3.IntVal(int(smt_string_val_to_string(string_val))),
            )
        elif var in length_vars:
            return z3_eq(
                fresh_var_map[var],
                z3.IntVal(len(smt_string_val_to_string(string_val))),
            )
        else:
            assert not var.is_numeric()
            return z3_eq(var.to_smt(), string_val)

    def safe_create_fixed_length_tree(
        self,
        var: language.Variable,
        model: z3.ModelRef,
        fresh_var_map: Dict[language.Variable, z3.ExprRef],
    ) -> DerivationTree:
        """
        Creates a :class:`~isla.derivation_tree.DerivationTree` for :code:`var` such
        that the type of the tree fits to :code:`var` and the length of its string
        representation fits to the length in :code:`model` for the fresh variable in
        :code:`fresh_var_map`. For example:

        >>> grammar = {
        ...     "<start>": ["<X>"],
        ...     "<X>": ["x", "x<X>"],
        ... }
        >>> x = language.Variable("x", "<X>")
        >>> x_0 = z3.Int("x_0")
        >>> f = z3_eq(x_0, z3.IntVal(5))
        >>> z3_solver = z3.Solver()
        >>> z3_solver.add(f)
        >>> z3_solver.check()
        sat
        >>> model = z3_solver.model()
        >>> solver = ISLaSolver(grammar)
        >>> tree = solver.safe_create_fixed_length_tree(x, model, {x: x_0})
        >>> tree.value
        '<X>'
        >>> str(tree)
        'xxxxx'

        :param var: The variable to create a
                    :class:`~isla.derivation_tree.DerivationTree` object for.
        :param model: The Z3 model to extract a solution to the length constraint.
        :param fresh_var_map: A map including a mapping :code:`var` -> :code:`var_0`,
                              where :code:`var_0` is an integer-valued variale included
                              in :code:`model`.
        :return: A tree of the type of :code:`var` and length as specified in
                :code:`model`.
        """

        assert var in fresh_var_map
        assert fresh_var_map[var].decl() in model.decls()

        fixed_length_tree = create_fixed_length_tree(
            start=var.n_type,
            canonical_grammar=self.canonical_grammar,
            target_length=model[fresh_var_map[var]].as_long(),
        )

        if fixed_length_tree is None:
            raise RuntimeError(
                f"Could not create a tree with the start symbol '{var.n_type}' "
                + f"of length {model[fresh_var_map[var]].as_long()}; try "
                + "running the solver without optimized Z3 queries or make "
                + "sure that lengths are restricted to syntactically valid "
                + "ones (according to the grammar).",
            )

        return fixed_length_tree

    def extract_model_value(
        self,
        var: language.Variable,
        model: z3.ModelRef,
        fresh_var_map: Dict[language.Variable, z3.ExprRef],
        length_vars: Set[language.Variable],
        int_vars: Set[language.Variable],
    ) -> DerivationTree:
        r"""
        Extracts a value for :code:`var` from :code:`model`. Considers the following
        special cases:

        Numeric Variables
            Returns a closed derivation tree of one node with a string representation
            of the numeric solution.

        "Length" Variables
            Returns a string of the length corresponding to the model and
            :code:`fresh_var_map`, see also
            :meth:`~isla.solver.ISLaSolver.safe_create_fixed_length_tree()`.

        "Int" Variables
            Tries to parse the numeric solution from the model (obtained via
            :code:`fresh_var_map`) into the type of :code:`var` and returns the
            corresponding derivation tree.

        >>> grammar = {
        ...     "<start>": ["<A>"],
        ...     "<A>": ["<X><Y>"],
        ...     "<X>": ["x", "x<X>"],
        ...     "<Y>": ["<digit>", "<digit><Y>"],
        ...     "<digit>": ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"],
        ... }
        >>> solver = ISLaSolver(grammar)

        **Numeric Variables:**

        >>> n = language.Variable("n", language.Variable.NUMERIC_NTYPE)
        >>> f = z3_eq(z3.StrToInt(n.to_smt()), z3.IntVal(15))
        >>> z3_solver = z3.Solver()
        >>> z3_solver.add(f)
        >>> z3_solver.check()
        sat
        >>> model = z3_solver.model()
        >>> DerivationTree.next_id = 1
        >>> solver.extract_model_value(n, model, {}, set(), set())
        DerivationTree('15', (), id=1)

        For a trivially true solution on numeric variables, we return a random number:

        >>> f = z3_eq(n.to_smt(), n.to_smt())
        >>> z3_solver = z3.Solver()
        >>> z3_solver.add(f)
        >>> z3_solver.check()
        sat

        >>> model = z3_solver.model()
        >>> DerivationTree.next_id = 1
        >>> random.seed(0)
        >>> solver.extract_model_value(n, model, {n: n.to_smt()}, set(), {n})
        DerivationTree('-2116850434379610162', (), id=1)

        **"Length" Variables:**

        >>> x = language.Variable("x", "<X>")
        >>> x_0 = z3.Int("x_0")
        >>> f = z3_eq(x_0, z3.IntVal(3))
        >>> z3_solver = z3.Solver()
        >>> z3_solver.add(f)
        >>> z3_solver.check()
        sat
        >>> model = z3_solver.model()
        >>> result = solver.extract_model_value(x, model, {x: x_0}, {x}, set())
        >>> result.value
        '<X>'
        >>> str(result)
        'xxx'

        **"Int" Variables:**

        >>> y = language.Variable("y", "<Y>")
        >>> y_0 = z3.Int("y_0")
        >>> f = z3_eq(y_0, z3.IntVal(5))
        >>> z3_solver = z3.Solver()
        >>> z3_solver.add(f)
        >>> z3_solver.check()
        sat
        >>> model = z3_solver.model()
        >>> DerivationTree.next_id = 1
        >>> solver.extract_model_value(y, model, {y: y_0}, set(), {y})
        DerivationTree('<Y>', (DerivationTree('<digit>', (DerivationTree('5', (), id=1),), id=2),), id=3)

        **"Flexible" Variables:**

        >>> f = z3_eq(x.to_smt(), z3.StringVal("xxxxx"))
        >>> z3_solver = z3.Solver()
        >>> z3_solver.add(f)
        >>> z3_solver.check()
        sat
        >>> model = z3_solver.model()
        >>> result = solver.extract_model_value(x, model, {}, set(), set())
        >>> result.value
        '<X>'
        >>> str(result)
        'xxxxx'

        **Special Number Formats**

        It may happen that the solver returns, e.g., "1" as a solution for an int
        variable, but the grammar only recognizes "+001". We support this case, i.e.,
        an optional "+" and optional 0 padding; an optional 0 padding for negative
        numbers is also supported.

        >>> grammar = {
        ...     "<start>": ["<int>"],
        ...     "<int>": ["<sign>00<leaddigit><digits>"],
        ...     "<sign>": ["-", "+"],
        ...     "<digits>": ["", "<digit><digits>"],
        ...     "<digit>": list("0123456789"),
        ...     "<leaddigit>": list("123456789"),
        ... }
        >>> solver = ISLaSolver(grammar)

        >>> i = language.Variable("i", "<int>")
        >>> i_0 = z3.Int("i_0")
        >>> f = z3_eq(i_0, z3.IntVal(5))

        >>> z3_solver = z3.Solver()
        >>> z3_solver.add(f)
        >>> z3_solver.check()
        sat

        The following test works when run from the IDE, but unfortunately not when
        started from CI/the `test_doctests.py` script. Thus, we only show it as code
        block (we added a unit test as a replacement)::

            model = z3_solver.model()
            print(solver.extract_model_value(i, model, {i: i_0}, set(), {i}))
            # Prints: +005

        :param var: The variable for which to extract a solution from the model.
        :param model: The model containing the solution.
        :param fresh_var_map: A map from variables to fresh symbols for "length" and
                              "int" variables.
        :param length_vars: The set of "length" variables.
        :param int_vars: The set of "int" variables.
        :return: A :class:`~isla.derivation_tree.DerivationTree` object corresponding
                 to the solution in :code:`model`.
        """

        f_flex_vars = self.extract_model_value_flexible_var
        f_int_vars = partial(self.extract_model_value_int_var, f_flex_vars)
        f_length_vars = partial(self.extract_model_value_length_var, f_int_vars)
        f_num_vars = partial(self.extract_model_value_numeric_var, f_length_vars)

        return f_num_vars(var, model, fresh_var_map, length_vars, int_vars)

    ExtractModelValueFallbackType = Callable[
        [
            language.Variable,
            z3.ModelRef,
            Dict[language.Variable, z3.ExprRef],
            Set[language.Variable],
            Set[language.Variable],
        ],
        DerivationTree,
    ]

    def extract_model_value_numeric_var(
        self,
        fallback: ExtractModelValueFallbackType,
        var: language.Variable,
        model: z3.ModelRef,
        fresh_var_map: Dict[language.Variable, z3.ExprRef],
        length_vars: Set[language.Variable],
        int_vars: Set[language.Variable],
    ) -> DerivationTree:
        """
        Addresses the case of numeric variables from
        :meth:`~isla.solver.ISLaSolver.extract_model_value`.

        :param fallback: The function to call if this function is not responsible.
        :param var: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :param model: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :param fresh_var_map: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :param length_vars: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :param int_vars: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :return: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        """
        if not var.is_numeric():
            return fallback(var, model, fresh_var_map, length_vars, int_vars)

        z3_var = z3.String(var.name)
        if z3_var.decl() in model.decls():
            model_value = model[z3_var]
        else:
            assert var in int_vars
            assert var in fresh_var_map

            model_value = model[fresh_var_map[var]]

            if model_value is None:
                # This can happen for universally true formulas, e.g., `x = x`.
                # In that case, we return a random integer.
                model_value = z3.IntVal(random.randint(-sys.maxsize, sys.maxsize))

        assert (
            model_value is not None
        ), f"No solution for variable {var} found in model {model}"

        string_value = smt_string_val_to_string(model_value)
        assert string_value
        assert (
            string_value.isnumeric()
            or string_value[0] == "-"
            and string_value[1:].isnumeric()
        )

        return DerivationTree(string_value, ())

    def extract_model_value_length_var(
        self,
        fallback: ExtractModelValueFallbackType,
        var: language.Variable,
        model: z3.ModelRef,
        fresh_var_map: Dict[language.Variable, z3.ExprRef],
        length_vars: Set[language.Variable],
        int_vars: Set[language.Variable],
    ) -> DerivationTree:
        """
        Addresses the case of length variables from
        :meth:`~isla.solver.ISLaSolver.extract_model_value`.

        :param fallback: The function to call if this function is not responsible.
        :param var: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :param model: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :param fresh_var_map: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :param length_vars: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :param int_vars: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :return: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        """
        if var not in length_vars:
            return fallback(var, model, fresh_var_map, length_vars, int_vars)

        return self.safe_create_fixed_length_tree(var, model, fresh_var_map)

    def extract_model_value_int_var(
        self,
        fallback: ExtractModelValueFallbackType,
        var: language.Variable,
        model: z3.ModelRef,
        fresh_var_map: Dict[language.Variable, z3.ExprRef],
        length_vars: Set[language.Variable],
        int_vars: Set[language.Variable],
    ) -> DerivationTree:
        """
        Addresses the case of int variables from
        :meth:`~isla.solver.ISLaSolver.extract_model_value`.

        :param fallback: The function to call if this function is not responsible.
        :param var: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :param model: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :param fresh_var_map: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :param length_vars: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :param int_vars: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :return: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        """
        if var not in int_vars:
            return fallback(var, model, fresh_var_map, length_vars, int_vars)

        str_model_value = model[fresh_var_map[var]].as_string()

        try:
            int_model_value = int(str_model_value)
        except ValueError:
            raise RuntimeError(f"Value {str_model_value} for {var} is not a number")

        var_type = var.n_type

        try:
            return self.parse(
                str(int_model_value),
                var_type,
                silent=True,
            )
        except SyntaxError:
            # This may happen, e.g, with padded values: Only "01" is a valid
            # solution, but not "1". Similarly, a grammar may expect "+1", but
            # "1" is returned by the solver. We support the number format
            # `[+-]0*<digits>`. Whenever the grammar recognizes at least this
            # set for the nonterminal in question, we return a derivation tree.
            # Otherwise, a RuntimeError is raised.

            z3_solver = z3.Solver()
            z3_solver.set("timeout", 300)

            maybe_plus_re = z3.Option(z3.Re("+"))
            zeroes_padding_re = z3.Star(z3.Re("0"))

            # TODO: Ensure symbols are fresh
            maybe_plus_var = z3.String("__plus")
            zeroes_padding_var = z3.String("__padding")

            z3_solver.add(z3.InRe(maybe_plus_var, maybe_plus_re))
            z3_solver.add(z3.InRe(zeroes_padding_var, zeroes_padding_re))

            z3_solver.add(
                z3.InRe(
                    z3.Concat(
                        maybe_plus_var if int_model_value >= 0 else z3.StringVal("-"),
                        zeroes_padding_var,
                        z3.StringVal(
                            str_model_value
                            if int_model_value >= 0
                            else str(-int_model_value)
                        ),
                    ),
                    self.extract_regular_expression(var.n_type),
                )
            )

            if z3_solver.check() != z3.sat:
                raise RuntimeError(
                    "Could not parse a numeric solution "
                    + f"({str_model_value}) for variable "
                    + f"{var} of type '{var.n_type}'; try "
                    + "running the solver without optimized Z3 queries or make "
                    + "sure that ranges are restricted to syntactically valid "
                    + "ones (according to the grammar).",
                )

            return self.parse(
                (
                    z3_solver.model()[maybe_plus_var].as_string()
                    if int_model_value >= 0
                    else "-"
                )
                + z3_solver.model()[zeroes_padding_var].as_string()
                + (str_model_value if int_model_value >= 0 else str(-int_model_value)),
                var.n_type,
            )

    def extract_model_value_flexible_var(
        self,
        var: language.Variable,
        model: z3.ModelRef,
        fresh_var_map: Dict[language.Variable, z3.ExprRef],
        length_vars: Set[language.Variable],
        int_vars: Set[language.Variable],
    ) -> DerivationTree:
        """
        Addresses the case of "flexible" variables from
        :meth:`~isla.solver.ISLaSolver.extract_model_value`.

        :param fallback: The function to call if this function is not responsible.
        :param var: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :param model: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :param fresh_var_map: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :param length_vars: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :param int_vars: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        :return: See :meth:`~isla.solver.ISLaSolver.extract_model_value`.
        """

        return self.parse(
            smt_string_val_to_string(model[z3.String(var.name)]),
            var.n_type,
        )

    @staticmethod
    def infer_variable_contexts(
        variables: Set[language.Variable], smt_formulas: ImmutableList[z3.BoolRef]
    ) -> Dict[str, Set[language.Variable]]:
        """
        Divides the given variables into

        1. those that occur only in :code:`length(...)` contexts,
        2. those that occur only in :code:`str.to.int(...)` contexts, and
        3. "flexible" constants occurring in other/various contexts.

        >>> x = language.Variable("x", "<X>")
        >>> y = language.Variable("y", "<Y>")

        Two variables in an arbitrary context.

        >>> f = z3_eq(x.to_smt(), y.to_smt())
        >>> contexts = ISLaSolver.infer_variable_contexts({x, y}, (f,))
        >>> contexts["length"]
        set()
        >>> contexts["int"]
        set()
        >>> contexts["flexible"] == {language.Variable("x", "<X>"), language.Variable("y", "<Y>")}
        True

        Variable x occurs in a length context, variable y in an arbitrary one.

        >>> f = z3.And(
        ...     z3.Length(x.to_smt()) > z3.IntVal(10),
        ...     z3_eq(y.to_smt(), z3.StringVal("y")))
        >>> ISLaSolver.infer_variable_contexts({x, y}, (f,))
        {'length': {Variable("x", "<X>")}, 'int': set(), 'flexible': {Variable("y", "<Y>")}}

        Variable x occurs in a length context, y does not occur.

        >>> f = z3.Length(x.to_smt()) > z3.IntVal(10)
        >>> ISLaSolver.infer_variable_contexts({x, y}, (f,))
        {'length': {Variable("x", "<X>")}, 'int': set(), 'flexible': {Variable("y", "<Y>")}}

        Variables x and y both occur in a length context.

        >>> f = z3.Length(x.to_smt()) > z3.Length(y.to_smt())
        >>> contexts = ISLaSolver.infer_variable_contexts({x, y}, (f,))
        >>> contexts["length"] == {language.Variable("x", "<X>"), language.Variable("y", "<Y>")}
        True
        >>> contexts["int"]
        set()
        >>> contexts["flexible"]
        set()

        Variable x occurs in a :code:`str.to.int` context.

        >>> f = z3.StrToInt(x.to_smt()) > z3.IntVal(17)
        >>> ISLaSolver.infer_variable_contexts({x}, (f,))
        {'length': set(), 'int': {Variable("x", "<X>")}, 'flexible': set()}

        Now, x also occurs in a different context; it's "flexible" now.

        >>> f = z3.And(
        ...     z3.StrToInt(x.to_smt()) > z3.IntVal(17),
        ...     z3_eq(x.to_smt(), z3.StringVal("17")))
        >>> ISLaSolver.infer_variable_contexts({x}, (f,))
        {'length': set(), 'int': set(), 'flexible': {Variable("x", "<X>")}}

        :param variables: The constants to divide/filter from.
        :param smt_formulas: The SMT formulas to consider in the filtering.
        :return: A pair of constants occurring in `str.len` contexts, and the
        remaining ones. The union of both sets equals `variables`, and both sets
        are disjoint.
        """

        parent_relationships = reduce(
            merge_dict_of_sets,
            [parent_relationships_in_z3_expr(formula) for formula in smt_formulas],
            {},
        )

        contexts: Dict[language.Variable, Set[int]] = {
            var: {
                expr.decl().kind()
                for expr in parent_relationships.get(var.to_smt(), set())
            }
            or {-1}
            for var in variables
        }

        # The set `length_vars` consists of all variables that only occur in
        # `str.len(...)` context.
        length_vars: Set[language.Variable] = {
            var
            for var in variables
            if all(context == z3.Z3_OP_SEQ_LENGTH for context in contexts[var])
        }

        # The set `int_vars` consists of all variables that only occur in
        # `str.to.int(...)` context.
        int_vars: Set[language.Variable] = {
            var
            for var in variables
            if all(context == z3.Z3_OP_STR_TO_INT for context in contexts[var])
        }

        # "Flexible" variables are the remaining ones.
        flexible_vars = variables.difference(length_vars).difference(int_vars)

        return {"length": length_vars, "int": int_vars, "flexible": flexible_vars}

    def generate_language_constraints(
        self,
        constants: Iterable[language.Variable],
        tree_substitutions: Dict[language.Variable, DerivationTree],
    ) -> List[z3.BoolRef]:
        formulas: List[z3.BoolRef] = []
        for constant in constants:
            if constant.is_numeric():
                regex = z3.Union(
                    z3.Re("0"),
                    z3.Concat(z3.Range("1", "9"), z3.Star(z3.Range("0", "9"))),
                )
            elif constant in tree_substitutions:
                # We have a more concrete shape of the desired instantiation available
                regexes = [
                    self.extract_regular_expression(t)
                    if is_nonterminal(t)
                    else z3.Re(t)
                    for t in split_str_with_nonterminals(
                        str(tree_substitutions[constant])
                    )
                ]
                assert regexes
                regex = z3.Concat(*regexes) if len(regexes) > 1 else regexes[0]
            else:
                regex = self.extract_regular_expression(constant.n_type)

            formulas.append(z3.InRe(z3.String(constant.name), regex))

        return formulas

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

                new_smt_formula = cast(
                    z3.BoolRef,
                    z3_subst(new_smt_formula, {subst_var.to_smt(): new_var.to_smt()}),
                )
                new_substitutions = {
                    new_var if k == subst_var else k: v
                    for k, v in new_substitutions.items()
                }
                new_instantiated_variables = {
                    new_var if v == subst_var else v for v in new_instantiated_variables
                }

            smt_formulas.append(
                language.SMTFormula(
                    new_smt_formula,
                    *subformula.free_variables_,
                    instantiated_variables=new_instantiated_variables,
                    substitutions=new_substitutions,
                )
            )

        return smt_formulas

    def process_new_states(
        self, new_states: List[SolutionState]
    ) -> List[DerivationTree]:
        return [
            tree
            for new_state in new_states
            for tree in self.process_new_state(new_state)
        ]

    def process_new_state(self, new_state: SolutionState) -> List[DerivationTree]:
        new_state = self.instantiate_structural_predicates(new_state)
        new_states = self.establish_invariant(new_state)
        new_states = [
            self.remove_nonmatching_universal_quantifiers(new_state)
            for new_state in new_states
        ]
        new_states = [
            self.remove_infeasible_universal_quantifiers(new_state)
            for new_state in new_states
        ]

        if self.activate_unsat_support and not self.currently_unsat_checking:
            self.currently_unsat_checking = True

            for new_state in list(new_states):
                if new_state.constraint == sc.true():
                    continue

                # Remove states with unsatisfiable SMT-LIB formulas.
                if any(
                    isinstance(f, language.SMTFormula)
                    for f in split_conjunction(new_state.constraint)
                ) and not is_successful(
                    self.eliminate_all_semantic_formulas(
                        new_state, max_instantiations=1
                    ).bind(lambda a: Some(a) if a else Nothing)
                ):
                    new_states.remove(new_state)
                    self.logger.debug(
                        "Dropping state %s, unsatisfiable SMT formulas", new_state
                    )

                # Remove states with unsatisfiable existential formulas.
                existential_formulas = [
                    f
                    for f in split_conjunction(new_state.constraint)
                    if isinstance(f, language.ExistsFormula)
                ]
                for existential_formula in existential_formulas:
                    old_start_time = self.start_time
                    old_timeout_seconds = self.timeout_seconds
                    old_queue = list(self.queue)
                    old_solutions = list(self.solutions)

                    self.queue = []
                    self.solutions = []
                    check_state = SolutionState(existential_formula, new_state.tree)
                    heapq.heappush(self.queue, (0, check_state))
                    self.start_time = int(time.time())
                    self.timeout_seconds = 2

                    try:
                        self.solve()
                    except StopIteration:
                        new_states.remove(new_state)
                        self.logger.debug(
                            "Dropping state %s, unsatisfiable existential formula %s",
                            new_state,
                            existential_formula,
                        )
                        break
                    finally:
                        self.start_time = old_start_time
                        self.timeout_seconds = old_timeout_seconds
                        self.queue = old_queue
                        self.solutions = old_solutions

            self.currently_unsat_checking = False

        assert all(
            state.tree.find_node(tree) is not None
            for state in new_states
            for quantified_formula in split_conjunction(state.constraint)
            if isinstance(quantified_formula, language.QuantifiedFormula)
            for _, tree in quantified_formula.in_variable.filter(lambda t: True)
        )

        solution_trees = [
            new_state.tree
            for new_state in new_states
            if self.state_is_valid_or_enqueue(new_state)
        ]

        for tree in solution_trees:
            self.cost_computer.signal_tree_output(tree)

        return solution_trees

    def state_is_valid_or_enqueue(self, state: SolutionState) -> bool:
        """
        Returns True if the given state is valid, such that it can be yielded. Returns False and enqueues the state
        if the state is not yet complete, otherwise returns False and discards the state.
        """

        if state.complete():
            for _, subtree in state.tree.paths():
                if subtree.children:
                    self.seen_coverages.add(
                        expansion_key(subtree.value, subtree.children)
                    )

            assert state.formula_satisfied(self.grammar).is_true()
            return True

        # Helps in debugging below assertion:
        # [(predicate_formula, [
        #     arg for arg in predicate_formula.args
        #     if isinstance(arg, DerivationTree) and not state.tree.find_node(arg)])
        #  for predicate_formula in get_conjuncts(state.constraint)
        #  if isinstance(predicate_formula, language.StructuralPredicateFormula)]

        self.assert_no_dangling_predicate_argument_trees(state)
        self.assert_no_dangling_smt_formula_argument_trees(state)

        if (
            self.enforce_unique_trees_in_queue
            and state.tree.structural_hash() in self.tree_hashes_in_queue
        ):
            # Some structures can arise as well from tree insertion (existential
            # quantifier elimination) and expansion; also, tree insertion can yield
            # different trees that have intersecting expansions. We drop those to output
            # more diverse solutions (numbers for SMT solutions and free nonterminals
            # are configurable, so you get more outputs by playing with those!).
            self.logger.debug("Discarding state %s, tree already in queue", state)
            return False

        if hash(state) in self.state_hashes_in_queue:
            self.logger.debug("Discarding state %s, already in queue", state)
            return False

        if self.propositionally_unsatisfiable(state.constraint):
            self.logger.debug("Discarding state %s", state)
            return False

        state = SolutionState(
            state.constraint, state.tree, level=self.current_level + 1
        )

        self.recompute_costs()

        cost = self.compute_cost(state)
        heapq.heappush(self.queue, (cost, state))
        self.tree_hashes_in_queue.add(state.tree.structural_hash())
        self.state_hashes_in_queue.add(hash(state))

        if self.debug:
            self.state_tree[self.current_state].append(state)
            self.costs[state] = cost

        self.logger.debug(
            "Pushing new state (%s, %s) (hash %d, cost %f)",
            state.constraint,
            state.tree.to_string(show_open_leaves=True, show_ids=True),
            hash(state),
            cost,
        )
        self.logger.debug("Queue length: %d", len(self.queue))
        if len(self.queue) % 100 == 0:
            self.logger.info("Queue length: %d", len(self.queue))

        return False

    def recompute_costs(self):
        if self.step_cnt % 400 != 0 or self.step_cnt <= self.last_cost_recomputation:
            return

        self.last_cost_recomputation = self.step_cnt
        self.logger.info(
            f"Recomputing costs in queue after {self.step_cnt} solver steps"
        )
        old_queue = list(self.queue)
        self.queue = []
        for _, state in old_queue:
            cost = self.compute_cost(state)
            heapq.heappush(self.queue, (cost, state))

    def assert_no_dangling_smt_formula_argument_trees(
        self, state: SolutionState
    ) -> None:
        if not assertions_activated() and not self.debug:
            return

        dangling_smt_formula_argument_trees = [
            (smt_formula, arg)
            for smt_formula in language.FilterVisitor(
                lambda f: isinstance(f, language.SMTFormula)
            ).collect(state.constraint)
            for arg in cast(language.SMTFormula, smt_formula).substitutions.values()
            if isinstance(arg, DerivationTree) and state.tree.find_node(arg) is None
        ]

        if dangling_smt_formula_argument_trees:
            message = "Dangling SMT formula arguments: ["
            message += ", ".join(
                [
                    str(f) + ", " + repr(a)
                    for f, a in dangling_smt_formula_argument_trees
                ]
            )
            message += "]"
            assert False, message

    def assert_no_dangling_predicate_argument_trees(self, state: SolutionState) -> None:
        if not assertions_activated() and not self.debug:
            return

        dangling_predicate_argument_trees = [
            (predicate_formula, arg)
            for predicate_formula in language.FilterVisitor(
                lambda f: isinstance(f, language.StructuralPredicateFormula)
            ).collect(state.constraint)
            for arg in cast(language.StructuralPredicateFormula, predicate_formula).args
            if isinstance(arg, DerivationTree) and state.tree.find_node(arg) is None
        ]

        if dangling_predicate_argument_trees:
            message = "Dangling predicate arguments: ["
            message += ", ".join(
                [str(f) + ", " + repr(a) for f, a in dangling_predicate_argument_trees]
            )
            message += "]"
            assert False, message

    def propositionally_unsatisfiable(self, formula: language.Formula) -> bool:
        return formula == sc.false()

        # NOTE: Deactivated propositional check for performance reasons
        # z3_formula = language.isla_to_smt_formula(formula, replace_untranslatable_with_predicate=True)
        # solver = z3.Solver()
        # solver.add(z3_formula)
        # return solver.check() == z3.unsat

    def establish_invariant(self, state: SolutionState) -> List[SolutionState]:
        formula = convert_to_dnf(convert_to_nnf(state.constraint), deep=False)
        return [
            SolutionState(disjunct, state.tree)
            for disjunct in split_disjunction(formula)
        ]

    def compute_cost(self, state: SolutionState) -> float:
        if state.constraint == sc.true():
            return 0

        return self.cost_computer.compute_cost(state)

    def remove_nonmatching_universal_quantifiers(
        self, state: SolutionState
    ) -> SolutionState:
        conjuncts = [conjunct for conjunct in get_conjuncts(state.constraint)]
        deleted = False

        for idx, universal_formula in reversed(list(enumerate(conjuncts))):
            if not isinstance(universal_formula, language.ForallFormula):
                continue

            if (
                universal_formula.in_variable.is_complete()
                and not matches_for_quantified_formula(universal_formula, self.grammar)
            ):
                deleted = True
                del conjuncts[idx]

        if not deleted:
            return state

        return SolutionState(sc.conjunction(*conjuncts), state.tree)

    def remove_infeasible_universal_quantifiers(
        self, state: SolutionState
    ) -> SolutionState:
        conjuncts = get_conjuncts(state.constraint)
        one_removed = False

        for idx, universal_formula in reversed(list(enumerate(conjuncts))):
            if not isinstance(universal_formula, language.ForallFormula):
                continue

            matches = matches_for_quantified_formula(universal_formula, self.grammar)

            all_matches_matched = all(
                universal_formula.is_already_matched(
                    match[universal_formula.bound_variable][1]
                )
                for match in matches
            )

            def some_leaf_might_match() -> bool:
                return any(
                    self.quantified_formula_might_match(
                        universal_formula, leaf_path, universal_formula.in_variable
                    )
                    for leaf_path, _ in universal_formula.in_variable.open_leaves()
                )

            if all_matches_matched and not some_leaf_might_match():
                one_removed = True
                del conjuncts[idx]

        return (
            state
            if not one_removed
            else SolutionState(
                reduce(lambda a, b: a & b, conjuncts, sc.true()),
                state.tree,
            )
        )

    def quantified_formula_might_match(
        self,
        qfd_formula: language.QuantifiedFormula,
        path_to_nonterminal: Path,
        tree: DerivationTree,
    ) -> bool:
        return quantified_formula_might_match(
            qfd_formula,
            path_to_nonterminal,
            tree,
            self.grammar,
            self.graph.reachable,
        )

    def extract_regular_expression(self, nonterminal: str) -> z3.ReRef:
        if nonterminal in self.regex_cache:
            return self.regex_cache[nonterminal]

        # For definitions like `<a> ::= <b>`, we only compute the regular expression
        # for `<b>`. That way, we might save some calls if `<b>` is used multiple times
        # (e.g., as in `<byte>`).
        canonical_expansions = self.canonical_grammar[nonterminal]

        if (
            len(canonical_expansions) == 1
            and len(canonical_expansions[0]) == 1
            and is_nonterminal(canonical_expansions[0][0])
        ):
            sub_nonterminal = canonical_expansions[0][0]
            assert (
                nonterminal != sub_nonterminal
            ), f"Expansion {nonterminal} => {sub_nonterminal}: Infinite recursion!"
            return self.regex_cache.setdefault(
                nonterminal, self.extract_regular_expression(sub_nonterminal)
            )

        # Similarly, for definitions like `<a> ::= <b> " x " <c>`, where `<b>` and `<c>`
        # don't reach `<a>`, we only compute the regular expressions for `<b>` and `<c>`
        # and return a concatenation. This also saves us expensive conversions (e.g.,
        # for `<seq> ::= <byte> <byte>`).
        if (
            len(canonical_expansions) == 1
            and any(is_nonterminal(elem) for elem in canonical_expansions[0])
            and all(
                not is_nonterminal(elem)
                or elem != nonterminal
                and not self.graph.reachable(elem, nonterminal)
                for elem in canonical_expansions[0]
            )
        ):
            result_elements: List[z3.ReRef] = [
                z3.Re(elem)
                if not is_nonterminal(elem)
                else self.extract_regular_expression(elem)
                for elem in canonical_expansions[0]
            ]
            return self.regex_cache.setdefault(nonterminal, z3.Concat(*result_elements))

        regex_conv = RegexConverter(
            self.grammar,
            compress_unions=True,
            max_num_expansions=self.grammar_unwinding_threshold,
        )
        regex = regex_conv.to_regex(nonterminal, convert_to_z3=False)
        self.logger.debug(
            f"Computed regular expression for nonterminal {nonterminal}:\n{regex}"
        )
        z3_regex = regex_to_z3(regex)

        if assertions_activated():
            # Check correctness of regular expression
            grammar = self.graph.subgraph(nonterminal).to_grammar()

            # L(regex) \subseteq L(grammar)
            self.logger.debug(
                "Checking L(regex) \\subseteq L(grammar) for "
                + "nonterminal '%s' and regex '%s'",
                nonterminal,
                regex,
            )
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
                        len(prev) + 1,
                        regex,
                    )
                    break
                new_inp = smt_string_val_to_string(s.model()[c])
                try:
                    next(parser.parse(new_inp))
                except SyntaxError:
                    assert (
                        False
                    ), f"Input '{new_inp}' from regex language is not in grammar language."
                prev.add(new_inp)

        self.regex_cache[nonterminal] = z3_regex

        return z3_regex


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
        reset_coverage_after_n_round_with_no_coverage: int = 100,
        symbol_costs: Optional[Dict[str, int]] = None,
    ):
        self.cost_settings = cost_settings
        self.graph = graph

        self.covered_k_paths: Set[Tuple[gg.Node, ...]] = set()
        self.rounds_with_no_new_coverage = 0
        self.reset_coverage_after_n_round_with_no_coverage = (
            reset_coverage_after_n_round_with_no_coverage
        )
        self.symbol_costs: Optional[Dict[str, int]] = symbol_costs

        self.logger = logging.getLogger(type(self).__name__)

    def __repr__(self):
        return (
            "GrammarBasedBlackboxCostComputer("
            + f"{repr(self.cost_settings)}, "
            + "graph, "
            + f"{self.reset_coverage_after_n_round_with_no_coverage}, "
            + f"{self.symbol_costs})"
        )

    def compute_cost(self, state: SolutionState) -> float:
        # How costly is it to finish the tree?
        tree_closing_cost = self.compute_tree_closing_cost(state.tree)

        # Quantifiers are expensive (universal formulas have to be matched, tree insertion for existential
        # formulas is even more costly). TODO: Penalize nested quantifiers more.
        constraint_cost = sum(
            [
                idx * (2 if isinstance(f, language.ExistsFormula) else 1) + 1
                for c in get_quantifier_chains(state.constraint)
                for idx, f in enumerate(c)
            ]
        )

        # k-Path coverage: Fewer covered -> higher penalty
        k_cov_cost = self._compute_k_coverage_cost(state)

        # Covered k-paths: Fewer contributed -> higher penalty
        global_k_path_cost = self._compute_global_k_coverage_cost(state)

        costs = [
            tree_closing_cost,
            constraint_cost,
            state.level,
            k_cov_cost,
            global_k_path_cost,
        ]
        assert tree_closing_cost >= 0, f"tree_closing_cost == {tree_closing_cost}!"
        assert constraint_cost >= 0, f"constraint_cost == {constraint_cost}!"
        assert state.level >= 0, f"state.level == {state.level}!"
        assert k_cov_cost >= 0, f"k_cov_cost == {k_cov_cost}!"
        assert global_k_path_cost >= 0, f"global_k_path_cost == {global_k_path_cost}!"

        # Compute geometric mean
        result = weighted_geometric_mean(costs, list(self.cost_settings.weight_vector))

        self.logger.debug(
            "Computed cost for state %s:\n%f, individual costs: %s, weights: %s",
            lazystr(lambda: f"({(str(state.constraint)[:50] + '...')}, {state.tree})"),
            result,
            costs,
            self.cost_settings.weight_vector,
        )

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

            self.covered_k_paths.update(
                tree.k_paths(
                    self.graph, self.cost_settings.k, include_potential_paths=False
                )
            )

            if old_covered_k_paths == self.covered_k_paths:
                self.rounds_with_no_new_coverage += 1

            graph_paths = self.graph.k_paths(
                self.cost_settings.k, include_terminals=False
            )
            if (
                self.rounds_with_no_new_coverage
                >= self.reset_coverage_after_n_round_with_no_coverage
                or self.covered_k_paths == graph_paths
            ):
                if self.covered_k_paths == graph_paths:
                    self.logger.debug("ALL PATHS COVERED")
                else:
                    self.logger.debug(
                        "COVERAGE RESET SINCE NO CHANGE IN COVERED PATHS SINCE %d "
                        + "ROUNDS (%d path(s) uncovered)",
                        self.reset_coverage_after_n_round_with_no_coverage,
                        len(graph_paths) - len(self.covered_k_paths),
                    )

                    # uncovered_paths = (
                    #     self.graph.k_paths(
                    #         self.cost_settings.k, include_terminals=False
                    #     )
                    #     - self.covered_k_paths
                    # )
                    # self.logger.debug(
                    #     "\n".join(
                    #         [
                    #             ", ".join(f"'{n.symbol}'" for n in p)
                    #             for p in uncovered_paths
                    #         ]
                    #     )
                    # )

                self.covered_k_paths = set()
            else:
                pass
                # uncovered_paths = (
                #     self.graph.k_paths(self.cost_settings.k, include_terminals=False)
                #     - self.covered_k_paths
                # )
                # self.logger.debug("%d uncovered paths", len(uncovered_paths))
                # self.logger.debug(
                #     "\n"
                #     + "\n".join(
                #         [", ".join(f"'{n.symbol}'" for n in p)
                #         for p in uncovered_paths]
                #     )
                #     + "\n"
                # )

            if (
                self.rounds_with_no_new_coverage
                >= self.reset_coverage_after_n_round_with_no_coverage
            ):
                self.rounds_with_no_new_coverage = 0

    def _compute_global_k_coverage_cost(self, state: SolutionState):
        if self.cost_settings.weight_vector.low_global_k_path_coverage_penalty == 0:
            return 0

        tree_k_paths = state.tree.k_paths(
            self.graph, self.cost_settings.k, include_potential_paths=False
        )
        all_graph_k_paths = self.graph.k_paths(
            self.cost_settings.k, include_terminals=False
        )

        contributed_k_paths = {
            path
            for path in all_graph_k_paths
            if path in tree_k_paths and path not in self.covered_k_paths
        }

        num_contributed_k_paths = len(contributed_k_paths)
        num_missing_k_paths = len(all_graph_k_paths) - len(self.covered_k_paths)

        # self.logger.debug(
        #     'k-Paths contributed by input %s:\n%s',
        #     state.tree,
        #     '\n'.join(map(
        #         lambda path: ' '.join(map(
        #             lambda n: n.symbol,
        #             filter(lambda n: not isinstance(n, gg.ChoiceNode), path))),
        #         contributed_k_paths)))
        # self.logger.debug('Missing k paths: %s', num_missing_k_paths)

        assert 0 <= num_contributed_k_paths <= num_missing_k_paths, (
            f"num_contributed_k_paths == {num_contributed_k_paths}, "
            f"num_missing_k_paths == {num_missing_k_paths}"
        )

        # return 1 - (num_contributed_k_paths / num_missing_k_paths)

        potential_tree_k_paths = state.tree.k_paths(
            self.graph, self.cost_settings.k, include_potential_paths=True
        )
        contributed_k_paths = {
            path
            for path in all_graph_k_paths
            if path in potential_tree_k_paths and path not in self.covered_k_paths
        }

        num_contributed_potential_k_paths = len(contributed_k_paths)

        if not num_missing_k_paths:
            return 0

        return 1 - weighted_geometric_mean(
            [
                num_contributed_k_paths / num_missing_k_paths,
                num_contributed_potential_k_paths / num_missing_k_paths,
            ],
            [0.2, 0.8],
        )

    def _compute_k_coverage_cost(self, state: SolutionState) -> float:
        if self.cost_settings.weight_vector.low_k_coverage_penalty == 0:
            return 0

        coverages = []
        for k in range(1, self.cost_settings.k + 1):
            coverage = state.tree.k_coverage(
                self.graph, k, include_potential_paths=False
            )
            assert 0 <= coverage <= 1, f"coverage == {coverage}"

            coverages.append(1 - coverage)

        return math.prod(coverages) ** (1 / float(self.cost_settings.k))

    def compute_tree_closing_cost(self, tree: DerivationTree) -> float:
        nonterminals = [leaf.value for _, leaf in tree.open_leaves()]
        return sum([self._symbol_costs()[nonterminal] for nonterminal in nonterminals])


def smt_formulas_referring_to_subtrees(
    smt_formulas: Sequence[language.SMTFormula],
) -> List[language.SMTFormula]:
    """
    Returns a list of SMT formulas whose solutions address subtrees of other SMT
    formulas, but whose own substitution subtrees are in turn *not* referred by
    top-level substitution trees of other formulas. Those must be solved first to avoid
    inconsistencies.

    :param smt_formulas: The formulas to search for references to subtrees.
    :return: The list of conflicting formulas that must be solved first.
    """

    def subtree_ids(formula: language.SMTFormula) -> Set[int]:
        return {
            subtree.id
            for tree in formula.substitutions.values()
            for _, subtree in tree.paths()
            if subtree.id != tree.id
        }

    def tree_ids(formula: language.SMTFormula) -> Set[int]:
        return {tree.id for tree in formula.substitutions.values()}

    subtree_ids_for_formula: Dict[language.SMTFormula, Set[int]] = {
        formula: subtree_ids(formula) for formula in smt_formulas
    }

    tree_ids_for_formula: Dict[language.SMTFormula, Set[int]] = {
        formula: tree_ids(formula) for formula in smt_formulas
    }

    def independent_from_solutions_of_other_formula(
        idx: int, formula: language.SMTFormula
    ) -> bool:
        return all(
            not tree_ids_for_formula[other_formula].intersection(
                subtree_ids_for_formula[formula]
            )
            for other_idx, other_formula in enumerate(smt_formulas)
            if other_idx != idx
        )

    def refers_to_subtree_of_other_formula(
        idx: int, formula: language.SMTFormula
    ) -> bool:
        return any(
            tree_ids_for_formula[formula].intersection(
                subtree_ids_for_formula[other_formula]
            )
            for other_idx, other_formula in enumerate(smt_formulas)
            if other_idx != idx
        )

    result = [
        formula
        for idx, formula in enumerate(smt_formulas)
        if refers_to_subtree_of_other_formula(idx, formula)
        and independent_from_solutions_of_other_formula(idx, formula)
    ]

    return result


def compute_tree_closing_cost(tree: DerivationTree, graph: GrammarGraph) -> float:
    nonterminals = [leaf.value for _, leaf in tree.open_leaves()]
    return sum(
        [compute_symbol_costs(graph)[nonterminal] for nonterminal in nonterminals]
    )


def get_quantifier_chains(
    formula: language.Formula,
) -> List[Tuple[Union[language.QuantifiedFormula, language.ExistsIntFormula], ...]]:
    univ_toplevel_formulas = get_toplevel_quantified_formulas(formula)
    return [
        (f,) + c
        for f in univ_toplevel_formulas
        for c in (get_quantifier_chains(f.inner_formula) or [()])
    ]


def shortest_derivations(graph: gg.GrammarGraph) -> Dict[str, int]:
    def avg(it) -> int:
        elems = [elem for elem in it if elem is not None]
        return math.ceil(math.prod(elems) ** (1 / len(elems)))

    parent_relation = {node: set() for node in graph.all_nodes}
    for parent, child in graph.all_edges:
        parent_relation[child].add(parent)

    shortest_node_derivations: Dict[gg.Node, int] = {}
    stack: List[gg.Node] = graph.filter(lambda node: isinstance(node, gg.TerminalNode))
    while stack:
        node = stack.pop()

        old_min = shortest_node_derivations.get(node, None)

        if isinstance(node, gg.TerminalNode):
            shortest_node_derivations[node] = 0
        elif isinstance(node, gg.ChoiceNode):
            shortest_node_derivations[node] = max(
                shortest_node_derivations.get(child, 0) for child in node.children
            )
        elif isinstance(node, gg.NonterminalNode):
            assert not isinstance(node, gg.ChoiceNode)

            shortest_node_derivations[node] = (
                avg(
                    shortest_node_derivations.get(child, None)
                    for child in node.children
                )
                + 1
            )

        if (old_min or sys.maxsize) > shortest_node_derivations[node]:
            stack.extend(parent_relation[node])

    return {
        nonterminal: shortest_node_derivations[graph.get_node(nonterminal)]
        for nonterminal in graph.grammar
    }


@lru_cache()
def compute_symbol_costs(graph: GrammarGraph) -> Dict[str, int]:
    grammar = graph.to_grammar()
    canonical_grammar = canonical(grammar)

    result: Dict[str, int] = shortest_derivations(graph)

    nonterminal_parents = [
        nonterminal
        for nonterminal in canonical_grammar
        if any(
            is_nonterminal(symbol)
            for expansion in canonical_grammar[nonterminal]
            for symbol in expansion
        )
    ]

    # Sometimes this computation results in some nonterminals having lower cost values
    # than nonterminals that are reachable from those (but not vice versa), which is
    # undesired. We counteract this by assuring that on paths with at most one cycle
    # from the root to any nonterminal parent, the costs are strictly monotonically
    # decreasing.
    for nonterminal_parent in nonterminal_parents:
        # noinspection PyTypeChecker
        for path in all_paths(graph, graph.root, graph.get_node(nonterminal_parent)):
            for idx in reversed(range(1, len(path))):
                source: gg.Node = path[idx - 1]
                target: gg.Node = path[idx]

                if result[source.symbol] <= result[target.symbol]:
                    result[source.symbol] = result[target.symbol] + 1

    return result


def all_paths(
    graph,
    from_node: gg.NonterminalNode,
    to_node: gg.NonterminalNode,
    cycles_allowed: int = 2,
) -> List[List[gg.NonterminalNode]]:
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
            if (
                not isinstance(child, gg.NonterminalNode)
                or visited[child] > cycles_allowed + 1
            ):
                continue

            visited[child] += 1
            queue.append(p + [child])

    return [[n for n in p if not isinstance(n, gg.ChoiceNode)] for p in result]


def implies(
    f1: language.Formula, f2: language.Formula, grammar: Grammar, timeout_seconds=5
) -> bool:
    solver = ISLaSolver(
        grammar, f1 & -f2, activate_unsat_support=True, timeout_seconds=timeout_seconds
    )

    return (
        safe(solver.solve, exceptions=(StopIteration,))()
        .map(lambda _: False)
        .lash(lambda _: Success(True))
    ).unwrap()


def equivalent(
    f1: language.Formula, f2: language.Formula, grammar: Grammar, timeout_seconds=5
) -> bool:
    solver = ISLaSolver(
        grammar,
        -(f1 & f2 | -f1 & -f2),
        activate_unsat_support=True,
        timeout_seconds=timeout_seconds,
    )

    return (
        safe(solver.solve)()
        .map(lambda _: False)
        .lash(lambda e: Success(isinstance(e, StopIteration)))
    ).unwrap()


def generate_abstracted_trees(
    inp: DerivationTree, participating_paths: Set[Path]
) -> List[DerivationTree]:
    """
    Yields trees that are more and more "abstracted," i.e., pruned, at prefixes of the
    paths specified in `participating_paths`.

    :param inp: The unabstracted input.
    :param participating_paths: The paths to abstract.
    :return: A generator of more and more abstract trees, beginning with the most
    concrete and ending with the most abstract ones.
    """
    parent_paths: Set[ImmutableList[Path]] = {
        tuple(
            [tuple(path[:i]) for i in reversed(range(1, len(path) + 1))]
            if path
            else [()]
        )
        for path in participating_paths
    }

    abstraction_candidate_combinations: Set[ImmutableList[Path]] = {
        tuple(eliminate_suffixes(combination))
        for k in range(1, len(participating_paths) + 1)
        for paths in itertools.product(*parent_paths)
        for combination in itertools.combinations(paths, k)
    }

    result: Dict[int, DerivationTree] = {}
    for paths_to_abstract in abstraction_candidate_combinations:
        abstracted_tree = inp.substitute(
            {
                inp.get_subtree(path_to_abstract): DerivationTree(
                    inp.get_subtree(path_to_abstract).value
                )
                for path_to_abstract in paths_to_abstract
            }
        )
        result[abstracted_tree.structural_hash()] = abstracted_tree

    return sorted(result.values(), key=lambda tree: -len(tree))


class EvaluatePredicateFormulasTransformer(NoopFormulaTransformer):
    def __init__(self, inp: DerivationTree):
        super().__init__()
        self.inp = inp

    def transform_predicate_formula(
        self, sub_formula: language.StructuralPredicateFormula
    ) -> language.Formula:
        return sc.true() if sub_formula.evaluate(self.inp) else sc.false()

    def transform_conjunctive_formula(
        self, sub_formula: language.ConjunctiveFormula
    ) -> language.Formula:
        return reduce(language.Formula.__and__, sub_formula.args)

    def transform_disjunctive_formula(
        self, sub_formula: language.DisjunctiveFormula
    ) -> language.Formula:
        return reduce(language.Formula.__or__, sub_formula.args)

    def transform_smt_formula(
        self, sub_formula: language.SMTFormula
    ) -> language.Formula:
        # We instantiate the formula and check whether it evaluates to
        # True (or False in a negation scope); in that case, we replace
        # it by "true." Otherwise, we keep it for later analysis.

        instantiated_formula = copy.deepcopy(sub_formula)
        set_smt_auto_subst(instantiated_formula, True)
        set_smt_auto_eval(instantiated_formula, True)
        instantiated_formula = instantiated_formula.substitute_expressions(
            sub_formula.substitutions, force=True
        )

        assert instantiated_formula in {sc.true(), sc.false()}

        return (
            sc.true()
            if (instantiated_formula == sc.true()) ^ self.in_negation_scope
            else sub_formula
        )


def create_fixed_length_tree(
    start: DerivationTree | str,
    canonical_grammar: CanonicalGrammar,
    target_length: int,
) -> Optional[DerivationTree]:
    nullable = compute_nullable_nonterminals(canonical_grammar)
    start = DerivationTree(start) if isinstance(start, str) else start
    stack: List[
        Tuple[DerivationTree, int, ImmutableList[Tuple[Path, DerivationTree]]]
    ] = [
        (start, int(start.value not in nullable), (((), start),)),
    ]

    while stack:
        tree, curr_len, open_leaves = stack.pop()

        if not open_leaves:
            if curr_len == target_length:
                return tree
            else:
                continue

        if curr_len > target_length:
            continue

        idx: int
        path: Path
        leaf: DerivationTree
        for idx, (path, leaf) in reversed(list(enumerate(open_leaves))):
            terminal_expansions, expansions = get_expansions(
                leaf.value, canonical_grammar
            )

            if terminal_expansions:
                expansions.append(random.choice(terminal_expansions))

            # Only choose one random terminal expansion; keep all nonterminal expansions
            expansions = sorted(
                expansions,
                key=lambda expansion: len(
                    [elem for elem in expansion if is_nonterminal(elem)]
                ),
            )

            for expansion in reversed(expansions):
                new_children = tuple(
                    [
                        DerivationTree(elem, None if is_nonterminal(elem) else ())
                        for elem in expansion
                    ]
                )

                expanded_tree = tree.replace_path(
                    path,
                    DerivationTree(
                        leaf.value,
                        new_children,
                    ),
                )

                stack.append(
                    (
                        expanded_tree,
                        curr_len
                        + sum(
                            [
                                len(child.value)
                                if child.children == ()
                                else (1 if child.value not in nullable else 0)
                                for child in new_children
                            ]
                        )
                        - int(leaf.value not in nullable),
                        open_leaves[:idx]
                        + tuple(
                            [
                                (path + (child_idx,), new_child)
                                for child_idx, new_child in enumerate(new_children)
                                if is_nonterminal(new_child.value)
                            ]
                        )
                        + open_leaves[idx + 1 :],
                    )
                )

    return None


def subtree_solutions(
    solution: Dict[language.Constant | DerivationTree, DerivationTree]
) -> Dict[language.Variable | DerivationTree, DerivationTree]:
    solution_with_subtrees: Dict[
        language.Variable | DerivationTree, DerivationTree
    ] = {}
    for orig, subst in solution.items():
        if isinstance(orig, language.Variable):
            solution_with_subtrees[orig] = subst
            continue

        assert isinstance(
            orig, DerivationTree
        ), f"Expected a DerivationTree, given: {type(orig).__name__}"

        # Note: It can happen that a path in the original tree is not valid in the
        #       substitution, e.g., if we happen to replace a larger with a smaller
        #       tree.
        for path, tree in [
            (p, t)
            for p, t in orig.paths()
            if t not in solution_with_subtrees and subst.is_valid_path(p)
        ]:
            solution_with_subtrees[tree] = subst.get_subtree(path)

    return solution_with_subtrees
