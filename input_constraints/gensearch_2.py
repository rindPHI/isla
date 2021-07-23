import copy
import logging
from functools import reduce, lru_cache
from typing import Generator, Dict, List, Set, cast, Optional, Iterable, Iterator, Tuple

import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import canonical, EarleyParser
from grammar_graph.gg import GrammarGraph
from grammar_to_regex.cfg2regex import RegexConverter
from orderedset import OrderedSet

from input_constraints import isla
import input_constraints.isla_shortcuts as sc
from input_constraints.existential_helpers import insert_tree
from input_constraints.helpers import visit_z3_expr, delete_unreachable, z3_and
from input_constraints.isla import DerivationTree, VariablesCollector, inline_var_in_tree
from input_constraints.type_defs import Grammar, Path


class Assignment:
    def __init__(self, constant: isla.Constant, constraint: isla.Formula, tree: DerivationTree):
        self.constant = constant
        self.constraint = constraint
        self.tree = tree

    def formula_satisfied(self, grammar: Grammar) -> bool:
        constant, formula, tree = self

        if tree.is_open():
            # Have to instantiate variables first
            return False

        if tree.is_complete():
            formula = isla.replace_formula(
                formula,
                lambda f: isinstance(f, isla.QuantifiedFormula) and f.in_variable != constant,
                isla.SMTFormula(z3.BoolVal(True)))

            # All top-level predicates should be instantiated if we want to continue, i.e.,
            # they should have no constants as arguments (bound variables are OK)

            visitor = isla.FilterVisitor(
                lambda sub: isinstance(sub, isla.PredicateFormula)
                            and any(isinstance(arg, isla.Constant) for arg in sub.args)
            )

            if visitor.collect(formula):
                return False

            return isla.evaluate(formula, {constant: (tuple(), tree)})

        if isinstance(formula, isla.ForallFormula):
            # if the quantified nonterminal is not reachable from any nonterminal, we
            # already know that formula is vacuously satisfied!

            return not quantified_nonterminals_reachable(grammar, formula, tree)
        elif isinstance(formula, isla.SMTFormula):
            s = z3.Solver()
            s.add(z3.Not(formula.formula))
            s.set("timeout", 1000)
            return s.check() == z3.unsat

        return False

    def complete(self) -> bool:
        return not self.tree.is_abstract() and not self.tree.is_open()

    def __iter__(self):
        yield self.constant
        yield self.constraint
        yield self.tree

    def __hash__(self):
        return hash((self.constant, self.constraint, self.tree))

    def __eq__(self, other):
        return isinstance(other, Assignment) and self.__dict__ == other.__dict__

    def __repr__(self):
        return f"Assignment({self.constant}, {self.constraint}, {self.tree})"


class SolutionState:
    def __init__(self, assignments: Optional[List[Assignment]]):
        self.assignments = [] if assignments is None else assignments

    def complete(self) -> bool:
        return all(assgn.complete() for assgn in self)

    def variables(self) -> Set[isla.Variable]:
        result: Set[isla.Variable] = set()
        for constant, formula, tree in self:
            result.add(constant)
            result.update(isla.VariablesCollector().collect(formula))
            result.update(tree.tree_variables())
        return result

    def __getitem__(self, item: int) -> Assignment:
        assert isinstance(item, int)
        return self.assignments[item]

    def __setitem__(self, key: int, value: Assignment):
        assert isinstance(key, int)
        assert isinstance(value, Assignment)
        self.assignments[key] = value

    def __delitem__(self, key: int):
        del self.assignments[key]

    def append(self, item: Assignment):
        assert isinstance(item, Assignment)
        self.assignments.append(item)

    def extend(self, items: Iterable[Assignment]):
        self.assignments.extend(items)

    def len(self):
        return len(self.assignments)

    def pop(self):
        return self.assignments.pop(0)

    def __add__(self, other: 'SolutionState') -> 'SolutionState':
        return SolutionState(self.assignments + other.assignments)

    def __iter__(self) -> Iterator[Assignment]:
        return iter(self.assignments)

    def __hash__(self):
        return hash(tuple(self.assignments))

    def __eq__(self, other):
        return isinstance(other, SolutionState) and self.assignments == other.assignments

    def __repr__(self):
        return f"SolutionState({self.assignments})"

    def __str__(self):
        return "{(" + "), (".join(map(str, [f"{constant.name}, {formula}, \"{tree}\""
                                            for constant, formula, tree in self])) + ")}"


class ISLaSolver:
    def __init__(self,
                 grammar: Grammar,
                 formula: isla.Formula,
                 initial_derivation_tree: Optional[DerivationTree] = None,
                 max_number_free_instantiations: int = 10,
                 max_number_smt_instantiations: int = 10
                 ):
        self.grammar = grammar
        self.canonical_grammar = canonical(grammar)

        self.formula = formula
        self.initial_derivation_tree = initial_derivation_tree

        self.max_number_free_instantiations: int = max_number_free_instantiations
        self.max_number_smt_instantiations: int = max_number_smt_instantiations

        self.logger = logging.getLogger(type(self).__name__)

    def solve(self) -> Generator[Dict[isla.Constant, DerivationTree], None, None]:
        top_constants: Set[isla.Constant] = set(
            [c for c in VariablesCollector().collect(self.formula)
             if type(c) is isla.Constant])
        assert len(top_constants) > 0

        queue: OrderedSet[SolutionState] = OrderedSet([
            SolutionState([
                Assignment(
                    constant,
                    self.formula,
                    self.initial_derivation_tree or DerivationTree(constant.n_type, None))
                for constant in top_constants
            ])])

        while queue:
            state: SolutionState = queue.pop(last=False)
            self.logger.debug(f"Polling new state {state}")
            self.logger.debug(f"Queue length: {len(queue)}")

            # Choose the first assignment with a non-abstract tree and an open leaf.
            assignments = ([assgn for assgn in state if not assgn.tree.is_abstract() and assgn.tree.is_open()]
                           or [assgn for assgn in state if assgn.tree.is_open()]
                           or state[0]
                           )

            assignment = assignments[0]

            constant, formula, tree = assignment
            assert satisfies_invariant(formula, self.grammar)

            # First, instantiate all top-level predicate formulas.
            formula = instantiate_predicates(formula, tree)

            # If the formula is already a semantic formula, evaluate directly
            if is_semantic_formula(formula):
                new_states = self.eliminate_semantic_formula(constant, formula, formula, tree, state, top_constants)
                for new_state in new_states:
                    for result in self.process_new_state(new_state, queue, top_constants):
                        yield result

                continue

            for disjunct in split_disjunction(formula):
                conjuncts = split_conjunction(disjunct)

                non_smt_indices = [idx for idx, conjunct in enumerate(conjuncts)
                                   if not isinstance(conjunct, isla.SMTFormula)]
                semantic_prefix = conjuncts if not non_smt_indices else conjuncts[:non_smt_indices[0]]
                non_semantic_postfix = [] if not non_smt_indices else conjuncts[non_smt_indices[0]:]
                assert len(semantic_prefix) + len(non_semantic_postfix) == len(conjuncts)

                if semantic_prefix:
                    prefix_conjunction = reduce(lambda a, b: a & b, semantic_prefix)
                    new_disjunct = prefix_conjunction & reduce(lambda a, b: a & b, non_semantic_postfix)

                    new_states = self.eliminate_semantic_formula(constant, prefix_conjunction, new_disjunct, tree,
                                                                 state, top_constants)
                    for new_state in new_states:
                        for result in self.process_new_state(new_state, queue, top_constants):
                            yield result

                    continue

                applicable_existential_formulas = [formula for formula in non_semantic_postfix
                                                   if isinstance(formula, isla.ExistsFormula)
                                                   and formula.in_variable == constant]
                applicable_universal_formulas = [formula for formula in non_semantic_postfix
                                                 if isinstance(formula, isla.ForallFormula)
                                                 and formula.in_variable == constant]

                if applicable_existential_formulas:
                    existential_formula = applicable_existential_formulas[0]

                    new_states = self.eliminate_existential_formula(
                        constant, existential_formula, disjunct, tree, state)
                    assert new_states

                    for new_state in new_states:
                        for result in self.process_new_state(new_state, queue, top_constants):
                            yield result

                elif applicable_universal_formulas:
                    new_states = self.match_universal_formulas(
                        constant, applicable_universal_formulas, disjunct, tree, state)

                    for new_state in new_states:
                        for result in self.process_new_state(new_state, queue, top_constants):
                            yield result

                    if new_states:
                        continue

                new_states = self.expand_tree(constant, disjunct, tree, state)
                for new_state in new_states:
                    for result in self.process_new_state(new_state, queue, top_constants):
                        yield result

    def expand_tree(self,
                    constant: isla.Constant,
                    disjunct: isla.Formula,
                    tree: DerivationTree,
                    state: SolutionState) -> List[SolutionState]:
        result: List[SolutionState] = []

        expanded_trees = [tree]
        for leaf_path, (leaf_node, _) in tree.open_concrete_leaves():
            if self.can_be_freely_instantiated(leaf_path, tree, constant, disjunct):
                continue

            if any(conjunct.in_variable == constant
                   and conjunct.bound_variable.n_type == leaf_node
                   for conjunct in split_conjunction(disjunct)
                   if isinstance(conjunct, isla.QuantifiedFormula)):
                continue

            # Expand the leaf, check matching instantiations
            old_expanded_trees = copy.deepcopy(expanded_trees)
            expanded_trees = []
            for expanded_tree in old_expanded_trees:
                new_trees = self.expand_tree_at(expanded_tree, leaf_path, leaf_node)
                for new_tree in new_trees:
                    if new_tree in expanded_trees:
                        continue
                    expanded_trees.append(new_tree)

        for expanded_tree in expanded_trees:
            if expanded_tree == tree:
                continue
            new_state = SolutionState([assgn for assgn in state if assgn.constant != constant])
            new_state.append(Assignment(constant, disjunct, expanded_tree))
            result.append(new_state)

        return result

    def expand_tree_at(self, tree: DerivationTree, leaf_path: Path, leaf_node: str) -> List[DerivationTree]:
        expanded_trees: List[DerivationTree] = []

        for expansion in self.canonical_grammar[leaf_node]:
            tree = copy.deepcopy(tree)
            expanded_trees.append(
                tree.replace_path(leaf_path, DerivationTree.from_parse_tree(
                    (leaf_node, [
                        (child, None if is_nonterminal(child) else [])
                        for child in expansion
                    ]))))

        return expanded_trees

    def match_universal_formulas(self,
                                 constant: isla.Constant,
                                 universal_formulas: List[isla.ForallFormula],
                                 context_formula: isla.Formula,
                                 tree: DerivationTree,
                                 state: SolutionState) -> List[SolutionState]:
        new_state = SolutionState([assgn for assgn in state if assgn.constant != constant])
        new_tree = copy.deepcopy(tree)

        for universal_formula in universal_formulas:
            matches: List[Dict[isla.Variable, Tuple[Path, DerivationTree]]] = \
                isla.matches_for_quantified_variable(universal_formula, tree)

            # Only consider open leaves. Others are validly instantiated.
            # TODO: Maybe we have to generalize this
            matches = [match for match in matches if any(p[1].children is None for _, p in match.items())]

            if not matches:
                # As we generally don't expand nonterminals that match a quantifier, we have to do a manual
                # expansion here to proceed.
                formula_wo_bind_expr = sc.forall(
                    universal_formula.bound_variable, universal_formula.in_variable, universal_formula.inner_formula)
                if (universal_formula.bind_expression is not None
                        and (matches := isla.matches_for_quantified_variable(formula_wo_bind_expr, tree), matches)[-1]):
                    expanded_trees = [new_tree]
                    for match in matches:
                        leaf_path, leaf_node = match[universal_formula.bound_variable]
                        if leaf_node.children is not None:
                            continue

                        for expanded_tree in copy.deepcopy(expanded_trees):
                            expanded_trees.remove(expanded_tree)
                            expanded_trees.extend(self.expand_tree_at(expanded_tree, leaf_path, leaf_node.value))

                    if expanded_trees == [new_tree]:
                        return []

                    return [new_state + SolutionState([Assignment(constant, universal_formula, expanded_tree)])
                            for expanded_tree in expanded_trees]

                return []

            for match in matches:
                constant_subst_map = {}
                all_vars = state.variables()
                for variable in match:
                    new_constant = fresh_constant(all_vars,
                                                  isla.Constant(variable.name, variable.n_type))
                    constant_subst_map[variable] = new_constant
                    all_vars.add(new_constant)

                qfd_var_path = match[universal_formula.bound_variable][0]
                qfd_var_const = constant_subst_map[universal_formula.bound_variable]
                new_tree = new_tree.replace_path(qfd_var_path, DerivationTree(qfd_var_const, None))

                inst_formula = universal_formula.inner_formula.substitute_variables(
                    constant_subst_map)

                qfd_var_tree = match[universal_formula.bound_variable][1]
                for variable, (match_path, match_tree) in match.items():
                    if variable is not universal_formula.bound_variable:
                        new_constant = constant_subst_map[variable]
                        new_state.append(
                            Assignment(
                                new_constant,
                                isla.replace_formula(context_formula, universal_formula, inst_formula),
                                match_tree))

                        rel_path = match_path[len(qfd_var_path):]
                        qfd_var_tree = qfd_var_tree.replace_path(
                            rel_path, DerivationTree(new_constant, None))

                new_state.append(Assignment(qfd_var_const, inst_formula, qfd_var_tree))

        new_state.append(Assignment(constant, context_formula, new_tree))

        return [new_state]

    def eliminate_existential_formula(self,
                                      constant: isla.Constant,
                                      existential_formula: isla.ExistsFormula,
                                      context_formula: isla.Formula,
                                      tree: DerivationTree,
                                      state: SolutionState) -> List[SolutionState]:
        all_vars = state.variables()
        new_constant = fresh_constant(
            all_vars, isla.Constant(existential_formula.bound_variable.name,
                                    existential_formula.bound_variable.n_type))
        inserted_tree = DerivationTree(new_constant, None)
        insertion_result = insert_tree(self.canonical_grammar, inserted_tree, tree)

        if not insertion_result:
            return []

        result: List[SolutionState] = []
        for possible_tree in insertion_result:
            const_subst_map = {existential_formula.bound_variable: new_constant}

            if existential_formula.bind_expression is not None:
                _, bind_expr_paths = existential_formula.bind_expression.to_tree_prefix(
                    existential_formula.bound_variable.n_type, self.grammar)
                for bv in existential_formula.bind_expression.bound_variables():
                    const_subst_map[bv] = fresh_constant(
                        all_vars, isla.Constant(bv.name, bv.n_type))

            new_state = SolutionState([assgn for assgn in state if assgn.constant is not constant])
            inst_formula = existential_formula.inner_formula.substitute_variables(const_subst_map)
            new_state.append(
                Assignment(constant,
                           isla.replace_formula(context_formula, existential_formula, inst_formula),
                           possible_tree))

            if existential_formula.bind_expression is None:
                new_state.append(Assignment(new_constant, inst_formula,
                                            DerivationTree(new_constant.n_type, None)))
            else:
                bind_expr_tree, _ = existential_formula.bind_expression \
                    .substitute_variables(const_subst_map) \
                    .to_tree_prefix(
                    existential_formula.bound_variable.n_type,
                    self.grammar)
                new_state.append(Assignment(new_constant, inst_formula, bind_expr_tree))
                for bound_variable in existential_formula.bind_expression.bound_variables():
                    const_for_bv = const_subst_map[bound_variable]
                    new_state.append(Assignment(const_for_bv, inst_formula,
                                                DerivationTree(const_for_bv.n_type, None)))

            result.append(new_state)

        return result

    def eliminate_semantic_formula(self,
                                   constant: isla.Constant,
                                   semantic_formula: isla.Formula,
                                   context_formula: isla.Formula,
                                   tree: DerivationTree,
                                   state: SolutionState,
                                   top_constants: Set[isla.Constant]) -> List[SolutionState]:
        """
        Solves a semantic formula and, for each solution, substitutes the solution for the respective
        constant in each assignment of the state. Also instantiates all "free" constants in the given
        tree. The SMT solver is passed a regular expression approximating the language of the nonterminal
        of each considered constant. Returns an empty list for unsolvable constraints.

        :param top_constants:
        :param constant: The constant of the current assignment. Relevant for trivial constraints to generate
        the new state.
        :param semantic_formula: The semantic (i.e., only containing logical connectors and SMT Formulas)
        formula to solve.
        :param context_formula: The conjunctive formula inside which the given semantic formula occurs as a conjunct.
        Used for creating the resulting state: The conjunctive element is replaced with "true" inside the context.
        :param tree: The derivation tree of the current assignment. Used to obtain free constrants, and for creating
        the solution state for trivial SMT formulas.
        :param state: The original solution state. Used to access other assignments (with constant different
        from `constant`).
        :return: A list of instantiated SolutionStates.
        """

        solutions = self.solve_quantifier_free_formula(semantic_formula)

        free_constants = [c for c in tree.tree_variables()
                          if not any(assgn.constant == c for assgn in state if assgn.constant != constant)
                          and c not in context_formula.free_variables()]

        for _ in range(len(solutions)):
            solution = solutions.pop(0)
            fuzzer = GrammarCoverageFuzzer(self.grammar)
            for _ in range(self.max_number_free_instantiations):
                solutions.append(
                    solution | {c: DerivationTree.from_parse_tree(fuzzer.expand_tree((c.n_type, None)))
                                for c in free_constants})

        results = []
        for solution in solutions:
            if solution:
                new_state = SolutionState([
                    Assignment(constant, sc.true(), solution[constant])
                    for constant in solution
                    if constant in top_constants
                ])
                new_state.extend(substitute_assignment(
                    SolutionState([assgn for assgn in state if assgn.constant not in solution]),
                    solution))
            else:
                new_state = SolutionState([
                    Assignment(
                        constant,
                        isla.replace_formula(context_formula, semantic_formula, sc.true()), tree)])

                new_state.extend(substitute_assignment(
                    SolutionState([assgn for assgn in state if assgn.constant is not constant]),
                    solution))

            results.append(new_state)

        return results

    def solve_quantifier_free_formula(
            self, formula: isla.Formula) -> List[Dict[isla.Constant, DerivationTree]]:
        solutions: List[Dict[isla.Constant, DerivationTree]] = []

        for _ in range(self.max_number_smt_instantiations):
            solver = z3.Solver()
            constant_collector = VariablesCollector()
            constants: OrderedSet[isla.Constant] = OrderedSet(
                [c for c in constant_collector.collect(formula) if
                 type(c) is isla.Constant])

            for constant in constants:
                regex = self.extract_regular_expression(constant.n_type)
                solver.add(z3.InRe(z3.String(constant.name), regex))

            for prev_solution in solutions:
                for constant in prev_solution:
                    solver.add(z3.Not(constant.to_smt() == z3.StringVal(str(prev_solution[constant]))))

            solver.add(qfr_free_formula_to_z3_formula(formula))

            if solver.check() != z3.sat:
                if not solutions:
                    return []
                else:
                    return solutions

            new_solution = {
                constant: self.parse(constant.n_type, solver.model()[z3.String(constant.name)].as_string())
                for constant in constants}

            if new_solution in solutions:
                # This can happen for trivial solutions, i.e., if the formula is logically valid.
                # Then, the assignment for that constant will always be {}
                return solutions
            else:
                solutions.append(new_solution)

        return solutions

    def process_new_state(
            self,
            new_state: SolutionState,
            queue: OrderedSet[SolutionState],
            top_constants: Set[isla.Constant]) -> List[Dict[isla.Constant, DerivationTree]]:
        # TODO: Establish invariant
        new_state = self.inline(new_state, top_constants)

        if (new_state.len() == len(top_constants) and
                all(not assignment.tree.is_abstract() and
                    all(self.can_be_freely_instantiated(path, assignment.tree,
                                                        assignment.constant, assignment.constraint)
                        for path, _ in assignment.tree.open_concrete_leaves())
                    for assignment in new_state)):
            new_states = self.instantiate_free_nonterminals(new_state, top_constants)
        else:
            new_states = [new_state]

        result: List[Dict[isla.Constant, DerivationTree]] = []

        for new_state in new_states:
            if new_state.complete() and all(assgn.formula_satisfied(self.grammar) for assgn in new_state):
                assert {assgn.constant for assgn in new_state} == top_constants
                result.append({c: t for c, _, t in new_state})
                continue

            if new_state.complete():
                # If this never happens, we can drop the expensive satisfaction check above
                self.logger.debug(f"Created state is complete, but constraints not satisfied: {new_state}")

            self.logger.debug(f"Pushing new state {new_state}")
            self.logger.debug(f"Queue length: {len(queue)}")
            queue.add(new_state)

        return result

    def instantiate_free_nonterminals(
            self, new_state: SolutionState, top_constants: Set[isla.Constant]) -> OrderedSet[SolutionState]:
        """
        Instantiates free nonterminals up to the set bound if the state only consists of top assignments.

        :param new_state: The state to expand
        :param top_constants: The top-level constants
        :return: A new set of states
        """

        if new_state.len() != len(top_constants):
            return OrderedSet([new_state])

        result: OrderedSet[SolutionState] = OrderedSet([])
        candidates: OrderedSet[SolutionState] = OrderedSet([new_state])
        fuzzer = GrammarCoverageFuzzer(self.grammar)

        while candidates:
            candidate: SolutionState = candidates.pop(last=False)
            assignment: Assignment
            has_free_leaves = False
            for idx, assignment in enumerate(candidate):
                assert assignment.constant in top_constants

                for _ in range(self.max_number_free_instantiations):
                    new_tree = copy.deepcopy(assignment.tree)
                    for path, subtree in assignment.tree.open_concrete_leaves():
                        if not self.can_be_freely_instantiated(
                                path, assignment.tree, assignment.constant, assignment.constraint):
                            continue

                        has_free_leaves = True

                        nonterminal_instantiation = DerivationTree.from_parse_tree(
                            fuzzer.expand_tree((subtree.value, None)))
                        new_tree = new_tree.replace_path(path, nonterminal_instantiation)

                    if has_free_leaves:
                        candidates.add(SolutionState(
                            candidate.assignments[:idx] +
                            [Assignment(assignment.constant, assignment.constraint, new_tree)] +
                            candidate.assignments[idx + 1:]
                        ))

            if not has_free_leaves:
                result.add(candidate)

        return result

    def inline(self, new_state: SolutionState, top_constants: Set[isla.Constant]) -> SolutionState:
        new_state = copy.deepcopy(new_state)

        while True:
            inlining_possibilities = [
                (idx, to_inline, into_idx, into_assgn)
                for idx, to_inline in enumerate(new_state)
                for into_idx, into_assgn in enumerate(new_state)
                if idx != into_idx
                   and self.can_inline(
                    to_inline.constant, to_inline.constraint, to_inline.tree,
                    into_assgn.constraint, into_assgn.tree, top_constants)]

            if not inlining_possibilities:
                break

            to_inline = inlining_possibilities[0][1]
            idx = inlining_possibilities[0][0]
            inline_information = [
                (into_idx, into_assgn)
                for _, other_to_inline, into_idx, into_assgn in inlining_possibilities
                if other_to_inline == to_inline]

            for into_idx, into_assgn in inline_information:
                new_state[into_idx] = inline_state_element(into_assgn, to_inline)

            del new_state[idx]

        return new_state

    def can_inline(self,
                   constant: isla.Constant, constraint: isla.Formula, tree: DerivationTree,
                   into_constraint: isla.Formula, into_tree: DerivationTree,
                   top_constants: Set[isla.Constant]) -> bool:
        if (constant in top_constants
                or constant not in into_tree.tree_variables()
                or tree.is_abstract()):
            return False

        if tree.is_complete():
            return True

        if constant in constraint.free_variables() or constant in into_constraint.free_variables():
            return False

        leaf_nonterminal_paths = OrderedSet([path for path, _ in tree.open_concrete_leaves()])
        return all(self.can_be_freely_instantiated(path, tree, constant, constraint)
                   for path in leaf_nonterminal_paths)

    def can_be_freely_instantiated(self, path_to_nonterminal: Path, in_tree: DerivationTree,
                                   in_constant: isla.Constant, formula: isla.Formula) -> bool:
        matching_quantified_formulas = [
            conjunct for disjunct in split_disjunction(formula)
            for conjunct in split_conjunction(disjunct)
            if isinstance(conjunct, isla.QuantifiedFormula) and conjunct.in_variable == in_constant]
        nonterminal = in_tree.get_subtree(path_to_nonterminal).value

        for qfd_formula in matching_quantified_formulas:
            qfd_nonterminal = qfd_formula.bound_variable.n_type
            if qfd_nonterminal == nonterminal or self.reachable(nonterminal, qfd_nonterminal):
                return False

            if (qfd_formula.bind_expression is not None
                    and nonterminal in [var.n_type for var in qfd_formula.bind_expression.bound_variables()]):
                prefix_tree, _ = qfd_formula.bind_expression.to_tree_prefix(
                    qfd_formula.bound_variable.n_type, self.grammar, to_abstract_tree=False)
                for path, subtree in in_tree.path_iterator():
                    if len(path) >= len(path_to_nonterminal) or path != path_to_nonterminal[:len(path)]:
                        continue

                    if subtree.is_prefix(prefix_tree):
                        return False

                return True

        return True

    @lru_cache()
    def reachable(self, nonterminal: str, to_nonterminal: str) -> bool:
        graph = GrammarGraph.from_grammar(self.grammar)
        return graph.get_node(nonterminal).reachable(graph.get_node(to_nonterminal))

    @lru_cache()
    def extract_regular_expression(self, nonterminal: str) -> z3.ReRef:
        regex_conv = RegexConverter(self.grammar)
        return regex_conv.to_regex(nonterminal)

    def parse(self, nonterminal: str, input: str) -> DerivationTree:
        grammar = copy.deepcopy(self.grammar)
        grammar["<start>"] = [nonterminal]
        delete_unreachable(grammar)
        parser = EarleyParser(grammar)
        return DerivationTree.from_parse_tree(list(parser.parse(input))[0][1][0])


def satisfies_invariant(formula: isla.Formula, grammar: Grammar) -> bool:
    for disjunct in split_disjunction(formula):
        conjuncts = split_conjunction(disjunct)

        # Is in DNF:
        # No disjunction in side conjunction
        if any(isinstance(conjunct, isla.DisjunctiveFormula) for conjunct in conjuncts):
            return False

        # Only predicates inside negation; for SMT formulas, has to be pushed into formula
        if any(isinstance(conjunct, isla.NegatedFormula)
               and not isinstance(conjunct.args[0], isla.PredicateFormula)
               for conjunct in conjuncts):
            return False

        # SMT formulas must be atoms: No logical connectives & quantifiers inside
        for smt_formula in [formula for formula in conjuncts if isinstance(formula, isla.SMTFormula)]:
            for smt_sub in visit_z3_expr(smt_formula.formula):
                if isinstance(smt_sub, z3.QuantifierRef):
                    return False

        # Conjunct order:
        # 1. SMT Formulas, 2. Predicate formulas, 3. Existential, 4. Universal
        type_map = {
            isla.SMTFormula: 1,
            isla.PredicateFormula: 2,
            isla.ExistsFormula: 3,
            isla.ForallFormula: 4,
        }

        conjunct_types: List[int] = list(map(
            lambda conjunct: -1 if type(conjunct) not in type_map else type_map[type(conjunct)],
            conjuncts))

        # Nothing else permitted at this point
        if -1 in conjunct_types:
            return False

        # Right order
        if sorted(conjunct_types) != conjunct_types:
            return False

        # Structure of universal formulas:
        # At most one univ. formula at a time must much any given subtree.
        # That is, when considering the tree prefixes to which the formulas apply, no two of these
        # prefixes must equal or be prefixes of each other.

        universal_tree_prefixes: List[DerivationTree] = [
            DerivationTree(formula.bound_variable.n_type, None) if formula.bind_expression is None
            else cast(isla.BindExpression, formula.bind_expression).to_tree_prefix(
                formula.bound_variable.n_type, grammar, to_abstract_tree=False)[0]
            for formula in conjuncts
            if isinstance(formula, isla.ForallFormula)
        ]

        return all(not any(tree_1.is_prefix(tree_2)
                           for tree_2 in universal_tree_prefixes
                           if tree_2 is not tree_1)
                   for tree_1 in universal_tree_prefixes)

    return True


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
                                          isinstance(f, isla.PredicateFormula) or
                                          isinstance(f, isla.QuantifiedFormula))
    return not pred_qfr_visitor.collect(formula)


def instantiate_predicates(formula: isla.Formula, tree: DerivationTree) -> isla.Formula:
    # Note: The current interpretation of these Python (non-SMT) predicates is that they are *structural* predicate,
    #       i.e., they are only concerned about positions / paths and not about actual parse trees.
    #       This means that we can already evaluate them when they still contain constants, as long as the constants
    #       occur in the derivation tree.
    predicate_formulas = [
        conjunct
        for disjunct in split_disjunction(formula)
        for conjunct in split_conjunction(disjunct)
        if isinstance(conjunct, isla.PredicateFormula)]

    for predicate_formula in predicate_formulas:
        instantiation = isla.SMTFormula(z3.BoolVal(predicate_formula.evaluate(tree)))
        formula = isla.replace_formula(formula, predicate_formula, instantiation)

    return formula


def split_conjunction(formula: isla.Formula) -> List[isla.Formula]:
    if not type(formula) is isla.ConjunctiveFormula:
        return [formula]
    else:
        formula: isla.ConjunctiveFormula
        return [elem for arg in formula.args for elem in split_conjunction(arg)]


def split_disjunction(formula: isla.Formula) -> List[isla.Formula]:
    if not type(formula) is isla.DisjunctiveFormula:
        return [formula]
    else:
        formula: isla.DisjunctiveFormula
        return [elem for arg in formula.args for elem in split_disjunction(arg)]


def substitute_assignment(in_state: SolutionState,
                          assignment: Dict[isla.Constant, DerivationTree]) -> SolutionState:
    result: SolutionState = copy.deepcopy(in_state)
    for idx in range(in_state.len()):
        for constant, tree in assignment.items():
            assignment_const, assignment_formula, assignment_tree = result[idx]

            if assignment_const == constant:
                continue

            result[idx] = Assignment(
                assignment_const,
                assignment_formula.substitute_expressions({constant: tree}),
                inline_var_in_tree(assignment_tree, constant, tree))

    return result


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


def inline_state_element(into_assgn: Assignment, assgn_to_inline: Assignment) -> Assignment:
    variable, formula, tree = assgn_to_inline
    into_var, into_formula, into_tree = into_assgn

    new_formula = (formula.substitute_expressions({variable: tree}) &
                   into_formula.substitute_expressions({variable: tree}))
    new_tree = inline_var_in_tree(into_tree, variable, tree)

    return Assignment(into_var, new_formula, new_tree)
