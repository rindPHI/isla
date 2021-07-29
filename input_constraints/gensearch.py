import copy
import heapq
import logging
import random
from functools import lru_cache, reduce
from typing import Union, Optional, Dict, Tuple, List, Generator, Set, cast, Callable

import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.GrammarFuzzer import GrammarFuzzer, tree_to_string
from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import canonical, non_canonical, EarleyParser
from grammar_graph.gg import GrammarGraph
from grammar_to_regex.cfg2regex import RegexConverter
from orderedset import OrderedSet

from input_constraints import isla
from input_constraints.existential_helpers import insert_tree
from input_constraints.helpers import is_canonical_grammar, delete_unreachable, open_concrete_leaves, dfs
from input_constraints.isla import VariablesCollector, state_to_string, SolutionState, Assignment, inline_var_in_tree, \
    DerivationTree
from input_constraints.type_defs import CanonicalGrammar, Grammar, Path, AbstractTree

gensearch_logger = logging.getLogger("gensearch")


def substitute_assignment(in_state: SolutionState, assignment: Dict[isla.Constant, DerivationTree]) -> SolutionState:
    result: SolutionState = copy.deepcopy(in_state)
    for idx in range(len(in_state)):
        for constant, tree in assignment.items():
            assignment_const, assignment_formula, assignment_tree = result[idx]

            if assignment_const == constant:
                continue

            result[idx] = (assignment_const,
                           assignment_formula.substitute_expressions({constant: tree}),
                           inline_var_in_tree(assignment_tree, constant, tree))

    return result


def inline_state_element(state: SolutionState, state_to_inline: Assignment) -> SolutionState:
    result: SolutionState = []
    variable, formula, tree = state_to_inline
    for state_element in state:
        other_var, other_formula, other_tree = state_element
        new_formula = (formula.substitute_expressions({variable: tree}) &
                       other_formula.substitute_expressions({variable: tree}))
        new_tree = inline_var_in_tree(other_tree, variable, tree)

        result.append((other_var, new_formula, new_tree))
    return result


def merge_state_elements(state: SolutionState) -> Assignment:
    # TODO: If we have more than one initial constant, we won't end up in a singleton state
    state_elements: SolutionState = copy.deepcopy(state)

    while len(state_elements) > 1:
        state_elements = inline_state_element(state_elements[:-1], state_elements[-1])

    return state_elements[0]


def is_semantic_formula(formula: isla.Formula) -> bool:
    pred_for_visitor = isla.FilterVisitor(lambda f:
                                          isinstance(f, isla.PredicateFormula) or
                                          isinstance(f, isla.QuantifiedFormula))
    return not pred_for_visitor.collect(formula)


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
    return not tree.is_abstract() and not tree.is_open()


def complete_state(state: SolutionState) -> bool:
    return all(complete_assignment(assgn) for assgn in state)


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


def get_tree_constants(tree: AbstractTree) -> OrderedSet[isla.Constant]:
    result: OrderedSet[isla.Constant] = OrderedSet([])

    def action(arg: AbstractTree):
        node, children = arg
        if isinstance(node, isla.Constant):
            result.add(node)

    dfs(tree, action)

    return result


def quantified_nonterminals_reachable(grammar: Grammar, formula: isla.QuantifiedFormula, tree: DerivationTree) -> bool:
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


class ISLaSolver:
    def __init__(self,
                 grammar: Union[Grammar, CanonicalGrammar],
                 formula: isla.Formula,
                 max_number_free_instantiations: int = 10,
                 max_number_smt_instantiations: int = 10
                 ):
        self.grammar = grammar
        if is_canonical_grammar(grammar):
            self.grammar = grammar
        else:
            self.grammar = canonical(grammar)

        self.formula = formula

        self.max_number_free_instantiations: int = max_number_free_instantiations
        self.max_number_smt_instantiations: int = max_number_smt_instantiations
        self.queue_size_limit: Optional[int] = 80
        self.queue_no_removed_items: int = 40

        self.logger = logging.getLogger(type(self).__name__)

    def find_solution(self) -> Generator[Dict[isla.Constant, DerivationTree], None, None]:
        constant_collector = VariablesCollector()
        top_constants: Set[isla.Constant] = set(
            [c for c in constant_collector.collect(self.formula) if type(c) is isla.Constant])
        assert len(top_constants) > 0
        assert len(top_constants) == 1 or not isinstance(self.formula, isla.QuantifiedFormula)

        queue: List[Tuple[int, SolutionStateWrapper]] = []

        heapq.heappush(queue, (0, SolutionStateWrapper(
            [(constant, self.formula, DerivationTree(constant.n_type, None))
             for constant in top_constants])))

        while queue:
            _, state_wrapper = heapq.heappop(queue)
            state = state_wrapper.state
            self.logger.debug(f"Polling new state {state_to_string(state)}")
            self.logger.debug(f"Queue length: {len(queue)}")

            # Choose the first assignment with a non-abstract tree and an open leaf.
            if len(state) == 1:
                assignment = state[0]
            else:
                assignment = next((assgn for assgn in state
                                   if (tree := assgn[2], not tree.is_abstract() and tree.is_open())[-1]))
            constant, formula, tree = assignment

            # First, instantiate all top-level predicate formulas.
            formula = instantiate_predicates(formula, tree)

            # Release free tree constants
            free_constants = [c for c in tree.tree_variables()
                              if not any(assgn_const == c for assgn_const, _, _ in state)
                              and c not in formula.free_variables()]
            tree = tree.substitute({c: (c.n_type, None) for c in free_constants})

            # Check if we can just freely instantiate
            # TODO Extend to situation where there is more than one top constant
            if len(state) == 1 and not tree.is_abstract():
                fuzzer = GrammarCoverageFuzzer(non_canonical(self.grammar))
                for _ in range(self.max_number_free_instantiations):
                    inst_tree = DerivationTree.from_parse_tree(fuzzer.expand_tree(copy.deepcopy(tree)))
                    if isla.evaluate(formula, {constant: (tuple(), inst_tree)}):
                        yield {constant: inst_tree}
                    else:
                        break
                else:
                    # Already found sufficiently many instantiations
                    continue

            # Invariant: Formula is in DNF, and in each disjunction, exactly one quantifier of each type
            #            applies to any input element.
            # TODO: Check and enforce invariant

            if is_semantic_formula(formula):
                new_states = self.handle_semantic_formula(constant, formula, formula, tree, state)
                for new_state in new_states:
                    for result in self.process_new_state(state, new_state, queue, top_constants):
                        yield result

                continue

            for disjunctive_element in split_disjunction(formula):
                tree_changed = False

                for conjunctive_element in split_conjunction(disjunctive_element):
                    # TODO: Should we also enforce in the normal form that SMT formulas come before
                    #       universal formulas, which come before existential formulas?
                    if is_semantic_formula(conjunctive_element):
                        new_states = self.handle_semantic_formula(constant, conjunctive_element, disjunctive_element,
                                                                  tree, state)
                        for new_state in new_states:
                            tree_changed = True
                            for result in self.process_new_state(state, new_state, queue, top_constants):
                                yield result

                        break

                    elif isinstance(conjunctive_element, isla.ExistsFormula):
                        all_vars = all_variables(state)

                        new_constant = fresh_constant(
                            all_vars, isla.Constant(conjunctive_element.bound_variable.name,
                                                    conjunctive_element.bound_variable.n_type))
                        inserted_tree = DerivationTree(new_constant, None)
                        insertion_result = insert_tree(self.grammar, inserted_tree, tree)

                        if insertion_result:
                            # tree_changed = True

                            for possible_tree in insertion_result:
                                const_subst_map = {conjunctive_element.bound_variable: new_constant}

                                if conjunctive_element.bind_expression is not None:
                                    _, bind_expr_paths = conjunctive_element.bind_expression.to_tree_prefix(
                                        conjunctive_element.bound_variable.n_type, non_canonical(self.grammar))
                                    for bv in conjunctive_element.bind_expression.bound_variables():
                                        const_subst_map[bv] = fresh_constant(
                                            all_vars, isla.Constant(bv.name, bv.n_type))

                                new_state = [assgn for assgn in state if assgn is not assignment]
                                inst_formula = conjunctive_element.inner_formula.substitute_variables(const_subst_map)
                                new_state.append(
                                    (constant,
                                     replace_formula(disjunctive_element, conjunctive_element, inst_formula),
                                     possible_tree))

                                if conjunctive_element.bind_expression is None:
                                    new_state.append((new_constant, inst_formula,
                                                      DerivationTree(new_constant.n_type, None)))
                                else:
                                    bind_expr_tree, _ = conjunctive_element.bind_expression \
                                        .substitute_variables(const_subst_map) \
                                        .to_tree_prefix(
                                        conjunctive_element.bound_variable.n_type,
                                        non_canonical(self.grammar))
                                    new_state.append((new_constant, inst_formula, bind_expr_tree))
                                    for bound_variable in conjunctive_element.bind_expression.bound_variables():
                                        const_for_bv = const_subst_map[bound_variable]
                                        new_state.append((const_for_bv, inst_formula,
                                                          DerivationTree(const_for_bv.n_type, None)))

                                # NOTE: The implemented procedure implies that we only yield a finite amount of
                                #       instantiations, which may come unexpected if the top-level formula is
                                #       existential. To avoid this, we have to add further expansions of the quantified
                                #       formula, and make sure to only yield formulas after an additional validity
                                #       check. This is because the expanded tree might be complete and therefore
                                #       yielded without further check.

                                for result in self.process_new_state(state, new_state, queue, top_constants):
                                    yield result

                            break

                        continue

                    elif isinstance(conjunctive_element, isla.ForallFormula):
                        if conjunctive_element.in_variable != constant:
                            continue

                        matches: List[Dict[isla.Variable, Tuple[Path, DerivationTree]]] = \
                            isla.matches_for_quantified_variable(conjunctive_element, tree)
                        new_tree = copy.deepcopy(tree)

                        # Only consider open leaves. Others are validly instantiated.
                        # TODO: Maybe we have to generalize this
                        matches = [match for match in matches if any(p[1].children is None for _, p in match.items())]

                        if matches:
                            tree_changed = True

                            new_state = [assgn for assgn in state if assgn is not assignment]

                            for match in matches:
                                constant_subst_map = {}
                                all_vars = all_variables(state)
                                for variable in match:
                                    new_constant = fresh_constant(all_vars,
                                                                  isla.Constant(variable.name, variable.n_type))
                                    constant_subst_map[variable] = new_constant
                                    all_vars.add(new_constant)

                                qfd_var_path = match[conjunctive_element.bound_variable][0]
                                qfd_var_const = constant_subst_map[conjunctive_element.bound_variable]
                                new_tree = new_tree.replace_path(qfd_var_path, DerivationTree(qfd_var_const, None))

                                inst_formula = conjunctive_element.inner_formula.substitute_variables(
                                    constant_subst_map)

                                qfd_var_tree = match[conjunctive_element.bound_variable][1]
                                for variable, (match_path, match_tree) in match.items():
                                    if variable is not conjunctive_element.bound_variable:
                                        new_constant = constant_subst_map[variable]
                                        new_state.append((new_constant,
                                                          replace_formula(formula, conjunctive_element, inst_formula),
                                                          match_tree))

                                        rel_path = match_path[len(qfd_var_path):]
                                        qfd_var_tree = qfd_var_tree.replace_path(
                                            rel_path, DerivationTree(new_constant, None))

                                new_state.append((qfd_var_const, inst_formula, qfd_var_tree))

                            new_state.append((constant, formula, new_tree))
                            for result in self.process_new_state(state, new_state, queue, top_constants):
                                yield result

                            continue
                    else:
                        assert False, f"Unsupported formula type {type(formula).__name__}"

                if tree_changed:
                    continue

                # Expand.

                expanded_trees = [tree]
                for leaf_path, (leaf_node, _) in tree.open_concrete_leaves():
                    # We do not expand nonterminals for which we are sure that they can be freely instantiated,
                    # which are those that are not reachable by nonterminals quantified over by any top level
                    # quantifier in disjunctive_element
                    if self.can_be_freely_instantiated(leaf_node, disjunctive_element, constant):
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
                    new_state: SolutionState = [assgn for assgn in state if assgn[0] != constant]
                    new_state.append((constant, disjunctive_element, expanded_tree))
                    # Must not yield here, since quantifiers have to be matched before!
                    self.process_new_state(state, new_state, queue, top_constants)

    def can_be_freely_instantiated(self, nonterminal: str, conjunctive_formula: isla.Formula,
                                   constant: isla.Constant) -> bool:
        qfd_nonterminals = {conj.bound_variable.n_type
                            for conj in split_conjunction(conjunctive_formula)
                            if isinstance(conj, isla.QuantifiedFormula) and conj.in_variable == constant}
        can_be_freely_instantiated = (not any(qfd_nonterminal == nonterminal or
                                              self.reachable(nonterminal, qfd_nonterminal)
                                              for qfd_nonterminal in qfd_nonterminals))
        return can_be_freely_instantiated

    def handle_semantic_formula(self,
                                constant: isla.Constant,
                                formula: isla.Formula,
                                context_formula: isla.Formula,
                                tree: DerivationTree,
                                state: SolutionState) -> List[SolutionState]:
        # TODO: Might have to stall such a formula if other, quantified,
        #       formulas referring to variables in this formula are not
        #       yet instantiated. We first process quantifiers, then the atoms.
        # TODO: Check whether this is actually true, find example!

        # free_constants = [c for c in get_tree_constants(tree)
        #                   if not any(assgn_const == c for assgn_const, _, _ in state)
        #                   and c not in formula.free_variables()]
        # TODO Cleanup / remove if really not needed
        free_constants = []
        solutions = self.solve_quantifier_free_formula(formula, OrderedSet(free_constants))

        # None solution ==> Unsolvable constraint... Nothing more to do here.
        solutions = [] if solutions is None else solutions

        results = []
        for solution in solutions:
            if solution:
                new_state: SolutionState = [(c, replace_formula(context_formula,
                                                                formula,
                                                                isla.SMTFormula(z3.BoolVal(True))), solution[c])
                                            for c in solution]

                new_state.extend(substitute_assignment([assgn for assgn in state
                                                        if assgn[0] not in solution], solution))
            else:
                new_state: SolutionState = [(constant, replace_formula(context_formula,
                                                                       formula,
                                                                       isla.SMTFormula(z3.BoolVal(True))), tree)]

                new_state.extend(substitute_assignment([assgn for assgn in state
                                                        if assgn[0] is not constant], solution))

            results.append(new_state)

        return results

    def solve_quantifier_free_formula(self, formula: isla.Formula,
                                      free_constants: OrderedSet[isla.Constant]) -> \
            Optional[List[Dict[isla.Constant, DerivationTree]]]:
        solutions: List[Dict[isla.Constant, DerivationTree]] = []

        for _ in range(self.max_number_smt_instantiations):
            solver = z3.Solver()
            constant_collector = VariablesCollector()
            constants: OrderedSet[isla.Constant] = OrderedSet([c for c in constant_collector.collect(formula) if
                                                               type(c) is isla.Constant]) | free_constants

            for constant in constants:
                regex = self.extract_regular_expression(constant.n_type)
                solver.add(z3.InRe(z3.String(constant.name), regex))

            for prev_solution in solutions:
                for constant in prev_solution:
                    solver.add(z3.Not(constant.to_smt() == z3.StringVal(tree_to_string(prev_solution[constant]))))

            solver.add(qfr_free_formula_to_z3_formula(formula))

            if solver.check() != z3.sat:
                if not solutions:
                    return None
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

    def get_open_relevant_leaves(self, formula: isla.QuantifiedFormula, tree: AbstractTree) -> \
            Generator[Tuple[Path, AbstractTree], None, None]:
        assert isinstance(formula, isla.QuantifiedFormula)

        qfd_nonterminals = [formula.bound_variable.n_type]
        if formula.bind_expression is not None:
            qfd_nonterminals.extend([variable.n_type for variable in formula.bind_expression.bound_variables()])

        for pair in open_concrete_leaves(tree):
            _, (node, _) = pair
            if any(self.reachable(node, qfd_nonterminal) for qfd_nonterminal in qfd_nonterminals):
                yield pair

    def expand_tree_at(self, tree, leaf_path, leaf_node) -> List[DerivationTree]:
        expanded_trees: List[DerivationTree] = []

        for expansion in self.grammar[leaf_node]:
            # TODO: Only expand nonterminals from which the nonterminal of the quantified variable
            #       can be reached. Also inline incomplete trees in that case. Batch-expand later on.
            tree = copy.deepcopy(tree)
            expanded_trees.append(tree.replace_path(leaf_path, DerivationTree.from_parse_tree((leaf_node, [
                (child, None if is_nonterminal(child) else []) for child in expansion
            ]))))

        return expanded_trees

    def process_new_state(self, orig_state: SolutionState, state: SolutionState,
                          queue: List[Tuple[int, 'SolutionStateWrapper']],
                          top_constants: Set[isla.Constant]) -> List[Dict[isla.Constant, DerivationTree]]:
        state = self.cleanup_state(state, top_constants)

        if all(self.formula_satisfied(assgn) for assgn in state):
            if complete_state(state):
                return [{c: t for c, _, t in state}]

            complete_assignments = [assgn for assgn in state if complete_assignment(assgn)]

            fuzzer = GrammarCoverageFuzzer(non_canonical(self.grammar))
            result = []
            for _ in range(self.max_number_free_instantiations):
                all_complete_assignments = copy.deepcopy(complete_assignments)
                all_complete_assignments.extend([
                    (constant, isla.SMTFormula(z3.BoolVal(True)), fuzzer.expand_tree(copy.deepcopy(tree)))
                    for constant, _, tree in [assgn for assgn in state if assgn not in complete_assignments]
                ])

                result.append({c: t for c, _, t in all_complete_assignments})

            return result

        if state == orig_state:
            return []

        top_constant_assignments = [assgn for assgn in state if assgn[0] in top_constants]
        heuristic_value = sum([100 - self.compute_heuristic_value(assgn)
                               for assgn in top_constant_assignments]
                              ) // len(top_constant_assignments)

        if self.queue_size_limit is not None and len(queue) > self.queue_size_limit:
            self.logger.debug(f"Balancing queue")
            nlargest = heapq.nlargest(self.queue_no_removed_items, queue)
            for elem in nlargest:
                queue.remove(elem)
            heapq.heapify(queue)

        heapq.heappush(queue, (heuristic_value, SolutionStateWrapper(state)))

        self.logger.debug(f"Pushing new state {state_to_string(state)}")
        self.logger.debug(f"Queue length: {len(queue)}")
        return []

    def cleanup_state(self, state: SolutionState, top_constants: Set[isla.Constant]) -> SolutionState:
        """Inlines all complete non-top-level assignments and removes formula conjuncts
        if unrelated to assignment constant"""
        new_state: SolutionState = copy.deepcopy(state)

        # Simplify formulas:
        # - Remove universal formulas if nonterminal of the "in" variable is not reachable in the tree and
        #   either the constant is top-level, or equals the "in" variable.
        # - Remove existential formula if already satisfied, or replace with false if quantified nonterminal
        #   is not reachable in tree, and (in both cases) either the constant is top-level, or equals the "in" variable.
        # - Remove any quantified formula (replacement with true for universal formulas, and false for existential)
        #   if the assignment constant is top, and the "in" variable of the formula neither equals the assignment
        #   constant nor appears in the tree.

        # PROBLEM: We must not remove quantified formulas, since we extend trees for existential
        #          quantifiers and then, quantified nonterminals might be reachable again!

        # for idx, assignment in enumerate(state):
        #    constant, formula, tree = assignment

        #    for conjunctive_element in split_conjunction(formula):
        #        if not isinstance(conjunctive_element, isla.QuantifiedFormula):
        #            continue

        #        if constant not in top_constants and constant != conjunctive_element.in_variable:
        #            continue

        #        # Remove formula (true for univ, false for exist) if constant is top
        #        # and "in" variable is not present in tree.
        #        if (constant in top_constants
        #                and conjunctive_element.in_variable != constant
        #                and constant not in isla.tree_variables(tree)):
        #            new_state[idx] = (constant,
        #                              replace_formula(formula, conjunctive_element,
        #                                              isla.SMTFormula(
        #                                                  z3.BoolVal(isinstance(conjunctive_element,
        #                                                                        isla.ForallFormula)))),
        #                              tree)
        #            continue

        #        qfd_nonterm_reachable = quantified_nonterminals_reachable(non_canonical(self.grammar),
        #                                                                  conjunctive_element, tree)

        #        if isinstance(conjunctive_element, isla.ForallFormula):
        #            if not qfd_nonterm_reachable:
        #                new_state[idx] = constant, replace_formula(formula, conjunctive_element, sc.true()), tree

        #        if isinstance(formula, isla.ExistsFormula):
        #            # TODO Check satisfaction (on potentially abstract tree!)
        #            if not qfd_nonterm_reachable:
        #                # TODO Should we rather not return a state instead of one with a False constraint?
        #                new_state[idx] = constant, replace_formula(formula, conjunctive_element, sc.false()), tree

        def can_inline(state: SolutionState, constant: isla.Constant, formula: isla.Formula, tree: DerivationTree,
                       into_constant: isla.Constant, into_formula: isla.Formula, into_tree: DerivationTree) -> bool:
            # TODO: We must only inline if 1) tree is concrete and formula is not an existential quantifier
            #       which can be solved at the level of the given assignment, and 2) the constraint cannot
            #       be solved at that level, e.g., because the quantifier refers to another constant.
            if constant in top_constants:
                return False

            if constant not in into_tree.tree_variables():
                return False

            # state_constants = [const for const, _, _ in state]
            # if ((not tree.is_abstract() or all(tree_constant not in state_constants
            #                                   for tree_constant in tree.tree_variables()))
            #        and all(self.can_be_freely_instantiated(leaf_node, formula, constant)
            #                for _, (leaf_node, _) in tree.open_concrete_leaves())):
            #    return True

            if tree.is_complete() and not (isinstance(formula, isla.ExistsFormula)
                                           and cast(isla.ExistsFormula, formula).in_variable == constant
                                           and tree == (constant, None)):
                return True

            # TODO Also do something similar for universal formulas! E.g.,:
            #      ($lhs_1_0, ∀ $var ∈ $rhs_1_0: (∃ '$lhs_2 " := " $rhs_2' = $assgn_2 ∈ $start:
            #          ((before($assgn_2, $assgn_1_0) ∧ $lhs_2 == $var))), "<var>")
            if (isinstance(formula, isla.ExistsFormula)
                    and cast(isla.ExistsFormula, formula).in_variable != constant
                    and tree == (constant.n_type, None)):
                return True

            return False

        try:
            while True:
                idx, to_inline, into_idx, into = next(((idx, assgn, into_idx, into_assgn)
                                                       for idx, assgn in enumerate(new_state)
                                                       for into_idx, into_assgn in enumerate(new_state)
                                                       if idx != into_idx
                                                       and can_inline(new_state, *assgn, *into_assgn)))
                if to_inline[2] == (to_inline[0].n_type, None):
                    new_state[into_idx] = inline_state_element([into], (to_inline[0],
                                                                        to_inline[1],
                                                                        DerivationTree(to_inline[0], None)))[0]
                else:
                    new_state[into_idx] = inline_state_element([into], to_inline)[0]
                del new_state[idx]
        except StopIteration:
            pass

        # Remove non-top level constant assignments that do not occur in any other tree

        obsolete_constants = {constant for constant, _, _ in new_state
                              if constant not in top_constants and
                              all(constant not in other_tree.tree_variables()
                                  for other_const, _, other_tree in new_state
                                  if constant != other_const)}

        new_state = [(constant, formula, tree)
                     for constant, formula, tree in new_state
                     if constant not in obsolete_constants]

        for idx, (constant, formula, tree) in enumerate(new_state):
            old_formula = formula
            formula = replace_formula(formula,
                                      lambda f: (isinstance(f, isla.QuantifiedFormula)
                                                 and f.in_variable in obsolete_constants),
                                      isla.SMTFormula(z3.BoolVal(True)))
            if old_formula != formula:
                new_state[idx] = (constant, formula, tree)

        # TODO: Enforce invariant (see find_solution function)

        return new_state

    def reachable(self, nonterminal: str, to_nonterminal: str) -> bool:
        graph = GrammarGraph.from_grammar(non_canonical(self.grammar))
        return graph.get_node(nonterminal).reachable(graph.get_node(to_nonterminal))

    def formula_satisfied(self, assignment: Assignment) -> bool:
        constant, formula, tree = assignment

        if tree.is_open():
            # Have to instantiate variables first
            return False

        if tree.is_complete():
            formula = replace_formula(formula,
                                      lambda f: isinstance(f, isla.QuantifiedFormula) and f.in_variable != constant,
                                      isla.SMTFormula(z3.BoolVal(True)))
            # TODO: Check if we need a non-trivial path here...
            result = isla.evaluate(formula, {constant: (tuple(), tree)})
            return result

        if isinstance(formula, isla.ForallFormula):
            # if the quantified nonterminal is not reachable from any nonterminal, we
            # already know that formula is vacuously satisfied!

            return not quantified_nonterminals_reachable(non_canonical(self.grammar), formula, tree)
        elif isinstance(formula, isla.SMTFormula):
            s = z3.Solver()
            s.add(z3.Not(formula.formula))
            s.set("timeout", 1000)
            return s.check() == z3.unsat

        return False

    @lru_cache()
    def extract_regular_expression(self, nonterminal: str) -> z3.ReRef:
        regex_conv = RegexConverter(non_canonical(self.grammar))
        return regex_conv.to_regex(nonterminal)

    def parse(self, nonterminal: str, input: str) -> DerivationTree:
        grammar = copy.deepcopy(non_canonical(self.grammar))
        grammar["<start>"] = [nonterminal]
        delete_unreachable(grammar)
        parser = EarleyParser(grammar)
        return DerivationTree.from_parse_tree(list(parser.parse(input))[0][1][0])

    def compute_heuristic_value(self, state: Assignment) -> int:
        """
        Computes a heuristic value between 0 (worst) and 100 (best) describing the quality of the present solution.
        Criteria are the cost of the expansion, and to what degree the constraint is satisfied (TODO).
        """
        constant, formula, tree = state
        symbols = set([pair[1].value for pair in tree.open_concrete_leaves()])

        if not symbols:
            return 100

        fuzzer = GrammarFuzzer(non_canonical(self.grammar))
        expansion_cost = max([fuzzer.symbol_cost(symbol) for symbol in symbols])

        # Normalization: We assume a maximum expansion cost of 20, and normalize with respect to that.
        # The result is scaled to the range 0 -- 100 and inverted, since 100 should be a "good" value
        max_value = 20
        normalized_depth_value = 100 - round((min(expansion_cost, max_value) / max_value) * 100)
        assert 0 <= normalized_depth_value <= 100

        # TODO: Add heuristics based on formula: E.g., disjunctions more expensive.

        return normalized_depth_value


def instantiate_predicates(formula: isla.Formula, tree: DerivationTree) -> isla.Formula:
    if isinstance(formula, isla.PredicateFormula):
        if any(isinstance(arg, isla.Variable) for arg in formula.args):
            return formula

        return isla.SMTFormula(z3.BoolVal(formula.evaluate(tree)))

    if isinstance(formula, isla.ConjunctiveFormula):
        return reduce(lambda a, b: a & b, [instantiate_predicates(child, tree) for child in formula.args])

    if isinstance(formula, isla.DisjunctiveFormula):
        return reduce(lambda a, b: a | b, [instantiate_predicates(child, tree) for child in formula.args])

    return formula


def replace_formula(in_formula: isla.Formula,
                    to_replace: Union[isla.Formula, Callable[[isla.Formula], Union[bool, isla.Formula]]],
                    replace_with: Optional[isla.Formula] = None) -> isla.Formula:
    """
    Replaces a formula inside a conjunction or disjunction.
    to_replace is either (1) a formula to replace, or (2) a predicate which holds if the given formula
    should been replaced (if it returns True, replace_with must not be None), or (3) a function returning
    the formula to replace if the subformula should be replaced, or False otherwise. For (3), replace_with
    may be None (it is irrelevant).
    """

    if callable(to_replace):
        result = to_replace(in_formula)
        if isinstance(result, isla.Formula):
            return result

        assert type(result) is bool
        if to_replace(in_formula):
            assert replace_with is not None
            return replace_with
    else:
        if in_formula == to_replace:
            return replace_with

    if isinstance(in_formula, isla.ConjunctiveFormula):
        return reduce(lambda a, b: a & b, [replace_formula(child, to_replace, replace_with)
                                           for child in in_formula.args])
    elif isinstance(in_formula, isla.DisjunctiveFormula):
        return reduce(lambda a, b: a | b, [replace_formula(child, to_replace, replace_with)
                                           for child in in_formula.args])

    return in_formula


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


class SolutionStateWrapper:
    def __init__(self, state: SolutionState):
        self.state = state

    def __hash__(self):
        return hash(tuple(self.state))

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
