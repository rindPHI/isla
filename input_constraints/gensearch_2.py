import copy
import logging
from functools import reduce, lru_cache
from typing import Generator, Dict, List, Set, cast, Optional, Iterable, Iterator, Tuple, Union

import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import canonical, EarleyParser
from grammar_graph.gg import GrammarGraph
from grammar_to_regex.cfg2regex import RegexConverter
from orderedset import OrderedSet

import input_constraints.isla_shortcuts as sc
from input_constraints import isla
from input_constraints.existential_helpers import insert_tree
from input_constraints.helpers import visit_z3_expr, delete_unreachable, dict_of_lists_to_list_of_dicts
from input_constraints.isla import DerivationTree, VariablesCollector, inline_var_in_tree
from input_constraints.type_defs import Grammar, Path


class SolutionState:
    def __init__(self, constraint: isla.Formula, tree: DerivationTree,
                 already_matched: Optional[Dict[isla.QuantifiedFormula, Set[int]]] = None):
        self.constraint = constraint
        self.tree = tree
        self.already_matched: Dict[isla.QuantifiedFormula, Set[int]] = already_matched or {}

    def add_already_matched(self, formula: isla.QuantifiedFormula, tree: DerivationTree):
        self.already_matched.setdefault(formula, set()).add(tree.id)

    def is_already_matched(self, formula: isla.QuantifiedFormula, tree: DerivationTree) -> bool:
        return tree.id in self.already_matched.setdefault(formula, set())

    def formula_satisfied(self, grammar: Grammar) -> bool:
        formula, tree = self

        if tree.is_open():
            # Have to instantiate variables first
            return False

        if tree.is_complete():
            eval_result = isla.evaluate(formula, {})
            # TODO: This should in principle always evaluate to True. Remove evaluation if this holds for tests.
            assert eval_result
            return eval_result

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
        # A complete state
        # 1) has a complete tree
        # 2) has complete top-level formulas. A complete formula
        #    2.1) does not contain top-level predicate formulas,
        #    2.2) equals "True" or does not contain top-level SMT formulas, and
        #    2.3) all "in" expressions of quantified top-level formulas must be complete trees.
        if not self.tree.is_complete():
            return False

        conjuncts = get_conjuncts(self.constraint)
        if conjuncts == [sc.true()]:
            return True

        return (all(not isinstance(conjunct, isla.SMTFormula) for conjunct in conjuncts)
                and all(not isinstance(conjunct, isla.PredicateFormula) for conjunct in conjuncts)
                and all(not isinstance(conjunct, isla.QuantifiedFormula)
                        or (isinstance(conjunct.in_variable, DerivationTree)
                            and conjunct.in_variable.is_complete())
                        for conjunct in conjuncts)
                )

    def variables(self) -> Set[isla.Variable]:
        result: Set[isla.Variable] = set()
        for constant, formula, tree in self:
            result.update(isla.VariablesCollector().collect(formula))
            result.update(tree.tree_variables())
        return result

    def __iter__(self):
        yield self.constraint
        yield self.tree

    def __hash__(self):
        return hash((self.constraint, self.tree))

    def __eq__(self, other):
        return isinstance(other, SolutionState) and self.__dict__ == other.__dict__

    def __repr__(self):
        return f"SolutionState({repr(self.constraint)}, {repr(self.tree)})"

    def __str__(self):
        return f"{{{self.constraint}, {self.tree}}}"


class ISLaSolver:
    def __init__(self,
                 grammar: Grammar,
                 formula: isla.Formula,
                 max_number_free_instantiations: int = 10,
                 max_number_smt_instantiations: int = 10
                 ):
        self.grammar = grammar
        self.canonical_grammar = canonical(grammar)

        self.formula = formula

        self.max_number_free_instantiations: int = max_number_free_instantiations
        self.max_number_smt_instantiations: int = max_number_smt_instantiations

        self.logger = logging.getLogger(type(self).__name__)

    def solve(self) -> Generator[DerivationTree, None, None]:
        top_constants: Set[isla.Constant] = set(
            [c for c in VariablesCollector().collect(self.formula)
             if type(c) is isla.Constant])
        assert len(top_constants) == 1

        top_constant = next(iter(top_constants))
        initial_tree = DerivationTree(top_constant.n_type, None)
        initial_formula = self.formula.substitute_expressions({top_constant: initial_tree})
        queue: OrderedSet[SolutionState] = OrderedSet([
            SolutionState(initial_formula, initial_tree, already_matched={})
        ])

        while queue:
            state: SolutionState = queue.pop(last=False)
            self.logger.debug(f"Polling new state {state}")
            self.logger.debug(f"Queue length: {len(queue)}")

            formula = state.constraint
            tree = state.tree
            # TODO: Relax invariant. Maybe: DNF, negations moved inside etc., but no restrictions on the quantifiers.
            # assert satisfies_invariant(formula, self.grammar)

            # Split disjunctions
            if isinstance(formula, isla.DisjunctiveFormula):
                queue.update([SolutionState(disjunct, tree) for disjunct in split_disjunction(formula)])
                continue

            # Instantiate all top-level predicate formulas.
            formula = instantiate_predicates(formula, tree)

            # Eliminate all semantic formulas
            if (results := self.eliminate_all_semantic_formulas(formula, state, queue)) is not None:
                yield from results
                continue

            # Eliminate first existential formula
            yield from self.eliminate_first_existential_formula(formula, state, queue)

            # Match all universal formulas
            if (results := self.match_all_universal_formulas(formula, state, queue)) is not None:
                yield from results
                continue

            # Expand the tree
            yield from [result for new_state in self.expand_tree(formula, state)
                        for result in self.process_new_state(new_state, queue)]

    def eliminate_all_semantic_formulas(self,
                                        formula: isla.Formula,
                                        state: SolutionState,
                                        queue: OrderedSet[SolutionState]) -> Optional[List[DerivationTree]]:
        conjuncts = split_conjunction(formula)
        semantic_formulas = [conjunct for conjunct in conjuncts if isinstance(conjunct, isla.SMTFormula)]

        if not semantic_formulas:
            return None

        prefix_conjunction = reduce(lambda a, b: a & b, semantic_formulas, sc.true())
        new_disjunct = (
                prefix_conjunction &
                reduce(lambda a, b: a & b,
                       [conjunct for conjunct in conjuncts if conjunct not in semantic_formulas],
                       sc.true()))

        return [result
                for new_state in self.eliminate_semantic_formula(prefix_conjunction, new_disjunct, state)
                for result in self.process_new_state(new_state, queue)]

    def eliminate_first_existential_formula(self,
                                            formula: isla.Formula,
                                            state: SolutionState,
                                            queue: OrderedSet[SolutionState]) -> List[DerivationTree]:
        existential_formulas = [
            conjunct for conjunct in split_conjunction(formula)
            if isinstance(conjunct, isla.ExistsFormula)]

        if not existential_formulas:
            return []

        return [
            result
            for new_state in self.eliminate_existential_formula(existential_formulas[0], formula, state.tree, state)
            for result in self.process_new_state(new_state, queue)
        ]

    def match_all_universal_formulas(self,
                                     formula: isla.Formula,
                                     state: SolutionState,
                                     queue: OrderedSet[SolutionState]) -> Optional[List[DerivationTree]]:
        universal_formulas = [
            conjunct for conjunct in split_conjunction(formula)
            if isinstance(conjunct, isla.ForallFormula)]

        if not universal_formulas:
            return None

        new_states = self.match_universal_formulas(universal_formulas, formula, state)

        if not new_states:
            return None

        return [result for new_state in new_states
                for result in self.process_new_state(new_state, queue)]

    def expand_tree(self, disjunct: isla.Formula, state: SolutionState) -> List[SolutionState]:
        """
        Expands the given tree, but not at nonterminals that can be freely instantiated of those that directly
        correspond to the assignment constant.

        :param disjunct: The conjunctive formula.
        :param state: The current state.
        :return: A (possibly empty) list of expanded trees.
        """

        possible_expansions: List[Dict[Path, List[DerivationTree]]] = dict_of_lists_to_list_of_dicts({
            leaf_path: [
                [DerivationTree(child, None if is_nonterminal(child) else []) for child in expansion]
                for expansion in self.canonical_grammar[leaf_node.value]
            ]
            for leaf_path, leaf_node in state.tree.open_concrete_leaves()
            if not self.can_be_freely_instantiated(leaf_path, disjunct, state.tree)
        })

        result: List[SolutionState] = []

        for possible_expansion in possible_expansions:
            expanded_tree = state.tree
            for path, new_children in possible_expansion.items():
                leaf_node = state.tree.get_subtree(path)
                expanded_tree = state.tree.replace_path(path, DerivationTree(leaf_node.value, new_children))

            updated_constraint = state.constraint.substitute_expressions({
                state.tree.get_subtree(path[:idx]): expanded_tree.get_subtree(path[:idx])
                for path in possible_expansion
                for idx in range(len(possible_expansion))
            })

            result.append(SolutionState(updated_constraint, expanded_tree, state.already_matched))

        return result

    def match_universal_formulas(self,
                                 universal_formulas: List[isla.ForallFormula],
                                 context_formula: isla.Formula,
                                 state: SolutionState) -> List[SolutionState]:
        matched: Dict[isla.QuantifiedFormula, Set[int]] = {}

        for universal_formula in universal_formulas:
            matches: List[Dict[isla.Variable, Tuple[Path, DerivationTree]]] = \
                isla.matches_for_quantified_variable(universal_formula)

            # Only consider open leaves. Others are validly instantiated.
            # TODO: Maybe we have to generalize this
            # TODO: This is anyway not clean; we only require here that one match is open.
            #       All is too strong, though, since for formulas with bind expression, the match for the in
            #       expression has children.
            matches = [match for match in matches
                       if any(tree.children is None for _, (_, tree) in match.items())]

            # if not matches:
            #    # As we generally don't expand nonterminals that match a quantifier, we have to do a manual
            #    # expansion here to proceed.
            #    formula_wo_bind_expr = sc.forall(
            #        universal_formula.bound_variable, universal_formula.in_variable, universal_formula.inner_formula)
            #    if (universal_formula.bind_expression is not None
            #            and (matches := isla.matches_for_quantified_variable(formula_wo_bind_expr, tree), matches)[-1]):
            #        expanded_trees = [new_tree]
            #        for match in matches:
            #            leaf_path, leaf_node = match[universal_formula.bound_variable]
            #            if leaf_node.children is not None:
            #                continue
            #
            #            for expanded_tree in copy.deepcopy(expanded_trees):
            #                expanded_trees.remove(expanded_tree)
            #                expanded_trees.extend(self.expand_tree_at(expanded_tree, leaf_path, leaf_node.value))
            #
            #        if expanded_trees == [new_tree]:
            #            return []
            #
            #        return [SolutionState(universal_formula, expanded_tree, state.already_matched)
            #                for expanded_tree in expanded_trees]
            #
            #    continue

            for match in matches:
                bound_var_match_tree = match[universal_formula.bound_variable][1]

                if state.is_already_matched(universal_formula, bound_var_match_tree):
                    continue

                matched.setdefault(universal_formula, set()).add(bound_var_match_tree.id)

                inst_formula = universal_formula.inner_formula.substitute_expressions({
                    variable: match_tree for variable, (_, match_tree) in match.items()
                })
                context_formula = inst_formula & context_formula

        if matched:
            return [SolutionState(context_formula, state.tree, state.already_matched | matched)]
        else:
            return []

    def eliminate_existential_formula(self,
                                      existential_formula: isla.ExistsFormula,
                                      context_formula: isla.Formula,
                                      tree: DerivationTree,
                                      state: SolutionState) -> List[SolutionState]:
        return []
        # all_vars = state.variables()
        # new_constant = fresh_constant(
        #    all_vars, isla.Constant(existential_formula.bound_variable.name,
        #                            existential_formula.bound_variable.n_type))
        # inserted_tree = DerivationTree(new_constant, None)
        # insertion_result = insert_tree(self.canonical_grammar, inserted_tree, tree)

        # if not insertion_result:
        #    return []

        # result: List[SolutionState] = []
        # for possible_tree in insertion_result:
        #    const_subst_map = {existential_formula.bound_variable: new_constant}

        #    if existential_formula.bind_expression is not None:
        #        _, bind_expr_paths = existential_formula.bind_expression.to_tree_prefix(
        #            existential_formula.bound_variable.n_type, self.grammar)
        #        for bv in existential_formula.bind_expression.bound_variables():
        #            const_subst_map[bv] = fresh_constant(
        #                all_vars, isla.Constant(bv.name, bv.n_type))

        #    new_state = SolutionState([assgn for assgn in state if assgn.constant is not constant])
        #    inst_formula = existential_formula.inner_formula.substitute_variables(const_subst_map)
        #    new_state.append(
        #        Assignment(constant,
        #                   isla.replace_formula(context_formula, existential_formula, inst_formula),
        #                   possible_tree))

        #    if existential_formula.bind_expression is None:
        #        new_state.append(Assignment(new_constant, inst_formula,
        #                                    DerivationTree(new_constant.n_type, None)))
        #    else:
        #        bind_expr_tree, _ = existential_formula.bind_expression \
        #            .substitute_variables(const_subst_map) \
        #            .to_tree_prefix(
        #            existential_formula.bound_variable.n_type,
        #            self.grammar)
        #        new_state.append(Assignment(new_constant, inst_formula, bind_expr_tree))
        #        for bound_variable in existential_formula.bind_expression.bound_variables():
        #            const_for_bv = const_subst_map[bound_variable]
        #            new_state.append(Assignment(const_for_bv, inst_formula,
        #                                        DerivationTree(const_for_bv.n_type, None)))

        #    result.append(new_state)

        # return result

    def eliminate_semantic_formula(self, semantic_formula: isla.Formula, context_formula: isla.Formula,
                                   state: SolutionState) -> List[SolutionState]:
        """
        Solves a semantic formula and, for each solution, substitutes the solution for the respective
        constant in each assignment of the state. Also instantiates all "free" constants in the given
        tree. The SMT solver is passed a regular expression approximating the language of the nonterminal
        of each considered constant. Returns an empty list for unsolvable constraints.

        :param semantic_formula: The semantic (i.e., only containing logical connectors and SMT Formulas)
        formula to solve.
        :param context_formula: The conjunctive formula inside which the given semantic formula occurs as a conjunct.
        Used for creating the resulting state: The conjunctive element is replaced with "true" inside the context.
        the solution state for trivial SMT formulas.
        :param state: The original solution state. Used to access other assignments (with constant different
        from `constant`).
        :return: A list of instantiated SolutionStates.
        """

        solutions: List[Dict[Union[isla.Constant, DerivationTree], DerivationTree]] = \
            self.solve_quantifier_free_formula(semantic_formula)

        results = []
        for solution in solutions:
            if solution:
                new_state = substitute_in_state(state, solution)
            else:
                new_state = SolutionState(
                    isla.replace_formula(context_formula, semantic_formula, sc.true()),
                    state.tree, state.already_matched)

            results.append(new_state)

        return results

    def solve_quantifier_free_formula(
            self, formula: isla.Formula) -> List[Dict[Union[isla.Constant, DerivationTree], DerivationTree]]:
        solutions: List[Dict[isla.Constant, DerivationTree]] = []
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
                regex = self.extract_regular_expression(constant.n_type)
                solver.add(z3.InRe(z3.String(constant.name), regex))

            for prev_solution in solutions:
                for constant in prev_solution:
                    solver.add(z3.Not(constant.to_smt() == z3.StringVal(str(prev_solution[constant]))))

            solver.add(smt_formula)

            if solver.check() != z3.sat:
                if not solutions:
                    return []
                else:
                    return solutions

            new_solution = {
                tree_substitutions.get(constant, constant):
                    self.parse(constant.n_type, solver.model()[z3.String(constant.name)].as_string())
                for constant in constants}

            if new_solution in solutions:
                # This can happen for trivial solutions, i.e., if the formula is logically valid.
                # Then, the assignment for that constant will always be {}
                return solutions
            else:
                solutions.append(new_solution)

        return solutions

    def process_new_state(
            self, new_state: SolutionState, queue: OrderedSet[SolutionState]) -> List[DerivationTree]:
        # TODO: Establish invariant

        open_concrete_leaves = list(new_state.tree.open_concrete_leaves())
        if (open_concrete_leaves and
                all(self.can_be_freely_instantiated(path, new_state.constraint, new_state.tree)
                    for path, _ in open_concrete_leaves)):
            new_states = self.instantiate_free_symbols(new_state)
        else:
            new_states = [new_state]

        result: List[DerivationTree] = []

        for new_state in new_states:
            if new_state.complete():
                assert new_state.formula_satisfied(self.grammar), \
                    f"Created state is complete, but constraints not satisfied: {new_state}"
                result.append(new_state.tree)
                continue

            self.logger.debug(f"Pushing new state {new_state}")
            self.logger.debug(f"Queue length: {len(queue)}")
            queue.add(new_state)

        return result

    def instantiate_free_symbols(self, new_state: SolutionState) -> OrderedSet[SolutionState]:
        """
        Instantiates free nonterminals and constants up to the set bound if the state only consists of top assignments.

        :param new_state: The state to expand
        :param top_constants: The top-level constants
        :return: A new set of states
        """

        result: OrderedSet[SolutionState] = OrderedSet([])
        fuzzer = GrammarCoverageFuzzer(self.grammar)

        for _ in range(self.max_number_free_instantiations):
            substitutions: Dict[DerivationTree, DerivationTree] = {
                subtree: DerivationTree.from_parse_tree(fuzzer.expand_tree((subtree.value, None)))
                for path, subtree in new_state.tree.open_leaves()
                if self.can_be_freely_instantiated(path, new_state.constraint, new_state.tree)
            }

            if substitutions:
                result.add(substitute_in_state(new_state, substitutions))

        return result or OrderedSet([new_state])

    def can_be_freely_instantiated(self, path_to_leaf: Path, formula: isla.Formula, in_tree: DerivationTree) -> bool:
        conjuncts = get_conjuncts(formula)
        quantified_formulas = [formula for formula in conjuncts if isinstance(formula, isla.QuantifiedFormula)]

        return all(not self.quantified_formula_might_match(qfd_formula, path_to_leaf, in_tree)
                   for qfd_formula in quantified_formulas)

    def quantified_formula_might_match(
            self, qfd_formula: isla.QuantifiedFormula, path_to_nonterminal: Path, in_tree: DerivationTree) -> bool:
        node_value = in_tree.get_subtree(path_to_nonterminal).value
        nonterminal = node_value if isinstance(node_value, str) else node_value.n_type

        qfd_nonterminal = qfd_formula.bound_variable.n_type
        if qfd_nonterminal == nonterminal or self.reachable(nonterminal, qfd_nonterminal):
            return True

        if (qfd_formula.bind_expression is not None
                and nonterminal in [var.n_type for var in qfd_formula.bind_expression.bound_variables()]):
            prefix_tree, _ = qfd_formula.bind_expression.to_tree_prefix(
                qfd_formula.bound_variable.n_type, self.grammar, to_abstract_tree=False)
            for path, subtree in in_tree.path_iterator():
                if len(path) >= len(path_to_nonterminal) or path != path_to_nonterminal[:len(path)]:
                    continue

                if subtree.make_concrete().is_prefix(prefix_tree):
                    return True

        return False

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
            lambda conjunct: type_map.get(type(conjunct), -1),
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
        conjunct for conjunct in get_conjuncts(formula)
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


def substitute_in_state(state: SolutionState,
                        substitution: Dict[Union[isla.Constant, DerivationTree], DerivationTree]) -> SolutionState:
    return SolutionState(state.constraint.substitute_expressions(substitution),
                         state.tree.substitute(substitution),
                         state.already_matched)
