import copy
from functools import reduce
from typing import Union, Optional, Set, Dict, cast, Tuple, List, Iterable

import z3
from orderedset import OrderedSet

from isla.helpers import z3_and, is_nonterminal, z3_or
from isla.isla_predicates import STANDARD_STRUCTURAL_PREDICATES, STANDARD_SEMANTIC_PREDICATES
from isla.language import Formula, DerivationTree, StructuralPredicate, SemanticPredicate, parse_isla, \
    VariablesCollector, Constant, FilterVisitor, NumericQuantifiedFormula, StructuralPredicateFormula, SMTFormula, \
    SemanticPredicateFormula, Variable, replace_formula, \
    BoundVariable, ExistsIntFormula, ForallIntFormula, QuantifiedFormula, PropositionalCombinator, \
    ConjunctiveFormula, ForallFormula, ExistsFormula, NegatedFormula, \
    DisjunctiveFormula, BindExpression
from isla.type_defs import Grammar, Path


class ThreeValuedTruth:
    FALSE = 0
    TRUE = 1
    UNKNOWN = 2

    def __init__(self, val: int):
        assert 0 <= val <= 2
        self.val = val

    def __eq__(self, other):
        return self.val == other.val

    def __hash__(self):
        return self.val

    def to_bool(self) -> bool:
        assert self.val != ThreeValuedTruth.UNKNOWN
        return bool(self.val)

    def __bool__(self):
        return self.to_bool()

    def is_false(self):
        return self.val == ThreeValuedTruth.FALSE

    def is_true(self):
        return self.val == ThreeValuedTruth.TRUE

    def is_unknown(self):
        return self.val == ThreeValuedTruth.UNKNOWN

    @staticmethod
    def from_bool(b: bool) -> 'ThreeValuedTruth':
        return ThreeValuedTruth(int(b))

    @staticmethod
    def all(args: Iterable['ThreeValuedTruth']) -> 'ThreeValuedTruth':
        args = list(args)
        if any(elem.is_false() for elem in args):
            return ThreeValuedTruth.false()
        if any(elem.is_unknown() for elem in args):
            return ThreeValuedTruth.unknown()
        return ThreeValuedTruth.true()

    @staticmethod
    def any(args: Iterable['ThreeValuedTruth']) -> 'ThreeValuedTruth':
        args = list(args)
        if any(elem.is_true() for elem in args):
            return ThreeValuedTruth.true()
        if any(elem.is_unknown() for elem in args):
            return ThreeValuedTruth.unknown()
        return ThreeValuedTruth.false()

    @staticmethod
    def not_(arg: 'ThreeValuedTruth') -> 'ThreeValuedTruth':
        if arg.is_true():
            return ThreeValuedTruth.false()
        if arg.is_false():
            return ThreeValuedTruth.true()
        return ThreeValuedTruth.unknown()

    @staticmethod
    def true():
        return ThreeValuedTruth(ThreeValuedTruth.TRUE)

    @staticmethod
    def false():
        return ThreeValuedTruth(ThreeValuedTruth.FALSE)

    @staticmethod
    def unknown():
        return ThreeValuedTruth(ThreeValuedTruth.UNKNOWN)

    def __repr__(self):
        return f"ThreeValuedTruth({self.val})"

    def __str__(self):
        return ("TRUE" if self.is_true() else
                "FALSE" if self.is_false() else
                "UNKNOWN")


def evaluate(
        formula: Union[Formula, str],
        reference_tree: DerivationTree,
        grammar: Grammar,
        structural_predicates: Set[StructuralPredicate] = STANDARD_STRUCTURAL_PREDICATES,
        semantic_predicates: Set[SemanticPredicate] = STANDARD_SEMANTIC_PREDICATES,
        assumptions: Optional[Set[Formula]] = None) -> ThreeValuedTruth:
    if isinstance(formula, str):
        formula = parse_isla(formula, grammar, structural_predicates, semantic_predicates)

    top_level_constants = {
        c for c in VariablesCollector.collect(formula)
        if isinstance(c, Constant) and not c.is_numeric()}
    assert len(top_level_constants) <= 1
    if len(top_level_constants) > 0:
        assert reference_tree is not None
        formula = formula.substitute_expressions({next(iter(top_level_constants)): reference_tree})

    res, msg = well_formed(formula, grammar)
    assert res, msg

    v = FilterVisitor(lambda f: isinstance(f, NumericQuantifiedFormula))
    formula.accept(v)
    if not v.result:
        # The legacy evaluation performs better, but only works w/o NumericQuantifiedFormulas.
        # TODO: Check whether it still performs better, more general evaluation improved!
        # TODO: If keeping legacy evaluation, also consider assumptions!
        return evaluate_legacy(formula, grammar, {}, reference_tree)

    qfr_free: Formula = eliminate_quantifiers(
        formula,
        grammar=grammar,
        numeric_constants={
            c for f in (assumptions | {formula}) for c in VariablesCollector.collect(f)
            if isinstance(c, Constant) and c.is_numeric()
        }
    )

    # Substitute assumptions

    # First, eliminate quantifiers in assumptions. We don't supply any numeric constants
    # here, as this would be unsound in assumptions: We know that the core holds for any
    # int, but not for which one.
    qfr_free_assumptions = {eliminate_quantifiers(assumption, grammar=grammar) for assumption in assumptions}

    # Then, replace the assumptions by True in the formula
    assumptions_instantiated = qfr_free
    for assumption in qfr_free_assumptions:
        assumptions_instantiated = replace_formula(assumptions_instantiated, assumption, SMTFormula(z3.BoolVal(True)))

    class NotYetReadyError(RuntimeError):
        def __init__(self, *args: object) -> None:
            super().__init__(*args)

    # Evaluate predicates
    def evaluate_predicates_action(formula: Formula) -> bool | Formula:
        if isinstance(formula, StructuralPredicateFormula):
            return SMTFormula(z3.BoolVal(formula.evaluate(reference_tree)))

        if isinstance(formula, SemanticPredicateFormula):
            eval_result = formula.evaluate(grammar)

            if not eval_result.ready():
                raise NotYetReadyError(f"Formula {formula} is not ready to be evaluated")

            if eval_result.true():
                return SMTFormula(z3.BoolVal(True))
            elif eval_result.false():
                return SMTFormula(z3.BoolVal(False))

            substs: Dict[Variable | DerivationTree, DerivationTree] = eval_result.result
            assert isinstance(substs, dict)
            assert all(isinstance(key, Variable) and key.n_type == Variable.NUMERIC_NTYPE for key in substs)
            return SMTFormula(z3_and([
                cast(z3.BoolRef, const.to_smt() == substs[const].value)
                for const in substs]), *substs.keys())

        return False

    try:
        without_predicates: Formula = replace_formula(assumptions_instantiated, evaluate_predicates_action)
    except NotYetReadyError:
        return ThreeValuedTruth.unknown()

    # The remaining formula is a pure SMT formula, which only needs to be converted.
    smt_formula: z3.BoolRef = isla_to_smt_formula(without_predicates)

    solver = z3.Solver()
    solver.add(z3.Not(smt_formula))
    z3_result = solver.check()
    if z3_result == z3.unknown:
        return ThreeValuedTruth.unknown()

    return ThreeValuedTruth(z3_result == z3.unsat)  # original formula is valid


def well_formed(formula: Formula,
                grammar: Grammar,
                bound_vars: Optional[OrderedSet[BoundVariable]] = None,
                in_expr_vars: Optional[OrderedSet[Variable]] = None,
                bound_by_smt: Optional[OrderedSet[Variable]] = None) -> Tuple[bool, str]:
    if bound_vars is None:
        bound_vars = OrderedSet([])
    if in_expr_vars is None:
        in_expr_vars = OrderedSet([])
    if bound_by_smt is None:
        bound_by_smt = OrderedSet([])

    unknown_typed_variables = [
        var for var in formula.free_variables()
        if is_nonterminal(var.n_type) and var.n_type not in grammar]
    if unknown_typed_variables:
        return False, "Unkown types of variables " + ", ".join(map(repr, unknown_typed_variables))

    if isinstance(formula, ExistsIntFormula) or isinstance(formula, ForallIntFormula):
        if formula.bound_variables().intersection(bound_vars):
            return False, f"Variables {', '.join(map(str, formula.bound_variables().intersection(bound_vars)))} " \
                          f"already bound in outer scope"

        unbound_variables = [
            free_var for free_var in formula.free_variables()
            if type(free_var) is BoundVariable
            if free_var not in bound_vars]
        if unbound_variables:
            return False, f"Unbound variables " + ", ".join(map(repr, unbound_variables)) + f" in {formula}"

        return well_formed(
            formula.inner_formula,
            grammar,
            bound_vars | formula.bound_variables(),
            in_expr_vars,
            bound_by_smt
        )
    elif isinstance(formula, QuantifiedFormula):
        if formula.in_variable in bound_by_smt:
            return False, f"Variable {formula.in_variable} in {formula} bound be outer SMT formula"
        if formula.bound_variables().intersection(bound_vars):
            return False, f"Variables {', '.join(map(str, formula.bound_variables().intersection(bound_vars)))} " \
                          f"already bound in outer scope"
        if type(formula.in_variable) is BoundVariable and formula.in_variable not in bound_vars:
            return False, f"Unbound variable {formula.in_variable} in {formula}"
        unbound_variables = [
            free_var for free_var in formula.free_variables()
            if type(free_var) is BoundVariable
            if free_var not in bound_vars]
        if unbound_variables:
            return False, f"Unbound variables " + ", ".join(map(repr, unbound_variables)) + f" in {formula}"

        unknown_typed_variables = [
            var for var in formula.bound_variables()
            if is_nonterminal(var.n_type) and var.n_type not in grammar]
        if unknown_typed_variables:
            return False, "Unkown types of variables " + ", ".join(map(repr, unknown_typed_variables)) + \
                   f" in {formula}"

        if formula.bind_expression is not None:
            unknown_typed_variables = [
                var for var in formula.bind_expression.all_bound_variables(grammar)
                if is_nonterminal(var.n_type) and var.n_type not in grammar]
            if unknown_typed_variables:
                return False, "Unkown types of variables " + ", ".join(map(repr, unknown_typed_variables)) + \
                       f" in match expression {formula.bind_expression}"

        return well_formed(
            formula.inner_formula,
            grammar,
            bound_vars | formula.bound_variables(),
            in_expr_vars | OrderedSet([formula.in_variable]),
            bound_by_smt
        )
    elif isinstance(formula, SMTFormula):
        if any(free_var in in_expr_vars for free_var in formula.free_variables()):
            return False, f"Formula {formula} binding variables of 'in' expressions in an outer quantifier."

        if any(free_var not in bound_vars
               for free_var in formula.free_variables()
               if type(free_var) is BoundVariable):
            return False, "(TODO)"

        return True, ""
    elif isinstance(formula, PropositionalCombinator):
        if isinstance(formula, ConjunctiveFormula):
            smt_formulas = [f for f in formula.args if type(f) is SMTFormula]
            other_formulas = [f for f in formula.args if type(f) is not SMTFormula]

            for smt_formula in smt_formulas:
                res, msg = well_formed(smt_formula, grammar, bound_vars, in_expr_vars, bound_by_smt)
                if not res:
                    return False, msg

            for smt_formula in smt_formulas:
                bound_vars |= [var for var in smt_formula.free_variables() if type(var) is BoundVariable]
                bound_by_smt |= smt_formula.free_variables()

            for f in other_formulas:
                res, msg = well_formed(f, grammar, bound_vars, in_expr_vars, bound_by_smt)
                if not res:
                    return False, msg

            return True, ""
        else:
            for subformula in formula.args:
                res, msg = well_formed(subformula, grammar, bound_vars, in_expr_vars, bound_by_smt)
                if not res:
                    return False, msg

            return True, ""
    elif isinstance(formula, StructuralPredicateFormula) or isinstance(formula, SemanticPredicateFormula):
        unbound_variables = [
            free_var for free_var in formula.free_variables()
            if type(free_var) is BoundVariable
            if free_var not in bound_vars]
        if unbound_variables:
            return False, f"Unbound variables " + ", ".join(map(repr, unbound_variables)) + f" in {formula}"
        return True, ""
    else:
        raise NotImplementedError(f"Unsupported formula type {type(formula).__name__}")


def evaluate_legacy(
        formula: Formula,
        grammar: Grammar,
        assignments: Dict[Variable, Tuple[Path, DerivationTree]],
        reference_tree: DerivationTree,
        vacuously_satisfied: Optional[Set[Formula]] = None) -> ThreeValuedTruth:
    """
    An evaluation method which is based on tracking assignments in a dictionary.
    This does not work with formulas containing numeric constant introductions,
    but is significantly faster than the more general method based on formula manipulations.

    :param formula: The formula to evaluate.
    :param assignments: The assignments recorded so far.
    :return: A (three-valued) truth value.
    """

    assert all(
        reference_tree.is_valid_path(path)
        for path, _ in assignments.values())
    assert all(
        reference_tree.find_node(tree) is not None
        for _, tree in assignments.values())
    assert all(
        reference_tree.get_subtree(path) == tree
        for path, tree in assignments.values())

    if vacuously_satisfied is None:
        vacuously_satisfied = set()

    if isinstance(formula, ExistsIntFormula):
        raise NotImplementedError("This method cannot evaluate IntroduceNumericConstantFormula formulas.")
    elif isinstance(formula, SMTFormula):
        instantiation = z3.substitute(
            formula.formula,
            *tuple({z3.String(symbol.name): z3.StringVal(str(symbol_assignment[1]))
                    for symbol, symbol_assignment
                    in assignments.items()}.items()))

        solver = z3.Solver()
        solver.add(z3.Not(instantiation))
        return ThreeValuedTruth.from_bool(solver.check() == z3.unsat)  # Set timeout?
    elif isinstance(formula, QuantifiedFormula):
        if isinstance(formula.in_variable, DerivationTree):
            in_inst = formula.in_variable
            in_path: Path = reference_tree.find_node(in_inst)
            assert in_path is not None
        else:
            assert formula.in_variable in assignments
            in_path, in_inst = assignments[formula.in_variable]

        assert all(
            reference_tree.is_valid_path(path) and
            reference_tree.find_node(tree) is not None and
            reference_tree.get_subtree(path) == tree
            for path, tree in assignments.values())

        new_assignments = matches_for_quantified_formula(formula, grammar, in_inst, {})

        assert all(
            in_inst.is_valid_path(path) and
            in_inst.find_node(tree) is not None and
            in_inst.get_subtree(path) == tree
            for assignment in new_assignments
            for path, tree in assignment.values())

        new_assignments = [
            {var: (in_path + path, tree) for var, (path, tree) in assignment.items()} | assignments
            for assignment in new_assignments]

        assert all(
            reference_tree.is_valid_path(path) and
            reference_tree.find_node(tree) is not None and
            reference_tree.get_subtree(path) == tree
            for assignment in new_assignments
            for path, tree in assignment.values())

        if isinstance(formula, ForallFormula):
            if not new_assignments:
                vacuously_satisfied.add(formula)

            return ThreeValuedTruth.all(
                evaluate_legacy(formula.inner_formula, grammar, new_assignment, reference_tree, vacuously_satisfied)
                for new_assignment in new_assignments)
        elif isinstance(formula, ExistsFormula):
            return ThreeValuedTruth.any(
                evaluate_legacy(formula.inner_formula, grammar, new_assignment, reference_tree, vacuously_satisfied)
                for new_assignment in new_assignments)
    elif isinstance(formula, StructuralPredicateFormula):
        arg_insts = [
            arg if isinstance(arg, str)
            else reference_tree.find_node(arg)
            if isinstance(arg, DerivationTree)
            else assignments[arg][0]
            for arg in formula.args]
        return ThreeValuedTruth.from_bool(formula.predicate.evaluate(reference_tree, *arg_insts))
    elif isinstance(formula, SemanticPredicateFormula):
        arg_insts = [arg if isinstance(arg, DerivationTree) or arg not in assignments
                     else assignments[arg][1]
                     for arg in formula.args]
        eval_res = formula.predicate.evaluate(grammar, *arg_insts)

        if eval_res.true():
            return ThreeValuedTruth.true()
        elif eval_res.false():
            return ThreeValuedTruth.false()

        if not eval_res.ready() or not all(isinstance(key, Constant) for key in eval_res.result):
            # Evaluation resulted in a tree update; that is, the formula is satisfiable, but only
            # after an update of its arguments. This result happens when evaluating formulas during
            # solution search after instantiating variables with concrete trees.
            return ThreeValuedTruth.unknown()

        assignments.update({const: (tuple(), assgn) for const, assgn in eval_res.result.items()})
        return ThreeValuedTruth.true()
    elif isinstance(formula, NegatedFormula):
        return ThreeValuedTruth.not_(evaluate_legacy(
            formula.args[0], grammar, assignments, reference_tree, vacuously_satisfied))
    elif isinstance(formula, ConjunctiveFormula):
        return ThreeValuedTruth.all(
            evaluate_legacy(sub_formula, grammar, assignments, reference_tree, vacuously_satisfied)
            for sub_formula in formula.args)
    elif isinstance(formula, DisjunctiveFormula):
        return ThreeValuedTruth.any(
            evaluate_legacy(sub_formula, grammar, assignments, reference_tree, vacuously_satisfied)
            for sub_formula in formula.args)
    else:
        raise NotImplementedError()


def eliminate_quantifiers(
        formula: Formula,
        grammar: Grammar,
        numeric_constants: Optional[Set[Constant]] = None) -> Formula:
    if numeric_constants is None:
        numeric_constants = {
            var for var in VariablesCollector().collect(formula)
            if isinstance(var, Constant) and var.is_numeric()}

    # We eliminate all quantified formulas over derivation tree elements
    # by replacing them by the finite set of matches in the inner trees.
    quantified_formulas = [f for f in get_toplevel_quantified_formulas(formula)
                           if isinstance(f, QuantifiedFormula)]

    if quantified_formulas:
        for quantified_formula in quantified_formulas:
            assert isinstance(quantified_formula.in_variable, DerivationTree)
            matches = [
                {var: tree for var, (_, tree) in match.items()}
                for match in matches_for_quantified_formula(
                    quantified_formula, grammar, quantified_formula.in_variable)]
            instantiations = [
                quantified_formula.inner_formula.substitute_expressions(match)
                for match in matches]

            if instantiations:
                reduce_op = (Formula.__and__ if isinstance(quantified_formula, ForallFormula)
                             else Formula.__or__)
                formula = replace_formula(
                    formula,
                    quantified_formula,
                    reduce(reduce_op, instantiations))
            else:
                formula = replace_formula(
                    formula,
                    quantified_formula,
                    SMTFormula(z3.BoolVal(isinstance(quantified_formula, ForallFormula))))

        return eliminate_quantifiers(formula, grammar, numeric_constants)

    numeric_quantified_formulas = [f for f in get_toplevel_quantified_formulas(formula)
                                   if isinstance(f, NumericQuantifiedFormula)]

    if numeric_quantified_formulas:
        for quantified_formula in numeric_quantified_formulas:
            if isinstance(quantified_formula, ExistsIntFormula):
                # There might be a constant for which this formula is satisfied
                formula = replace_formula(
                    formula,
                    quantified_formula,
                    ExistsIntFormula(
                        quantified_formula.bound_variable,
                        eliminate_quantifiers(quantified_formula.inner_formula, grammar, numeric_constants)))

                formula = formula | reduce(Formula.__or__, [
                    eliminate_quantifiers(
                        quantified_formula.inner_formula.substitute_variables({
                            quantified_formula.bound_variable: constant}),
                        grammar,
                        numeric_constants)
                    for constant in numeric_constants
                ], SMTFormula(z3.BoolVal(False)))
            elif isinstance(quantified_formula, ForallIntFormula):
                formula = replace_formula(
                    formula,
                    quantified_formula,
                    ForallIntFormula(
                        quantified_formula.bound_variable,
                        eliminate_quantifiers(quantified_formula.inner_formula, grammar, numeric_constants)))

    return formula


def matches_for_quantified_formula(
        formula: QuantifiedFormula,
        grammar: Grammar,
        in_tree: Optional[DerivationTree] = None,
        initial_assignments: Optional[Dict[Variable, Tuple[Path, DerivationTree]]] = None) -> \
        List[Dict[Variable, Tuple[Path, DerivationTree]]]:
    if in_tree is None:
        in_tree = formula.in_variable
        assert isinstance(in_tree, DerivationTree)

    qfd_var: BoundVariable = formula.bound_variable
    bind_expr: Optional[BindExpression] = formula.bind_expression
    new_assignments: List[Dict[Variable, Tuple[Path, DerivationTree]]] = []
    if initial_assignments is None:
        initial_assignments = {}

    def search_action(path: Path, tree: DerivationTree) -> None:
        nonlocal new_assignments
        node, children = tree
        if node == qfd_var.n_type:
            if bind_expr is not None:
                maybe_match: Optional[Tuple[Tuple[BoundVariable, Tuple[Path, DerivationTree]]], ...]
                maybe_match = bind_expr.match(tree, grammar)

                if maybe_match is not None:
                    maybe_match = dict(maybe_match)
                    new_assignment = copy.copy(initial_assignments)
                    new_assignment[qfd_var] = path, tree
                    new_assignment.update({v: (path + p[0], p[1]) for v, p in maybe_match.items()})

                    # The assignment is correct if there is not any non-matched leaf
                    if all(any(len(match_path) <= len(leaf_path) and match_path == leaf_path[:len(match_path)]
                               for match_path, _ in maybe_match.values()) for leaf_path, _ in tree.leaves()):
                        new_assignments.append(new_assignment)
            else:
                new_assignment = copy.copy(initial_assignments)
                new_assignment[qfd_var] = path, tree
                new_assignments.append(new_assignment)

    in_tree.traverse(search_action)
    return new_assignments


def get_toplevel_quantified_formulas(formula: Formula) -> \
        List[Union[QuantifiedFormula, NumericQuantifiedFormula]]:
    if isinstance(formula, QuantifiedFormula) or isinstance(formula, NumericQuantifiedFormula):
        return [formula]
    elif isinstance(formula, PropositionalCombinator):
        return [f for arg in formula.args for f in get_toplevel_quantified_formulas(arg)]
    else:
        return []


def isla_to_smt_formula(
        formula: Formula,
        replace_untranslatable_with_predicate=False,
        prog_var_mapping: Optional[Dict[Formula, z3.BoolRef]] = None) -> z3.BoolRef:
    assert not prog_var_mapping or replace_untranslatable_with_predicate
    if prog_var_mapping is None:
        prog_var_mapping = {}

    if isinstance(formula, SMTFormula):
        return formula.formula

    if isinstance(formula, ConjunctiveFormula):
        return z3_and([isla_to_smt_formula(child, replace_untranslatable_with_predicate, prog_var_mapping)
                       for child in formula.args])

    if isinstance(formula, DisjunctiveFormula):
        return z3_or([isla_to_smt_formula(child, replace_untranslatable_with_predicate, prog_var_mapping)
                      for child in formula.args])

    if isinstance(formula, NegatedFormula):
        return z3.Not(isla_to_smt_formula(formula.args[0], replace_untranslatable_with_predicate, prog_var_mapping))

    if isinstance(formula, ForallIntFormula):
        return z3.ForAll(
            [formula.bound_variable.to_smt()],
            isla_to_smt_formula(formula.inner_formula, replace_untranslatable_with_predicate, prog_var_mapping))

    if isinstance(formula, ExistsIntFormula):
        return z3.Exists(
            [formula.bound_variable.to_smt()],
            isla_to_smt_formula(formula.inner_formula, replace_untranslatable_with_predicate, prog_var_mapping))

    if not replace_untranslatable_with_predicate:
        raise NotImplementedError(f"Don't know how to translate formula {formula} to SMT")

    if formula not in prog_var_mapping:
        name_idx = 1
        replacement = z3.Bool(f"P_{name_idx}")
        while replacement in prog_var_mapping.values():
            replacement = z3.Bool(f"P_{name_idx}")
            name_idx += 1

        assert replacement not in prog_var_mapping.values()
        prog_var_mapping[formula] = replacement

    return prog_var_mapping[formula]
