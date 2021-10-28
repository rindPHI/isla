import copy
from typing import List

import z3

from input_constraints import isla
import input_constraints.isla_shortcuts as sc


def set_smt_auto_eval(formula: isla.Formula, auto_eval: bool = False):
    class AutoEvalVisitor(isla.FormulaVisitor):
        def visit_smt_formula(self, formula: isla.SMTFormula):
            formula.auto_eval = auto_eval

    formula.accept(AutoEvalVisitor())


def vacuously_satisfies(inp: isla.DerivationTree, formula: isla.Formula) -> bool:
    # Note: This assumes that `inp` *does* satisfy `formula`!
    assert isla.evaluate(formula, inp)

    formula = copy.deepcopy(formula)
    set_smt_auto_eval(formula, False)

    constant = next(
        c for c in isla.VariablesCollector.collect(formula)
        if isinstance(c, isla.Constant))
    qfr_free: List[isla.Formula] = isla.eliminate_quantifiers(formula.substitute_expressions({constant: inp}))

    qfr_free_dnf: List[isla.Formula] = [isla.convert_to_dnf(isla.convert_to_nnf(f)) for f in qfr_free]
    clauses: List[List[isla.Formula]] = [
        isla.split_conjunction(_f)
        for f in qfr_free_dnf
        for _f in isla.split_disjunction(f)
    ]

    # There needs to be one non-trivial clause for non-vacuous satisfaction
    clauses = [
        clause for clause in clauses
        if all(f != sc.false() for f in clause)
           and any(not isinstance(f, isla.SMTFormula) or not z3.is_true(f.formula) for f in clause)
    ]

    return not clauses
