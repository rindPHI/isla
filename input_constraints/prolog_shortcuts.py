import input_constraints.prolog_structs as pl


def anon_var() -> pl.Variable:
    return pl.Variable("_")


def infix_term(op: str, left: pl.Term, right: pl.Term) -> pl.CompoundTerm:
    return pl.CompoundTerm(pl.Functor(op, 2, infix=True), [left, right])


def pair(left: pl.Term, right: pl.Term) -> pl.CompoundTerm:
    return infix_term("-", left, right)


def clp_eq(left: pl.Term, right: pl.Term) -> pl.PredicateApplication:
    return pl.PredicateApplication(pl.Predicate("#=", 2, infix=True), [left, right])


def clp_lt(left: pl.Term, right: pl.Term) -> pl.PredicateApplication:
    return pl.PredicateApplication(pl.Predicate("#<", 2, infix=True), [left, right])


def clp_le(left: pl.Term, right: pl.Term) -> pl.PredicateApplication:
    return pl.PredicateApplication(pl.Predicate("#=<", 2, infix=True), [left, right])


def clp_gt(left: pl.Term, right: pl.Term) -> pl.PredicateApplication:
    return pl.PredicateApplication(pl.Predicate("#>", 2, infix=True), [left, right])


def clp_ge(left: pl.Term, right: pl.Term) -> pl.PredicateApplication:
    return pl.PredicateApplication(pl.Predicate("#>=", 2, infix=True), [left, right])


def clp_iff(left: pl.Goal, right: pl.Goal) -> pl.Goal:
    return pl.GoalCombinatorApplication(pl.GoalCombinator("#<==>", 2, infix=True), [left, right])


def unify(left: pl.Term, right: pl.Term) -> pl.PredicateApplication:
    return pl.PredicateApplication(pl.Predicate("=", 2, infix=True), [left, right])


def ite(condition: pl.Goal, then_branch: pl.Goal, else_branch: pl.Goal) -> pl.Goal:
    return pl.Conditional(condition, then_branch, else_branch)


def conj(*arguments: pl.Goal) -> pl.Goal:
    return pl.Conjunction(arguments)


def disj(*arguments: pl.Goal) -> pl.Goal:
    return pl.Disjunction(arguments)


def list_term(*arguments: pl.Term) -> pl.ListTerm:
    return pl.ListTerm(arguments)


def pred(name: str, *args: pl.Term) -> pl.PredicateApplication:
    return pl.PredicateApplication(pl.Predicate(name, len(args), infix=False), list(args))


def infix_pred(name: str, *args: pl.Term) -> pl.PredicateApplication:
    return pl.PredicateApplication(pl.Predicate(name, len(args), infix=True), list(args))
