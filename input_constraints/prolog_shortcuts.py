import input_constraints.prolog_structs as pl


def anon_var() -> pl.Variable:
    return pl.Variable("_")


def pair(left: pl.Term, right: pl.Term) -> pl.CompoundTerm:
    return pl.CompoundTerm(pl.Functor("-", 2, infix=True), [left, right])


def unify(left: pl.Term, right: pl.Term) -> pl.PredicateApplication:
    return pl.PredicateApplication(pl.Predicate("=", 2, infix=True), [left, right])
