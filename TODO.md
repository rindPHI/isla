# TODOs and Open Issues

- Check reST test case / case study; fails though it shouldn't.
- Translation of "free nonterminals" together with unnamed bound variables:
  Support formulas like `(...<A>...) and (exists <A>: ...<A>...)` or check
  whether this is already supported. But at least in one combination of the
  elements of the propositional combination, it probably fails (a free variable
  remains).
- Support & test XPath expressions in ISLa predicates.
- Address unsatisfiability of formulas with existential quantifiers. Currently, we
  can only handle these cases ingeneral by setting a timeout. Otherwise, we continue
  inserting and expanding trees for an infinite amount of time. Have to find
  a termination criterion eventually.