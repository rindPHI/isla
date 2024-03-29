# TODOs and Open Issues

- Test with newer Z3 versions (>= 4.12.1.0), e.g., the heartbleed examples. I experienced
  problems with these during a demo preparation.
- Unicode symbols in BNF syntax (e.g., \u0001)
- Add CLI option for `enable-optimized-z3-queries`.
- XPath: Formula `exists <assgn> assgn: assgn..<digit> = "7"` cannot be parsed
  (assignment language).
- Repair too aggressive; example (assignment language):
  `isla repair grammar.bnf def-use.isla -i "a := 1 ; c := b"`
- Fix TAR test! Problem introduced in commit with ID 9a82766f76247c1ff0cab738ef7c3133b36e44ce (10.0.9)
  Note: Cannot reproduce anymore; but have to look into the TAR case study, it seens to have slowed down.
- Fix test case `test_predicates.test_count_pred_var_as_third_arg`
- Translation of formulas with XPath expressions in `in` qualifiers of quantifiers; see test
  case `test_xpath_in_in_expr`.
- Translation of "free nonterminals" together with unnamed bound variables:
  Support formulas like `(...<A>...) and (exists <A>: ...<A>...)` or check
  whether this is already supported. But at least in one combination of the
  elements of the propositional combination, it probably fails (a free variable
  remains).
- Support & test XPath expressions in ISLa predicates.
- Address buggy test case: `test_evaluator.test_addition_with_more_than_two_operands`
  [GitHub Issue](https://github.com/rindPHI/isla/issues/2)
