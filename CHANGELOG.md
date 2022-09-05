# Changelog

This file contains the notable changes in the ISLa project since version 0.2a1
(February 2022). Changes prior to this date are not documented.

## [unreleased]

### Changed

- Integrated the [black](https://github.com/psf/black) code style.

## [0.10.10] - 2022-09-01

### Changed

- Upgraded `grammar_graph` library, which now integrates better caching. Significant
  performance improvement.
- Upgraded `grammar_to_regex` library, which incorporates a bug fix in expansing nonregular
  subgrammars.

## [0.10.9] - 2022-09-01

### Changed

- Upgraded `grammar_graph` library, which now caches (k)-paths of subtrees. This gives a
  performance boost in particular for long trees with redundant subtrees like from the
  TAR case study.
- Fixed the TAR parser from the TAR case study.

## [0.10.8] - 2022-08-31

### Changed

- Passing bytes rather than str to the `ijson` library to address deprecation warning.
- Increased version of required `grammar_to_regex` library; works better when expressing
  constraints on nonterminals with certain nonregular sub-languages.

## [0.10.7] - 2022-08-31

### Changed

- Non-recursive length computation for derivation trees; prevents recursion depth errors for
  deep trees.

## [0.10.6] - 2022-08-30

### Changed

- Bug fix in performance evaluator.

## [0.10.5] - 2022-08-30

### Changed

- Upgraded `grammar_graph` library; includes performance fix.
- Including ISLa 0.10.15 in Dockerfile.

## [0.10.4] - 2022-08-30

### Changed

- Added solver parameter `grammar_unwinding_threshold` to customize the grammar unwinding
  depth for nonregular nonterminal grammars involved in SMT-LIB formulas.

## [0.10.3] - 2022-08-29

Bugfix release for 0.10.2.

## [0.10.2] - 2022-08-29

### Changed

- If multiple solutions to an SMT formula are required (see solver parameter
  `max_number_smt_instantiations`), we add a negated *conjunction* of the values 
  for all variables in a previous solution; before, we only added a negation
  of the individual values, which sometimes resulted in fewer solutions than possible
  (see [this GitHub issue](https://github.com/rindPHI/isla/issues/4)).
- Using iterative JSON deserialization in performance evaluators and derivation tree
  deserialization, works better for large inputs (e.g., TAR files).

## [0.10.1] - 2022-08-26

### Changed

- Fixed a bug in computing more than one solution to an SMT-LIB formula. Before, it was
  pure coincidence if another solution dropped out.
- Updated dependency to `grammar_graph` library, which had a major bug before which could
  render k-path coverage guidance useless.
- Recalibrated weight vectors (including default weight vector) to account for the bug
  fix in the grammar graph library.

## [0.10.0] - 2022-08-22

### Changed

- Major overhaul of cost computation. The solver finds much more diverse inputs now. 

## [0.9.6] - 2022-08-20

### Changed

- Bug fix in performance_evaluator, regression due to API change in ISLaSolver (return of TIMEOUT values)
- Increased maximum recursion depth for evaluation; this is needed in the TAR case study.

## [0.9.5] - 2022-08-19

### Changed

- Bug fix deserialization of `isla.language.SMTFormula` in conjunction with escaped quotation marks.

## [0.9.4] - 2022-08-19

### Changed

- Bug fix in `ISLaUnparser`: Quotation marks in SMT-LIB string literals are escaped according to the [ISLa
  language specification](https://rindphi.github.io/isla/islaspec/#lexer-rules), using `\"`.

## [0.9.3] - 2022-08-19

### Added

- Added functions `isla.solver.implies` and `isla.solver.equivalent` for implication and equivalence
  checking.

### Changed

- Bug fix in unsatisfiability testing for existential quantifiers. Before, SAT was reported instead
  of UNSAT in certain cases.

## [0.9.2] - 2022-08-19

### Changed

- Using Trie implementation that is more efficient in retrieving sub-tries. All trie functionality is now
  bundled in the `isla.trie.SubtreesTrie` class.

## [0.9.1] - 2022-08-19

### Changed

- Re-introduced PEGParser to `isla.parser`
- Using PEGParser first in bind expression parsing; make a huge performance difference for complex (PEG) grammars.

## [0.9.0] - 2022-08-18

### Added

- With the solver flag `activate_unsat_support` set, an additional unsatisfiability check is executed
  for existential formulas arising during solving, which, in many cases, can make the solver terminate
  with an adequate `ISLaSolver.UNSAT` response. This flag should only be set if an unsatisfiable answer
  is expected or deemed possible, since the additional checks impact the solver performance. With this
  release, ISLa is approaching the state of being a *solver/checker for both satisfiable and unsatisfiable problems*.

## [0.8.18] - 2022-08-18

### Changed

- The `ISLaSolver.fuzz()` and `ISLaSolver.solver()` methods now return either (a generator of) derivation
  trees *or* the special constants `ISLaSolver.TIMEOUT` or `ISLaSolver.UNSAT` for occurred timeouts or
  unsatisfiable problems.
- Changes to a crucial solver function drastically improved performance.
- Small bug fix in DerivationTree.

## [0.8.17] - 2022-08-17

### Added

- Added a method `ISLaSolver.fuzz()` that produces one solution at each call, i.e., not a generator of
  solutions as returned by `ISLaSolver.solver()`.

### Changed

- Better support for unsatisfiable formulas: States with unsatisfiable SMT-LIB atoms in their formulas
  are discarded early. Before, it could happen that the solver diverged. When checking unsatisfiable
  formulas with existential quantifiers, you have to set a timeout; the solver usually diverges (without
  producing an output) in these cases. \
  To use this, pass the parameter `activate_unsat_support=True` to the solver.

## [0.8.16] - 2022-08-16

### Added

- The *descendant* axis `..` is now supported in XPath expressions, as in `<xml-open-tag>.<id>..<id-char> = "a"`.
  Consult the [ISLa Language Specification](https://rindphi.github.io/isla/islaspec/#x-path-expressions)
  for more information.

### Changed

- Escaping in unparsing of grammars.

## [0.8.15] - 2022-08-15

### Added

- We added an `unparse_grammar` function that produces a string in concrete BNF syntax from a Python grammar.

### Changed

- Consolidated match expression matching and the conversion of match expression to tree prefixes; now conforms to the
  state described in the 
  [ISLa Language Specification](https://rindphi.github.io/isla/islaspec/#tree-quantifiers-with-match-expressions).
- We removed the mandatory semicolons as line terminators from the concrete grammar syntax; they are not necessary
  for parsing in our syntax, even with multi-line expansions. Now, the syntax is identical to classical BNF.
  Adding semicolon line terminators remains possible, but is optional (and superfluous).

## [0.8.14] - 2022-08-10

### Added

- Added parser for concrete BNF syntax. One can now call the ISLaSolver and the evaluate function
  with a string representation of the grammar, e.g.,
  
  ```bnf
   <start> ::= <stmt> ;
   <stmt> ::= <assgn> | <assgn> " ; " <stmt> ;
   <assgn> ::= <var> " := " <rhs> ;
   <rhs> ::= <var> | <digit> ;
   <var> ::= "a" | "b" | "c" ;
   <digit> ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ; 
  ```

## [0.8.13] - 2022-08-09

### Changed

- Bug fix in DerivationTree serialization.

## [0.8.12] - 2022-08-09

### Changed

- More space-efficient serialization of DerivationTree objects.
  
## [0.8.11] - 2022-08-09

### Changed

- Better serialization of DerivationTree objects.

## [0.8.10] - 2022-08-09

### Changed

- Linking new Fuzzing Book tutorial on ISLa in README.md.
- Added evaluation scripts.

## [0.8.9] - 2022-08-08

### Changed

- Propositional combinators (and, or, ...) can not be used also on SMT level, i.e., in s-expression syntax.

## [0.8.8] - 2022-08-08

### Changed

- Formulas like `forall <a> in <start>: ...` get now parsed like `forall <a> in start: ...`. Before, another quantifier
  was added to close over `<start>`.
- The `count` predicate now accepts a literal value as third argument, expected a variable before.
- Bug fix in handling of XPath expressions where at least two share a prefix (test case `test_length_prefixed_strings` in `test_concrete_syntax.py`).
- Bug fix in extracting strings from Z3 models: Now also handling null characters ("\u{}") correctly.

## [0.8.7] - 2022-08-07

### Added

- `isla.language.unparse_isla` shortcut to `ISLaUnparser` for getting the textual representation of an ISLa formula.
- Added `ISLaSolver.evaluate(tree)` method to quickly evaluate inputs based on an existing ISLaSolver object.

### Changed

- Bug fix: Indexes in XPath expressions (like `<a>.<b>[2].<c>`) work now. Remember: Counting starts from 1, which
  also is the default if you omit an index.
- Bug fix: ISLa's unparser returns correct result for nullary SMT-LIB functions (e.g., `re.all` instead of `(re.all)`).
- Bug fix: SMT-LIBs `div` and `mod` operators work now (also in infix syntax).
- Added mod to `evaluate_z3_expression` shortcut (which does not require Z3 solver calls).

## [0.8.6] - 2022-08-05

### Added

- Implemented `direct_child` predicate upon request.

## [0.8.5] - 2022-08-04

Small bugfix release.

## [0.8.4] - 2022-08-04

### Changed

- Updated build/test/install information in README.

## [0.8.1], [0.8.2], [0.8.3] - 2022-08-03 to 2022-08-04

Small bugfix releases.

## [0.8] - 2022-08-03

### Added

- Brief descriptions of the built-in predicates added to the README.md file.
  
### Changed

- Project package information was extended to prepare for publishing at PyPi.
- Version jump to signal PyPi maturity :) We're planning for an 1.0 release soon!

## [0.3] - 2022-08-03

### Added

- Cost computation is not outsourced to exchangeable `CostComputer` classes. The existing cost computation strategy
  is encapsulated in the class `GrammarBasedBlackboxCostComputer`.
- ISLa now has a simplified syntax layer, which is translated to the core syntax (it's "syntactic sugar"):
  * Names in quantifiers may be omitted; quantified elements can be referred to
    by their nonterminal types (if unambiguous) in quantifier core.
  * "Free" nonterminals are permitted, and are universally quantified (and `in <start>`) as default.
  * The `in ...` part of quantifiers may be omitted and defaults to `in <start>`.
  * For SMT expressions, we support an infix (for binary operators) and prefix (for unary ones) syntax 
    instead of the usual SMT-LIB S-Expressions.
  * Additionally to match expressions, we permit the *descendant axis* `.` (`..` is not yet implemented,
    but planned) borrowed from the [XPath abbreviated syntax](https://www.w3.org/TR/1999/REC-xpath-19991116/#path-abbrev)
    (there, one writes `/` and `//`). For `.`, the specification of a *position
    predicate* `[n]`, for $n=1,2,\dots$, is required, as in `<id>.<char>[2]` (the
    second `<char>` occurrence in an `<id>` nonterminal). If it is omitted, it
    defaults to `[1]`.

### Changed

- Removed deprecated/unused "cost phase" feature; `CostSettings` now expect a single `CostWeightVector` and a value
  for `k`, exclusively.
- Removed deprecated "vacuous penalty" cost feature from cost vector.
- Performance fix in tree expansion: If there is a limit on the number of desired expansions, we don't compute all
  of them and choose a subset afterward, but only compute the desired number of (random) expansions.
- Bug fix in tree expansion, more precisely in determining whether a nonterminal can be freely instantiated: If the
  nonterminal can be associated with a *dummy* variable in the match expression, we not correctly report that it
  is not bound by the quantifier and can be freely instantiated. This mitigates state explosion in certain cases.
- Performance fix: Lazy computation of complex string arguments passed to the logger.
- Removed all `fuzzingbook` dependencies. This significantly reduces the number of indirect dependencies
  that have to be installed.
- Split dependencies into required, dev, and test dependencies. If you want to develop or test ISLa, use
  `pip install -e .[dev,test]` in your virtual environment.
- Removed an assertion that made the solver fail for SMT constraints on non-regular nonterminals. For nonterminals
  with a context-free language, the regular expression passed to the SMT solver will always be an approximation,
  and it cannot be asserted that the languages of the subgrammar and the regex are identical.

## [0.2b3] - 2022-06-03

### Changed

- Simplification in assignment language example in README.
- Added README section about the new ISLa Docker image.

## [0.2b2] - 2022-06-03

### Added

- More precise translation of ISLa formulas to SMT (`evaluator.isla_to_smt_formula`),
  implication (`evaluator.implies`) and equivalence (`evaluator.equivalent`) checks.

### Changed

- Bugfixes in translation of Z3 regexes to Python.
- Z3 translation method `evaluate_z3_expression` can handle open variables and returns closures.
  Better caching opportunities.
- Factored out Z3 helpers from `isla.helpers` to `isla.z3_helpers`.
- `z3.ExprRef.__eq__` is pointed to `z3.AstRef.__eq__` when loading `isla.language`. The reason is
  that `__eq__` is called, e.g., when requesting elements from hash maps, but the `z3.ExprRef`
  implementation creates a new `z3.BoolRef` instead of returning a bool. We perform a structural
  comparison instead. To construct `z3.BoolRef` equations, use `isla.z3_helpers.z3_eq` instead.
- Performance optimization for semantic predicates.
- Performance optimizations in match expression matching.
- Cleaned up and relaxed requirements.

## [0.2b1] - 2022-02-25

### Added

- Evaluation routine for concrete Z3 expressions without solver calls. Speedups of 50 % to
  100 % in calls to `helpers.is_valid(Formula)`.
- Added a structural predicate `nth(idx, tree, in_tree)` which holds if `tree` is the `idx`-th
  occurrence of a tree with its nonterminal within `in_tree`. This is useful, e.g., in CSV files.

### Changed

- More efficient DerivationTree.replaceTree method.
- The evaluator for *concrete* SMT-LIB expressions handles `(str.to.int float_str)` for strings representing floating
  point numbers by rounding them to Integers. This differs from the standard SMT-LIB/Z3 semantics, where the result is
  -1 for all strings that are not positive Integers. It is planned to also integrate this into the more general Z3-based
  evaluation and into the solver.

## [0.2a2] - 2022-02-03

### Added

- Both the evaluator and the solver are passed default sets of predicates. Thus, unless some
  user-defined special predicates should be used, one does not need to pass the predicates to
  the solver/evaluator when generating from/checking a constraint in ISLa's concrete syntax
  (a string).
- Added universal integer quantification method for a special case:
  
      forall int i:
        exists <?> elem in container: 
          not phi(elem, i) 
  
  is transformed to

      exists int i: (
        exists <?> elem in container: 
          phi(elem, i) and 
        exists <?> elem in container: 
          not phi(elem, i))
 
  if the predicate / formula phi exactly holds true for a single instantiation of `i` once elem
  (and potentially other parameters) have fixed values. In the code, we briefly sketch a correctness
  proof that this transformation is equivalence-preserving.
- Constraint checking can consider preconditions. This is highly useful when eliminating existential
  quantifiers (esp. after re-insertion): They may not generally hold, but taking the already existing
  constraints into account.
- Added forgotten mention of the renaming of `isla.isla` to `isla.language` to
  the changelog (this file), section 0.2a1.
- It is now possible to create infinite streams of solutions from existential formulas. Before, the
  number of solutions was usually exactly one, unless one increased the number of free instantiations.

### Changed

- Factored out functions related to ISLa evaluations from `isla.language` to `isla.evaluator`.
  The previous `isla.evaluator` file was named `isla.performance_evaluator`. This change is also
  reflected in the organization of the tests in `tests/`.
- Checking whether existential (integer / tree) quantifiers are already satisfied, taking into account
  existing constraints (assumptions).
- Corrections in README.txt + clarifies in README that ISLa is a grammar-aware String constraint solver.

### Removed

- Removed "eval_results" folder. New evaluation scripts output SQLITE files.
- The deprecated solver parameter "expand_after_existential_elimination" was removed. The solver now
  always expands in parallel to existential elimination / tree insertion, thus infinite solution streams
  for existential formulas become possible. In recent ISLa versions, this parameter was anyway ignored.

## [0.2a1] - 2022-02-01

### Added

- Support for universal and existential quantifiers over integers: `forall int
  x: ...` and `exists int x: ...`. Existential quantification replaces the
  previous `num x: ...` syntax, universal quantification is new. ISLa is now
  also closed under negation for numeric quantifiers. The ISLa solver uses an
  incomplete approach to instantiate universal quantifiers over integers,
  depending on SMT formula (and possibly semantic predicates) on top level
  inside the inner formula.
- ISLa now has its own, performance-optimized grammar fuzzer (forked from
  the Fuzzing Book).

### Changed

- The ISLa concrete syntax was changed. In the new syntax, there is not variable
  definition block (`vars`) and the constant declaration is now optional (only
  needed if the top-level constant is not named "start" and has the nonterminal
  type `<start>`). Instead, all types are directly declared inside the
  constraint: E.g., `forall <expr> expr="{<sum> sum} + {<factor> factor}": ...`.
  The `constraint` keyword was also removed; an ISLa specification either
  consists of a constant declaration followed by an ISLa formula, or only of an
  ISLa formula.
- The ISLa source is now organized with a so-called ["src layout"](https://docs.pytest.org/en/6.2.x/goodpractices.html).
- The package `isla.isla` (i.e., the `isla.py` file in the `isla` package) was
  renamed to `isla.language`. Thus, you have to replace all `from isla.isla import ...`
  import statements (or similar) by `from isla.language import ...`.
- The existing language formalizations (e.g., Scriptsize-C and TAR) were moved
  into a package `isla_formalizations` under the `src` directory. Tests are now
  in the top-level directory `tests`, the evaluation scripts for the
  formalizations in the top-level `evaluations` directory. The demo file
  `xml_demo.py` moved to inside the `tests` directory. You can still run `tox`
  in the top-level directory to run tests. For running tests without tox, you
  might have to do a `pip install -e .` for an editable installation of ISLa
  (preferrably within a virtual environment).
- Switched to a PEP517-based build system. You can now run `python3 -m build`
  from inside the virtual environment to run a build. All settings are now in
  `setup.cfg`, the `setup.py` file is only there for backward compatibility and
  to make the "setuptools-antlr" package work (`python3 setup.py antlr`). Only
  ISLa developers need this.
- Various bug fixes, enhancements and new safety assertions related to
  existential quantifier solving (both instantiation and tree insertion).

### Removed

- The outdated formalizations for tiny-C and minipy were removed.
