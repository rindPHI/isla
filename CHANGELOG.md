# Changelog

This file contains the notable changes in the ISLa project since version 0.2a1
(February 2022). Changes prior to this date are not documented.

## [Unreleased]

### Added

- More precise translation of ISLa formulas to SMT (`evaluator.isla_to_smt_formula`),
  implication (`evaluator.implies`) and equivalence (`evaluator.equivalent`) checks.

### Changed

- Bugfixes in translation of Z3 regexes to Python
- Z3 translation method `evaluate_z3_expression` can handle open variables and returns closures.
  Better caching opportunities.
- Factored out Z3 helpers from `isla.helpers` to `isla.z3_helpers`.
- `z3.ExprRef.__eq__` is pointed to `z3.AstRef.__eq__` when loading `isla.language`. The reason is
  that `__eq__` is called, e.g., when requesting elements from hash maps, but the `z3.ExprRef`
  implementation creates a new `z3.BoolRef` instead of returning a bool. We perform a structural
  comparison instead. To construct `z3.BoolRef` equations, use `isla.z3_helpers.z3_eq` instead.
- Performance optimization for semantic predicates.
- Performance optimizations in match expression matching.

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
