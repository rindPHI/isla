ISLa: Input Specification Language
==================================

[![Python](https://img.shields.io/pypi/pyversions/isla-solver.svg)](https://pypi.python.org/pypi/isla-solver/)
[![Version](http://img.shields.io/pypi/v/isla-solver.svg)](https://pypi.python.org/pypi/isla-solver)
[![Build Status](https://img.shields.io/github/workflow/status/rindPHI/isla/Test%20ISLa)](https://github.com/rindPHI/isla/actions/workflows/test-isla.yml)
[![Coverage Status](https://coveralls.io/repos/github/rindPHI/isla/badge.svg?branch=main)](https://coveralls.io/github/rindPHI/isla?branch=main)
[![Dependencies](https://img.shields.io/librariesio/release/github/rindphi/isla)](https://libraries.io/github/rindPHI/isla)

ISLa is a grammar-aware String constraint solver with its own specification
language. The language is a superset of SMT-LIB for String constraints, and adds
the power of structural quantifiers over derivation trees on top. ISLa supports
universal and existential quantifiers as well as structural (e.g., "occurs
before") and semantic (e.g., "is a checksum") predicates. Its generation
mechanism uses feedback from Z3 to solve SMT-LIB formulas, and constructive
insertion for eliminating existential quantifiers. Universal quantifiers and
structural predicates are solved by a deterministic, heuristic-based search
(with a configurable cost function).

For more information on the ISLa language, take a look at the [**ISLa Language
Specification**](https://rindphi.github.io/isla/islaspec/). The specification
contains a list of [supported default
predicates](https://rindphi.github.io/isla/islaspec/#structural-predicates),
which might be useful in many cases.

We also offer an [**interactive ISLa
tutorial**](https://www.fuzzingbook.org/beta/html/FuzzingWithConstraints.html)
as part of the Fuzzing Book.

## Example

Consider a grammar of a simple assignment programming language (e.g., "x := 1 ; y := x"):

```python
import string

LANG_GRAMMAR = {
    "<start>":
        ["<stmt>"],
    "<stmt>":
        ["<assgn>", "<assgn> ; <stmt>"],
    "<assgn>":
        ["<var> := <rhs>"],
    "<rhs>":
        ["<var>", "<digit>"],
    "<var>": list(string.ascii_lowercase),
    "<digit>": list(string.digits)
}
```

An interesting, context-sensitive property for this language is that all right-hand side variables have been declared
somewhere before. In ISLa's concrete syntax, this can be expressed as a constraint

```
forall <assgn> assgn_1="<var> := {<var> rhs}" in start:
  exists <assgn> assgn_2="{<var> lhs} := <rhs>" in start:
    (before(assgn_2, assgn_1) and (= rhs lhs))
```

ISLa also allows writing binary SMT-LIB S-expressions in infix syntax: `(= rhs lhs)` gets `rhs = lhs`.
Furthermore, the `in start` is optional, and the "match expressions" `"{<var> lhs} := <rhs>"` etc. can (at least
in such simple cases) be expressed using a syntax inspired by the 
[XPath abbreviated syntax](https://www.w3.org/TR/1999/REC-xpath-19991116/#path-abbrev):

```
forall <assgn> assgn_1:
  exists <assgn> assgn_2:
    (before(assgn_2, assgn_1) and assgn_1.<rhs>.<var> = assgn_2.<var>)
```

Additionally, top-level universal quantifiers without match expressions (like `forall <assgn> assgn_1`) can be
omitted; instead of the bound name (e.g., `assgn_1`) one then simply uses the type (`<assgn>`) in the inner
formula. This only works for one such quantifier over any type, since otherwise, the names are needed for
disambiguation. The final, simpler formula is:

```
exists <assgn> assgn:
  (before(assgn, <assgn>) and <assgn>.<rhs>.<var> = assgn.<var>)
```

Using the Python API, the same constraint is written as follows:

```python
from isla import language
import isla.isla_shortcuts as sc 

mgr = language.VariableManager()

formula: language.Formula = mgr.create(sc.forall_bind(
    mgr.bv("$lhs_1", "<var>") + " := " + mgr.bv("$rhs_1", "<rhs>"),
    mgr.bv("$assgn_1", "<assgn>"),
    mgr.const("$start", "<start>"),
    sc.forall(
        mgr.bv("$var", "<var>"),
        mgr.bv("$rhs_1"),
        sc.exists_bind(
            mgr.bv("$lhs_2", "<var>") + " := " + mgr.bv("$rhs_2", "<rhs>"),
            mgr.bv("$assgn_2", "<assgn>"),
            mgr.const("$start"),
            sc.before(mgr.bv("$assgn_2"), mgr.bv("$assgn_1")) &
            mgr.smt(cast(z3.BoolRef, mgr.bv("$lhs_2").to_smt() == mgr.bv("$var").to_smt()))
        )
    )
))
```

The ISLa solver can find satisfying assignments for this formula:

```python
from isla.solver import ISLaSolver

solver = ISLaSolver(
    grammar=LANG_GRAMMAR,
    formula=formula,
    max_number_free_instantiations=10,
    max_number_smt_instantiations=10)

it = solver.solve()
while True:
    try:
        print(next(it))
    except StopIteration:
        break
```

When calling the solver with an ISLa formula in concrete syntax (a string), one has to supply a "signature" of the
structural and semantic predicate symbols used:

```python
from isla.solver import ISLaSolver
from isla.isla_predicates import BEFORE_PREDICATE

solver = ISLaSolver(
    grammar=LANG_GRAMMAR,
    formula=concrete_syntax_formula,
    structural_predicates={BEFORE_PREDICATE},
    max_number_free_instantiations=10,
    max_number_smt_instantiations=10)

it = solver.solve()
while True:
    try:
        print(next(it))
    except StopIteration:
        break
```

To create more diverse inputs, ISLa can be configured to perform a *bounded expansion* of grammar nonterminals that are
irrelevant for any constraint (parameter `max_number_free_instantiations`). Similarly, the number of solutions for
semantic SMT formulas can be configured (`max_number_smt_instantiations`).

In certain cases, ISLa will only produce a finite amount of solutions. This holds in particular for simple existential
constraints. The existential quantifier will be eliminated and the solution output; the search terminates then. Usually,
though, the stream of solutions will be infinite (given that the grammar contains recursions).

## Resources / Important Files

* The file `tests/xml_demo.py` demonstrates most ISLa features along the example of an XML constraint.
* In the directory `src/isla_formalizations/`, you find our specifications for the subject languages
  of our experimental evaluation.
* The files `evaluations/evaluate_...` are the scripts we used to collect and analyze our 
  evaluation data. By running these scripts without arguments, a digest of the most recent results is returned.
* The most important files of our implementation are `src/isla/language.py`, `src/isla/evaluator.py` 
  and `input_constraints/solver.py`, containing ISLa language features, the constraint checker, 
  and the ISLa solver. 

## Build, Run, Install

ISLa depends on Python 3.10 and the Python header files. To compile all of ISLa's dependencies, you need
gcc, g++ make, and cmake. To check out the current ISLa version, git will be needed. Furthermore, 
python3.10-venv is required to run ISLearn in a virtual environment. Additionally, for testing
ISLa, clang and the `csvlint` executable are required (for the Scriptsize-C and CSV case studies).

On *Alpine Linux*, all dependencies (but `csvlint`) can be installed using

```shell
apk add python3.10 python3.10-dev python3.10-venv gcc g++ make cmake git clang
```

The `csvlint` executable can be obtained from
https://github.com/Clever/csvlint/releases/download/v0.3.0/csvlint-v0.3.0-linux-amd64.tar.gz. You obtain and
unpack `csvlint` by running (in a Unix shell)

```shell
wget https://github.com/Clever/csvlint/releases/download/v0.3.0/csvlint-v0.3.0-linux-amd64.tar.gz -O /tmp/csvlint.tar.gz
tar xzf /tmp/csvlint.tar.gz -C /tmp
```

Then, move the file `/tmp/csvlint-v0.3.0-linux-amd64/csvlint` to some location in your PATH (e.g., `/usr/bin`).

### Docker

For testing ISLa without having to care about external dependencies like Python, we provide a Docker container,
which already contains all dependencies.

First, pull and run the Docker container:

```shell
docker pull dsteinhoefel/isla:latest
docker run -it --name isla dsteinhoefel/isla
```

You should now have entered the container. Next, check out the ISLa repository, and update the requirements:

```shell
git clone https://github.com/rindPHI/isla.git
cd isla/
```

Now, you can perform an editable installation of ISLa and run the ISLa tests:

```shell
pip install -e .[dev,test]
python3.10 -m pytest -n 16 tests
```

### Install

If all external dependencies are available, a simple `pip install isla-solver` suffices. We recommend installing 
ISLa inside a virtual environment (virtualenv):

```shell
python3.10 -m venv venv
source venv/bin/activate
pip install --upgrade pip
pip install isla-solver
```

### Build 

ISLearn is built locally as follows:

```shell
git clone https://github.com/rindPHI/isla.git
cd isla/

python3.10 -m venv venv
source venv/bin/activate

pip install --upgrade pip
pip install --upgrade build
python3 -m build
```

Then, you will find the built wheel (`*.whl`) in the `dist/` directory.

### Testing & Development

For development, we recommend using ISLa inside a virtual environment (virtualenv). By thing the following steps in a
standard shell (bash), one can run the ISLa tests:

```shell
git clone https://github.com/rindPHI/isla.git
cd isla/

python3.10 -m venv venv
source venv/bin/activate

pip install --upgrade pip
pip install -r requirements_test.txt

# Run tests
pip install -e .[dev,test]
python3 -m pytest -n 16 tests
```

Then you can, for instance, run `python3 tests/xml_demo.py` inside the virtual environment.

## Changelog

See [CHANGELOG.md](CHANGELOG.md).
