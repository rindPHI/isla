ISLa: Input Specification Language
==================================

ISLa is a specification language for constraints on complex structured inputs conforming to a given, context-free
grammar. It contains the language of SMT (z3) formulas as an island language, and adds the power of structural
quantifiers over derivation trees on top. ISLa supports universal and existential quantifiers as well as structural
predicates (e.g., "occurs before"). Its generation mechanism uses feedback from z3 to solve atomic
"semantic" formulas, and constructive insertion for eliminating existential quantifiers. Universal quantifiers and
structural predicates are treated by a deterministic, heuristic breath-first search.

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
forall <assgn> assgn_1="{<var> lhs_1} := {<rhs> rhs_1}" in start:
  forall <var> var in rhs_1:
    exists <assgn> assgn_2="{<var> lhs_2} := {<rhs> rhs_2}" in start:
      (before(assgn_2, assgn_1) and (= lhs_2 var))
```

or, using the Python API,

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

* The file `input_constraints/xml_demo.py` demonstrates most ISLa features along the example of an XML constraint.
* In the directory `input_constraints/tests/subject_languages/`, you find our specifications for the subject languages
  of our experimental evaluation.
* The files `input_constraints/evaluations/evaluate_...` are the scripts we used to collect and analyze our 
  evaluation data. By running these scripts without arguments, a digest of the most recent results is returned.
* In `eval_results`, you find the raw data of our experimental analysis. These files generally consist of the number
  of seconds since start of the experiment when a data item was collected, and the accumulated numbers of valid / 
  invalid inputs or k-paths, depending on the file.
* The most important files of our evaluation are `input_constraints/isla.py` and `input_constraints/solver.py`,
  containing most ISLa features (and the constraint checker) resp. the ISLa solver. 

## Build, Run, Install

ISLa depends on Python 3.10 and the Python header files (from package python3.10-dev in Ubuntu Linux). Furthermore, 
python3.10-venv is required to run ISLa in a virtual environment.

On Ubuntu Linux, the dependencies can be installed using

```shell
sudo apt-get update
sudo apt-get upgrade
sudo apt-get install python3.10 python3.10-dev python3.10-venv
```

For development and testing, we recommend to use ISLa inside a virtual environment (virtualenv).
By thing the following steps in a standard shell (bash), one can run the ISLa tests:

```shell
curl -L https://anonymous.4open.science/r/isla-pldi/ISLa-v0.1.zip
unzip ISLa-v0.1.zip

python3.10 -m venv venv
source venv/bin/activate

pip install --upgrade pip
pip install -r requirements.txt
pip install z3-solver=4.8.14.0

# Run tests
tox
```

NOTE: This projects needs z3 >= 4.8.13.0, but the requirements only list
4.8.8.0 due to a strict requirement in the fuzzingbook package. After
installing from requirements, you have to manually install a new z3 version
(e.g., `pip install z3-solver=4.8.14.0`) and simply ignore the upcoming
warning.

For running scripts without tox, you have to add the path to the ISLa folder to the PYTHONPATH environment
variable; this is done by typing (in bash)

```shell
export PYTHONPATH=$PYTHONPATH:`pwd`
```

inside the ISLa top-level directory. Then you can, for instance, run `python3 input_constraints/xml_demo.py` (after
entering the virtual environment as described above). For using ISLa in Visual Studio, you might have to set
the value of the environment variable in the launch.json file; in Pycharm, we did not have to apply any special 
settings.

---

To install ISLa globally (not recommended, less well tested), run

```shell
python3 -m build
```

## Changelog

See [CHANGELOG.md](CHANGELOG.md).
