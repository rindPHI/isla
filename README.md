ISLa: Input Specification Language
==================================

[![Python](https://img.shields.io/pypi/pyversions/isla-solver.svg)](https://pypi.python.org/pypi/isla-solver/)
[![Version](http://img.shields.io/pypi/v/isla-solver.svg)](https://pypi.python.org/pypi/isla-solver)
[![Build Status](https://img.shields.io/github/workflow/status/rindPHI/isla/Test%20ISLa)](https://github.com/rindPHI/isla/actions/workflows/test-isla.yml)
[![Coverage Status](https://coveralls.io/repos/github/rindPHI/isla/badge.svg?branch=main)](https://coveralls.io/github/rindPHI/isla?branch=main)
[![Dependencies](https://img.shields.io/librariesio/release/github/rindphi/isla)](https://libraries.io/github/rindPHI/isla)
[![DOI](https://zenodo.org/badge/428626626.svg)](https://zenodo.org/badge/latestdoi/428626626)
[![Code style: black](https://img.shields.io/badge/code%20style-black-000000.svg)](https://github.com/psf/black)

<img src="isla_logo_bright_transparent.png" alt="ISLa Logo" style="margin-left: auto; margin-right: auto; display: block; width: 400px;"/> 

**_Inputs on Demand!_**

ISLa is a *grammar-aware string constraint solver* with its own specification language.
With ISLa, it is possible to specify *input constraints* like "a variable has to be
defined before it is used," "the `file name' block must be 100 bytes long," or "the
number of columns in all CSV rows must be identical."

Building on modern constraint solvers, ISLa provides you with a unique
flexibility to specify&mdash;and generate&mdash;the system inputs you need. ISLa can be
used for *precise fuzzing:* Keep adding input specifications until you are satisfied
with the number of inputs passing the tested system's parser. Furthermore, you can write
ISLa specifications to carve out specific inputs for testing a *particular program
functionality*.

## Example

Our running example is a simple "assignment language" consisting of strings such as
`x := 1 ; y := x`. As a first step towards using ISLa, we formalize this language as
a context-free grammar in [BNF](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form):

```bnf
<start> ::= <stmt> 
<stmt>  ::= <assgn> | <assgn> " ; " <stmt> 
<assgn> ::= <var> " := " <rhs> 
<rhs>   ::= <var> | <digit> 
<var>   ::= "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | 
            "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" |
            "u" | "v" | "w" | "x" | "y" | "z" 
<digit> ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
```

After saving this grammar to a file, say, `assgn.bnf`, we can already generate inputs
from the assignment grammar using the ISLa command line interface:

```bash
> isla solve assgn.bnf
s := t
```

The following command creates 10 assignments:

```bash
> isla solve -n 10 assgn.bnf
a := 6 ; j := x
q := u
e := h ; o := l ; g := w
s := i
k := v ; d := m ; f := 1
n := y ; t := 5
z := 3 ; p := 7 ; b := 0
c := 2 ; r := 4
q := 8 ; l := 9
u := 0
```

The setting `-n -1` specifies that we want to generate an infinite number of inputs.
Since we did not choose an ISLa constraint, we additionally have to choose a value
for the `-f` flag. This setting determines the number of times an input element that
is not subject to any constraint (which is the case here) should be expanded. The final
line "UNSAT" means that after these 10 solutions, no further solution could be found.
If "UNSAT" is the *first* line output by the solver, it is likely that the given
constraint is *unsatisfiable*, i.e., there exists no solution of this constraint with
respect to the current grammar.

With ISLa, we can restrict the assignment language on-demand. For example, the ISLa
constraint `<var> = "a"` results in assignment sequences only containing "a" variables:

```bash
> isla solve /tmp/assgn.bnf -n 10 -f 1 --constraint '<var> = "a"' 
a := 5 ; a := a ; a := 7
a := 6
a := a
a := 0 ; a := a ; a := a
a := a ; a := 1 ; a := 4
a := a ; a := 3 ; a := a
a := 8 ; a := 2
a := 9 ; a := a
a := a ; a := 9
a := a ; a := a
```

> :bulb: The setting `-f 1` restricts the number of times that ILSa randomly
> instantiates unconstrained input elements to one time. Here, this affects the
> `<digit>` nonterminals: Without `-f 1`, we would see 10 different variants of the
> first input with variying numbers in the first and third assignment.

Or do we prefer assignments where all digits can be divided by 2 without remainder? No
problem with ISLa:

```bash
> isla solve assgn.bnf -n 10 -f 1 -s 2 --constraint "str.to.int(<digit>) mod 2 = 0"
i := a ; x := 0 ; u := s
p := l ; m := 8 ; b := y
k := c ; t := d ; r := q
j := z
h := 0
e := 4
g := n ; v := f ; w := 4
o := o ; j := a ; c := 0
t := r ; k := 0 ; e := 0
k := t ; f := 8 ; e := 8
```

> :bulb: The `-s` flag specifies how many results for a single query should be obtained
> from the SMT solver Z3. We limited this number to 2 (the default is 10&mdash;the same
> default value is used for the `-f` flag) to obtain a wider diversity of inputs within
> the first 10 results.

The constraints above talk over *all* `<var>` and `<digit>` grammar nonterminals in
any derivation tree derived from the assignment language grammar. In addition to such
simple constraints, ISLa allows to explicitly *quantify* over grammar elements using
the `forall` and `exists` keywords.

Assume that an interpreter for our assignment language rejects inputs where a variable
is accessed that has not been previously assigned a value. This "definition-use"
property, which is a *semantic input property* of the language, is expressed as follows:

```
forall <assgn> assgn_1:
  exists <assgn> assgn_2: (
    before(assgn_2, assgn_1) and 
    assgn_1.<rhs>.<var> = assgn_2.<var>)
```

Since this is a more lengthy constraint, let us save it in a file `defuse.isla`. The
following command line invocation uses this constraint:

```bash
> isla solve -n 10 -f 1 -s 1 assgn.bnf defuse.isla
q := 2 ; m := 1 ; c := 4
p := 8 ; o := 3 ; l := p
z := 7 ; p := 6 ; e := p
d := 5 ; a := d ; h := 9
s := 0 ; x := 0
k := 8
p := 4 ; r := p
p := 6 ; u := p
p := 5 ; v := p
p := 3 ; p := 5 ; w := p
```

As we can see, all right-hand side variables occur at the left-hand side of a prior
assignment.

For more information on the command line interface, run `isla -h`. Each sub command
comes with its own help text; for example, `isla solve -h` provides details on how to
use the `solve` command.

You can also use the ISLa solver via its Python API:

```python
from isla.solver import ISLaSolver

grammar = '''
<start> ::= <stmt> 
<stmt>  ::= <assgn> | <assgn> " ; " <stmt> 
<assgn> ::= <var> " := " <rhs> 
<rhs>   ::= <var> | <digit> 
<var>   ::= "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | 
            "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" |
            "u" | "v" | "w" | "x" | "y" | "z" 
<digit> ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
'''

constraint = """
forall <assgn> assgn_1:
  exists <assgn> assgn_2: (
    before(assgn_2, assgn_1) and 
    assgn_1.<rhs>.<var> = assgn_2.<var>)
"""

solver = ISLaSolver(
    grammar=grammar,
    formula=constraint,
    max_number_free_instantiations=1,  # -f
    max_number_smt_instantiations=1,  # -s
)

for _ in range(10):
    print(solver.solve())
```

An example output of the above program snippet is:

```
q := 7 ; m := 1 ; c := 8
p := 2 ; o := 2 ; l := p
z := 9 ; p := 4 ; e := p
d := 8 ; a := d ; h := 5
s := 0 ; x := 0
k := 7
p := 8 ; r := p
p := 9 ; u := p
p := 4 ; v := p
p := 2 ; p := 1 ; w := p
```

## Further Resources

* Our [**interactive ISLa tutorial**](https://www.fuzzingbook.org/beta/html/FuzzingWithConstraints.html),
  published as a part of the Fuzzing Book, provides an easily accessible introduction
  to the specification and generation of custom system inputs using ISLa.

* We published a [**paper on ISLa**](https://publications.cispa.saarland/3596/7/Input%20Invariants.pdf)
  at ESEC/FSE 2022. The paper describes the ISLa language and solver more formally.

* The [**ISLa Language Specification**](https://rindphi.github.io/isla/islaspec/)
  precisely specifies the syntax and semantics of ISLa constraints. The specification
  also contains a list of
  [supported default predicates](https://rindphi.github.io/isla/islaspec/#structural-predicates).

* In the directory `src/isla_formalizations/`, you find our specifications for the
  subject languages of our experimental evaluation.
  
* The files `run_eval_....fish` are the scripts we used to collect and analyze our
  evaluation data. To analyze ISLa's current performance yourself, you can run the
  scripts with the `-h` argument to obtain some guidance on their parameters (the fish
  shell is required to use these scripts).

## Build, Run, Install

ISLa depends on **Python 3.10** and the Python header files. To compile all of ISLa's
dependencies, you need gcc, g++ make, and cmake. To check out the current ISLa version,
git will be needed. Furthermore, python3.10-venv is required to run ISLearn in a virtual
environment.

Additionally, *for testing ISLa*, clang and the `csvlint` executable are required (for
the Scriptsize-C and CSV case studies).

On *Alpine Linux*, all dependencies (but `csvlint`) can be installed using

```shell
apk add python3.10 python3.10-dev python3.10-venv gcc g++ make cmake git clang
```

The `csvlint` executable can be obtained from
https://github.com/Clever/csvlint/releases/download/v0.3.0/csvlint-v0.3.0-linux-amd64.tar.gz.
You obtain and unpack `csvlint` by running (in a Unix shell)

```shell
wget https://github.com/Clever/csvlint/releases/download/v0.3.0/csvlint-v0.3.0-linux-amd64.tar.gz -O /tmp/csvlint.tar.gz
tar xzf /tmp/csvlint.tar.gz -C /tmp
```

Then, move the file `/tmp/csvlint-v0.3.0-linux-amd64/csvlint` to some location in your
PATH (e.g., `/usr/bin`).

### Install

If all external dependencies are available, a simple `pip install isla-solver` suffices.
We recommend installing ISLa inside a virtual environment (virtualenv):

```shell
python3.10 -m venv venv
source venv/bin/activate
pip install --upgrade pip
pip install isla-solver
```

Now, the `isla` command should be available on the command line within the virtual
environment.

### Docker

For testing ISLa without having to care about external dependencies like Python, we provide a Docker container,
which already contains all dependencies.

First, pull and run the Docker container:

```shell
docker pull dsteinhoefel/isla:latest
docker run -it --name isla dsteinhoefel/isla
```

You should now have entered the container. Next, check out the ISLa repository, and
update the requirements:

```shell
git clone https://github.com/rindPHI/isla.git
cd isla/
```

Now, you can perform an editable installation of ISLa and run the ISLa tests:

```shell
pip install -e .[dev,test]
python3.10 -m pytest -n 16 tests
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

## Copyright, Authors and License

Copyright © 2022 [CISPA Helmholtz Center for Information Security](https://cispa.de/en).

The ISLa code and documentation was, unless otherwise indicated, authored by
[Dominic Steinhöfel](https://www.dominic-steinhoefel.de).

ISLa is released under the GNU General Public License v3.0 (see [COPYING](COPYING)).