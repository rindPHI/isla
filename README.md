ISLa: Input Specification Language
==================================

ISLa is a specification language for constraints on structured inputs conforming to a given, context-free grammar. It
contains the language of SMT (z3) formulas as an island language, and adds the power of structural quantifiers over
derivation trees on top. ISLa supports universal and existential quantifiers as well as structural predicates (e.g., "
occurs before"). Its generation mechanism uses feedback from z3 to solve atomic
"semantic" formulas, and constructive insertion for eliminating existential quantifiers. Universal quantifiers and
structural predicates are treated by a top-level, deterministic breath-first search.

## Example

Consider a grammar of a simple assignment programming language (e.g., "x := 1 ; y := x"):

```python
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
const start: <start>;

vars {
    lhs_1, var, lhs_2: <var>;
    rhs_1, rhs_2: <rhs>;
    assgn_1, assgn_2: <assgn>;
}

constraint {
  forall assgn_1="{lhs_1} := {rhs_1}" in start:
    forall var in rhs_1:
      exists assgn_2="{lhs_2} := {rhs_2}" in start:
        (before(assgn_2, assgn_1) and (= lhs_2 var))
}
```

or, using the Python API,

```python
from input_constraints import isla

mgr = isla.VariableManager()

formula: isla.Formula = mgr.create(sc.forall_bind(
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
from input_constraints.solver import ISLaSolver
from input_constraints.tests.test_data import LANG_GRAMMAR

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
from input_constraints.solver import ISLaSolver
from input_constraints.tests.test_data import LANG_GRAMMAR
from input_constraints.isla_predicates import BEFORE_PREDICATE

solver = ISLaSolver(
    grammar=LANG_GRAMMAR,
    formula=concrete_syntax_formula,
    structural_predicates={"before": BEFORE_PREDICATE},
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

## ISLa Concrete Syntax

The (abbreviated) E-BNF grammar for the concrete syntax of ISLa formulas is:

```
⟨start⟩ := ⟨const⟩⟨vars_block⟩⟨constraint_decl⟩
⟨const⟩ := ‘const␣’⟨id⟩‘:␣’⟨nonterminal⟩‘;’

⟨vars_block⟩ := 𝜖| ‘vars␣{’⟨var_decl⟩+‘}’
⟨var_decl⟩ := ⟨ID⟩𝓁‘:␣’⟨nonterminal⟩‘;’
⟨nonterminal⟩ := ‘<’⟨LETTER⟩+‘>’

⟨constraint_decl⟩ := ‘constraint␣{’⟨constraint⟩‘}’
⟨constraint⟩ := ⟨disjunction⟩
⟨disjunction⟩ := ⟨conjunction⟩
| ‘(’ ⟨conjunction⟩ ‘␣or␣’ ⟨disjunction⟩ ‘)’

⟨conjunction⟩ := ⟨negation⟩ | ‘(’ ⟨negation⟩ ‘␣and␣’ ⟨conjunction⟩ ‘)’
⟨negation⟩ := ⟨smt_atom⟩ | ⟨predicate_atom⟩ | ⟨quantified_formula⟩ | ‘not␣(’ ⟨constraint⟩ ‘)’

⟨quantified_formula⟩ := ⟨quantifier⟩ ‘␣’ ⟨id⟩ ‘␣in␣’ ⟨id⟩ ‘:␣’ ⟨constraint⟩ | ⟨quantifier⟩ ‘␣’ ⟨id⟩ ‘=’

⟨match_expr⟩ ‘␣in␣’ ⟨id⟩ ‘:␣’ ⟨constraint⟩
⟨quantifier⟩ := ‘forall’ | ‘exists’
⟨match_expr⟩ := ‘"’ ⟨var_esc_char⟩𝓁 ‘"’

⟨var_esc_char⟩ := ‘{’⟨id⟩‘}’| ...
⟨smt_atom⟩ := ⟨smt_bool⟩
⟨smt_bool⟩ := ‘true’| ‘false’ | ‘(’ ⟨FSYM⟩ ‘␣’ ⟨sexpr⟩ (‘␣’ ⟨sexpr⟩)* ‘)’

⟨sexpr⟩ := ⟨smt_bool⟩ | ⟨NUMBER⟩ | ⟨id⟩ | ⟨STRING⟩
⟨predicate_atom⟩ := ⟨predicate⟩‘(’⟨arg⟩𝓁‘)’
⟨arg⟩ := ⟨id⟩ | ⟨NUMBER⟩ | ⟨STRING⟩
```

For any `⟨arg⟩`, the symbol `⟨arg⟩𝓁` stands for `⟨arg⟩ | ⟨arg⟩ ',␣' ⟨arg⟩𝓁`. The most important context-sensitive
property of the language is that all identifiers have to be declared; furthermore, SMT expressions have to use function
symbols declared in some theory and arguments of the right sorts. Predicate symbols have to stem from a known signature,
and the arity of the predicate symbol has to match the number of the supplied predicates.

## Build and Install

To install ISLa globally, run

```shell
pip install -r requirements.txt
python setup.py install
```

For development, we recommend to use ISLa inside a virtual environment (virtualenv):

```shell
virtualenv -p python3 venv
source venv/bin/activate
pip install -r requirements.txt

# Run tests
tox
```
