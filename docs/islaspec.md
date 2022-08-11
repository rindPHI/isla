---
title: "The ISLa Language Specification"
permalink: /islaspec/
---

# The ISLa Language Specification

The Input Specification Language (ISLa) is a notation for formally specifying
context-sensitive properties of strings structured by a context-free grammar.
The purpose of this document is to precisely specify ISLa's syntax and
semantics.

The ISLa version considered in this document is ISLa
[0.8.14](https://github.com/rindPHI/isla/tree/v0.8.14). Please consult the [ISLa
CHANGELOG](https://github.com/rindPHI/isla/blob/main/CHANGELOG.md) to find out
if there were recent additions.

## [Table of Contents](#toc)


<!-- vim-markdown-toc GFM -->

- [Introduction](#introduction)
- [Syntax](#syntax)
  - [Grammars](#grammars)
  - [Lexer Rules](#lexer-rules)
  - [Parser Rules](#parser-rules)
  - [Match Expression Lexer Rules](#match-expression-lexer-rules)
  - [Match Expression Parser Rules](#match-expression-parser-rules)
- [Simplified Syntax](#simplified-syntax)
- [Semantics](#semantics)
  - [Atoms](#atoms)
    - [SMT-LIB Expressions](#smt-lib-expressions)
    - [Structural Predicates](#structural-predicates)
    - [Semantic Predicates](#semantic-predicates)
  - [Propositional Combinators](#propositional-combinators)
  - [Quantifiers](#quantifiers)
    - [Tree Quantifiers](#tree-quantifiers)
    - [Numeric Quantifiers](#numeric-quantifiers)
- [Footnotes](#footnotes)

<!-- vim-markdown-toc -->

## [Introduction](#introduction)

Strings are the basic datatype for software testing and debugging at the system
level: All programs inputs and outputs are strings, or can be straightforwardly
represented as such. In parsing and fuzzing, Context-Free Grammars (CFGs) are a
popular formalism to decompose unstructured strings of data.

Consider, for example, a simple language of assignments such as `x := 1 ; y :=
x`. The following grammar, here presented in [Extended Backus–Naur Form
(EBNF)](https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form), can be
used to parse and produce syntactically valid assignment programs:

```
stmt  = assgn, { " ; ", stmt } ;
assgn = var, " := ", rhs ;
rhs   = var | digit ;
var   = "a" | "b" | "c" | ... ;
digit = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
```

Using this grammar, the input `x := 1 ; y := x` can be parsed into the following
tree structure:

```
stmt
├─ assgn
│  ├─ var
│  │  └─ "x"
│  ├─ " := "
│  └─ rhs
│     └─ digit
│        └─ "1"
├─ " ; "
└─ stmt
   └─ assgn
      ├─ var
      │  └─ "y"
      ├─ " := "
      └─ rhs
         └─ var
            └─ "x"
```

In the context of parsing, such trees are called "parse trees;" in the fuzzing
domain, the notion "derivation tree" is preferred. In this document, we will use
the term "derivation tree."

We call labels of the inner nodes of derivation trees such as `stmt` that have
to be further *expanded* to produce or parse a string "nonterminal elements" or
simply "nonterminals;" consequently, the leaves of the tree are labeled with
"terminal elements" or "terminals." From a tree, we obtain a string by chaining
the terminals in the order in which they are visited in a depth-first traversal
of the tree. CFGs map nonterminals to one or more *expansion alternatives* or,
simply, *expansions.* When using a grammar for fuzzing, we can expand a
nonterminal using any alternative. During parsing, we have to find the right
alternative for the given input (that is, *one* right alternative, since CFGs
can be *ambiguous*).

CFGs allow decomposing strings into their elements. However, they are&mdash;by
definition&mdash;too coarse to capture *context-sensitive* language features. In
the case of our assignment language, `x := 1 ; y := z` is not considered a valid
element of the language, since the identifier `z` has not been assigned before
(such that its value is `undefined`). Similarly, the program `x := x` is
"illegal." This property, that all right-hand side variables must have been
assigned in a previous assignment, could, in principle, be expressed in a less
restricted grammar. Examples are context-sensitive or even unrestricted
grammars, where left-hand sides can contain additional context in addition to a
single nonterminal value. However, such grammars are tedious to use in
specification, and we do not know any parsing or fuzzing tool based on more
general grammar formalisms.

Enter ISLa. ISLa specifications are based on a *reference grammar.* The
nonterminals of that grammar determine the vocabulary of the grammar. They take
the roles of variables in unit-level specification languages like
[JML](https://www.cs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman.html). The
following ISLa constraint restricts the language of the reference grammar shown
above to exactly those assignment programs using only previously assigned
variables as right-hand sides:

```
forall <assgn> assgn:
  exists <assgn> decl: (
    before(decl, assgn) and 
    assgn.<rhs>.<var> = decl.<var>
  )
```

In ISLa language, nonterminals are surrounded by angular brackets (see also the
[section on grammars](#grammars)). The above constraint specifies that 

* **for all** `<assgn>` elements that have a `<var>` right-hand side (to
  satisfy the `assgn.<rhs>.<var>`) and which we refer to with the name `assgn`,
* there has to **exist** an `<assgn>` element that we will call `decl`,
* such that `decl` appears **before** `assgn` in the input **and**
* the variable in the right-hand side of `assgn` equals the variable in `decl`.
 
Note that the `.` syntax allows accessing *immediate* children of elements in
the parse tree; `decl.<var>` thus uniquely identifies the left-hand side of an
assignment (since variables in right-hand sides appear as a child of a `<rhs>`
nonterminal).

In the remainder of this document, we specify the [syntax](#syntax) and
[semantics](#semantics) of ISLa formulas.

## [Syntax](#syntax)

In this section, we describe the [syntax of ISLa's reference
grammars](#grammars) and the syntax of ISLa formulas themselves. We introduce
the ISLa syntax on a high level by providing grammars in
[EBNF](https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form). In the
[section on ISLa's semantics](#semantics), we discuss the individual ISLa syntax
elements in more details and explain their meaning formally and based on
examples.

### [Grammars](#grammars)

ISLa's uses simple CFGs as reference grammars, i.e., without repetition etc.
Valid ISLa grammars are exactly those that can be expressed in [Backus-Naur Form
(BNF)](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form).[^1] The only
syntactical addition is that ISLa's grammar rules have to end with a semi-colon
`;`, which facilitates the definition of rules spanning multiple lines.

[^1]: From [ISLa 0.8.14](https://github.com/rindPHI/isla/blob/v0.8.14/CHANGELOG.md) on, the `ISLaSolver` and the `evaluate` function both accept grammars in concrete syntax in addition to the Python dictionary format of the [Fuzzing Book](https://www.fuzzingbook.org/html/Grammars.html).

The EBNF grammar for the concrete syntax of ISLa reference grammars looks as
follows, where `NO_ANGLE_BRACKET` represents any character but `<` and `>`:

```
bnf_grammar = derivation_rule, { derivation_rule } ;

derivation_rule = NONTERMINAL, "::=", alternative, { "|", alternative }, ";" ;

alternative = ( STRING | NONTERMINAL ) { STRING | NONTERMINAL } ;

NONTERMINAL = "<", NO_ANGLE_BRACKET, { NO_ANGLE_BRACKET }, ">" ;

STRING = '"' { ESC|. }? '"';
ESC = '\\' ("b" | "t" | "n" | "r" | '"' | "\\") ;
```

Here's how our example grammar from the [introduction](#introduction) looks in
this format (we abbreviated the definition of `<var>`):

```
<start> ::= <stmt> ;
<stmt> ::= <assgn> | <assgn> " ; " <stmt> ;
<assgn> ::= <var> " := " <rhs> ;
<rhs> ::= <var> | <digit> ;
<var> ::= "a" | "b" | "c" | ... ;
<digit> ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
```

### [Lexer Rules](#lexer-rules)

ISLa's lexer grammar is shown below. In addition to the rules shown, ISLa knows
Python-style line comments starting with `#`. These comments as well as
whitespace between tokens are ignored during lexing. The only string delimiter
known to ISLa are double quotes `"`. Inside strings, double quotes are escaped
using a backslash character: `\"`. Most notably, this also holds for [SMT-LIB
expressions](#smt-lib-expressions), which is a deviation from the SMT-LIB
standard where quotes are escaped by doubling them. In standard SMT-LIB, a
quotation mark inside double quotes is expressed (`""""`), whereas in ISLa, one
writes `"\""`.

```
AND = "and" ;
OR = "or" ;
NOT = "not" ;

XOR = "xor" ;
IMPLIES_SMT = "=>" ;
IMPLIES_ISLA = "implies" ;

SMT_INFIX_RE_STR =
      "re.++"
    | "str.++"
    | "str.<="
    ;

SMT_NONBINARY_OP =
      ABS
    | "re.+"
    | "re.*"
    | "str.len"
    | "str.in_re"
    | "str.to_re"
    | "re.none"
    | "re.all"
    | "re.allchar"
    | "str.at"
    | "str.substr"
    | "str.prefixof"
    | "str.suffixof"
    | "str.contains"
    | "str.indexof"
    | "str.replace"
    | "str.replace_all"
    | "str.replace_re"
    | "str.replace_re_all"
    | "re.comp"
    | "re.diff"
    | "re.opt"
    | "re.range"
    | "re.loop"
    | "str.is_digit"
    | "str.to_code"
    | "str.from_code"
    | "str.to.int"
    | "str.from_int"
    ;

XPATHEXPR = (ID | VAR_TYPE), XPATHSEGMENT, { XPATHSEGMENT } ;

XPATHSEGMENT =
      DOT, VAR_TYPE
    | DOT, VAR_TYPE, BROP, INT, BRCL
    | TWODOTS, VAR_TYPE
    ;

VAR_TYPE  = LT, ID, GT ;

DIV = "div" ;
MOD = "mod" ;
ABS = "abs" ;

STRING = '"', { ESC | . }?, '"';
ID = ID_LETTER, { ID_LETTER | DIGIT } ;
INT  = DIGIT, { DIGIT } ;
ESC  = "\\", ( "b" | "t" | "n" | "r" | '"' | "\\" ) ;

DOT  = "." ;
TWODOTS  = ".." ;
BROP  = "[" ;
BRCL  = "]" ;

MUL = "*" ;
PLUS = "+" ;
MINUS = "-" ;
GEQ = ">=" ;
LEQ = "<=" ;
GT = ">" ;
LT = "<" ;

ID_LETTER  = "a".."z" | "A".."Z" | "_" | "\\" | "-" | "." | "^" ;
DIGIT  = "0".."9" ;
```

### [Parser Rules](#parser-rules)

Below, you find ISLa's parser grammar. [SMT-LIB
expressions](#smt-lib-expressions) are usually expressed in a Lisp-like
S-expression syntax, e.g., `(= x (+ y 13))`. This is fully supported by ISLa,
and is robust to extensions in the SMT-LIB format as long as new function
symbols can be parsed as alphanumeric identifiers. Our prefix and infix syntax
that we added on top of S-expressions, as well as expressions using operators
with special characters, are only parsed correctly if the operators appear in
the [lexer grammar](#lexer-rules). This is primarily to distinguish expressions
in prefix syntax (`op(arg1, arg1, ...)`) from
[structural](#strucural-predicates) and [semantic
predicates](#semantic-predicates). In future versions of the grammar, we might
relax this constraint.

Match expressions (see the section on [quantifiers](#quantifiers)) are hidden
inside the underspecified nonterminal `MATCH_EXPR`. We describe the
[lexer](#match-expression-lexer-rules) and [parser](#match-expression-parser-rules) grammars
for match expressions further below.

```
isla_formula = [ const_decl ], formula;

const_decl = "const", ID, ":", VAR_TYPE, ";" ;

formula =
    "forall", VAR_TYPE, [ ID ],                  [ "in" (ID | VAR_TYPE) ], ":", formula
  | "exists", VAR_TYPE, [ ID ],                  [ "in" (ID | VAR_TYPE) ], ":", formula
  | "forall", VAR_TYPE, [ ID ], "=", MATCH_EXPR, [ "in" (ID | VAR_TYPE) ], ":", formula
  | "exists", VAR_TYPE, [ ID ], "=", MATCH_EXPR, [ "in" (ID | VAR_TYPE) ], ":", formula
  | "exists", "int", ID, ":", formula
  | "forall", "int", ID, ":", formula
  | "not", formula
  | formula, AND, formula
  | formula, OR, formula
  | formula, XOR, formula
  | formula, IMPLIES_ISLA, formula
  | formula, "iff", formula
  | ID, "(", predicate_arg, { ",", predicate_arg }, ")"
  | "(", formula, ")"
  | sexpr
  ;

sexpr =
    "true"
  | "false"
  | INT
  | ID
  | XPATHEXPR
  | VAR_TYPE
  | STRING
  | SMT_NONBINARY_OP 
  | smt_binary_op
  | SMT_NONBINARY_OP, "(", [ sexpr, { "," sexpr } ], ")"
  | sexpr, SMT_INFIX_RE_STR, sexpr
  | sexpr, ( PLUS | MINUS ), sexpr
  | sexpr, ( MUL | DIV | MOD ), sexpr
  | sexpr, ( "=" | GEQ | LEQ | GT | LT ), sexpr
  | "(", sexpr, sexpr, { sexpr }, ")"
  ;

predicate_arg = ID | VAR_TYPE | INT | STRING | XPATHEXPR ;


smt_binary_op:
  '=' | GEQ | LEQ | GT | LT | MUL | DIV | MOD | PLUS | MINUS | SMT_INFIX_RE_STR | AND | OR | IMPLIES_SMT | XOR ;
```

### [Match Expression Lexer Rules](#match-expression-lexer-rules)

We show the actual ANTLR rules of the match expression lexer, since they use
ANTLR "modes" to parse variable declarations and optional match expression
elements into tokens. For details on match expressions, we refer to the [section
on quantifiers](#quantifiers).

```
BRAOP : '{' -> pushMode(VAR_DECL) ;

OPTOP : '[' -> pushMode(OPTIONAL) ;

TEXT : (~ [{[]) + ;

NL : '\n' + -> skip ;

mode VAR_DECL;
BRACL : '}' -> popMode ;
ID: ID_LETTER (ID_LETTER | DIGIT) * ;
fragment ID_LETTER : 'a'..'z'|'A'..'Z' | [_\-.] ;
fragment DIGIT : '0'..'9' ;
GT: '>' ;
LT: '<' ;
WS : [ \t\n\r]+ -> skip ;

mode OPTIONAL;
OPTCL : ']' -> popMode ;
OPTTXT : (~ ']') + ;
```

### [Match Expression Parser Rules](#match-expression-parser-rules)

The parser rules for match expressions are depicted below in the EBNF format.

```
matchExpr = matchExprElement, { matchExprElement } ;

matchExprElement =
    BRAOP, varType, ID, BRACL
  | OPTOP, OPTTXT, OPTCL
  | TEXT
  ;

varType : LT ID GT ;
```

## [Simplified Syntax](#simplified-syntax)

(work in progress)

## [Semantics](#semantics)

In this section, we discuss ISLa's *semantics*, i.e., what an ISLa specification
*means*. Clearly, there has to be a relation between ISLa formulas and strings,
since ISLa is a specification language for strings.  However, it is more
convenient to define the semantics of an ISLa formula as the set of *derivation
trees* it represents.

On a high level, we define the semantics of a context-free grammar as the set of
derivation trees that can be (transitively) derived from its start symbol. In
the subsequent sections, we define (for each ISLa syntax element) a relation
\\(t\models{}\varphi\\) that holds if, and only if, the derivation tree \\(t\\)
*satisfies* the ISLa formula \\(\varphi\\). Finally, the semantics of an ISLa
formula \\(\varphi\\) are all derivation trees represented by the reference
grammar that satisfy \\(\varphi\\).

The *language* of CFGs, i.e., the strings they represent, is thoroughly defined
in the standard literature.[^2] We follow the same style. We assume a relation
\\(t\Rightarrow{}t'\\) between derivation trees that holds if \\(t'\\) can be
*derived* from \\(t\\) by adding to some leaf node in \\(t\\) labeled with a
nonterminal symbol \\(n\\) new children nodes corresponding to some expansion
alternative for \\(n\\). For example, consider the following derivation tree:

[^2]: For example, 	John E. Hopcroft, Rajeev Motwani, Jeffrey D. Ullman: *Introduction to Automata Theory, Languages, and Computation, 3rd Edition*. Pearson international edition, Addison-Wesley 2007, ISBN 978-0-321-47617-3.

```
<stmt>
├─ <assgn>
│  ├─ <var>
│  │  └─ "x"
│  ├─ " := "
│  └─ <rhs>
│     └─ <digit>
│        └─ "1"
├─ " ; "
└─ <stmt>
```

Using the expansion alternative `<stmt> ::= <assgn>` from the [(BNF) grammar for
our assignment language](#grammars), we can expand the open `<stmt>` node by
adding an `<assgn>` child. The result looks as follows:

```
<stmt>
├─ <assgn>
│  ├─ <var>
│  │  └─ "x"
│  ├─ " := "
│  └─ <rhs>
│     └─ <digit>
│        └─ "1"
├─ " ; "
└─ <stmt>
   └─ <assgn>
```

This is not the only option: We can also expand `<stmt>` with the expansion
alternative `<stmt> ::= <assgn> " ; " <stmt>`, which results in

```
<stmt>
├─ <assgn>
│  ├─ <var>
│  │  └─ "x"
│  ├─ " := "
│  └─ <rhs>
│     └─ <digit>
│        └─ "1"
├─ " ; "
└─ <stmt>
   ├─ <assgn>
   ├─ " ; "
   └─ <stmt>
```

If \\(t\\) is the initial tree and \\(t_1\\) and \\(t_2\\) are the two
expansions, then both \\(t\Rightarrow{}t_1\\) and \\(t\Rightarrow{}t_2\\) hold.
Now, let \\(\Rightarrow^\star\\) be the reflexive and transitive closure of
\\(\Rightarrow\\). Then, the set of derivation trees \\(T(G)\\) represented by a
CFG \\(G\\) is defined as \\(T(G):=\\{t\,\vert\,t_0\Rightarrow^\star{}t\\}\\),
where \\(t_0\\) is a derivation tree consisting only of the grammar's start
symbol.

Assuming the relation \\(\models\\) has been defined, we define the semantics
\\([\\![\varphi]\\!]\\) of an ISLa formula \\(\varphi\\) as
\\([\\![\varphi]\\!]:=\\{t\in{}T(G)\,\vert\,t\models\varphi\wedge\mathit{closed}(t)\\}\\), 
where \\(G\\) is the reference grammar for \\(\varphi\\) and
the predicate \\(\mathit{closed}\\) holds for all derivation trees whose leaves
are labeled with *terminals*.

In the remaining parts of this section, we discuss each element of the ISLa
syntax and define the relation \\(\models\\) along the way.

When doing so, we also need (and define step by step) a function
\\(\mathit{freeVars}(\varphi)\\) that returns the *free variables* of a formula
\\(\varphi\\). Those are the variables that are not bound by a
[quantifier](#quantifiers). 

In ISLa, all variables are of "string" sort. This is especially important when
writing [SMT-LIB expressions](#smt-lib-expressions), since appropriate
conversions have to be added when, e.g., comparing a variable *representing* an
integer to an actual integer.

To define \\(\models\\) for formulas with free variables, we use an additional
*variable assignment* \\(\beta\\) associating variables with derivation trees.
We write \\(\beta\models\varphi\\) to express that \\(\varphi\\) holds when
instantiating free variables in \\(\varphi\\) according to the assignments in
\\(\beta\\).

The notation \\(t\models\varphi\\) used above, where \\(t\\) is a derivation
tree, is a *shortcut*. When specifying an ISLa formula, we can declare a *global
constant* using the syntax `const constant_name: <constant_type>;` (cf. the
[ISLa grammar](#parser-rules)). The declaration is optional; if it is not
present, a constant `start` of type `<start>` will be assumed. Assuming `c` is
this constant, then \\(t\models\varphi\\) is 

* *undefined* if \\(\mathit{freeVars}(\varphi)\neq\\{c\\}\\).
* equivalent to \\([c\mapsto{}t]\models\varphi\\), where \\([c\mapsto{}t]\\) is a variable
  assignment mapping \\(c\\) to \\(t\\). 

### [Atoms](#atoms)

The name ISLa has a double meaning: First, it is an acronym for "Input
specification language;" and second, "isla" is the Spanish word for "island."
The reason for this second meaning is that ISLa embeds the [SMT-LIB
language](https://smtlib.cs.uiowa.edu/) as an *island language.* Around this
embedded language, ISLa essentially adds quantifiers aware of the structure of
context-free grammars. Thus, SMT-LIB expressions are the heart and the most
important *atomic* ISLa formulas. Atomic means that they do not contain
additional ISLa subformulas. ISLa also knows another type of atomic formula:
*predicate formulas.* Here, we distinguish *structural* and *semantic*
predicates. Structural predicates allow addressing structural relations such as
"before" of "inside;" semantic predicates complement SMT-LIB and allow
expressing complex constraints that are out of reach of the SMT-LIB language.
This section address all three types of ISLa atoms.

#### [SMT-LIB Expressions](#smt-lib-expressions)

ISLa embeds the SMT-LIB language. Since all ISLa variables are strings, the
[SMT-LIB string
theory](https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml) is the most
relevant theory in the ISLa context. The function `str.to.int`[^3] converts
strings to integers, such that integer operations using the [integer
theory](https://smtlib.cs.uiowa.edu/theories-Ints.shtml) are possible. A typical
SMT-LIB ISLa constraint (inspired by our [ISLa
tutorial](https://www.fuzzingbook.org/beta/html/FuzzingWithConstraints.html)) is
`(>= (str.to.int pagesize) 100)`. For this to work, all derivation trees that
can be substituted for the `pagesize` variable have to be *positive* integers
(cf. the response by Z3's lead developer Nikolaj Bjorner in [this GitHub
issue](https://github.com/Z3Prover/z3/issues/1846#issuecomment-424809364)).
SMT-LIB uses a Lisp-like S-expression syntax. We abstain from discussing this
syntax here and instead refer to the [SMT-LIB
documentation](https://smtlib.cs.uiowa.edu/language.shtml).

[^3]: In the SMT-LIB standard, this function is called `str.to_int`. ISLa, however, uses the Z3 SMT solver, where the corresponding function has the name `str.to.int`. Obviously, [Z3 supported `str.to.int` before `str.to_int` became an official standard](https://stackoverflow.com/questions/46524843/missing-str-to-int-s-in-z3-4-5-1#answer-46528332).

**Free variables.** The set \\(freeVars(\varphi)\\) for an SMT-LIB expression
\\(\varphi\\) consists of all symbols not part of the [SMT-LIB
language](https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf)
and not contained in one of the (built-in) [SMT-LIB
theories](https://smtlib.cs.uiowa.edu/theories.shtml), in particular the
[integer](https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml) and
[string](https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml) theories.

We assume a function \\(\mathit{sat}\\) mapping an SMT-LIB formula (expression
of Boolean type) to the values \\(\mathit{SAT}\\), \\(\mathit{UNSAT}\\), or
\\(\mathit{UNDEFINED}\\). \\(\mathit{SAT}\\) means that there exists a variable
assignment for which the formula holds. A returned \\(\mathit{UNSAT}\\) value
implies that there does not exist any such an assignment. Furthermore, the
\\(\mathit{UNDEFINED}\\) value is issued if no definitive decision could be made
(e.g., due to a timeout or a prover insufficiency). We will not define
\\(\mathit{sat}\\) formally in this document, since it is no original
contribution of ISLa. The ISLa solver implements \\(\mathit{sat}\\) by calling
the [Z3 theorem prover](https://github.com/Z3Prover/z3).

**Semantics.** Let \\(\beta\\) be a variable assignment and \\(\varphi\\) an
SMT-LIB formula.  Furthermore, let \\(\varphi'\\) be a formula resulting from
*negating* the *instantiation* of \\(\varphi\\) according to \\(\beta\\). Then,
\\(\beta\models\varphi\\) holds if, and only if,
\\(\mathit{sat}(\varphi')=\mathit{UNSAT}\\). When instantiating \\(\varphi\\),
we have to convert the derivation trees in \\(\beta\\) to strings first, since
SMT and Z3 do not know derivation trees.

#### [Structural Predicates](#strucural-predicates)

Consider the assignment language from [the introduction](#introduction). The
relevant semantic property for this language is that for each right-hand side
variable, there has to exist a *preceding* assignment to that variable. SMT-LIB
expressions are insufficient for expressing such structural relations because
they are unaware of grammatical structure. In simple cases, we could in
principle express them using string functions (e.g., comparing indices). Too
many such constraints, however, often result in solver timeouts. More
complex use cases (e.g., some element has to occur *inside* or as the *n-th
child* of another one) can even be impossible to express using SMT-LIB alone. To
that end, ISLa introduces so-called *structural predicates*. These predicates
mostly reason about the relative positions of elements in a parse tree. An
example is the `before` predicate used for the assignment language example:

```
forall <assgn> assgn:
  exists <assgn> decl: (
    before(decl, assgn) and 
    assgn.<rhs>.<var> = decl.<var>
  )
```

This predicate accepts two variables as arguments, and holds if, and only if,
the first argument occurs earlier in the *reference tree* than the second one.
The reference tree is the instantiation of the global constant (implicitly)
declared in an ISLa specification. Structural predicates might also accept
string literals as arguments. For example, `level("GE", "<block>", decl, expr)`,
inspired by the definition-use constraint of a C-like language, expresses that
the declaration `decl` has to occur at the same or a greater `<block>` level
than `expr`, as in {% raw %}`{int x; {int y = x;}}`{% endraw %}, where `expr`
would be the `x` in `int y = x;` and `decl` the `int x;` declaration. The
program {% raw %}`{{int x;} int y = x;}`{% endraw %} would not satisfy this constraint. 

In the following table, we informally describe the meaning of the ISLa built-in
structural predicates.

| Predicate                                  | Intuitive Meaning                                                                                                                                      |
|--------------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------|
| `after(node_1, node_2)`                    | `node_1` occurs after `node_2` (not below) in the parse tree.                                                                                          |
| `before(node_1, node_2)`                   | `node_1` occurs before `node_2` (not below) in the parse tree.                                                                                         |
| `consecutive(node_1, node_2)`              | `node_1` and `node_2` are consecutive leaves in the parse tree.                                                                                        |
| `different_position(node_1, node_2)`       | `node_1` and `node_2` occur at different positions (cannot be the same node).                                                                          |
| `direct_child(node_1, node_2)`             | `node_1` is a direct child of `node_2` in the derivation tree.                                                                                         |
| `inside(node_1, node_2)`                   | `node_1` is a subtree of `node_2`.                                                                                                                     |
| `level(PRED, NONTERMINAL, node_1, node_2)` | `node_1` and `node_2` are related relatively to each other as specified by `PRED` and `NONTERMINAL` (see below). `PRED` and `NONTERMINAL` are Strings. |
| `nth(N, node_1, node_2)`                   | `node_1` is the `N`-th occurrence of a node with its nonterminal symbol within `node_2`. `N` is a numeric String.                                      |
| `same_position(node_1, node_2)`            | `node_1` and `node_2` occur at the same position (have to be the same node).                                                                           |

**Free variables.** All structural predicate atoms \\(\varphi\\) are of the form
\\(\mathit{pred}(a_1,a_2,\dots,a_n)\\). The free variables
\\(\mathit{free_vars}(\varphi)\\) of \\(\varphi\\) consists of all those
\\(a_i\\) that are not string literals.

**Semantics.** To evaluate structural predicates, we need to access elements in
the derivation tree assigned to the global ISLa constant \\(c\\) in the variable
assignment \\(\beta\\). Thus, we assume that we know \\(c\\).[^4] The semantics
of structural predicate atoms can only be defined for each predicate
individually. Below, we demonstrate this along the example of `before`.

[^4]: In the ISLa implementation, we distinguish two types of variables: *bound variables* (bound by [quantifiers](#quantifiers)) and *constants*. Thus, we can always extract reference trees from variable assignments.

**Semantics of `before`.** Since `before` reasons about *relative positions* of
derivation trees, we need to encode these positions. To that end, we introduce
the notion of *paths* in derivation trees. A path is a (potentially empty) tuple
of natural numbers \\((n_1,n_2,\dots,n_2)\\). In a tree \\(t\\), the empty path
\\(()\\) points to the tree itself, the path \\((n)\\) to the \\(n\\)-th child
of \\(t\\)'s root, the path \\((n,m)\\) to the \\(m\\)-th child of the
\\(n\\)-th child of the root, and so on. Counting start from 0, so \\((0)\\) is
the path of the root's first child. Below, we indicate the paths of each subtree
in the derivation tree from the [introduction](#introduction):
```
<stmt>                 <- ()
├─ <assgn>             <- (0)
│  ├─ <var>            <- (0,0)
│  │  └─ "x"           <- (0,0,0)
│  ├─ " := "           <- (0,1)
│  └─ <rhs>            <- (0,2)
│     └─ <digit>       <- (0,2,0)
│        └─ "1"        <- (0,2,0,0)
├─ " ; "               <- (1)
└─ <stmt>              <- (2)
   └─ <assgn>          <- (2,0)
      ├─ <var>         <- (2,0,0)
      │  └─ "y"        <- (2,0,0,0)
      ├─ " := "        <- (2,0,1)
      └─ <rhs>         <- (2,0,2)
         └─ <var>      <- (2,0,2,0)
            └─ "x"     <- (2,0,2,0,0)
```

The subtree with path \\((2,0,2)\\) in this tree, for example, is the tree

```
<rhs>
└─ <var>
   └─ "x"
```

We assume a partial function \\(\mathit{path}(t_1, t_2)\\) that returns that
path pointing to \\(t_1\\) in the tree \\(t_2\\).[^5] The function is defined
if, and only if, \\(t_1\\) occurs in \\(t_1\\). For example, if \\(t_1\\) is the
`<rhs>`-tree above and \\(t_2\\) the `<stmt>` tree from which we extracted it, 
\\(\mathit{path}(t_1, t_2)=(0,2,0)\\).

[^5]: In the ISLa system, derivation trees have unique identifiers, such that we can distinguish trees with identical structure.

Let \\(\beta\\) be a variable assignment, \\(c\\) the global constant from the
ISLa specification, and \\(p_i\\) be the paths \\(\mathit{path}(t_i, \beta(c))\\)
for \\(i=1,2\\). Now, \\(\beta\models\mathit{before}(t_1, t_2)\\) holds if, and
only if, the function \\(\mathit{isBefore}(p_1, p_2)\\) returns \\(\top\\). We
recursively define \\(\mathit{isBefore}\\) as follows:

$$
\mathit{isBefore}(p_1, p_2) =
\begin{cases}
  \bot                                              & \text{if } p_1 = () \text{ or } p_2 = () \\
  \bot                                              & \text{if } p_2^1 < p_1^1 \\
  \top                                              & \text{if } p_1^1 < p_2^1 \\
  isBefore((\mathit{tail}(p_1), \mathit{tail}(p_2)) & \text{otherwise}
\end{cases}
$$

where \\(p^1\\) is the first element of the tuple \\(p\\) and
\\(\mathit{tail}(p)\\) is the (possibly empty) tuple resulting from removing the
first element of \\(p\\).

The remaining structural predicates can be defined in a similar fashion. Only
for predicates like `level` we additionally need to retrieve labels of subtrees
(grammar symbols) in addition to paths.

#### [Semantic Predicates](#semantic-predicates)

Semantic predicates were introduced mainly to compensate shortcomings of SMT-LIB
expressions. A classic example would be a constraint involving a checksum
computation. For example, the [checksum for TAR
archives](https://en.wikipedia.org/wiki/Tar_(computing)#File_format) involves
setting the original checksum to spaces, summing up the TAR header, and
converting the results to an octal number. Even if this was expressible in
SMT-LIB, it would probably result in solver timeouts in many cases. When using
semantic predicates in input generation, they not only can evaluate to a Boolean
value, but also change the reference derivation tree. For example, they might
assign the part of the tree corresponding to the checksum value with a tree
representing the correct checksum.

The below table displays the semantic predicates currently supported by ISLa.
For special purposes, it is possible to add dedicated semantic predicates (e.g.,
for checksum computation in binary formats) that must be implemented in Python.

| Predicate                                  | Intuitive Meaning                                                                                                                                      |
|--------------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------|
| `count(in_tree, NEEDLE, NUM)`              | There are `NUM` occurrences of the `NEEDLE` nonterminal in `in_tree`. `NEEDLE` is a String, `NUM` a numeric String or int variable.                    |

The currently only standard semantic ISLa predicate is `count`. For example,
`count(in_tree, "<line>", "3")` holds if, and only if, there exist exactly three
children labeled with the `<line>` nonterminal inside the derivation tree
`in_tree`. What distinguishes `count` from a structural predicate is, e.g., that
it is possible to pass a *numeric variable* (see the section [on numeric
quantifiers](#numeric-quantifiers)) instead of a string literal as the third
argument. Structural predicates could not handle this: Whether the predicate
holds or not would depend on the actual&mdash;not present&mdash;value of that
variable. The semantic predicate `count` can, however, count the `<line>`
occurrences in `in_tree` and assign the resulting number to the variable.

**Free variables and semantics.** For the purpose of defining the semantics of
semantic predicates, we can, however, re-use the definitions from the section on
[structural predicates](#structural-predicates). Since the variable assignment
\\(\beta\\) must assign values to all variables, there do not occur any
remaining "free" variables in the arguments of a semantic predicates. Thus, also
a semantic predicate atom can either hold or not hold for a given variable
assignment and list of arguments.

### [Propositional Combinators](#propositional)

Propositional combinators allow combining ISLa formulas to more complex
specifications. ISLa supports `not`, `and`, and `or`. Additionally, one can use
the derived combinators `xor`, `implies`, and `iff`. The formula `A xor B` is
translated to `(A and (not B)) or (B and (not A))`; `A implies B` is translated
to `(not A) or B`; and `A iff B` is translated to `(A and B) or ((not A) and
(not B))`.

In many cases, we can omit parentheses based on the *operator precedence* of
propositional combinators. This precedence is specified by the order of the
combinators in the [ISLa parser grammar](#parser-rules). The list of operators
ordered by their binding strength in increasing order is `not`, `and`, `or`,
`xor`, `implies`, `iff`. Thus, `(A and (not B)) or (B and (not A))` (the
encoding of `A xor B`) is equivalent to `A and not B or B and not A`&mdash;we do
not need any parentheses.

**Free variables.** For `not`, we define
\\(\mathit{freeVars}(\mathtt{not}~\varphi):=\mathit{freeVars}(\varphi)\\). Let
\\(\circ\\) be one of the binary propositional combinators and
\\(\varphi,\,\psi\\) be two ISLa formulas. Then,
\\(\mathit{freeVars}(\varphi\circ\psi):=\mathit{freeVars}(\varphi)\cup\mathit{freeVars}(\psi)\\).

**Semantics.** We define the semantics for `not`, `and`, and `or` as follows:

* \\(\beta\models\mathtt{not}~\varphi\\) holds if, and only if,
  \\(\beta\models\varphi\\) does *not* hold.
* \\(\beta\models\varphi~\mathtt{and}~\psi\\) holds if, and only if, 
  \\(\beta\models\varphi\\) and \\(\beta\models\psi\\) *both* hold.
* \\(\beta\models\varphi~\mathtt{or}~\psi\\) holds if, and only if, 
  at least one of \\(\beta\models\varphi\\) *or* \\(\beta\models\psi\\) hold.

### [Quantifiers](#quantifiers)

#### [Tree Quantifiers](#tree-quantifiers)

(work in progress)

#### [Numeric Quantifiers](#numeric-quantifiers)

(work in progress)

## [Footnotes](#footnotes)
