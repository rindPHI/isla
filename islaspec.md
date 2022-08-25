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
[0.8.16](https://github.com/rindPHI/isla/tree/v0.8.16). Please consult the [ISLa
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
  - [Simplified Syntax by Example](#simplified-syntax-by-example)
  - [Generalized SMT-LIB syntax](#generalized-smt-lib-syntax)
  - [Omission of `in start`](#omission-of-in-start)
  - [Omission of Bound Variable Names](#omission-of-bound-variable-names)
  - [Free Nonterminals](#free-nonterminals)
  - [X-Path Expressions](#x-path-expressions)
- [Semantics](#semantics)
  - [Atoms](#atoms)
    - [SMT-LIB Expressions](#smt-lib-expressions)
    - [Structural Predicates](#structural-predicates)
    - [Semantic Predicates](#semantic-predicates)
  - [Propositional Combinators](#propositional-combinators)
  - [Quantifiers](#quantifiers)
    - [Tree Quantifiers](#tree-quantifiers)
      - [Tree Quantifiers without Match Expressions](#tree-quantifiers-without-match-expressions)
      - [Tree Quantifiers with Match Expressions](#tree-quantifiers-with-match-expressions)
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
(BNF)](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form).[^1] 

[^1]: From [ISLa 0.8.14](https://github.com/rindPHI/isla/blob/v0.8.14/CHANGELOG.md) on, the `ISLaSolver` and the `evaluate` function both accept grammars in concrete syntax in addition to the Python dictionary format of the [Fuzzing Book](https://www.fuzzingbook.org/html/Grammars.html).

The EBNF grammar for the concrete syntax of ISLa reference grammars looks as
follows, where `NO_ANGLE_BRACKET` represents any character but `<` and `>`:

```
bnf_grammar = derivation_rule, { derivation_rule } ;

derivation_rule = NONTERMINAL, "::=", alternative, { "|", alternative } ;

alternative = ( STRING | NONTERMINAL ) { STRING | NONTERMINAL } ;

NONTERMINAL = "<", NO_ANGLE_BRACKET, { NO_ANGLE_BRACKET }, ">" ;

STRING = '"' { ESC|. }? '"';
ESC = '\\' ("b" | "t" | "n" | "r" | '"' | "\\") ;
```

Here's how our example grammar from the [introduction](#introduction) looks in
this format (we abbreviated the definition of `<var>`):

```
<start> ::= <stmt>
<stmt> ::= <assgn> | <assgn> " ; " <stmt>
<assgn> ::= <var> " := " <rhs>
<rhs> ::= <var> | <digit>
<var> ::= "a" | "b" | "c" | ...
<digit> ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
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
symbols can be parsed as alphanumeric identifiers. Our [prefix and infix syntax
that we added on top of S-expressions](#generalized-smt-lib-syntax), as well as
expressions using operators with special characters, are only parsed correctly
if the operators appear in the [lexer grammar](#lexer-rules). This is primarily
to distinguish expressions in prefix syntax (`op(arg1, arg1, ...)`) from
[structural](#strucural-predicates) and [semantic
predicates](#semantic-predicates). In future versions of the grammar, we might
relax this constraint.

The *top-level constant declaration* `const my_const: <my_type>;` is optional.
We default to `const start: <start>;`. Consequently, if no top-level constant is
provided, the start symbol of the [reference grammar](#grammars) must be
`<start>` and all [quantified formulas](#tree-quantifiers) without an explicit
`in ...` specification [address elements `in start`](#omission-of-in-start).

Match expressions (see the section on [quantifiers](#quantifiers)) are hidden
inside the underspecified nonterminal `MATCH_EXPR`. We describe the
[lexer](#match-expression-lexer-rules) and
[parser](#match-expression-parser-rules) grammars for match expressions further
below.

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

[ISLa 0.3](https://github.com/rindPHI/isla/blob/v0.3/CHANGELOG.md) added a
simplified syntax layer allowing to specify ISLa constraints much more concisely
in many cases. Furthermore, [SMT-LIB expressions](#smt-lib-expressions) can be
expressed in the more common prefix or infix instead of S-expression syntax. All
the additions described in this section are "syntactic sugar;" they are
*translated to core ISLa* during parsing. In the [semantics](#semantics)
section, we thus exclusively focus on "core ISLa" (with explicit variable names,
without "free nonterminals" and XPath expressions, etc.), assuming that all
features described in this section are translated to that language core as
described here.

### [Simplified Syntax by Example](#simplified-syntax-by-example)

Before we describe the syntactic additions one by one, we demonstrate most of
them along the example of the assignment language from the
[introduction](#introduction). The definition-use constraint discussed there is
expressed as follows in core ISLa:

```
forall <assgn> assgn="<var> := {<var> rhs}" in start:
  exists <assgn> decl="{<var> lhs} := <rhs>" in start: (
    before(decl, assgn) and 
    (= lhs rhs)
  )
```

As a first simplification step, we can remove the `in start`, which is the
default (since `start` is the default "global" constant; cf. the explanations in
the [semantics](#semantics) section): 

```
forall <assgn> assgn="<var> := {<var> rhs}":
  exists <assgn> decl="{<var> lhs} := <rhs>": (
    before(decl, assgn) and 
    (= lhs rhs)
  )
```

Binary SMT-LIB expressions can be written in infix syntax:

```
forall <assgn> assgn="<var> := {<var> rhs}":
  exists <assgn> decl="{<var> lhs} := <rhs>": (
    before(decl, assgn) and 
    lhs = rhs
  )
```

While match expressions such as `"<var> := {<var> rhs}"` permit a lot of
flexibility for pattern matching and binding variables in subtrees, it is often
easier (but subject to individual taste) to use ISLa's "XPath" syntax. This
syntax allows addressing children of variables using a dot notation. It is
inspired by the [XPath abbreviated
syntax](https://www.w3.org/TR/1999/REC-xpath-19991116/#path-abbrev), but uses
dots `.` instead of slashes `/`. Our assignment language constraint can be
equivalently expressed as

```
forall <assgn> assgn:
  exists <assgn> decl: (
    before(decl, assgn) and 
    assgn.<rhs>.<var> = decl.<var>
  )
```

Finally, we can omit the universal quantifiers, and instead use its *nonterminal
symbol* in the quantified formula. Such "free nonterminals" are during parsing
replaced by a new variable bound by an added top-level universal quantifier.
Thus, the most concise formulation of the definition-use constraint is

```
exists <assgn> decl: (
  before(decl, <assgn>) and 
  <assgn>.<rhs>.<var> = decl.<var>
)
```

### [Generalized SMT-LIB syntax](#generalized-smt-lib-syntax)

At the core of ISLa are SMT-LIB expressions; quantifiers and predicate formulas
are constructed around those. In the [SMT-LIB
language](https://smtlib.cs.uiowa.edu/language.shtml), all expressions are
written in the S-expression format `(op arg1 arg2)` known from languages like
LISP and Scheme. In addition to this syntax, ISLa supports the prefix notation
`op(arg1, arg2)` more commonly used in mathematics and programming languages
and, for binary operators, the infix notation `arg1 op arg2`. Thus, one may
write 

```
17 + str.to.int(y) = str.to.int(x)
```

instead of 

```
(= (+ 17 (str.to.int y)) (str.to.int x))
```

in ISLa. When parsing an ISLa formula, all such prefix and infix expressions are
translated to S-expressions, which is why S-expressions are printed when
unparsing a formula, regardless of whether you used the generalized syntax to
specify the formula originally or not.

**Name conflicts with ISLa predicates.** To distinguish SMT-LIB expressions in
prefix syntax from ISLa predicates, the ISLa parser checks whether the provided
operator is an SMT-LIB function. If so, the expression is parsed as an SMT-LIB
expression. This implies that if an operator name is used both in an SMT-LIB
theory and for an ISLa predicate, the SMT-LIB operator always "wins;" it will
not be possible to parse the predicate. Thus, name clashes with SMT-LIB
operators should be avoided when defining a new ISla predicate.

### [Omission of `in start`](#omission-of-in-start)

Let `const my_const: <my_type>; formula` be an ISLa specification; if the
`const` declaration is omitted, we assume a specification `const start: <start>;`
as a default. Then, all subformulas `forall <type> name:` and `exists <type>
name:` in `formula` (where [the `name` part is
optional](#omission-of-bound-variable-names)) are translated to `forall <type>
name in start:` and `exists <type> name in start:` during parsing.

### [Omission of Bound Variable Names](#omission-of-bound-variable-names)

ISLa permits the omission of a name for the bound variable in quantifiers. In
that case, the nonterminal type of the bound variable may be used to address
that variable, as in

```
exists <assgn>: <assgn> = "x := y"
```

Formulas of this or similar shape translate to

```
exists <assgn> assgn in start: (= assgn "x := y")
```

More formally, in all formulas `Q <type> in v: formula`, where `Q` is `forall`
or `exists`, we choose a "fresh" variable name `name` and replace the formula 
`Q <type> name in v: formula'`,
where `formula'` results from `formula` by replacing all occurrences of `<typ>`
appearing at places where a variable may appear `name`. Fresh means that the
name `name` is not used anywhere in that formula.

### [Free Nonterminals](#free-nonterminals)

In an ISLa formula, you can use a nonterminal from the reference grammar at
every position where a variable may occur, also if that nonterminal [is not
bound by a quantifier](#omission-of-bound-variable-names). Those nonterminals
represent *universally bound variables.* A formula `formula` with at least one
unbound occurrence of a nonterminal symbol `<type>` is turned into a formula
`forall <type> name in start: formula'`, where 

* `name` is a fresh variable name not occurring in `formula`, and
* `formula'` results from `formula` by replacing all the `<type>` occurrences by
  `name`,
* `start` is the constant specified in the `const` part of an ISLa
  specification, or `start` if no such specification is given.

### [X-Path Expressions](#x-path-expressions)

As an alternative to [match
expressions](#tree-quantifiers-with-match-expressions), ISLa supports accessing
derivation tree children using a notation inspired by the [XPath abbreviated
syntax](https://www.w3.org/TR/1999/REC-xpath-19991116/#path-abbrev). In
particular, it supports the "child" and "descendant" axes, i.e., referring
direct children and "deeper" descendants of those. In contrast to the original
XPath syntax, we use dots `.` instead of slashes `/`. We still use the term
"XPath expression" to refer to such expressions.

At any position in an ISLa formula where a variable may occur, one may
alternatively use an XPath expression. An XPath expression in ISLa consists of
one or more *segments* of the form `var.<type1>[pos1].<type2>[pos2]` (for the
first segment) or `<type>.<type1>[pos1].<type2>[pos2]` (for the second and later
segments). Note that the second form can also be used when specifying an ISLa
constraint, but is translated to the first form by [universally closing over the
free nonterminal `<type>`](#free-nonterminals). Segments are connected using the
`..` operator (descendent axis). Each segment consists of one of more child
axis usages connected by `.`. The `[pos]` specifiers are optional and default to
`[1]`.

Semantically, `var.<type1>[pos1]` refers to the `pos1`-th *direct* child of type
`<type1>` in the derivation tree associated to `var`, where counting starts from
1; `var.<type1>[pos1].<type2>[pos2]` to the `pos2`-th child of type `<type2>` of
*that* element, and so on.

Using the descendent axis, we can address derivation tree children at a greater
distance (than 1). The exact distance cannot be specified. An XPath expression
`var.<type1>[pos1]..<type2>.<type3>[pos3]` refers to 

* the `pos3`-th *direct* child with type `<type3>` 
* of *all* `<type2>` elements that are (indirect) children 
* of the `pos1`-th *direct* child with type `<type1>` 
* of the derivation tree associated with `var`.

A simple example for the use of the `..` axis is the formula

```
checksum(<header>, <header>..<checksum>)
```

It specifies that a `checksum` predicate should hold for a `<header>` element
and all `<checksum>` elements somewhere below `<header>`.

**Translation of XPath expressions.** During parsing, XPath segments are
translated into match expressions. If more than one possible such translation is
possible, we build a conjunction (for universal formulas) or disjunction (for
existential formulas). We illustrate this along the example of an XML
constraint. The example is based on the following grammar:

```
<start> ::= <xml-tree>
<xml-tree> ::=   <text> 
               | <xml-open-tag> <xml-tree> <xml-close-tag> 
               | <xml-tree> <xml-tree>
<xml-open-tag> ::= "<" <id> ">" | "<" <id> " " <xml-attribute> ">"
<xml-close-tag> ::= "</" <id> ">"
<xml-attribute> ::= <id> "=" <id> | <xml-attribute> " " <xml-attribute>
<id> ::= <LETTER> | <id> <LETTER>
<text> ::= <text> <LETTER_SPACE> | <LETTER_SPACE>
<LETTER> ::= "a" | "b" | "c" | ... | "0" | "1" | ... | "\"" | "'" | "."
<LETTER_SPACE> ::= "a" | "b" | "c" | ... | "\"" | "'" | " " | "\t"
```

Now, consider the constraint `<xml-open-tag>.<id> = "a"` specifying that
identifiers in opening tags should equal the letter `a`. First, we introduce a
new variable for `<xml-open-tag>` which we bind in a universal quantifier (as
described in the section on [free nonterminals](#free-nonterminals)):

```
forall <xml-open-tag> optag in start: optag.<id> = "a"
```

Next, we search the reference grammar for expansions of `<xml-open-tag>`
containing at least one `<id>` nonterminal, which are both expansions for that
nonterminal. Thus, we create a match expression for both of these alternative,
and obtain the following conjunction of two quantified formulas:

```
forall <xml-open-tag> optag="<{<id> id}>" in start: id = "a" and
forall <xml-open-tag> optag="<{<id> id} <xml-attribute>>" in start: id = "a"
```

We can also allow longer identifiers, but restrict the allowed letters to "a."
This can be concisely expressed with the descendant axis `..`:
`<xml-open-tag>.<id>..<LETTER> = "a"`. When translating this formula to core
ISLa, we start from the outside and obtain

```
forall <xml-open-tag> optag="<{<id> id}>" in start: id..<LETTER> = "a" and
forall <xml-open-tag> optag="<{<id> id} <xml-attribute>>" in start: id..<LETTER> = "a"
```

Next, we "eliminate" the first XPath segment by introducing a universal
quantifier inside the already added one:

```
forall <xml-open-tag> optag="<{<id> id}>" in start: 
  forall <LETTER> letter in id:
    letter = "a" and
forall <xml-open-tag> optag="<{<id> id} <xml-attribute>>" in start:
  forall <LETTER> letter in id:
    letter = "a"
```

In summary,

* Individual XPath segments are translated to match expressions. The child axis
  `.` allows addressing *direct* children of a nonterminal that appear in at
  least one expansion alternative. If more than one occurrence of a nonterminal
  symbol appear in the same expansion alternative, indices `<type>[idx]` can be
  used to choose the one to constrain.
* For each segment chain consisting of more than one segment, we eliminate the
  segments from left to right by introducing universal quantifiers.
* XPath expressions *do not add expressiveness* to ISLa: They are translated to
  match expressions and quantifiers during parsing.

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

[^4]: In the ISLa implementation, we distinguish two types (in the sense of object-oriented classes) of variables: *bound variables* (bound by [quantifiers](#quantifiers)) and *constants*. Thus, we can always extract reference trees from variable assignments.

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

The remaining structural predicates can be defined similarly. Only
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

$$
\mathit{freeVars}(\varphi\circ\psi):=\mathit{freeVars}(\varphi)\cup\mathit{freeVars}(\psi)
$$

**Semantics.** We define the semantics for `not`, `and`, and `or` as follows:

* \\(\beta\models\mathtt{not}~\varphi\\) holds if, and only if,
  \\(\beta\models\varphi\\) does *not* hold.
* \\(\beta\models\varphi~\mathtt{and}~\psi\\) holds if, and only if, 
  \\(\beta\models\varphi\\) and \\(\beta\models\psi\\) *both* hold.
* \\(\beta\models\varphi~\mathtt{or}~\psi\\) holds if, and only if, 
  at least one of \\(\beta\models\varphi\\) *or* \\(\beta\models\psi\\) hold.

### [Quantifiers](#quantifiers)

Quantifiers come in two flavors in ISLa. First, we have quantifiers over
derivation trees, e.g., `forall <type> name in tree: ...`. In the
[introduction](#introduction), we have shown examples for those. A second type
of quantifier are the quantifiers over *integers*. They have the form `forall
int name: ...` or `exists int name: ...`. The variable `name` is, as all ISLa
variables, of string sort, but ranges over numeric values.

#### [Tree Quantifiers](#tree-quantifiers)

There are four types of tree quantifiers in ISLa, as universal quantifiers
(`forall`) and existential quantifiers (`exists`) can come with or without a
specified *match expression*. We first discuss the semantics of tree quantifiers
without match expressions, and then focus on those with match expressions.

##### [Tree Quantifiers without Match Expressions](#tree-quantifiers-without-match-expressions)

Intuitively, a formula `forall <type> name in tree: A` is true if A holds *for
all* subtrees in `tree` labeled with `<type>`. Conversely, `exists <type> name
in tree: A` holds if there is just *some* such subtree in `tree`.

**Free variables.** In a quantified tree formula without match expression, the
free variables are the free variables of the formula in the core of the
quantifier as well as the variable after `in`; the variable `name` is excluded
from this set, since it is *bound* by the quantifier. Let \\(Q\\) be either
`forall` or `exists`. We define

$$
\mathit{freeVars}(Q~T~v~\mathtt{in}~\mathit{t}:~\varphi)
:=\left(\mathit{freeVars}(\varphi)\cup\{t\}\right)\setminus\{v\}
$$

**Semantics.** Let \\(\mathit{subtrees}(N, t)\\) be the subtrees of the
derivation tree \\(t\\) labeled with the nonterminal symbol \\(N\\). Then, we
define the semantics of quantified formulas without match expressions as
follows:

* \\(\beta\models\mathtt{forall}~T~v~\mathtt{in}~t:\,\varphi\\) holds if, and
  only if, \\(\beta[v\mapsto{}t']\models\varphi\\) holds for all
  \\(t'\in\mathit{subtrees}(T, \beta(t))\\)
* \\(\beta\models\mathtt{exists}~T~v~\mathtt{in}~t:\,\varphi\\) holds if, and
  only if, \\(\beta[v\mapsto{}t']\models\varphi\\) holds for some
  \\(t'\in\mathit{subtrees}(T, \beta(t))\\)

where \\(\beta[v\mapsto{}t']\\) is the variable assignment mapping variable
\\(v\\) to the derivation tree \\(t'\\) and all other variables to their mapping
in \\(\beta\\).

##### [Tree Quantifiers with Match Expressions](#tree-quantifiers-with-match-expressions)

A *match expression* is an abstract word from the language of the reference
grammar. For example, `x := y` is a concrete word from our assignment language
(see [introduction](#introduction)); `<var> := y` would be a valid match
expression. Additionally, match expressions allow binding elements of that
"abstract" word to variables, as in `{<var> myvar} := y`. By using match
expressions in quantifiers, we can (1) restrict the possible instantiations of
the bound variable to those that match the match expression, and (2) access
elements of these instantiations by giving them names that can be referred in
the quantified formula.

To increase the flexibility of match expressions, they can contain *optional*
elements inside square brackets `[...]`. Elements inside these optionals cannot
be bound to variables: Only plain terminal and nonterminal symbols may occur
there. For example, `<assgn>[ ; <stmt>]` is a possible match expression for a
`<stmt>` nonterminal in the assignment language. It matches statements
consisting of a single assignment and one with an assignment followed by a
statement. Match expressions can also go "deeper." The expression 
`<assgn>[ ; <assgn>]` is also a valid match expression for a `<stmt>`, matching
any statement consisting of exactly one *or* two assignments.

**Free variables.** For a match expression \\(\mathit{mexpr}\\), let
\\(\mathit{freeVars}(\mathit{mexpr})\\) be the variables specified in curly
braces inside \\(\mathit{mexpr}\\). Let \\(Q\\) be `forall` or `exists`. Then,
we define 

$$
\mathit{freeVars}(Q~T~v\mathtt{=}\text{"$\mathit{mexpr}$"}~\mathtt{in}~\mathit{t}:~\varphi)
:=\left(\mathit{freeVars}(\varphi)\cup\mathit{freeVars}(\mathit{mexpr})\cup\{t\}\right)\setminus\{v\}
$$

To define the *semantics* of quantifiers with match expressions, we parse the
match expression into a set of (typically open, i.e., containing nonterminal
leaves) derivation trees. We can get more than one result: Either because
optionals are used, or because the reference grammar is ambiguous. If the match
expression contains variables, we record the paths from the root of these trees
to the nodes corresponding to the bound elements. Then, we continue as for
[quantified formulas without match
expressions](#tree-quantifiers-without-match-expressions): If `Q <type>
var="mexpr" in tree: A` is the formula (`Q` being either `forall` or `exists`),
we collect subtrees from `tree` with roots labeled with `<type>`. Then, however,
we select only those of which some derivation tree for the match expression
is a *prefix*. Then, we instantiate `var` and all variables in `mexpr` according
to the found match, and check whether `A` holds for all/one of these
instantiations.

To make this&mdash;slightly&mdash;more formal, we "define" a function
\\(\mathit{mexprTrees}\\) by example.  The result of
\\(\mathit{mexprTrees}(T,\mathit{mexpr})\\), for a nonterminal symbol \\(T\\)
match expression \\(\mathit{mexpr}\\), is a set of pairs \\((t,P)\\) of (1) a
derivation tree \\(t\\) corresponding to the parsed match expression, where
\\(T\\) is used as a start symbol (such that the root of \\(t\\) is labeled with
\\(T\\)), and (2) a mapping \\(P\\) of variables bound in match expressions to
the paths where the corresponding tree elements occur in \\(t\\).

Consider again the assignment language and let the match expression
\\(\mathit{mexpr}\\) be `{<var> lhs} := {<var> rhs}[ ; <assgn>]`. We visualize
the result of
\\(\mathit{mexprTrees}(\mathtt{\langle{}stmt\rangle},\mathit{mexpr})\\) by
indicating the mapping \\(P\\) in the textual representation of the two
resulting derivation trees. The first element of the result set, where the
optional part has been left out, is

```
stmt
└─ assgn
   ├─ var      lhs ↦ (0,0)
   ├─ " := "
   └─ rhs
      └─ var   rhs ↦ (0,2,0)
```

The second element, which contains the optional second assignment, is

```
stmt
├─ assgn
│  ├─ var      lhs ↦ (0,0)
│  ├─ " := "
│  └─ rhs
│     └─ var   rhs ↦ (0,2,0)
├─ " ; "
└─ stmt
   └─ assgn
```

We need a function \\(\mathit{match}(t, t', P)\\) taking a derivation tree
\\(t\\) and a pair \\(t',P\\) computed by \\(\mathit{mexprTrees}\\) and
returning (1) \\(\bot\\) if \\(t'\\) does not match \\(t\\), or otherwise (2) a
*variable assignment* mapping variables in \\(P\\) to the corresponding
subtrees in \\(t\\).

We now recursively define \\(\mathit{match}\\). Thereby,

* \\(l(t)\\) is the label of the tree \\(t\\);
* all alternatives in the definition are *mutually exclusive* (the first
  applicable one is applied);
* by \\(\mathit{numc}(t)\\) we denote the number of  children of the derivation
  tree \\(t\\);
* by \\(\mathit{child}(t, i)\\) we denote the \\(i\\)-th child of t, starting
  with 1; 
* \\(P_i\\) is computed from a mapping \\(P\\) from variables to paths by
  discarding all paths in \\(P\\) not starting with \\(i\\) and taking the
  *tail* (discarding the first element) for all other paths; and
* we use standard set union notation \\(\bigcup_{i=1}^n\beta_i\\) for combining 
  variable assignments \\(\beta_i\\).

$$
\mathit{match}(t, t', P) :=
\begin{cases}
\bot                                                                                  & \text{if }l(t)\neq{}l(t')\vee(\mathit{numc}(t')>0\wedge \\
                                                                                      & \qquad\mathit{numc}(t)\neq\mathit{numc}(t')) \\
[v\mapsto{}t]                                                                         & \text{if }P=[v\mapsto{}()]\text{ for some }v \\
\bot                                                                                  & \text{if }\mathit{match}(\mathit{child}(t, i), \mathit{child}(t', i), P_i)=\bot \\
                                                                                      & \qquad\text{for any }i\in[1,\dots,\mathit{numc}(t)] \\
\bigcup_{i=1}^{\mathit{numc}(t)}\Big( & \\
\quad\mathit{match}\big(\mathit{child}(t, i),                  & \\
\quad\hphantom{\mathit{match}\big(}\mathit{child}(t', i), P_i\big)\Big) & \text{otherwise} \\
\end{cases}
$$

Based on \\(match\\) and \\(mexprTrees\\), we can now define the semantics of
quantified formulas with match expressions.

* \\(\beta\models\mathtt{forall}~T~v\mathtt{=}\text{"$\mathit{mexpr}$"}~\mathtt{in}~t:\,\varphi\\)
  holds if, and only if, 
  * **for all** \\(t_1\in\mathit{subtrees}(T, \beta(t))\\) and 
  * **for all** \\((t_2,P) \in \mathit{mexprTrees}(T, \mathit{mexpr})\\), it holds that
  * \\(\mathit{match}(t_1, t_2, P)\neq\bot\\) **implies that**
  * \\(\beta[v\mapsto{}t_1]\cup\mathit{match}(t_1, t_2, P)\models\varphi\\).
* \\(\beta\models\mathtt{exists}~T~v\mathtt{=}\text{"$\mathit{mexpr}$"}~\mathtt{in}~t:\,\varphi\\)
  holds if, and only if, 
  * **there is a** \\(t_1\in\mathit{subtrees}(T, \beta(t))\\) and 
  * **there is a** \\((t_2,P) \in \mathit{mexprTrees}(T, \mathit{mexpr})\\) such that
  * \\(\mathit{match}(t_1, t_2, P)\neq\bot\\) **and**
  * \\(\beta[v\mapsto{}t_1]\cup\mathit{match}(t_1, t_2, P)\models\varphi\\).


#### [Numeric Quantifiers](#numeric-quantifiers)

Numeric quantifiers are of the form `forall int var; A` or `exists int var; A`.
They allow introducing a fresh variable, unconnected to the reference grammar,
ranging over strings representing *positive* integers. We only allow positive
integers since the SMT solver used by ISLa, Z3, does not support converting
negative numeric strings to integers and back (see [this GitHub
issue](https://github.com/Z3Prover/z3/issues/1846#issuecomment-424809364)). The
main use case of numeric quantifiers is connecting several semantic predicates.
Consider, for example, the following ISLa constraint for CSV files:

```
exists int colno: (
  str.to.int(colno) >= 3 and 
  str.to.int(colno) <= 5 and 
  count(<csv-header>, "<column>", colno) and 
  forall <csv-record> line:
    count(line, "<column>", colno))
```

This constraint expresses that the number of columns in the `<csv-header>` field
of a CSV header is between 3 and 5, and that all lines after the header have to
share the same number of columns. If it was possible to express the `count`
predicate using pure SMT-LIB expressions, we could have expressed this
constraint without semantic predicates and, consequently, without the
existential integer quantifier by forming an equation of the number of columns
in the header and the number of columns in each line.

The `forall int` quantifier expresses that a property has to hold *for all*
possible positive integers. In our experience, it is not often used in practice.
However, if we wanted to *negate* the above property for CSV files, the result
would contain such a quantifier.

**Free variables.** The free variables set is computed similarly as for [tree
quantifiers](#tree-quantifiers). Let \\(Q\\) be `forall` or `exists`. We define

$$
\mathit{freeVars}(Q~\mathtt{int}~v:~\varphi):=\mathit{freeVars}(\varphi)\setminus\{v\}
$$

**Semantics.** Let \\(N\\) be the set of all derivation trees whose string
representation correspond to that of a positive integer, e.g., "0", 1", "17",
etc. We define the semantics of quantified integer formulas as follows:

* \\(\beta\models\mathtt{forall~int}~v:\,\varphi\\) holds if, and
  only if, \\(\beta[v\mapsto{}n]\models\varphi\\) holds for all
  \\(n\in{}N\\)
* \\(\beta\models\mathtt{exists~int}~v:\,\varphi\\) holds if, and
  only if, \\(\beta[v\mapsto{}n]\models\varphi\\) holds for some
  \\(n\in{}N\\)

## [Footnotes](#footnotes)
