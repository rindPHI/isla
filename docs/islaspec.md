---
title: "The ISLa Language Specification"
permalink: /islaspec/
---

The Input Specification Language (ISLa) is a notation for formally specifying
context-sensitive properties of strings structured by a context-free grammar.
The purpose of this document is to precisely specify ISLa's syntax and
semantics.

## [Table of Contents](#toc)


<!-- vim-markdown-toc GFM -->

- [Introduction](#introduction)
- [ISLa EBNF](#isla-ebnf)
  - [Lexer Rules](#lexer-rules)
  - [Parser Rules](#parser-rules)
  - [Match Expression Lexer Rules](#match-expression-lexer-rules)
  - [Match Expression Parser Rules](#match-expression-parser-rules)
- [Grammars](#grammars)
- [Semantics](#semantics)
- [Atoms](#atoms)
  - [SMT-LIB Expressions](#smt-lib-expressions)
  - [Structural Predicates](#structural-predicates)
  - [Semantic Predicates](#semantic-predicates)
- [Propositional Combinators](#propositional-combinators)
- [Quantifiers](#quantifiers)

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

In the remainder of this document, we 

* provide a [context-free grammar of ISLa](#isla-ebnf) itself in EBNF form,
* explain the format of ISLa's [reference grammars](#grammars), and
* introduce the [semantics of ISLa formulas](#semantics) at a high level.

Subsequently, we discuss the individual building blocks of the ISLa language:

* The [atoms of the language](#atoms), which are [SMT-LIB expressions](#smt-lib-expressions), [structural predicates](#structural-predicates), and [semantic predicates](#semantic-predicates),
* [propositional combinators](#propositional) such as `and` or `or`, and
* [quantifiers](#quantifiers), i.e., `forall` and `exists`.

## [ISLa EBNF](#isla-ebnf)

In this section, we provide a grammar of the ISLa language in
[EBNF](https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form). We
obtained this grammar form ISLa's ANTLR grammar used for parsing its concrete
syntax. We start by discussing [lexical features](#lexer-rules), followed by an
introduction of the [parser rules](#parser-rules).

### [Lexer Rules](#lexer-rules)

ISLa's lexer grammar is shown below. In addition of the rules shown, ISLa knows
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

## [Grammars](#grammars)

ISLa's reference grammars are simple CFGs, i.e., without repetition etc. Valid
ISLa grammars are exactly those that can be expressed in [Backus-Naur Form
(BNF)](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form).[^1] The only
addition is that grammar rules have to end with a semi-colon `;`, which
facilitates the definition of rules spanning multiple lines.

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

## [Semantics](#semantics)

$ sdaf $

## [Atoms](#grammars)

### [SMT-LIB Expressions](#smt-lib-expressions)

### [Structural Predicates](#strucural-predicates)

### [Semantic Predicates](#semantic-predicates)

## [Propositional Combinators](#propositional)

## [Quantifiers](#quantifiers)

