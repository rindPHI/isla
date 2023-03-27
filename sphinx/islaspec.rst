.. role:: python(code)
  :language: python
  :class: highlight

The ISLa Language Specification
===============================

The Input Specification Language (ISLa) is a notation for formally specifying
context-sensitive properties of strings structured by a context-free grammar.
The purpose of this document is to precisely specify ISLa's syntax and
semantics.

The ISLa version considered in this document is ISLa
`0.8.16 <https://github.com/rindPHI/isla/tree/v0.8.16>`_. Please consult the
`ISLa CHANGELOG <https://github.com/rindPHI/isla/blob/main/CHANGELOG.md>`_
to find out
if there were recent additions.

.. _introduction:

Introduction
------------

Strings are the basic datatype for software testing and debugging at the system
level: All programs inputs and outputs are strings, or can be straightforwardly
represented as such. In parsing and fuzzing, Context-Free Grammars (CFGs) are a
popular formalism to decompose unstructured strings of data.

Consider, for example, a simple language of assignments such as :code:`x := 1 ; y := x`.
The following grammar, here presented in
`Extended Backus–Naur Form (EBNF) <https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form>`_,
can be used to parse and produce syntactically valid assignment programs:

.. code-block:: abnf

   stmt  = assgn, { " ; ", stmt } ;
   assgn = var, " := ", rhs ;
   rhs   = var | digit ;
   var   = "a" | "b" | "c" | ... ;
   digit = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;

Using this grammar, the input :code:`x := 1 ; y := x` can be parsed into the following
tree structure:

.. code-block::

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

In the context of parsing, such trees are called "parse trees;" in the fuzzing
domain, the notion "derivation tree" is preferred. In this document, we will use
the term "derivation tree."

We call labels of the inner nodes of derivation trees such as :code:`stmt` that have
to be further *expanded* to produce or parse a string "nonterminal elements" or
simply "nonterminals;" consequently, the leaves of the tree are labeled with
"terminal elements" or "terminals." From a tree, we obtain a string by chaining
the terminals in the order in which they are visited in a depth-first traversal
of the tree. CFGs map nonterminals to one or more *expansion alternatives* or,
simply, *expansions.* When using a grammar for fuzzing, we can expand a
nonterminal using any alternative. During parsing, we have to find the right
alternative for the given input (that is, *one* right alternative, since CFGs
can be *ambiguous*).

CFGs allow decomposing strings into their elements. However, they are—by
definition—too coarse to capture *context-sensitive* language features. In
the case of our assignment language, :code:`x := 1 ; y := z` is not considered a valid
element of the language, since the identifier :code:`z` has not been assigned before
(such that its value is :code:`undefined`). Similarly, the program :code:`x := x` is
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
`JML <https://www.cs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman.html>`_. The
following ISLa constraint restricts the language of the reference grammar shown
above to exactly those assignment programs using only previously assigned
variables as right-hand sides:

.. code-block::

   forall <assgn> assgn:
     exists <assgn> decl: (
       before(decl, assgn) and
       assgn.<rhs>.<var> = decl.<var>
     )

In ISLa language, nonterminals are surrounded by angular brackets (see also the
:ref:`section on grammars <grammars>`). The above constraint specifies that

* **for all** :code:`<assgn>` elements that have a :code:`<var>` right-hand side (to
  satisfy the :code:`assgn.<rhs>.<var>`) and which we refer to with the name :code:`assgn`,
* there has to **exist** an :code:`<assgn>` element that we will call :code:`decl`,
* such that :code:`decl` appears **before** :code:`assgn` in the input **and**
* the variable in the right-hand side of :code:`assgn` equals the variable in :code:`decl`.

Note that the :code:`.` syntax allows accessing *immediate* children of elements in
the parse tree; :code:`decl.<var>` thus uniquely identifies the left-hand side of an
assignment (since variables in right-hand sides appear as a child of a :code:`<rhs>`
nonterminal).

In the remainder of this document, we specify the :ref:`syntax <syntax>` and :ref:`semantics <semantics>` of ISLa formulas.

.. _syntax:

Syntax
------

In this section, we describe the
:ref:`syntax of ISLa's reference grammars <grammars>`
and the syntax of ISLa formulas themselves. We introduce
the ISLa syntax on a high level by providing grammars in
`EBNF <https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form>`_. In the
:ref:`section on ISLa's semantics <semantics>`, we discuss the individual ISLa syntax
elements in more details and explain their meaning formally and based on
examples.

.. _grammars:

Grammars
^^^^^^^^

ISLa's uses simple CFGs as reference grammars, i.e., without repetition etc.
Valid ISLa grammars are exactly those that can be expressed in
`Backus-Naur Form (BNF) <https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form>`_. [#f1]_

The EBNF grammar for the concrete syntax of ISLa reference grammars looks as
follows, where :code:`NO_ANGLE_BRACKET` represents any character but :code:`<` and :code:`>`:

.. code-block:: abnf

   bnf_grammar = derivation_rule, { derivation_rule } ;

   derivation_rule = NONTERMINAL, "::=", alternative, { "|", alternative } ;

   alternative = ( STRING | NONTERMINAL ) { STRING | NONTERMINAL } ;

   NONTERMINAL = "<", NO_ANGLE_BRACKET, { NO_ANGLE_BRACKET }, ">" ;

   STRING = '"' { ESC|. }? '"';
   ESC = '\\' ("b" | "t" | "n" | "r" | '"' | "\\") ;

Here's how our example grammar from the :ref:`introduction <introduction>` looks in
this format (we abbreviated the definition of :code:`<var>`):

.. code-block:: bnf

   <start> ::= <stmt>
   <stmt> ::= <assgn> | <assgn> " ; " <stmt>
   <assgn> ::= <var> " := " <rhs>
   <rhs> ::= <var> | <digit>
   <var> ::= "a" | "b" | "c" | ...
   <digit> ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"

.. _lexer-rules:

Lexer Rules
^^^^^^^^^^^

ISLa's lexer grammar is shown below. In addition to the rules shown, ISLa knows
Python-style line comments starting with :code:`#`. These comments as well as
whitespace between tokens are ignored during lexing. The only string delimiter
known to ISLa are double quotes :code:`"`. Inside strings, double quotes are escaped
using a backslash character: :code:`\"`. Most notably, this also holds for
:ref:`SMT-LIB expressions <smt-lib-expressions>`, which is a deviation from the SMT-LIB
standard where quotes are escaped by doubling them. In standard SMT-LIB, a
quotation mark inside double quotes is expressed (:code:`""""`), whereas in ISLa, one
writes :code:`"\\""`.

.. code-block:: abnf

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

.. _parser-rules:

Parser Rules
^^^^^^^^^^^^

Below, you find ISLa's parser grammar.
:ref:`SMT-LIB expressions <smt-lib-expressions>` are usually expressed in a Lisp-like
S-expression syntax, e.g., :code:`(= x (+ y 13))`. This is fully supported by ISLa,
and is robust to extensions in the SMT-LIB format as long as new function
symbols can be parsed as alphanumeric identifiers. Our
:ref:`prefix and infix syntax that we added on top of S-expressions <generalized-smt-lib-syntax>`,
as well as expressions using operators with special characters, are only parsed correctly
if the operators appear in the :ref:`lexer grammar <lexer-rules>`. This is primarily
to distinguish expressions in prefix syntax (:code:`op(arg1, arg1, ...)`) from
:ref:`structural <structural-predicates>` and
:ref:`semantic predicates <semantic-predicates>`. In future versions of the grammar, we might
relax this constraint.

The *top-level constant declaration* :code:`const my_const: <my_type>;` is optional.
We default to :code:`const start: <start>;`. Consequently, if no top-level constant is
provided, the start symbol of the :ref:`reference grammar <grammars>` must be
:code:`<start>` and all :ref:`quantified formulas <tree-quantifiers>` without an explicit
:code:`in ...` specification :ref:`address elements in start <omission-of-in-start>`.

Match expressions (see the section on :ref:`quantifiers <quantifiers>`) are hidden
inside the underspecified nonterminal :code:`MATCH_EXPR`. We describe the
:ref:`lexer <match-expression-lexer-rules>` and
:ref:`parser <match-expression-parser-rules>` grammars for match expressions further
below.

.. code-block:: abnf

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

.. _match-expression-lexer-rules:

Match Expression Lexer Rules
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

We show the actual ANTLR rules of the match expression lexer, since they use
ANTLR "modes" to parse variable declarations and optional match expression
elements into tokens. For details on match expressions, we refer to the
:ref:`section on quantifiers <quantifiers>`.

.. code-block:: abnf

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

.. _match-expression-parser-rules:

Match Expression Parser Rules
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The parser rules for match expressions are depicted below in the EBNF format.

.. code-block:: abnf

   matchExpr = matchExprElement, { matchExprElement } ;

   matchExprElement =
       BRAOP, varType, ID, BRACL
     | OPTOP, OPTTXT, OPTCL
     | TEXT
     ;

   varType : LT ID GT ;

.. _simplified-syntax:

Simplified Syntax
-----------------

`ISLa 0.3 <https://github.com/rindPHI/isla/blob/v0.3/CHANGELOG.md>`_ added a
simplified syntax layer allowing to specify ISLa constraints much more concisely
in many cases. Furthermore, :ref:`SMT-LIB expressions <smt-lib-expressions>` can be
expressed in the more common prefix or infix instead of S-expression syntax. All
the additions described in this section are "syntactic sugar;" they are
*translated to core ISLa* during parsing. In the :ref:`semantics <semantics>`
section, we thus exclusively focus on "core ISLa" (with explicit variable names,
without "free nonterminals" and XPath expressions, etc.), assuming that all
features described in this section are translated to that language core as
described here.

.. _simplified-syntax-by-example:

Simplified Syntax by Example
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Before we describe the syntactic additions one by one, we demonstrate most of
them along the example of the assignment language from the
:ref:`introduction <introduction>`. The definition-use constraint discussed there is
expressed as follows in core ISLa:

.. code-block::

   forall <assgn> assgn="<var> := {<var> rhs}" in start:
     exists <assgn> decl="{<var> lhs} := <rhs>" in start: (
       before(decl, assgn) and
       (= lhs rhs)
     )

As a first simplification step, we can remove the :code:`in start`, which is the
default (since :code:`start` is the default "global" constant; cf. the explanations in
the :ref:`semantics` section):

.. code-block::

   forall <assgn> assgn="<var> := {<var> rhs}":
     exists <assgn> decl="{<var> lhs} := <rhs>": (
       before(decl, assgn) and
       (= lhs rhs)
     )

Binary SMT-LIB expressions can be written in infix syntax:

.. code-block::

   forall <assgn> assgn="<var> := {<var> rhs}":
     exists <assgn> decl="{<var> lhs} := <rhs>": (
       before(decl, assgn) and
       lhs = rhs
     )

While match expressions such as :code:`"<var> := {<var> rhs}"` permit a lot of
flexibility for pattern matching and binding variables in subtrees, it is often
easier (but subject to individual taste) to use ISLa's "XPath" syntax. This
syntax allows addressing children of variables using a dot notation. It is
inspired by the
`XPath abbreviated syntax <https://www.w3.org/TR/1999/REC-xpath-19991116/#path-abbrev>`_,
but uses
dots :code:`.` instead of slashes :code:`/`. Our assignment language constraint can be
equivalently expressed as

.. code-block::

   forall <assgn> assgn:
     exists <assgn> decl: (
       before(decl, assgn) and
       assgn.<rhs>.<var> = decl.<var>
     )

Finally, we can omit the universal quantifiers, and instead use its *nonterminal
symbol* in the quantified formula. Such "free nonterminals" are during parsing
replaced by a new variable bound by an added top-level universal quantifier.
Thus, the most concise formulation of the definition-use constraint is

.. code-block::

   exists <assgn> decl: (
     before(decl, <assgn>) and
     <assgn>.<rhs>.<var> = decl.<var>
   )

.. _generalized-smt-lib-syntax:

Generalized SMT-LIB syntax
^^^^^^^^^^^^^^^^^^^^^^^^^^

At the core of ISLa are SMT-LIB expressions; quantifiers and predicate formulas
are constructed around those. In the
`SMT-LIB language`_,
all expressions are written in the S-expression format :code:`(op arg1 arg2)` known from languages like
LISP and Scheme. In addition to this syntax, ISLa supports the prefix notation
:code:`op(arg1, arg2)` more commonly used in mathematics and programming languages
and, for binary operators, the infix notation :code:`arg1 op arg2`. Thus, one may
write

.. code-block::

   17 + str.to.int(y) = str.to.int(x)

instead of

.. code-block::

   (= (+ 17 (str.to.int y)) (str.to.int x))

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

.. _omission-of-in-start:

Omission of :code:`in start`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Let :code:`const my_const: <my_type>; formula` be an ISLa specification; if the
:code:`const` declaration is omitted, we assume a specification :code:`const start: <start>;`
as a default. Then, all subformulas :code:`forall <type> name:` and :code:`exists <type>
name:` in :code:`formula` (where
the :code:`name` part :ref:`is optional <omission-of-bound-variable-names>`
) are translated to
:code:`forall <type> name in start:` and
:code:`exists <type> name in start:` during parsing.

.. _omission-of-bound-variable-names:

Omission of Bound Variable Names
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

ISLa permits the omission of a name for the bound variable in quantifiers. In
that case, the nonterminal type of the bound variable may be used to address
that variable, as in

.. code-block::

   exists <assgn>: <assgn> = "x := y"

Formulas of this or similar shape translate to

.. code-block::

   exists <assgn> assgn in start: (= assgn "x := y")

More formally, in all formulas :code:`Q <type> in v: formula`, where :code:`Q` is :code:`forall`
or :code:`exists`, we choose a "fresh" variable name :code:`name` and replace the formula
:code:`Q <type> name in v: formula'`,
where :code:`formula'` results from :code:`formula` by replacing all occurrences of :code:`<type>`
appearing at places where a variable may appear :code:`name`. Fresh means that the
name :code:`name` is not used anywhere in that formula.

.. _free-nonterminals:

Free Nonterminals
^^^^^^^^^^^^^^^^^

In an ISLa formula, you can use a nonterminal from the reference grammar at
every position where a variable may occur, also if that nonterminal
:ref:`is not bound by a quantifier <omission-of-bound-variable-names>`.
Those nonterminals represent *universally bound variables.* A formula :code:`formula` with at least one
unbound occurrence of a nonterminal symbol :code:`<type>` is turned into a formula
:code:`forall <type> name in start: formula'`, where

* :code:`name` is a fresh variable name not occurring in :code:`formula`, and
* :code:`formula'` results from :code:`formula` by replacing all the :code:`<type>` occurrences by
  :code:`name`,
* :code:`start` is the constant specified in the :code:`const` part of an ISLa
  specification, or :code:`start` if no such specification is given.

.. _x-path-expressions:

X-Path Expressions
^^^^^^^^^^^^^^^^^^

As an alternative to
:ref:`match expressions <tree-quantifiers-with-match-expressions>`,
ISLa supports accessing
derivation tree children using a notation inspired by the
`XPath abbreviated syntax <https://www.w3.org/TR/1999/REC-xpath-19991116/#path-abbrev>`_.
In particular, it supports the "child" and "descendant" axes, i.e., referring
direct children and "deeper" descendants of those. In contrast to the original
XPath syntax, we use dots :code:`.` instead of slashes :code:`/`. We still use the term
"XPath expression" to refer to such expressions.

At any position in an ISLa formula where a variable may occur, one may
alternatively use an XPath expression. An XPath expression in ISLa consists of
one or more *segments* of the form :code:`var.<type1>[pos1].<type2>[pos2]` (for the
first segment) or :code:`<type>.<type1>[pos1].<type2>[pos2]` (for the second and later
segments). Note that the second form can also be used when specifying an ISLa
constraint, but is translated to the first form by
:ref:`universally closing <free-nonterminals>` over the free nonterminal :code:`<type>`.
Segments are connected using the
:code:`..` operator (descendent axis). Each segment consists of one of more child
axis usages connected by :code:`.`. The :code:`[pos]` specifiers are optional and default to
:code:`[1]`.

Semantically, :code:`var.<type1>[pos1]` refers to the :code:`pos1`-th *direct* child of type
:code:`<type1>` in the derivation tree associated to :code:`var`, where counting starts from
1; :code:`var.<type1>[pos1].<type2>[pos2]` to the :code:`pos2`-th child of type `<type2>` of
*that* element, and so on.

Using the descendent axis, we can address derivation tree children at a greater
distance (than 1). The exact distance cannot be specified. An XPath expression
:code:`var.<type1>[pos1]..<type2>.<type3>[pos3]` refers to

* the :code:`pos3`-th *direct* child with type :code:`<type3>`
* of *all* :code:`<type2>` elements that are (indirect) children
* of the :code:`pos1`-th *direct* child with type :code:`<type1>`
* of the derivation tree associated with :code:`var`.

A simple example for the use of the :code:`..` axis is the formula

.. code-block::

   checksum(<header>, <header>..<checksum>)

It specifies that a :code:`checksum` predicate should hold for a :code:`<header>` element
and all :code:`<checksum>` elements somewhere below :code:`<header>`.

**Translation of XPath expressions.** During parsing, XPath segments are
translated into match expressions. If more than one possible such translation is
possible, we build a conjunction (for universal formulas) or disjunction (for
existential formulas). We illustrate this along the example of an XML
constraint. The example is based on the following grammar:

.. code-block:: bnf

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

Now, consider the constraint :code:`<xml-open-tag>.<id> = "a"` specifying that
identifiers in opening tags should equal the letter :code:`a`. First, we introduce a
new variable for :code:`<xml-open-tag>` which we bind in a universal quantifier (as
described in the section on :ref:`free nonterminals <free-nonterminals>`):

.. code-block::

   forall <xml-open-tag> optag in start: optag.<id> = "a"

Next, we search the reference grammar for expansions of :code:`<xml-open-tag>`
containing at least one :code:`<id>` nonterminal, which are both expansions for that
nonterminal. Thus, we create a match expression for both of these alternative,
and obtain the following conjunction of two quantified formulas:

.. code-block::

   forall <xml-open-tag> optag="<{<id> id}>" in start: id = "a" and
   forall <xml-open-tag> optag="<{<id> id} <xml-attribute>>" in start: id = "a"

We can also allow longer identifiers, but restrict the allowed letters to "a."
This can be concisely expressed with the descendant axis :code:`..`:
:code:`<xml-open-tag>.<id>..<LETTER> = "a"`. When translating this formula to core
ISLa, we start from the outside and obtain

.. code-block::

   forall <xml-open-tag> optag="<{<id> id}>" in start: id..<LETTER> = "a" and
   forall <xml-open-tag> optag="<{<id> id} <xml-attribute>>" in start: id..<LETTER> = "a"

Next, we "eliminate" the first XPath segment by introducing a universal
quantifier inside the already added one:

.. code-block::

   forall <xml-open-tag> optag="<{<id> id}>" in start:
     forall <LETTER> letter in id:
       letter = "a" and
   forall <xml-open-tag> optag="<{<id> id} <xml-attribute>>" in start:
     forall <LETTER> letter in id:
       letter = "a"

In summary,

* Individual XPath segments are translated to match expressions. The child axis
  :code:`.` allows addressing *direct* children of a nonterminal that appear in at
  least one expansion alternative. If more than one occurrence of a nonterminal
  symbol appear in the same expansion alternative, indices :code:`<type>[idx]` can be
  used to choose the one to constrain.
* For each segment chain consisting of more than one segment, we eliminate the
  segments from left to right by introducing universal quantifiers.
* XPath expressions *do not add expressiveness* to ISLa: They are translated to
  match expressions and quantifiers during parsing.

.. _semantics:

Semantics
---------

In this section, we discuss ISLa's *semantics*, i.e., what an ISLa specification
*means*. Clearly, there has to be a relation between ISLa formulas and strings,
since ISLa is a specification language for strings.  However, it is more
convenient to define the semantics of an ISLa formula as the set of *derivation
trees* it represents.

On a high level, we define the semantics of a context-free grammar as the set of
derivation trees that can be (transitively) derived from its start symbol. In
the subsequent sections, we define (for each ISLa syntax element) a relation
:math:`t\models{}\varphi` that holds if, and only if, the derivation tree :math:`t`
*satisfies* the ISLa formula :math:`\varphi`. Finally, the semantics of an ISLa
formula :math:`\varphi` are all derivation trees represented by the reference
grammar that satisfy :math:`\varphi`.

The *language* of CFGs, i.e., the strings they represent, is thoroughly defined
in the standard literature. [#f2]_ We follow the same style. We assume a relation
:math:`t\Rightarrow{}t'` between derivation trees that holds if :math:`t'` can be
*derived* from :math:`t` by adding to some leaf node in :math:`t` labeled with a
nonterminal symbol :math:`n` new children nodes corresponding to some expansion
alternative for :math:`n`. For example, consider the following derivation tree:

.. code-block::

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

Using the expansion alternative :code:`<stmt> ::= <assgn>` from the
:ref:`(BNF) grammar for our assignment language <grammars>`,
we can expand the open :code:`<stmt>` node by
adding an :code:`<assgn>` child. The result looks as follows:

.. code-block::

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

This is not the only option: We can also expand :code:`<stmt>` with the expansion
alternative :code:`<stmt> ::= <assgn> " ; " <stmt>`, which results in

.. code-block::

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

If :math:`t` is the initial tree and :math:`t_1` and :math:`t_2` are the two
expansions, then both :math:`t\Rightarrow{}t_1` and :math:`t\Rightarrow{}t_2` hold.
Now, let :math:`\Rightarrow^\star` be the reflexive and transitive closure of
:math:`\Rightarrow`. Then, the set of derivation trees :math:`T(G)` represented by a
CFG :math:`G` is defined as :math:`T(G):=\{t\,\vert\,t_0\Rightarrow^\star{}t\}`,
where :math:`t_0` is a derivation tree consisting only of the grammar's start
symbol.

Assuming the relation :math:`\models` has been defined, we define the semantics
:math:`[[\varphi]]` of an ISLa formula :math:`\varphi` as
:math:`[[\varphi]]:=\{t\in{}T(G)\,\vert\,t\models\varphi\wedge\mathit{closed}(t)\}`,
where :math:`G` is the reference grammar for :math:`\varphi` and
the predicate :math:`\mathit{closed}` holds for all derivation trees whose leaves
are labeled with *terminals*.

In the remaining parts of this section, we discuss each element of the ISLa
syntax and define the relation :math:`\models` along the way.

When doing so, we also need (and define step by step) a function
:math:`\mathit{freeVars}(\varphi)` that returns the *free variables* of a formula
:math:`\varphi`. Those are the variables that are not bound by a
:ref:`quantifier <quantifiers>`.

In ISLa, all variables are of "string" sort. This is especially important when
writing :ref:`SMT-LIB expressions <smt-lib-expressions>`, since appropriate
conversions have to be added when, e.g., comparing a variable *representing* an
integer to an actual integer.

To define :math:`\models` for formulas with free variables, we use an additional
*variable assignment* :math:`\beta` associating variables with derivation trees.
We write :math:`\beta\models\varphi` to express that :math:`\varphi` holds when
instantiating free variables in :math:`\varphi` according to the assignments in
:math:`\beta`.

The notation :math:`t\models\varphi` used above, where :math:`t` is a derivation
tree, is a *shortcut*. When specifying an ISLa formula, we can declare a *global
constant* using the syntax :code:`const constant_name: <constant_type>;` (cf. the
:ref:`ISLa grammar <parser-rules>`). The declaration is optional; if it is not
present, a constant :code:`start` of type :code:`<start>` will be assumed. Assuming :code:`c` is
this constant, then :math:`t\models\varphi` is

* *undefined* if :math:`\mathit{freeVars}(\varphi)\neq\{c\}`.
* equivalent to :math:`[c\mapsto{}t]\models\varphi`, where :math:`[c\mapsto{}t]` is a variable
  assignment mapping :math:`c` to :math:`t`.

.. _atoms:

Atoms
^^^^^

The name ISLa has a double meaning: First, it is an acronym for "Input
specification language;" and second, "isla" is the Spanish word for "island."
The reason for this second meaning is that ISLa embeds the
`SMT-LIB language`_ as an *island language.* Around this
embedded language, ISLa essentially adds quantifiers aware of the structure of
context-free grammars. Thus, SMT-LIB expressions are the heart and the most
important *atomic* ISLa formulas. Atomic means that they do not contain
additional ISLa subformulas. ISLa also knows another type of atomic formula:
*predicate formulas.* Here, we distinguish *structural* and *semantic*
predicates. Structural predicates allow addressing structural relations such as
"before" of "inside;" semantic predicates complement SMT-LIB and allow
expressing complex constraints that are out of reach of the SMT-LIB language.
This section address all three types of ISLa atoms.

.. _smt-lib-expressions:

SMT-LIB Expressions
"""""""""""""""""""

ISLa embeds the SMT-LIB language. Since all ISLa variables are strings, the
`SMT-LIB string theory <https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml>`_
is the most relevant theory in the ISLa context. The function :code:`str.to.int` [#f3]_ converts
strings to integers, such that integer operations using the
`integer theory <https://smtlib.cs.uiowa.edu/theories-Ints.shtml>`_
are possible. A typical SMT-LIB ISLa constraint (inspired by our
`ISLa tutorial <https://www.fuzzingbook.org/beta/html/FuzzingWithConstraints.html>`_) is
:code:`(>= (str.to.int pagesize) 100)`. For this to work, all derivation trees that
can be substituted for the :code:`pagesize` variable have to be *positive* integers
(cf. the response by Z3's lead developer Nikolaj Bjorner in
`this GitHub issue <https://github.com/Z3Prover/z3/issues/1846#issuecomment-424809364>`_).
SMT-LIB uses a Lisp-like S-expression syntax. We abstain from discussing this
syntax here and instead refer to the
`SMT-LIB documentation <https://smtlib.cs.uiowa.edu/language.shtml>`_.

**Free variables.** The set :math:`freeVars(\varphi)` for an SMT-LIB expression
:math:`\varphi` consists of all symbols not part of the
`SMT-LIB language`_ and not contained in one of the (built-in)
`SMT-LIB theories <https://smtlib.cs.uiowa.edu/theories.shtml>`_, in particular the
`integer <https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml>`_ and
`string <https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml>`_ theories.

We assume a function :math:`\mathit{sat}` mapping an SMT-LIB formula (expression
of Boolean type) to the values :math:`\mathit{SAT}`, :math:`\mathit{UNSAT}`, or
:math:`\mathit{UNDEFINED}`. :math:`\mathit{SAT}` means that there exists a variable
assignment for which the formula holds. A returned :math:`\mathit{UNSAT}` value
implies that there does not exist any such an assignment. Furthermore, the
:math:`\mathit{UNDEFINED}` value is issued if no definitive decision could be made
(e.g., due to a timeout or a prover insufficiency). We will not define
:math:`\mathit{sat}` formally in this document, since it is no original
contribution of ISLa. The ISLa solver implements :math:`\mathit{sat}` by calling
the `Z3 theorem prover <https://github.com/Z3Prover/z3>`_.

**Semantics.** Let :math:`\beta` be a variable assignment and :math:`\varphi` an
SMT-LIB formula.  Furthermore, let :math:`\varphi'` be a formula resulting from
*negating* the *instantiation* of :math:`\varphi` according to :math:`\beta`. Then,
:math:`\beta\models\varphi` holds if, and only if,
:math:`\mathit{sat}(\varphi')=\mathit{UNSAT}`. When instantiating :math:`\varphi`,
we have to convert the derivation trees in :math:`\beta` to strings first, since
SMT and Z3 do not know derivation trees.

.. _structural-predicates:

Structural Predicates
"""""""""""""""""""""

Consider the assignment language from :ref:`the introduction <introduction>`. The
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
example is the :code:`before` predicate used for the assignment language example:

.. code-block::

   forall <assgn> assgn:
     exists <assgn> decl: (
       before(decl, assgn) and
       assgn.<rhs>.<var> = decl.<var>
     )

This predicate accepts two variables as arguments, and holds if, and only if,
the first argument occurs earlier in the *reference tree* than the second one.
The reference tree is the instantiation of the global constant (implicitly)
declared in an ISLa specification. Structural predicates might also accept
string literals as arguments. For example, :code:`level("GE", "<block>", decl, expr)`,
inspired by the definition-use constraint of a C-like language, expresses that
the declaration :code:`decl` has to occur at the same or a greater :code:`<block>` level
than :code:`expr`, as in :code:`{int x; {int y = x;}}`, where :code:`expr`
would be the :code:`x` in :code:`int y = x;` and :code:`decl` the :code:`int x;` declaration. The
program :code:`{{int x;} int y = x;}` would not satisfy this constraint.

In the following table, we informally describe the meaning of the ISLa built-in
structural predicates.

================================================  ======================================================================================================================================================
Predicate                                         Intuitive Meaning
================================================  ======================================================================================================================================================
:code:`after(node_1, node_2)`                           :code:`node_1` occurs after :code:`node_2` (not below) in the parse tree.
:code:`before(node_1, node_2)`                          :code:`node_1` occurs before :code:`node_2` (not below) in the parse tree.
:code:`consecutive(node_1, node_2)`                     :code:`node_1` and :code:`node_2` are consecutive leaves in the parse tree.
:code:`different_position(node_1, node_2)`              :code:`node_1` and :code:`node_2` occur at different positions (cannot be the same node).
:code:`direct_child(node_1, node_2)`                    :code:`node_1` is a direct child of :code:`node_2` in the derivation tree.
:code:`inside(node_1, node_2)`                          :code:`node_1` is a subtree of :code:`node_2`.
:code:`level(PRED, NONTERMINAL, node_1, node_2)`    :code:`node_1` and :code:`node_2` are related relatively to each other as specified by :code:`PRED` and :code:`NONTERMINAL` (see below). :code:`PRED` and :code:`NONTERMINAL` are Strings.
:code:`nth(N, node_1, node_2)`                          :code:`node_1` is the :code:`N`-th occurrence of a node with its nonterminal symbol within :code:`node_2`. :code:`N` is a numeric String.
:code:`same_position(node_1, node_2)`                   :code:`node_1` and :code:`node_2` occur at the same position (have to be the same node).
================================================  ======================================================================================================================================================

**Free variables.** All structural predicate atoms :math:`\varphi` are of the form
:math:`\mathit{pred}(a_1,a_2,\dots,a_n)`. The free variables
:math:`\mathit{free_vars}(\varphi)` of :math:`\varphi` consists of all those
:math:`a_i` that are not string literals.

**Semantics.** To evaluate structural predicates, we need to access elements in
the derivation tree assigned to the global ISLa constant :math:`c` in the variable
assignment :math:`\beta`. Thus, we assume that we know :math:`c`. [#f4]_ The semantics
of structural predicate atoms can only be defined for each predicate
individually. Below, we demonstrate this along the example of :code:`before`.

**Semantics of :code:`before`.** Since :code:`before` reasons about *relative positions* of
derivation trees, we need to encode these positions. To that end, we introduce
the notion of *paths* in derivation trees. A path is a (potentially empty) tuple
of natural numbers  :math:`(n_1,n_2,\dots,n_2)`. In a tree :math:`t`, the empty path
:math:`()` points to the tree itself, the path :math:`(n)` to the :math:`n`-th child
of :math:`t`'s root, the path :math:`(n,m)` to the :math:`m`-th child of the
:math:`n`-th child of the root, and so on. Counting start from 0, so :math:`(0)` is
the path of the root's first child. Below, we indicate the paths of each subtree
in the derivation tree from the :ref:`introduction`:

.. code-block::

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

The subtree with path :math:`(2,0,2)` in this tree, for example, is the tree

.. code-block::

   <rhs>
   └─ <var>
      └─ "x"

We assume a partial function :math:`\mathit{path}(t_1, t_2)` that returns that
path pointing to :math:`t_1` in the tree :math:`t_2`. [#f5]_ The function is defined
if, and only if, :math:`t_1` occurs in :math:`t_1`. For example, if :math:`t_1` is the
:code:`<rhs>`-tree above and :math:`t_2` the :code:`<stmt>` tree from which we extracted it,
:math:`\mathit{path}(t_1, t_2)=(0,2,0)`.

Let :math:`\beta` be a variable assignment, :math:`c` the global constant from the
ISLa specification, and :math:`p_i` be the paths :math:`\mathit{path}(t` \beta(c))\\)
for :math:`i=1,2`. Now, :math:`\beta\models\mathit{before}(t_1, t_2)` holds if, and
only if, the function :math:`\mathit{isBefore}(p_1, p_2)` returns :math:`\top`. We
recursively define :math:`\mathit{isBefore}` as follows:

.. math::

   \mathit{isBefore}(p_1, p_2) =
   \begin{cases}
     \bot                                              & \text{if } p_1 = () \text{ or } p_2 = () \\
     \bot                                              & \text{if } p_2^1 < p_1^1 \\
     \top                                              & \text{if } p_1^1 < p_2^1 \\
     isBefore((\mathit{tail}(p_1), \mathit{tail}(p_2)) & \text{otherwise}
   \end{cases}

where :math:`p^1` is the first element of the tuple :math:`p` and
:math:`\mathit{tail}(p)` is the (possibly empty) tuple resulting from removing the
first element of :math:`p`.

The remaining structural predicates can be defined similarly. Only
for predicates like :code:`level` we additionally need to retrieve labels of subtrees
(grammar symbols) in addition to paths.

.. _semantic-predicates:

Semantic Predicates
"""""""""""""""""""

Semantic predicates were introduced mainly to compensate shortcomings of SMT-LIB
expressions. A classic example would be a constraint involving a checksum
computation. For example, the
`checksum for TAR archives <https://en.wikipedia.org/wiki/Tar_(computing)#File_format>`_ involves
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

===================================  ===================================================================================================================================
Predicate                            Intuitive Meaning
===================================  ===================================================================================================================================
:code:`count(in_tree, NEEDLE, NUM)`  There are :code:`NUM` occurrences of the :code:`NEEDLE` nonterminal in :code:`in_tree`. :code:`NEEDLE` is a String, :code:`NUM` a numeric String or int variable.                    |
===================================  ===================================================================================================================================

The currently only standard semantic ISLa predicate is :code:`count`. For example,
:code:`count(in_tree, "<line>", "3")` holds if, and only if, there exist exactly three
children labeled with the :code:`<line>` nonterminal inside the derivation tree
:code:`in_tree`. What distinguishes :code:`count` from a structural predicate is, e.g., that
it is possible to pass a *numeric variable* (see the section
:ref:`on numeric quantifiers <numeric-quantifiers>`)
instead of a string literal as the third
argument. Structural predicates could not handle this: Whether the predicate
holds or not would depend on the actual—not present—value of that
variable. The semantic predicate :code:`count` can, however, count the :code:`<line>`
occurrences in :code:`in_tree` and assign the resulting number to the variable.

**Free variables and semantics.** For the purpose of defining the semantics of
semantic predicates, we can, however, re-use the definitions from the section on
:ref:`structural predicates <structural-predicates>`. Since the variable assignment
:math:`\beta` must assign values to all variables, there do not occur any
remaining "free" variables in the arguments of a semantic predicates. Thus, also
a semantic predicate atom can either hold or not hold for a given variable
assignment and list of arguments.

.. _propositional:

Propositional Combinators
^^^^^^^^^^^^^^^^^^^^^^^^^

Propositional combinators allow combining ISLa formulas to more complex
specifications. ISLa supports :code:`not`, :code:`and`, and :code:`or`. Additionally, one can use
the derived combinators :code:`xor`, :code:`implies`, and :code:`iff`. The formula :code:`A xor B` is
translated to :code:`(A and (not B)) or (B and (not A))`; :code:`A implies B` is translated
to :code:`(not A) or B`; and :code:`A iff B` is translated to
:code:`(A and B) or ((not A) and (not B))`.

In many cases, we can omit parentheses based on the *operator precedence* of
propositional combinators. This precedence is specified by the order of the
combinators in the :ref:`ISLa parser grammar <parser-rules>`. The list of operators
ordered by their binding strength in increasing order is :code:`not`, :code:`and`, :code:`or`,
:code:`xor`, :code:`implies`, :code:`iff`. Thus, :code:`(A and (not B)) or (B and (not A))` (the
encoding of :code:`A xor B`) is equivalent to :code:`A and not B or B and not A`—we do
not need any parentheses.

**Free variables.** For :code:`not`, we define
:math:`\mathit{freeVars}(\mathtt{not}~\varphi):=\mathit{freeVars}(\varphi)`. Let
:math:`\circ` be one of the binary propositional combinators and
:math:`\varphi,\,\psi` be two ISLa formulas. Then,

.. math::

   \mathit{freeVars}(\varphi\circ\psi):=\mathit{freeVars}(\varphi)\cup\mathit{freeVars}(\psi)

**Semantics.** We define the semantics for :code:`not`, :code:`and`, and :code:`or` as follows:

* :math:`\beta\models\mathtt{not}~\varphi` holds if, and only if,
  :math:`\beta\models\varphi` does *not* hold.
* :math:`\beta\models\varphi~\mathtt{and}~\psi` holds if, and only if,
  :math:`\beta\models\varphi` and :math:`\beta\models\psi` *both* hold.
* :math:`\beta\models\varphi~\mathtt{or}~\psi` holds if, and only if,
  at least one of :math:`\beta\models\varphi` *or* :math:`\beta\models\psi` hold.

.. _quantifiers:

Quantifiers
^^^^^^^^^^^

Quantifiers come in two flavors in ISLa. First, we have quantifiers over
derivation trees, e.g., :code:`forall <type> name in tree: ...`. In the
:ref:`introduction`, we have shown examples for those. A second type
of quantifier are the quantifiers over *integers*. They have the form
:code:`forall int name: ...` or :code:`exists int name: ...`. The variable :code:`name` is, as all ISLa
variables, of string sort, but ranges over numeric values.

.. _tree-quantifiers:

Tree Quantifiers
""""""""""""""""

There are four types of tree quantifiers in ISLa, as universal quantifiers
(:code:`forall`) and existential quantifiers (:code:`exists`) can come with or without a
specified *match expression*. We first discuss the semantics of tree quantifiers
without match expressions, and then focus on those with match expressions.

.. _tree-quantifiers-without-match-expressions:

Tree Quantifiers without Match Expressions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Intuitively, a formula :code:`forall <type> name in tree: A` is true if A holds *for
all* subtrees in :code:`tree` labeled with :code:`<type>`. Conversely,
:code:`exists <type> name in tree: A` holds if there is just *some* such subtree in :code:`tree`.

**Free variables.** In a quantified tree formula without match expression, the
free variables are the free variables of the formula in the core of the
quantifier as well as the variable after :code:`in`; the variable :code:`name` is excluded
from this set, since it is *bound* by the quantifier. Let :math:`Q` be either
:code:`forall` or :code:`exists`. We define

.. math::

   \mathit{freeVars}(Q~T~v~\mathtt{in}~\mathit{t}:~\varphi)
   :=\left(\mathit{freeVars}(\varphi)\cup\{t\}\right)\setminus\{v\}

**Semantics.** Let :math:`\mathit{subtrees}(N,t)` be the subtrees of the
derivation tree :math:`t` labeled with the nonterminal symbol :math:`N`. Then, we
define the semantics of quantified formulas without match expressions as
follows:

* :math:`\beta\models\mathtt{forall}~T~v~\mathtt{in}~t:\,\varphi` holds if, and
  only if, :math:`\beta[v\mapsto{}t']\models\varphi` holds for all
  :math:`t'\in\mathit{subtrees}` \beta(t))\\)
* :math:`\beta\models\mathtt{exists}~T~v~\mathtt{in}~t:\,\varphi` holds if, and
  only if, :math:`\beta[v\mapsto{}t']\models\varphi` holds for some
  :math:`t'\in\mathit{subtrees}` \beta(t))\\)

where :math:`\beta[v\mapsto{}t']` is the variable assignment mapping variable
:math:`v` to the derivation tree :math:`t'` and all other variables to their mapping
in :math:`\beta`.

.. _tree-quantifiers-with-match-expressions:

Tree Quantifiers with Match Expressions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A *match expression* is an abstract word from the language of the reference
grammar. For example, :code:`x := y` is a concrete word from our assignment language
(see :ref:`introduction`); :code:`<var> := y` would be a valid match
expression. Additionally, match expressions allow binding elements of that
"abstract" word to variables, as in :code:`{<var> myvar} := y`. By using match
expressions in quantifiers, we can (1) restrict the possible instantiations of
the bound variable to those that match the match expression, and (2) access
elements of these instantiations by giving them names that can be referred in
the quantified formula.

To increase the flexibility of match expressions, they can contain *optional*
elements inside square brackets :code:`[...]`. Elements inside these optionals cannot
be bound to variables: Only plain terminal and nonterminal symbols may occur
there. For example, :code:`<assgn>[ ; <stmt>]` is a possible match expression for a
:code:`<stmt>` nonterminal in the assignment language. It matches statements
consisting of a single assignment and one with an assignment followed by a
statement. Match expressions can also go "deeper." The expression
:code:`<assgn>[ ; <assgn>]` is also a valid match expression for a :code:`<stmt>`, matching
any statement consisting of exactly one *or* two assignments.

**Free variables.** For a match expression :math:`\mathit{mexpr}`, let
:math:`\mathit{freeVars}(\mathit{mexpr})` be the variables specified in curly
braces inside :math:`\mathit{mexpr}`. Let :math:`Q` be :code:`forall` or :code:`exists`. Then,
we define

.. math::

   \mathit{freeVars}(Q~T~v\mathtt{=}\text{"$\mathit{mexpr}$"}~\mathtt{in}~\mathit{t}:~\varphi)
   :=\left(\mathit{freeVars}(\varphi)\cup\mathit{freeVars}(\mathit{mexpr})\cup\{t\}\right)\setminus\{v\}

To define the *semantics* of quantifiers with match expressions, we parse the
match expression into a set of (typically open, i.e., containing nonterminal
leaves) derivation trees. We can get more than one result: Either because
optionals are used, or because the reference grammar is ambiguous. If the match
expression contains variables, we record the paths from the root of these trees
to the nodes corresponding to the bound elements. Then, we continue as for
:ref:`quantified formulas without match expressions <tree-quantifiers-without-match-expressions>`:
If :code:`Q <type> var="mexpr" in tree: A` is the formula (:code:`Q` being either :code:`forall` or :code:`exists`),
we collect subtrees from :code:`tree` with roots labeled with :code:`<type>`. Then, however,
we select only those of which some derivation tree for the match expression
is a *prefix*. Then, we instantiate :code:`var` and all variables in :code:`mexpr` according
to the found match, and check whether :code:`A` holds for all/one of these
instantiations.

To make this—slightly—more formal, we "define" a function
:math:`\mathit{mexprTrees}` by example.  The result of
:math:`\mathit{mexprTrees}(T,\mathit{mexpr})`, for a nonterminal symbol :math:`T` and
match expression :math:`\mathit{mexpr}`, is a set of pairs :math:`(t,P)` of (1) a
derivation tree :math:`t` corresponding to the parsed match expression, where
:math:`T` is used as a start symbol (such that the root of :math:`t` is labeled with
:math:`T`), and (2) a mapping :math:`P` of variables bound in match expressions to
the paths where the corresponding tree elements occur in :math:`t`.

Consider again the assignment language and let the match expression
:math:`\mathit{mexpr}` be :code:`{<var> lhs} := {<var> rhs}[ ; <assgn>]`. We visualize
the result of
:math:`\mathit{mexprTrees}(\mathtt{\langle{}stmt\rangle},\mathit{mexpr})` by
indicating the mapping :math:`P` in the textual representation of the two
resulting derivation trees. The first element of the result set, where the
optional part has been left out, is

.. code-block::

   stmt
   └─ assgn
      ├─ var      lhs ↦ (0,0)
      ├─ " := "
      └─ rhs
         └─ var   rhs ↦ (0,2,0)

The second element, which contains the optional second assignment, is

.. code-block::

   stmt
   ├─ assgn
   │  ├─ var      lhs ↦ (0,0)
   │  ├─ " := "
   │  └─ rhs
   │     └─ var   rhs ↦ (0,2,0)
   ├─ " ; "
   └─ stmt
      └─ assgn

We need a function :math:`\mathit{match}(t, t', P)` taking a derivation tree
:math:`t` and a pair :math:`t',P` computed by :math:`\mathit{mexprTrees}` and
returning (1) :math:`\bot` if :math:`t'` does not match :math:`t`, or otherwise (2) a
*variable assignment* mapping variables in :math:`P` to the corresponding
subtrees in :math:`t`.

We now recursively define :math:`\mathit{match}`. Thereby,

* :math:`l(t)` is the label of the tree :math:`t`;
* all alternatives in the definition are *mutually exclusive* (the first
  applicable one is applied);
* by :math:`\mathit{numc}(t)` we denote the number of  children of the derivation
  tree :math:`t`;
* by :math:`\mathit{child}(t, i)` we denote the :math:`i`-th child of t, starting
  with 1;
* :math:`P_i` is computed from a mapping :math:`P` from variables to paths by
  discarding all paths in :math:`P` not starting with :math:`i` and taking the
  *tail* (discarding the first element) for all other paths; and
* we use standard set union notation :math:`\bigcup_{i=1}^n\beta_i` for combining
  variable assignments :math:`\beta_i`.

.. math::

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

Based on :math:`\mathit{match}` and :math:`\mathit{mexprTrees}`, we can now define the semantics of
quantified formulas with match expressions.

* :math:`\beta\models\mathtt{forall}~T~v\mathtt{=}\text{"$\mathit{mexpr}$"}~\mathtt{in}~t:\,\varphi`
  holds if, and only if,
  * **for all** :math:`t_1\in\mathit{subtrees}(T, \beta(t))` and
  * **for all** :math:`(t_2,P) \in \mathit{mexprTrees}(T, \mathit{mexpr})`, it holds that
  * :math:`\mathit{match}(t_1, t_2, P)\neq\bot` **implies that**
  * :math:`\beta[v\mapsto{}t_1]\cup\mathit{match}(t_1, t_2, P)\models\varphi`.
* :math:`\beta\models\mathtt{exists}~T~v\mathtt{=}\text{"$\mathit{mexpr}$"}~\mathtt{in}~t:\,\varphi`
  holds if, and only if,
  * **there is a** :math:`t_1\in\mathit{subtrees}(T, \beta(t))` and
  * **there is a** :math:`(t_2,P) \in \mathit{mexprTrees}(T, \mathit{mexpr})` such that
  * :math:`\mathit{match}(t_1, t_2, P)\neq\bot` **and**
  * :math:`\beta[v\mapsto{}t_1]\cup\mathit{match}(t_1, t_2, P)\models\varphi`.

.. _numeric-quantifiers:

Numeric Quantifiers
"""""""""""""""""""

Numeric quantifiers are of the form :code:`forall int var; A` or :code:`exists int var; A`.
They allow introducing a fresh variable, unconnected to the reference grammar,
ranging over strings representing *positive* integers. We only allow positive
integers since the SMT solver used by ISLa, Z3, does not support converting
negative numeric strings to integers and back (see
`this GitHub issue <https://github.com/Z3Prover/z3/issues/1846#issuecomment-424809364>`_). The
main use case of numeric quantifiers is connecting several semantic predicates.
Consider, for example, the following ISLa constraint for CSV files:

.. code-block::

   exists int colno: (
     str.to.int(colno) >= 3 and
     str.to.int(colno) <= 5 and
     count(<csv-header>, "<column>", colno) and
     forall <csv-record> line:
       count(line, "<column>", colno))

This constraint expresses that the number of columns in the :code:`<csv-header>` field
of a CSV header is between 3 and 5, and that all lines after the header have to
share the same number of columns. If it was possible to express the :code:`count`
predicate using pure SMT-LIB expressions, we could have expressed this
constraint without semantic predicates and, consequently, without the
existential integer quantifier by forming an equation of the number of columns
in the header and the number of columns in each line.

The :code:`forall int` quantifier expresses that a property has to hold *for all*
possible positive integers. In our experience, it is not often used in practice.
However, if we wanted to *negate* the above property for CSV files, the result
would contain such a quantifier.

**Free variables.** The free variables set is computed similarly as for
:ref:`tree quantifiers <tree-quantifiers>`. Let :math:`Q` be :code:`forall` or :code:`exists`. We define

.. math::

   \mathit{freeVars}(Q~\mathtt{int}~v:~\varphi):=\mathit{freeVars}(\varphi)\setminus\{v\}

**Semantics.** Let :math:`N` be the set of all derivation trees whose string
representation correspond to that of a positive integer, e.g., "0", 1", "17",
etc. We define the semantics of quantified integer formulas as follows:

* :math:`\beta\models\mathtt{forall~int}~v:\,\varphi` holds if, and
  only if, :math:`\beta[v\mapsto{}n]\models\varphi` holds for all
  :math:`n\in{}N`
* :math:`\beta\models\mathtt{exists~int}~v:\,\varphi` holds if, and
  only if, :math:`\beta[v\mapsto{}n]\models\varphi` holds for some
  :math:`n\in{}N`

.. _footnotes:

.. rubric:: Footnotes

.. [#f1] From `ISLa 0.8.14 <https://github.com/rindPHI/isla/blob/v0.8.14/CHANGELOG.md>`_ on, the :code:`ISLaSolver` and the :code:`evaluate` function both accept grammars in concrete syntax in addition to the Python dictionary format of the `Fuzzing Book <https://www.fuzzingbook.org/html/Grammars.html>`_.
.. [#f2] For example, John E. Hopcroft, Rajeev Motwani, Jeffrey D. Ullman: *Introduction to Automata Theory, Languages, and Computation, 3rd Edition*. Pearson international edition, Addison-Wesley 2007, ISBN 978-0-321-47617-3.
.. [#f3] In the SMT-LIB standard, this function is called :code:`str.to_int`. ISLa, however, uses the Z3 SMT solver, where the corresponding function has the name :code:`str.to.int`. Obviously, Z3 supported :code:`str.to.int` before :code:`str.to_int` became an official standard (see https://stackoverflow.com/questions/46524843/missing-str-to-int-s-in-z3-4-5-1#answer-46528332).
.. [#f4] In the ISLa implementation, we distinguish two types (in the sense of object-oriented classes) of variables: *bound variables* (bound by :ref:`quantifiers`) and *constants*. Thus, we can always extract reference trees from variable assignments.
.. [#f5] In the ISLa system, derivation trees have unique identifiers, such that we can distinguish trees with identical structure.

.. _SMT-LIB Language: https://smtlib.cs.uiowa.edu
