import string

from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import srange

# This grammar is LL(1).
# Test at https://www.cs.princeton.edu/courses/archive/spring20/cos320/LL1/:
#
# STMT ::= ASSIGNMENT
# STMT ::= if PAREN_EXPR STMT else STMT
# STMT ::= while PAREN_EXPR STMT
# STMT ::= do STMT while PAREN_EXPR ;
# STMT ::= BLOCK
# STMT ::= ;
#
# ASSIGNMENT ::= id = EXPR ;
#
# BLOCK ::= { STATEMENTS }
#
# STATEMENTS ::= ''
# STATEMENTS ::= BLOCK_STATEMENT STATEMENTS
# BLOCK_STATEMENT ::= DECLARATION
# BLOCK_STATEMENT ::= STATEMENT
# DECLARATION ::= int id DECLARATION' ;
# DECLARATION' ::= ''
# DECLARATION' ::= = EXPR
#
# EXPR ::= TEST
# TEST ::= ADD TEST'
# TEST' ::= ''
# TEST' ::= < ADD
# ADD ::= MUL ADD'
# ADD' ::= ''
# ADD' ::= + MUL ADD'
# ADD' = - MUL ADD'
#
# MUL ::= TERM MUL'
# MUL' ::= ''
# MUL' ::= * TERM MUL'
# MUL' ::= / TERM MUL'
#
# TERM ::= num
# TERM ::= id
# TERM ::= PAREN_EXPR
# PAREN_EXPR ::= ( TEST )

# Compared to Scriptsize-C, removed
# * the if statement without else
# * assignment *expressions*, so assignments are statements and expressions are side-effect free.
# * Consequently, remove the expression statement since it has no effect any more.

GRAMMAR = {
    "<start>": ["<statement>"],
    "<statement>": [
        "<block>",
        "if<paren_expr> <statement> else <statement>",
        "while<paren_expr> <statement>",
        "do <statement> while<paren_expr>;",
        "<assignment>"
        ";"
    ],
    "<block>": ["{<statements>}"],
    "<statements>": ["<block_statement><statements>", ""],
    "<block_statement>": ["<statement>", "<declaration>"],
    "<declaration>": [
        "int <id><declaration'>;",
    ],
    "<declaration'>": [
        "",
        "= <expr>"
    ],
    "<assignment>": [
        "<id> = <expr>;"
    ],
    "<expr>": ["<test>"],
    "<test>": ["<add><test'>"],
    "<test'>": [
        "",
        "<<add>",
    ],
    "<add>": ["<mul><add'>"],
    "<add'>": [
        "",
        "+<mul><add'>",
        "-<mul><add'>",
    ],
    "<mul>": ["<term><mul'>"],
    "<mul'>": [
        "",
        "*<term><mul'>",
        "/<term><mul'>",
    ],
    "<term>": [
        "<num>",
        "<id>",
        "<paren_expr>",
    ],
    "<paren_expr>": [
        "(<test>)",
    ],
    "<id>": srange(string.ascii_lowercase),
    "<num>": [
        "<digit_nonzero><digits>",
        "<digit>",
    ],
    "<digits>": [
        "<digit><num>",
        "<digit>",
    ],
    "<digit>": srange(string.digits),
    "<digit_nonzero>": list(set(srange(string.digits)) - {"0"}),
}

fuzzer = GrammarCoverageFuzzer(GRAMMAR)
for _ in range(100):
    print(fuzzer.fuzz())
