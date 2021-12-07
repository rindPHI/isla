import string

from fuzzingbook.Grammars import srange

GRAMMAR = {
    "<start>": ["<stmts>"],
    "<stmts>": ["<stmt><NEWLINE><stmts>", "<stmt>"],
    "<loop_body_stmts>": ["<loop_body_stmt><NEWLINE><loop_body_stmts>", "<loop_body_stmt>"],
    "<stmt>": ["<compound_stmt>", "<simple_stmt>"],
    "<loop_body_stmt>": ["<compound_stmt>", "<simple_loop_body_stmt>"],
    "<simple_stmt>": [
        "pass",
        "<return_stmt>",
        "<assignment>",
        "<expression>",
        # "<raise_stmt>",
        # "<assert_stmt>",
    ],
    "<simple_loop_body_stmt>": [
        "pass",
        "break",
        "continue",
        "<return_stmt>",
        "<assignment>",
        "<expression>",
        # "<raise_stmt>",
        # "<assert_stmt>",
    ],
    "<compound_stmt>": [
        # "<function_def>",
        # "<try_stmt>",
        "<if_stmt>",
        "<while_stmt>"
        # "<for_stmt>",
    ],
    "<assignment>": ["<NAME> = <expression>"],
    "<return_stmt>": ["return <expression>"],
    # "<raise_stmt>": ["raise <expression>"],
    "<if_stmt>": ["if <expression>: <block><maybe_else_block>"],
    "<maybe_else_block>": ["<NEWLINE>else: <block>", ""],
    "<while_stmt>": ["while <expression>: <loop_block><maybe_else_block>"],
    # "<try_stmt>": ["try: <block><except_block>"],

    # "<function_def>": ["def <NAME>(<params>) -> <type>: <block>"],

    # "<except_block>": [
    #     "<NEWLINE>except <NAME>: <block>",
    #     "<NEWLINE>except: <block>"],
    "<block>": ["{<NEWLINE><stmts>}"],
    "<loop_block>": ["{<NEWLINE><loop_body_stmts>}"],

    # "<params>": ["<param>, <params>", "<param>", ""],
    # "<param>": ["<NAME>: <type>"],

    "<type>": ["int", "bool", "tuple"],

    "<expression>": ["<conjunction><or_conjunctions>"],
    "<or_conjunctions>": ["<or_conjunction><or_conjunctions>", ""],
    "<or_conjunction>": [" or <conjunction>"],
    "<conjunction>": ["<inversion><and_inversions>"],
    "<and_inversions>": ["<and_inversion><and_inversions>", ""],
    "<and_inversion>": [" and <inversion>"],
    "<inversion>": ["not <inversion>", "<comparison>", "(<expression>)"],
    "<comparison>": ["<sum><maybe_compare>"],
    "<maybe_compare>": [" <compare_op> <sum>", ""],
    "<compare_op>": ["==", "!=", "<=", ">=", "<", ">"],
    "<sum>": ["<term> <ssym> <sum>", "<term>"],
    "<ssym>": ["+", "-"],
    "<term>": [
        "<factor> <tsym> <term>",
        "<factor> <tsym> (<sum>)",
        "(<sum>) <tsym> <factor>",
        "(<sum>) <tsym> (<sum>)",

        "<factor>",
    ],
    "<tsym>": ["*", "//", "%"],
    "<factor>": ["+<factor>", "-<factor>", "<primary>"],
    "<primary>": [
        "<atom>[<expression>]",
        "<NAME>(<args>)[<expression>]",
        "<NAME>(<args>)",
        "<atom>"
    ],
    "<args>": ["<expression>, <args>", "<expression>", ""],
    "<atom>": ["True", "False", "<tuple>", "<NAME>", "<NUMBER>"],
    "<tuple>": ["(<expression>, <expression_list>)"],
    "<expression_list>": ["<expression>, <expression_list>", ""],

    "<NEWLINE>": ["\n"],
    "<NUMBER>": ["<DIGIT><NUMBER>", "<DIGIT>"],
    "<DIGIT>": srange(string.digits),
    "<NAME>": ["<INIT_CHAR><IDCHARS>"],
    "<INIT_CHAR>": srange(string.ascii_letters + "_"),
    "<IDCHARS>": ["<IDCHAR><IDCHARS>", "<IDCHAR>", ""],
    "<IDCHAR>": srange(string.ascii_letters + string.digits + "_"),
}


def to_real_python(inp: str) -> str:
    indent = 0
    result = ""

    for i in range(len(inp)):
        if inp[i] == "{":
            indent += 1
        elif inp[i] == "}":
            indent -= 1
        elif inp[i] == "\n":
            result += "\n" + "".ljust(indent * 4)
        else:
            result += inp[i]

    return result
