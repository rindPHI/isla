import string

from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import srange

ISLA_GRAMMAR = {
    "<start>": ["<const><vars_block><constraint_decl>"],

    "<const>": ["const <id>: <nonterminal>;\n"],

    "<vars_block>": ["", "vars {\n<var_decls>\n}\n"],
    "<var_decls>": ["<var_decl>", "<var_decl>\n<var_decls>"],
    "<var_decl>": ["  <ids_list>: <nonterminal>;"],
    "<nonterminal>": ["<<letters>>"],

    "<constraint_decl>": ["constraint {\n  <constraint>\n}"],
    "<constraint>": ["<disjunction>"],
    "<disjunction>": ["<conjunction>", "(<conjunction> or <disjunction>)"],
    "<conjunction>": ["<negation>", "(<negation> and <conjunction>)"],
    "<negation>": [
        "<smt_atom>",
        "<predicate_atom>",
        "<quantified_formula>",
        "<quantified_formula>",
        "not (<constraint>)"
    ],

    "<quantified_formula>": [
        "<quantifier> <id> in <id>: <constraint>",
        "<quantifier> <id>=<bind_expr> in <id>: <constraint>"
    ],
    "<quantifier>": ["forall", "exists"],
    "<bind_expr>": ["\"<var_esc_char_list>\""],
    "<var_esc_char_list>": ["<var_esc_char>", "<var_esc_char><var_esc_char_list>"],
    "<var_esc_char>": ["{<id>}", '\\"', "\\{", "\\}"] + list(set(string.printable) - {'"', "{", "}"}),

    "<smt_atom>": ["(<fsym> <sexpr_list>)"],
    "<sexpr_list>": ["<sexpr>", "<sexpr>, <sexpr_list>"],
    "<sexpr>": ["<number>", "<id>", "<string>", "(<fsym> <sexpr_list>)"],
    "<fsym>": ["<fsymchar_nondigit><fsymchars>"],
    "<fsymchar_nondigit>": ["<letter>"] + srange("~!@$%^&*_-+=<>.?/"),
    "<fsymchars>": ["<fsymchar>", "<fsymchar><fsymchars>"],
    "<fsymchar>": ["<letter>", "<digit>"] + srange("~!@$%^&*_-+=<>.?/"),

    "<predicate_atom>": ["<predicate>(<args>)"],
    "<predicate>": ["<letters>"],
    "<args>": ["<arg>", "<arg><args>"],
    "<arg>": ["<id>", "<number>", "<string>"],

    "<ids_list>": ["<id>", "<id>, <ids_list>"],
    "<id>": ["<letters>"],
    "<string>": ["\"<escaped_string>\""],
    "<escaped_string>": ["<escaped_string_char>", "<escaped_string_char><escaped_string>"],
    "<escaped_string_char>": list(set(string.printable) - {'"'}) + ['\\"'],
    "<number>": ["<digits>"],
    "<digits>": ["<digit>", "<digit><digits>"],
    "<digit>": srange(string.digits),
    "<letters>": ["<letter>", "<letter><letters>"],
    "<letter>": srange(string.ascii_lowercase)
}

fuzzer = GrammarCoverageFuzzer(ISLA_GRAMMAR)
for _ in range(100):
    print(fuzzer.fuzz())
