import string

from fuzzingbook.Grammars import srange

ISLA_GRAMMAR = {
    "<start>": ["<const><vars_block><constraint_decl>"],

    "<const>": ["const<wss><id>:<mwss><nonterminal><mwss>;<mwss>"],

    "<vars_block>": ["vars<mwss>{<mwss><var_decls><mwss>}<mwss>", ""],
    "<var_decls>": ["<var_decl><mwss><var_decls>", "<var_decl>"],
    "<var_decl>": ["<ids_list><mwss>:<mwss><var_type><mwss>;"],
    "<var_type>": ["<nonterminal>", "NUM"],
    "<nonterminal>": ["<<nonterminal_chars>>"],

    "<constraint_decl>": ["constraint<mwss>{<mwss><constraint><mwss>}"],
    "<constraint>": ["<disjunction>"],
    "<disjunction>": ["(<mwss><conjunction><wss>or<wss><disjunction><mwss>)", "<conjunction>"],
    "<conjunction>": ["(<mwss><negation><wss>and<wss><conjunction><mwss>)", "<negation>"],
    "<negation>": [
        "not<wss><constraint>",
        "<smt_atom>",
        "<num_intro>",
        "<quantified_formula>",
        "<predicate_atom>",
    ],

    "<num_intro>": ["num<wss><id>:<mwss><constraint>"],

    "<quantified_formula>": [
        "<quantifier><wss><id>=<bind_expr><wss>in<wss><id>:<mwss><constraint>",
        "<quantifier><wss><id><wss>in<wss><id>:<mwss><constraint>",
    ],
    "<quantifier>": ["forall", "exists"],
    "<bind_expr>": ["\"<var_or_esc_chars_list>\""],
    "<var_or_esc_chars_list>": [
        "<var><var_or_esc_chars_list>",
        "<esc_chars><var_or_esc_chars_list>",
        "<var>",
        "<esc_chars>"
    ],
    "<var>": ["{<id>}"],
    "<esc_chars>": ["<esc_char><esc_chars>", "<esc_char>"],
    "<esc_char>": ['\\"', "{{", "}}"] + list(set(string.printable) - {'"', "{", "}"}),

    "<smt_atom>": ["<smt_bool_term>"],
    "<smt_bool_term>": ["true", "false", "(<fsym><wss><sexpr_list>)"],
    "<sexpr_list>": ["<sexpr><wss><sexpr_list>", "<sexpr>"],
    "<sexpr>": ["<smt_bool_term>", "<number>", "<id>", "<string>"],
    "<fsym>": ["<fsymchar_nondigit><fsymchars>"],
    "<fsymchar_nondigit>": ["<letter>"] + srange("~!@$%^&*_-+=<>.?/"),
    "<fsymchars>": ["<fsymchar><fsymchars>", ""],
    "<fsymchar>": ["<letter>", "<digit>"] + srange("~!@$%^&*_-+=<>.?/"),

    "<predicate_atom>": ["<predicate>(<args>)"],
    "<predicate>": ["<letter><idchars>", "<letter>"],
    "<args>": ["<arg>,<wss><args>", "<arg>"],
    "<arg>": ["<id>", "<number>", "<string>"],

    "<ids_list>": ["<id>,<mwss><ids_list>", "<id>"],
    "<id>": ["<letter><idchars>", "<letter>"],
    "<string>": ["\"<escaped_string>\""],
    "<escaped_string>": ["<escaped_string_char><escaped_string>", "<escaped_string_char>"],
    "<escaped_string_char>": list(set(string.printable) - {'"'}) + ['\\"'],
    "<number>": ["<digits>"],
    "<digits>": ["<digit><digits>", "<digit>"],
    "<digit>": srange(string.digits),
    "<idchar>": ["<letter>", "<digit>", "_"],
    "<idchars>": ["<idchar><idchars>", "<idchar>"],
    "<letter>": srange(string.ascii_lowercase),
    "<nonterminal_chars>": ["<nonterminal_char><nonterminal_chars>", "<nonterminal_char>"],
    "<nonterminal_char>": srange(string.ascii_letters + "-_"),

    "<mwss>": ["<wss>", ""],
    "<wss>": ["<ws><wss>", "<ws>"],
    "<ws>": srange("\n\r\t ")
}
