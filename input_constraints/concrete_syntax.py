import string
from typing import List, cast, Union, Dict, Optional

import z3
from fuzzingbook.Grammars import srange
from fuzzingbook.Parser import PEGParser

from input_constraints import isla
from input_constraints.helpers import get_symbols

ISLA_GRAMMAR = {
    "<start>": ["<const><vars_block><constraint_decl>"],

    "<const>": ["const<wss><id>:<mwss><nonterminal><mwss>;<mwss>"],

    "<vars_block>": ["vars<mwss>{<mwss><var_decls><mwss>}<mwss>", ""],
    "<var_decls>": ["<var_decl><mwss><var_decls>", "<var_decl>"],
    "<var_decl>": ["<ids_list><mwss>:<mwss><nonterminal><mwss>;"],
    "<nonterminal>": ["<<nonterminal_chars>>"],

    "<constraint_decl>": ["constraint<mwss>{<mwss><constraint><mwss>}"],
    "<constraint>": ["<disjunction>"],
    "<disjunction>": ["(<mwss><conjunction><wss>or<wss><disjunction><mwss>)", "<conjunction>"],
    "<conjunction>": ["(<mwss><negation><wss>and<wss><conjunction><mwss>)", "<negation>"],
    "<negation>": [
        "not<wss>(<constraint>)",
        "<smt_atom>",
        "<quantified_formula>",
        "<predicate_atom>",
    ],

    "<quantified_formula>": [
        "<quantifier><wss><id>=<bind_expr><wss>in<wss><id>:<wss><constraint>",
        "<quantifier><wss><id><wss>in<wss><id>:<wss><constraint>",
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
    "<esc_char>": ['\\"', "\\{", "\\}"] + list(set(string.printable) - {'"', "{", "}"}),

    "<smt_atom>": ["<smt_bool_term>"],
    "<smt_bool_term>": ["true", "false", "(<fsym><wss><sexpr_list>)"],
    "<sexpr_list>": ["<sexpr><wss><sexpr_list>", "<sexpr>"],
    "<sexpr>": ["<smt_bool_term>", "<number>", "<id>", "<string>"],
    "<fsym>": ["<fsymchar_nondigit><fsymchars>"],
    "<fsymchar_nondigit>": ["<letter>"] + srange("~!@$%^&*_-+=<>.?/"),
    "<fsymchars>": ["<fsymchar><fsymchars>", ""],
    "<fsymchar>": ["<letter>", "<digit>"] + srange("~!@$%^&*_-+=<>.?/"),

    "<predicate_atom>": ["<predicate>(<args>)"],
    "<predicate>": ["<letters>"],
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
    "<letters>": ["<letter><letters>", "<letter>"],
    "<idchar>": ["<letter>", "<digit>", "_"],
    "<idchars>": ["<idchar><idchars>", "<idchar>"],
    "<letter>": srange(string.ascii_lowercase),
    "<nonterminal_chars>": ["<nonterminal_char><nonterminal_chars>", "<nonterminal_char>"],
    "<nonterminal_char>": srange(string.ascii_letters + "-_"),

    "<mwss>": ["<wss>", ""],
    "<wss>": ["<ws><wss>", "<ws>"],
    "<ws>": srange("\n\r\t ")
}


def parse_isla(inp: str,
               structural_predicates: Optional[Dict[str, isla.StructuralPredicate]] = None,
               semantic_predicates: Optional[Dict[str, isla.SemanticPredicate]] = None) -> isla.Formula:
    if structural_predicates is None:
        structural_predicates = {}
    if semantic_predicates is None:
        semantic_predicates = {}

    pegparser = PEGParser(ISLA_GRAMMAR)
    tree = isla.DerivationTree.from_parse_tree(pegparser.parse(inp.strip())[0])

    const_decl = tree.filter(lambda n: n.value == "<const>", enforce_unique=True)[0][1]
    const = isla.Constant(str(const_decl.children[2]), str(const_decl.children[-4]))

    var_decls = tree.filter(lambda n: n.value == "<var_decl>")
    variables: List[isla.BoundVariable] = []
    for var_decl in var_decls:
        ids = [str(id) for _, id in var_decl[1].filter(lambda n: n.value == "<id>")]
        ntype = [str(nt) for _, nt in var_decl[1].filter(lambda n: n.value == "<nonterminal>")][0]
        variables.extend([isla.BoundVariable(id, ntype) for id in ids])

    all_vars = [cast(isla.Variable, const)] + variables

    def check_undeclared_ids(tree: isla.DerivationTree) -> None:
        undeclared_ids = [
            str(var[1]) for var in tree.filter(lambda n: n.value == "<id>")
            if all(decl_var.name != str(var[1]) for decl_var in all_vars)
        ]

        if undeclared_ids:
            raise SyntaxError(f"Undeclared symbols '{', '.join(undeclared_ids)}' in {tree}")

    def parse_constraint(tree: isla.DerivationTree) -> isla.Formula:
        if tree.value == "<constraint>":
            return parse_constraint(tree.children[0])
        if tree.value == "<disjunction>":
            if len(tree.children) == 1:
                return parse_constraint(tree.children[0])
            else:
                return parse_constraint(tree.children[2]) | parse_constraint(tree.children[-3])
        elif tree.value == "<conjunction>":
            if len(tree.children) == 1:
                return parse_constraint(tree.children[0])
            else:
                return parse_constraint(tree.children[2]) & parse_constraint(tree.children[-3])
        elif tree.value == "<negation>":
            if len(tree.children) == 1:
                return parse_constraint(tree.children[0])
            else:
                return -parse_constraint(tree.children[-2])
        elif tree.value == "<smt_atom>":
            check_undeclared_ids(tree)

            z3_constr = z3.parse_smt2_string(
                f"(assert {str(tree)})",
                decls={var.name: z3.String(var.name) for var in all_vars})[0]
            free_vars = [v for v in [cast(isla.Variable, const)] + variables
                         if v.name in [str(s) for s in get_symbols(z3_constr)]]
            return isla.SMTFormula(z3_constr, *free_vars)
        elif tree.value == "<predicate_atom>":
            check_undeclared_ids(tree)

            predicate_name = str(tree.children[0])
            if predicate_name not in structural_predicates and predicate_name not in semantic_predicates:
                raise SyntaxError(f"Unknown predicate {predicate_name} in {tree}")

            args = [
                next(var for var in all_vars if var.name == str(arg[1].children[0]))
                if arg[1].children[0].value == "<id>"
                else int(str(arg)) if arg[1].children[0].value == "<number>"
                else str(arg)
                for arg in tree.filter(lambda n: n.value == "<arg>")]

            is_structural = predicate_name in structural_predicates

            predicate = (
                structural_predicates[predicate_name] if is_structural
                else semantic_predicates[predicate_name])

            if len(args) != predicate.arity:
                raise SyntaxError(
                    f"Unexpected number {len(args)} for predicate {predicate_name} "
                    f"({predicate.arity} expected) in {tree}")

            if is_structural:
                return isla.StructuralPredicateFormula(predicate, *args)
            else:
                return isla.SemanticPredicateFormula(predicate, *args)
        elif tree.value == "<quantified_formula>":
            qfr_sym = str(tree.children[0])
            bvar_sym = str(tree.children[2])
            invar_sym = str(tree.children[-4])

            for sym in [bvar_sym, invar_sym]:
                if all(v.name != sym for v in all_vars):
                    raise SyntaxError(f"Undeclared symbol {sym} in {str(tree)}")

            bvar = next(v for v in variables if v.name == bvar_sym)
            invar = next(v for v in all_vars if v.name == invar_sym)

            bexpr = None
            if tree.children[4].value == "<bind_expr>":
                bexpr = parse_bind_expr(tree.children[4])

            inner_constraint = parse_constraint(tree.children[-1])

            if qfr_sym == "forall":
                return isla.ForallFormula(bvar, invar, inner_constraint, bind_expression=bexpr)
            else:
                return isla.ExistsFormula(bvar, invar, inner_constraint, bind_expression=bexpr)
        else:
            raise NotImplementedError(f"Cannot parse expression {str(tree)}, symbol {tree.value}")

    def parse_bind_expr(tree: isla.DerivationTree) -> isla.BindExpression:
        result_elements: List[Union[str, isla.BoundVariable]] = []
        curr_terminal = ""

        leaves = cast(isla.DerivationTree, tree.children[1]).filter(
            lambda n: n.value in ["<var>", "<esc_char>"])

        for _, leaf in leaves:
            if leaf.value == "<esc_char>":
                curr_terminal += str(leaf)
            else:
                if curr_terminal:
                    result_elements.append(curr_terminal)
                    curr_terminal = ""

                try:
                    result_elements.append(next(v for v in variables if v.name == str(leaf.children[1])))
                except StopIteration:
                    raise SyntaxError(f"Undeclared symbol {str(leaf.children[1])} in {str(tree)}")

        if curr_terminal:
            result_elements.append(curr_terminal)

        return isla.BindExpression(*result_elements)

    return parse_constraint(
        tree.filter(lambda n: n.value == "<constraint_decl>", True)[0][1].children[-3])
