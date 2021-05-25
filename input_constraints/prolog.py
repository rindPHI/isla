from typing import List, Dict, Tuple, Union

from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import non_canonical
from grammar_graph.gg import GrammarGraph
from pyswip import Prolog

from input_constraints.type_defs import CanonicalGrammar, Grammar


def predicate_names_for_nonterminals(grammar: Union[Grammar, CanonicalGrammar]) -> Dict[str, str]:
    """
    Creates a mapping of nonterminal names (w/o the "<", ">") to the corresponding predicate names. Accounts
    for predefined predicates.

    :param grammar: The grammar, for extracting the nonterminals.
    :return: The mapping.
    """
    prolog = Prolog()
    predicate_map: Dict[str, str] = {}
    for nonterminal in grammar:
        nonterminal = nonterminal[1:-1]
        idx = 0
        curr_name = nonterminal
        while list(prolog.query(f"current_predicate({curr_name}/1)")):
            curr_name = f"{nonterminal}_{idx}"
            idx += 1

        predicate_map[nonterminal] = curr_name

    return predicate_map


def translate_grammar(
        grammar: CanonicalGrammar,
        predicate_map: Dict[str, str],
        numeric_nonterminals: Dict[str, Tuple[int, int]],
        atomic_string_nonterminals: Dict[str, int]
) -> List[str]:
    """
    Translates a grammar to Prolog.

    :param grammar: The grammar in canonical form.
    :param predicate_map: Mapping of nonterminal names (w/o the "<", ">") to the corresponding predicate names. Accounts
    for predefined predicates.
    :param numeric_nonterminals: Nonterminals of integer type, mapped to their bounds.
    :param atomic_string_nonterminals: Nonterminals of string type whose internal structure does not matter for
    the constraint at hand, and which therefore can be abstracted by integers (for later fuzzing).
    :return: The prolog translation of `grammar`.
    """
    lines: List[str] = []
    graph = GrammarGraph.from_grammar(non_canonical(grammar))

    for nonterminal, alternatives in [(n, a) for n, a in grammar.items()
                                      if n not in numeric_nonterminals
                                         and n not in atomic_string_nonterminals]:
        nonterminal = nonterminal[1:-1]
        for alternative in alternatives:
            params: List[str] = []
            variables: Dict[str, str] = {}
            for symbol in alternative:
                if is_nonterminal(symbol):
                    symbol_type = symbol[1:-1]
                    var_name = symbol_type.capitalize()
                    i = 1
                    while var_name in variables:
                        var_name += f"_{i}"
                    variables[var_name] = symbol_type
                    params.append(var_name)
                else:
                    params.append(f'["{symbol}", []]')

            params_str = "[" + ", ".join(params) + "]"
            line = f"{predicate_map[nonterminal]}(['{nonterminal}', {params_str}])"

            if variables:
                # Need to call recursive nonterminals first
                variables_list = sorted(variables.keys(),
                                        key=lambda n: (
                                            node := graph.get_node(f"<{variables[n]}>"),
                                            chr(0) if node.reachable(node) else n[1:-1])[-1])

                line += " :- "
                line += ", ".join([f"{predicate_map[variables[variable]]}({variable})" for variable in variables_list])

            lines.append(line)

    for nonterminal in numeric_nonterminals:
        lines.append(f"{predicate_map[nonterminal[1:-1]]}(['{nonterminal[1:-1]}', "
                     f"[[C, []]]]) :- "
                     f"{numeric_nonterminals[nonterminal][0]} #=< C, "
                     f"C #=< {numeric_nonterminals[nonterminal][1]}")

    for nonterminal in atomic_string_nonterminals:
        lines.append(f"{predicate_map[nonterminal[1:-1]]}(['{nonterminal[1:-1]}', "
                     f"[[C, []]]]) :- "
                     f"0 #=< C, "
                     f"C #=< {atomic_string_nonterminals[nonterminal]}")

    return lines
