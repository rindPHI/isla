from operator import itemgetter
from typing import List, Dict, Tuple, Union
from pyswip import Prolog

from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import non_canonical
from grammar_graph.gg import GrammarGraph, ChoiceNode
from itertools import groupby

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
) -> str:
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

    terminal_parents: Dict[str, List[str]] = {}
    for nonterminal in grammar.keys():
        node = graph.get_node(nonterminal)
        if node.reachable(node):
            continue

        subgraph = graph.subgraph(node)
        children = [n.symbol for n in subgraph.all_nodes()
                    if type(n) is not ChoiceNode
                    and n.symbol not in ["<start>", nonterminal]]
        if all(not is_nonterminal(child) for child in children):
            terminal_parents[nonterminal] = children

    for nonterminal, alternatives in [(n, a) for n, a in grammar.items() if n not in terminal_parents]:
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

            line += "."
            lines.append(line)

    for nonterminal in terminal_parents:
        assert all(map(lambda c: len(c) == 1, terminal_parents[nonterminal]))
        children = sorted(list(map(ord, terminal_parents[nonterminal])))
        nonterminal = nonterminal[1:-1]
        ranges = [list(map(itemgetter(1), g)) for k, g in groupby(enumerate(children), lambda p: p[0] - p[1])]
        for range in ranges:
            if len(range) == 1:
                lines.append(f"{predicate_map[nonterminal]}(['{nonterminal}', [[{range[0]}, []]]).")
            else:
                lines.append(f"{predicate_map[nonterminal]}(['{nonterminal}', "
                             f"[[C, []]]) :- {range[0]} #=< C, C #=< {range[-1]}.")

    return "\n".join(lines)
