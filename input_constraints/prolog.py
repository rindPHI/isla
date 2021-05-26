from typing import List, Dict, Tuple, Type, Callable

import sys
import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import non_canonical
from grammar_graph.gg import GrammarGraph
from orderedset import OrderedSet
from pyswip import Prolog

from input_constraints.helpers import visit_z3_expr
from input_constraints.lang import Formula, SMTFormula, FormulaVisitor, ForallFormula, ExistsFormula, VariablesCollector
from input_constraints.prolog_structs import Rule, PredicateApplication, Predicate, Term, Variable, ListTerm, \
    StringTerm, Atom, Number
from input_constraints.type_defs import CanonicalGrammar


def translate_grammar(
        grammar: CanonicalGrammar,
        predicate_map: Dict[str, str],
        numeric_nonterminals: Dict[str, Tuple[int, int]],
        atomic_string_nonterminals: Dict[str, int]
) -> List[Rule]:
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
    rules: List[Rule] = []
    graph = GrammarGraph.from_grammar(non_canonical(grammar))

    for nonterminal, alternatives in [(n, a) for n, a in grammar.items()
                                      if n not in numeric_nonterminals
                                         and n not in atomic_string_nonterminals]:
        nonterminal = nonterminal[1:-1]
        for alternative in alternatives:
            params: List[Term] = []
            variables: Dict[str, str] = {}
            for symbol in alternative:
                if is_nonterminal(symbol):
                    symbol_type = symbol[1:-1]
                    var_name = symbol_type.capitalize()
                    i = 1
                    while var_name in variables:
                        var_name += f"_{i}"
                    variables[var_name] = symbol_type
                    params.append(Variable(var_name))
                else:
                    params.append(ListTerm([StringTerm(symbol), ListTerm([])]))

            atom_name = predicate_map[nonterminal]
            head = PredicateApplication(
                Predicate(atom_name, 1),
                [ListTerm([Atom(atom_name), ListTerm(params)])])

            goals = []
            if variables:
                # Need to call recursive nonterminals first
                variables_list = sorted(variables.keys(),
                                        key=lambda n: (
                                            node := graph.get_node(f"<{variables[n]}>"),
                                            chr(0) if node.reachable(node) else n[1:-1])[-1])

                goals = [PredicateApplication(Predicate(predicate_map[variables[variable]], 1),
                                              [Variable(variable)])
                         for variable in variables_list]

            rules.append(Rule(head, goals))

    for nonterminal in numeric_nonterminals:
        nonterminal_name = nonterminal[1:-1]
        c = Variable("C")
        leq = Predicate("#=<", 2, infix=True)

        rules.append(Rule(PredicateApplication(
            Predicate(predicate_map[nonterminal_name], 1),
            [ListTerm([Atom(nonterminal_name), ListTerm([ListTerm([c, ListTerm([])])])])]
        ), [
            PredicateApplication(leq, [Number(numeric_nonterminals[nonterminal][0]), c]),
            PredicateApplication(leq, [c, Number(numeric_nonterminals[nonterminal][1])])
        ]))

    for nonterminal in atomic_string_nonterminals:
        nonterminal_name = nonterminal[1:-1]
        c = Variable("C")
        leq = Predicate("#=<", 2, infix=True)

        rules.append(Rule(PredicateApplication(
            Predicate(predicate_map[nonterminal_name], 1),
            [ListTerm([Atom(nonterminal_name), ListTerm([ListTerm([c, ListTerm([])])])])]
        ), [
            PredicateApplication(leq, [Number(0), c]),
            PredicateApplication(leq, [c, Number(atomic_string_nonterminals[nonterminal])])
        ]))

    return rules


def translate_constraint(formula: Formula) -> str:
    translation_methods: Dict[Type[Formula], Type[Callable[[Formula], str]]] = {
        SMTFormula: translate_smt_formula
    }

    if type(formula) not in translation_methods:
        raise NotImplementedError

    return translation_methods[type(formula)](formula)


def translate_smt_formula(formula: SMTFormula) -> str:
    pass


class Translator:
    FUZZING_DEPTH_ATOMIC_STRING_NONTERMINALS = 10

    def __init__(self, grammar: CanonicalGrammar, formula: Formula):
        self.grammar = grammar
        self.formula = formula

        self.predicate_map: Dict[str, str] = self.compute_predicate_names_for_nonterminals()
        self.numeric_nonterminals: Dict[str, Tuple[int, int]] = self.compute_numeric_nonterminals()
        self.atomic_string_nonterminals: Dict[str, int] = self.compute_atomic_string_nonterminals()

    def compute_atomic_string_nonterminals(self) -> Dict[str, int]:
        non_atomic_variables = set()

        class NonAtomicVisitor(FormulaVisitor):
            def visit_forall_formula(self, formula: ForallFormula):
                non_atomic_variables.add(formula.in_variable)
                if formula.bind_expression is not None:
                    non_atomic_variables.add(formula.bound_variable)

            def visit_exists_formula(self, formula: ExistsFormula):
                non_atomic_variables.add(formula.in_variable.n_type)
                if formula.bind_expression is not None:
                    non_atomic_variables.add(formula.bound_variable)

            def visit_smt_formula(self, formula: SMTFormula):
                for expr in visit_z3_expr(formula.formula):
                    # Any non-trivial string expression, e.g., substring computations
                    # or regex operations, exclude the involved variables from atomic
                    # representations, since their internal structure matters.
                    # TODO: Have to more thoroughly test whether this suffices.
                    if expr.decl().name() == "str.in_re":
                        non_atomic_variables.update(formula.free_variables())

                    if z3.is_string(expr) and not z3.is_string_value(expr) and not z3.is_const(expr):
                        non_atomic_variables.update(formula.free_variables())

        self.formula.accept(NonAtomicVisitor())

        non_atomic_nonterminals = [variable.n_type for variable in non_atomic_variables]
        return {nonterminal: Translator.FUZZING_DEPTH_ATOMIC_STRING_NONTERMINALS
                for nonterminal in set(self.grammar.keys()).difference(non_atomic_nonterminals)}

    def compute_numeric_nonterminals(self) -> Dict[str, Tuple[int, int]]:
        result = {}
        noncanonical = non_canonical(self.grammar)
        for nonterminal in self.grammar:
            fuzzer = GrammarCoverageFuzzer(GrammarGraph.from_grammar(noncanonical).subgraph(nonterminal).to_grammar())
            lower_bound, upper_bound = sys.maxsize, -1
            for _ in range(100):
                try:
                    maybe_int = int(fuzzer.fuzz())
                    if maybe_int < lower_bound:
                        lower_bound = maybe_int
                    elif maybe_int > upper_bound:
                        upper_bound = maybe_int
                except ValueError:
                    break
            else:
                result[nonterminal] = (lower_bound, upper_bound)

        return result

    def compute_predicate_names_for_nonterminals(self) -> Dict[str, str]:
        """
        Creates a mapping of nonterminal names (w/o the "<", ">") to the corresponding predicate names. Accounts
        for predefined predicates.

        :return: The mapping.
        """
        prolog = Prolog()
        predicate_map: Dict[str, str] = {}
        for nonterminal in self.grammar:
            nonterminal = nonterminal[1:-1]
            idx = 0
            curr_name = nonterminal
            while list(prolog.query(f"current_predicate({curr_name}/1)")):
                curr_name = f"{nonterminal}_{idx}"
                idx += 1

            predicate_map[nonterminal] = curr_name

        return predicate_map
