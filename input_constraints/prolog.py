import logging
import re
import tempfile
from typing import List, Dict, Tuple, Type, Callable, Union

import pyswip
import sys
import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.GrammarFuzzer import tree_to_string
from fuzzingbook.Grammars import is_nonterminal
from fuzzingbook.Parser import non_canonical, canonical
from grammar_graph.gg import GrammarGraph, ChoiceNode, NonterminalNode, Node
from orderedset import OrderedSet
from pyswip import Prolog, registerForeign

from input_constraints.helpers import visit_z3_expr, is_canonical_grammar, is_z3_var, pyswip_output_to_str
import input_constraints.lang as isla
import input_constraints.prolog_structs as pl
from input_constraints.type_defs import CanonicalGrammar, Grammar
import input_constraints.prolog_shortcuts as psc

# A TranslationResult for a constraint is a list of Prolog rules together with a list of foreign foreign predicates,
# each consisting of the Python function for the predicate, the predicate name, and its arity.
TranslationResult = Tuple[List[pl.Rule], List[Tuple[Callable, str, int]]]


class Translator:
    # TODO: Make configurable
    FUZZING_DEPTH_ATOMIC_STRING_NONTERMINALS = 10

    def __init__(self, grammar: Union[Grammar, CanonicalGrammar], formula: isla.Formula):
        if is_canonical_grammar(grammar):
            self.grammar = grammar
        else:
            self.grammar = canonical(grammar)

        self.formula = formula

        self.used_variables: OrderedSet[isla.Variable] = isla.VariablesCollector(formula).collect()
        self.isla_to_prolog_var_map: Dict[isla.Variable, pl.Variable] = \
            {iv: self.to_prolog_var(iv) for iv in self.used_variables}
        self.isla_var_name_to_prolog_var_map: Dict[isla.Variable, pl.Variable] = \
            {iv.name: pv for iv, pv in self.isla_to_prolog_var_map.items()}
        self.predicate_map: Dict[str, str] = self.compute_predicate_names_for_nonterminals()
        self.numeric_nonterminals: Dict[str, Tuple[int, int]] = self.compute_numeric_nonterminals()
        self.atomic_string_nonterminals: Dict[str, int] = self.compute_atomic_string_nonterminals()

        self.logger = logging.getLogger(type(self).__name__)

    def translate(self) -> Prolog:
        def numeric_nonterminal(atom: pyswip.easy.Atom) -> bool:
            return f"<{atom.value}>" in self.numeric_nonterminals

        def atomic_string_nonterminal(atom: pyswip.easy.Atom) -> bool:
            return f"<{atom.value}>" in self.atomic_string_nonterminals

        fuzz_results: Dict[str, List[str]] = {}
        fuzzers: Dict[str, GrammarCoverageFuzzer] = {}

        def fuzz(atom: pyswip.easy.Atom, idx: int, result: pyswip.easy.Variable) -> bool:
            nonterminal = f"<{atom.value}>"

            grammar = GrammarGraph.from_grammar(non_canonical(self.grammar)).subgraph(nonterminal).to_grammar()
            fuzzer = fuzzers.setdefault(nonterminal, GrammarCoverageFuzzer(grammar))
            fuzz_results.setdefault(nonterminal, [])

            while len(fuzz_results[nonterminal]) <= idx:
                fuzz_results[nonterminal].append(fuzzer.fuzz())

            result.value = fuzz_results[nonterminal][idx]
            return True

        prolog = Prolog()

        try:
            import importlib.resources as pkg_resources
        except ImportError:
            # Try backported to PY<37 `importlib_resources`.
            import importlib_resources as pkg_resources

        preamble = pkg_resources.read_text(__package__, 'prolog_defs.pl')

        with tempfile.NamedTemporaryFile() as tmp:
            tmp.write(preamble.encode())
            prolog.consult(tmp.name)

        next(prolog.query("use_module(library(clpfd))"))

        for pred in ["atomic_nonterminal/1", "atomic_string_nonterminal/1", "fuzz/3"]:
            next(prolog.query(f"abolish({pred})"))

        registerForeign(numeric_nonterminal, name="numeric_nonterminal", arity=1)
        registerForeign(atomic_string_nonterminal, name="atomic_string_nonterminal", arity=1)
        registerForeign(fuzz, name="fuzz", arity=3)

        pl_grammar = self.translate_grammar()
        for rule in pl_grammar:
            prolog.assertz(str(rule))

        try:
            rules, foreign_functions = self.translate_constraint(self.formula)
            for rule in rules:
                prolog.assertz(str(rule))
            for func, name, arity in foreign_functions:
                registerForeign(func, name=name, arity=arity)
        except NotImplementedError as e:
            # TODO: Remove. Only for testing during ongoing development
            self.logger.warning(f"Translation method not implemented: {str(e)}")

        return prolog

    def translate_constraint(self, formula: isla.Formula, counter: int = 0) -> TranslationResult:
        translation_methods: Dict[Type[isla.Formula], Type[Callable[[isla.Formula, int], TranslationResult]]] = {
            isla.SMTFormula: self.translate_smt_formula,
            isla.PredicateFormula: self.translate_predicate_formula,
        }

        if type(formula) not in translation_methods:
            raise NotImplementedError(f"Translation for '{type(formula).__name__}' not implemented.")

        return translation_methods[type(formula)](formula, counter)

    def translate_predicate_formula(self, formula: isla.PredicateFormula, counter: int) -> TranslationResult:
        predicate = formula.predicate
        if predicate is isla.BEFORE_PREDICATE:
            head, isla_to_pl_vars_mapping, free_pl_vars, result_var, all_pl_vars = self.create_head(formula, counter)
            pvar1 = self.fresh_variable("Path1", all_pl_vars)
            pvar2 = self.fresh_variable("Path2", all_pl_vars.union([pvar1]))

            goals: List[pl.Goal] = [
                psc.unify(psc.pair(pvar1, psc.anon_var()), isla_to_pl_vars_mapping[formula.args[0]]),
                psc.unify(psc.pair(pvar2, psc.anon_var()), isla_to_pl_vars_mapping[formula.args[1]]),
                psc.ite(
                    pl.PredicateApplication(
                        pl.Predicate("path_is_before", 2), [pvar1, pvar2]
                    ),
                    psc.clp_eq(result_var, pl.Number(1)),
                    psc.clp_eq(result_var, pl.Number(0)),
                )
            ]

            return [pl.Rule(head, goals)], []
        else:
            raise NotImplementedError

    def translate_smt_formula(self, formula: isla.SMTFormula, counter: int) -> TranslationResult:
        z3_formula: z3.BoolRef = formula.formula
        free_isla_vars: OrderedSet[isla.Variable] = formula.free_variables()
        head, isla_to_pl_vars_mapping, free_pl_vars, result_var, all_pl_vars = self.create_head(formula, counter)

        if str(z3_formula.decl()) == "==" and all(is_z3_var(child) or z3.is_string_value(child)
                                                  for child in z3_formula.children()):
            tvar1 = self.fresh_variable("Tree1", all_pl_vars)
            tvar2 = self.fresh_variable("Tree2", all_pl_vars.union([tvar1]))

            vars_in_order = [isla_to_pl_vars_mapping[next(variable for variable in free_isla_vars
                                                          if variable.name == z3_formula.children()[i].as_string())]
                             for i in range(2)]

            goals: List[pl.Goal] = [
                psc.unify(psc.pair(psc.anon_var(), tvar1), vars_in_order[0]),
                psc.unify(psc.pair(psc.anon_var(), tvar2), vars_in_order[1]),
                pl.PredicateApplication(
                    pl.Predicate("equal", 3), [tvar1, tvar2, result_var]
                )
            ]

            return [pl.Rule(head, goals)], []
        else:
            def solve_smt(*atoms: bytes) -> bool:
                instantiation = z3.substitute(
                    z3_formula,
                    *tuple({z3.String(variable.name): z3.StringVal(pyswip_output_to_str(atom)[1:-1])
                            for variable, atom in zip(free_isla_vars, atoms)}.items()))

                z3.set_param("smt.string_solver", "z3str3")
                solver = z3.Solver()
                solver.add(instantiation)
                return solver.check() == z3.sat  # Set timeout?

            vars_var = self.fresh_variable("Vars", all_pl_vars)
            all_pl_vars.add(vars_var)
            goals: List[pl.Goal] = [
                psc.pred("term_variables", pl.ListTerm(free_pl_vars), vars_var),
                psc.pred("label", vars_var)
            ]

            tvars: List[pl.Variable] = []
            strvars: List[pl.Variable] = []
            for variable in free_pl_vars:
                tvar = self.fresh_variable("Tree", free_pl_vars.union([result_var]).union(tvars).union(strvars))
                strvar = self.fresh_variable("StrTree", free_pl_vars.union([result_var]).union(tvars).union(strvars))
                tvars.append(tvar)
                strvars.append(strvar)
                goals.append(psc.unify(psc.pair(psc.anon_var(), tvar), variable))
                goals.append(psc.pred("tree_to_string", tvar, strvar))

            function_name = f"solve_smt_{counter}"
            smt_pred_appl = psc.pred(function_name, *strvars)
            goals.append(psc.disj(psc.conj(psc.clp_eq(result_var, pl.Number(1)), smt_pred_appl),
                                  psc.conj(psc.clp_eq(result_var, pl.Number(0)), smt_pred_appl)))

            return [pl.Rule(head, goals)], [(solve_smt, function_name, len(free_pl_vars))]

    def create_head(self, formula: isla.Formula, counter: int) -> \
            Tuple[
                pl.PredicateApplication,
                Dict[isla.Variable, pl.Variable],  # Mapping from isla to prolog variables
                OrderedSet[pl.Variable],  # Free prolog variables
                pl.Variable,  # The result variable
                OrderedSet[pl.Variable]  # Free prolog variables + result variable
            ]:
        free_isla_vars: OrderedSet[isla.Variable] = formula.free_variables()
        isla_to_pl_vars_mapping: List[Tuple[isla.Variable, pl.Variable]] = \
            [(isla_var, self.isla_to_prolog_var_map[isla_var]) for isla_var in free_isla_vars]
        free_pl_vars = OrderedSet([pl_variable for _, pl_variable in isla_to_pl_vars_mapping])
        all_pl_vars: OrderedSet[pl.Variable] = OrderedSet(free_pl_vars)

        result_var = self.fresh_variable("Result", free_pl_vars)
        all_pl_vars.add(result_var)

        head = pl.PredicateApplication(
            pl.Predicate(f"pred{counter}", len(all_pl_vars)),
            all_pl_vars
        )

        return head, dict(isla_to_pl_vars_mapping), free_pl_vars, result_var, all_pl_vars

    def fresh_variable(self, name_pattern: str, context_vars: OrderedSet[pl.Variable]) -> pl.Variable:
        name = name_pattern
        i = 0
        while any(cvar for cvar in context_vars if cvar.name == name):
            name = f"{name_pattern}_{i}"
            i += 1

        return pl.Variable(name)

    def to_prolog_var(self, variable: Union[str, isla.Variable]) -> pl.Variable:
        result = variable if type(variable) is str else variable.name
        result = re.sub('[^_a-zA-Z0-9]', '', result)

        if result[0] != "_" and not result[0].isupper():
            if result[0].isalpha():
                result = result[0].upper() + result[1:]
            else:
                result = "_" + result

        return pl.Variable(result)

    def translate_grammar(self) -> List[pl.Rule]:
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
        rules: List[pl.Rule] = []
        graph = GrammarGraph.from_grammar(non_canonical(self.grammar))

        for nonterminal, alternatives in [(n, a) for n, a in self.grammar.items()
                                          if n not in self.numeric_nonterminals
                                             and n not in self.atomic_string_nonterminals]:
            nonterminal = nonterminal[1:-1]
            for alternative in alternatives:
                params: List[pl.Term] = []
                variables: Dict[str, str] = {}
                for symbol in alternative:
                    if is_nonterminal(symbol):
                        symbol_type = symbol[1:-1]
                        var_name = symbol_type.capitalize()
                        i = 1
                        while var_name in variables:
                            var_name += f"_{i}"
                        variables[var_name] = symbol_type
                        params.append(pl.Variable(var_name))
                    else:
                        params.append(pl.ListTerm([pl.StringTerm(symbol), pl.ListTerm([])]))

                atom_name = self.predicate_map[nonterminal]
                head = pl.PredicateApplication(
                    pl.Predicate(atom_name, 1),
                    [pl.ListTerm([pl.Atom(atom_name), pl.ListTerm(params)])])

                goals = []
                if variables:
                    # Need to call recursive nonterminals first
                    variables_list = sorted(variables.keys(),
                                            key=lambda n: (
                                                node := graph.get_node(f"<{variables[n]}>"),
                                                chr(0) if node.reachable(node) else n[1:-1])[-1])

                    goals = [pl.PredicateApplication(pl.Predicate(self.predicate_map[variables[variable]], 1),
                                                     [pl.Variable(variable)])
                             for variable in variables_list]

                rules.append(pl.Rule(head, goals))

        for nonterminal in self.numeric_nonterminals:
            nonterminal_name = nonterminal[1:-1]
            c = pl.Variable("C")
            leq = pl.Predicate("#=<", 2, infix=True)

            rules.append(pl.Rule(pl.PredicateApplication(
                pl.Predicate(self.predicate_map[nonterminal_name], 1),
                [pl.ListTerm([pl.Atom(nonterminal_name), pl.ListTerm([pl.ListTerm([c, pl.ListTerm([])])])])]
            ), [
                pl.PredicateApplication(leq, [pl.Number(self.numeric_nonterminals[nonterminal][0]), c]),
                pl.PredicateApplication(leq, [c, pl.Number(self.numeric_nonterminals[nonterminal][1])])
            ]))

        for nonterminal in self.atomic_string_nonterminals:
            nonterminal_name = nonterminal[1:-1]
            c = pl.Variable("C")
            leq = pl.Predicate("#=<", 2, infix=True)

            rules.append(pl.Rule(pl.PredicateApplication(
                pl.Predicate(self.predicate_map[nonterminal_name], 1),
                [pl.ListTerm([pl.Atom(nonterminal_name), pl.ListTerm([pl.ListTerm([c, pl.ListTerm([])])])])]
            ), [
                pl.PredicateApplication(leq, [pl.Number(0), c]),
                pl.PredicateApplication(leq, [c, pl.Number(self.atomic_string_nonterminals[nonterminal])])
            ]))

        return rules

    def compute_atomic_string_nonterminals(self) -> Dict[str, int]:
        assert hasattr(self, "numeric_nonterminals")

        used_nonterminals = OrderedSet([variable.n_type for variable in self.used_variables])

        unused_sink_nonterminals: OrderedSet[str] = OrderedSet([])
        for unused_nonterminal in OrderedSet(self.grammar.keys()) \
                .difference(used_nonterminals).difference(set(self.numeric_nonterminals.keys())):
            graph = GrammarGraph.from_grammar(non_canonical(self.grammar))
            dist = graph.dijkstra(graph.get_node(unused_nonterminal))[0]
            reachable_nonterminals = set([node.symbol for node in dist.keys()
                                          if dist[node] < sys.maxsize
                                          and node.symbol != unused_nonterminal
                                          and type(node) is NonterminalNode])
            if not reachable_nonterminals.intersection(used_nonterminals):
                unused_sink_nonterminals.add(unused_nonterminal)

        non_atomic_variables = OrderedSet([])

        class NonAtomicVisitor(isla.FormulaVisitor):
            def visit_forall_formula(self, formula: isla.ForallFormula):
                non_atomic_variables.add(formula.in_variable)
                if formula.bind_expression is not None:
                    non_atomic_variables.add(formula.bound_variable)

            def visit_exists_formula(self, formula: isla.ExistsFormula):
                non_atomic_variables.add(formula.in_variable)
                if formula.bind_expression is not None:
                    non_atomic_variables.add(formula.bound_variable)

            def visit_smt_formula(self, formula: isla.SMTFormula):
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
                for nonterminal in used_nonterminals
                    .difference(non_atomic_nonterminals)
                    .union(unused_sink_nonterminals)}

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
            while self.predicate_defined(curr_name, 1):
                curr_name = f"{nonterminal}_{idx}"
                idx += 1

            predicate_map[nonterminal] = curr_name

        return predicate_map

    def predicate_defined(self, name: str, arity: int):
        prolog = Prolog()
        return len(list(prolog.query(f"current_predicate({name}/{arity})"))) > 0
