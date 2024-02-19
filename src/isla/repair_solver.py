import itertools
import logging
import operator
import random
import sys
import time
from functools import reduce, lru_cache
from typing import (
    FrozenSet,
    Tuple,
    cast,
    Dict,
    Iterator,
    Mapping,
    Optional,
    Sequence,
    List,
    Set,
    Iterable,
    Callable,
)

import grammar_graph.gg as gg
import z3
from frozendict import frozendict
from grammar_to_regex.cfg2regex import RegexConverter
from grammar_to_regex.regex import regex_to_z3
from orderedset import FrozenOrderedSet
from returns.converters import result_to_maybe
from returns.curry import partial
from returns.functions import tap
from returns.maybe import Maybe, Nothing, Some
from returns.pipeline import flow
from returns.pipeline import is_successful
from returns.pointfree import map_
from returns.result import safe
from typeguard import typechecked

from isla.derivation_tree import DerivationTree
from isla.evaluator import matches_for_quantified_formula, evaluate
from isla.fuzzer import GrammarCoverageFuzzer
from isla.helpers import deep_str, depth_indent, star, lazystr, eassert, sum_of_maybes
from isla.helpers import (
    frozen_canonical,
    is_nonterminal,
    grammar_to_frozen,
    lazyjoin,
    cluster_by_common_elements,
    get_elem_by_equivalence,
    merge_dict_of_sets,
    get_expansions,
    compute_nullable_nonterminals,
    delete_unreachable,
    grammar_to_unfrozen,
)
from isla.isla_predicates import STANDARD_STRUCTURAL_PREDICATES
from isla.isla_shortcuts import disjunction, conjunction
from isla.language import (
    set_smt_auto_eval,
    Formula,
    QuantifiedFormula,
    PropositionalCombinator,
    ForallFormula,
    replace_formula,
    ExistsFormula,
    FilterVisitor,
    Variable,
    StructuralPredicateFormula,
    SMTFormula,
    true,
    BoundVariable,
    convert_to_nnf,
    VariablesCollector,
    Constant,
    parse_isla,
    ensure_unique_bound_variables,
    set_smt_auto_subst,
    FormulaVisitor,
    fresh_constant,
    false,
    parse_bnf,
    validate_structural_predicate_arguments,
    fresh_bound_variable,
    validate_smt_formula_substitutions,
    to_dnf_clauses,
)
from isla.parser import EarleyParser, PEGParser
from isla.tree_insertion import insert_tree
from isla.type_defs import FrozenGrammar, Path, Grammar, FrozenCanonicalGrammar
from isla.z3_helpers import (
    z3_subst,
    visit_z3_expr,
    numeric_intervals_from_regex,
    z3_or,
    z3_solve,
    parent_relationships_in_z3_expr,
    smt_string_val_to_string,
    z3_eq,
    z3_concat,
)

LOGGER = logging.getLogger(__name__)

ExtractModelValueFallbackType = Callable[
    [
        Variable,
        z3.ModelRef,
        Mapping[Variable, z3.ExprRef],
        Set[Variable],
        Set[Variable],
    ],
    Maybe[DerivationTree],
]


def compute_bound_tree_paths(
    tree: DerivationTree, smt_constraints: Iterable[SMTFormula]
) -> frozendict[Path, Variable]:
    """
    TODO: Document.

    :param tree:
    :param smt_constraints:
    :return:
    """

    assert all(
        tree.find_node(subtree) is not None
        for smt_formula in smt_constraints
        for subtree in smt_formula.substitutions.values()
    )

    return frozendict(
        (tree.find_node(subtree), variable)
        for smt_formula in smt_constraints
        for variable, subtree in smt_formula.substitutions.items()
    )


def describe_subtree_structure(
    current_node: DerivationTree,
    bound_tree_paths: frozendict[Path, Variable],
    current_path: Path = (),
    first_call: bool = True,
    fresh_vars: frozendict[Variable, str] = frozendict({}),
) -> Tuple[frozendict[Variable, str], Tuple[Variable | str, ...]]:
    r"""
    TODO: Document.

    Example
    -------

    >>> simplified_xml_grammar = '''
    ...     <start> ::= <xml-tree>
    ...     <xml-tree> ::= "" | <xml-open-tag> <xml-tree> <xml-close-tag>
    ...     <xml-open-tag> ::= "<" <tag-id> <attrs> ">"
    ...     <xml-close-tag> ::= "</" <tag-id> ">"
    ...     <attrs> ::= "" | " " <attr> <attrs>
    ...     <attr> ::= <attr-id> "=\\"XXX\\""
    ...     <tag-id> ::= <letter-no-x> ":" <letter>
    ...     <attr-id> ::= <letter> ":" <letter>
    ...     <letter> ::= "a" | "b" | "c" | "x"
    ...     <letter-no-x> ::= "a" | "b" | "c"
    ... '''

    >>> solver = RepairSolver(simplified_xml_grammar)
    >>> prefix_def_0_path = (0, 0, 2, 1, 0, 2)
    >>> tree: DerivationTree = (
    ...     solver.parse('<b:x x:c="XXX"></a:x>')
    ...     .unwrap()
    ...     .replace_path(prefix_def_0_path, DerivationTree("<letter>", None))
    ... )

    >>> print(tree)
    <b:x x:<letter>="XXX"></a:x>

    >>> prefix_def_0 = BoundVariable("prefix_def_0", "<letter>")
    >>> prefix_use_1 = BoundVariable("prefix_use_1", "<letter_no_x>")
    >>> prefix_use_1_path = (0, 0, 1, 0)
    >>> opid = BoundVariable("opid", "<tag-id>")
    >>> opid_path = (0, 0, 1)
    >>> clid = BoundVariable("clid", "<tag-id>")
    >>> clid_path = (0, 2, 2)

    >>> smt_constraint_1 = SMTFormula(
    ...     z3_eq(prefix_use_1.to_smt(), prefix_def_0.to_smt()),
    ...     prefix_use_1,
    ...     prefix_def_0,
    ...     auto_eval=False,
    ...     auto_subst=False,
    ... ).substitute_expressions(
    ...     {
    ...         prefix_use_1: tree.get_subtree(prefix_use_1_path),
    ...         prefix_def_0: tree.get_subtree(prefix_def_0_path),
    ...     }
    ... )

    >>> print(smt_constraint_1)
    (prefix_use_1 == prefix_def_0, {'prefix_use_1': 'b', 'prefix_def_0': '<letter>'})

    >>> smt_constraint_2 = SMTFormula(
    ...     z3_eq(opid.to_smt(), clid.to_smt()),
    ...     opid,
    ...     clid,
    ...     auto_eval=False,
    ...     auto_subst=False,
    ... ).substitute_expressions(
    ...     {
    ...         opid: tree.get_subtree(opid_path),
    ...         clid: tree.get_subtree(clid_path),
    ...     }
    ... )

    >>> print(smt_constraint_2)
    (opid == clid, {'opid': 'b:x', 'clid': 'a:x'})

    >>> bound_tree_paths = compute_bound_tree_paths(
    ...     tree, (smt_constraint_1, smt_constraint_2)
    ... )

    >>> print(deep_str(bound_tree_paths))
    {(0, 0, 1, 0): prefix_use_1, (0, 0, 2, 1, 0, 2): prefix_def_0, (0, 0, 1): opid, (0, 2, 2): clid}

    The interesting case of the output below is the structure of "opid."
    Observe how the last element of the returned tuple is a fresh variable
    :code:`letter` that is introduced to generalize the structure of the
    substitution. The original value of the subtree represented by this
    variable ("x") is also returned.

    >>> print(
    ...     "\n".join(
    ...         map(
    ...             deep_str,
    ...             (
    ...                 (
    ...                     var,
    ...                     describe_subtree_structure(
    ...                         tree.get_subtree(path), bound_tree_paths, current_path=path
    ...                     ),
    ...                 )
    ...                 for path, var in bound_tree_paths.items()
    ...             ),
    ...         )
    ...     )
    ... )
    (prefix_use_1, ({}, ('b',)))
    (prefix_def_0, ({}, ()))
    (opid, ({letter: 'x'}, (prefix_use_1, ':', letter)))
    (clid, ({}, ('a:x',)))

    :param current_node:
    :param bound_tree_paths:
    :param current_path:
    :param first_call:
    :param fresh_vars:
    :return:
    """

    if current_path in bound_tree_paths:
        if first_call and not current_node.children:
            return fresh_vars, ()
        if not first_call:
            return fresh_vars, (bound_tree_paths[current_path],)

    if all(
        path[: len(current_path)] != current_path
        for path in bound_tree_paths
        if len(path) > len(current_path)
    ):
        if is_nonterminal(current_node.value) and not first_call:
            fresh_var = fresh_bound_variable(
                FrozenOrderedSet(fresh_vars.keys())
                | FrozenOrderedSet(bound_tree_paths.values()),
                BoundVariable(current_node.value[1:-1], current_node.value),
                add=False,
            )

            return fresh_vars.set(fresh_var, str(current_node)), (fresh_var,)

        return fresh_vars, (str(current_node),)

    resulting_structures = ()
    for i, child in enumerate(current_node.children):
        new_fresh_vars, sub_result = describe_subtree_structure(
            child,
            bound_tree_paths,
            current_path + (i,),
            first_call=False,
            fresh_vars=fresh_vars,
        )

        fresh_vars = frozendict(fresh_vars | new_fresh_vars)
        resulting_structures += sub_result

    return fresh_vars, resulting_structures


def value_suggestion_constraints(
    tree: DerivationTree,
    smt_constraints: Iterable[SMTFormula],
) -> Tuple[FrozenOrderedSet[Variable], Tuple[z3.BoolRef, ...], Tuple[z3.BoolRef, ...]]:
    r"""
    This function extracts constraints describing the values and structures of
    the tree substitutions in the given SMT constraints. It returns a triple of

    1. A set of fresh variables use to generalize the structural constraints.
    2. A sequence of "value constraints" describing precise string values for
       substitution elements that are independent of the values of other
       substitutions.
    3. A sequence of "structural" constraints describing the structure of
       substitutions that depend on other substitutions in terms of these
       other substitutions and string literals. To facilitate an as general
       usage of this class of constraints as possible, the structural
       constraints can contain fresh variables whose values are constrained
       by formulas returned as part of the value constraints.

    Example
    -------

    Consider the following simplificed XML grammar with namespaces that are
    declared by attributes prefixed with :code:`x:`:

    >>> simplified_xml_grammar = '''
    ...     <start> ::= <xml-tree>
    ...     <xml-tree> ::= "" | <xml-open-tag> <xml-tree> <xml-close-tag>
    ...     <xml-open-tag> ::= "<" <tag-id> <attrs> ">"
    ...     <xml-close-tag> ::= "</" <tag-id> ">"
    ...     <attrs> ::= "" | " " <attr> <attrs>
    ...     <attr> ::= <attr-id> "=\\"XXX\\""
    ...     <tag-id> ::= <letter-no-x> ":" <letter>
    ...     <attr-id> ::= <letter> ":" <letter>
    ...     <letter> ::= "a" | "b" | "c" | "x"
    ...     <letter-no-x> ::= "a" | "b" | "c"
    ... '''

    Our reference tree will be :code:`<b:x x:<letter>="XXX"></a:x>`.

    >>> solver = RepairSolver(simplified_xml_grammar)
    >>> prefix_def_0_path = (0, 0, 2, 1, 0, 2)
    >>> tree: DerivationTree = (
    ...     solver.parse('<b:x x:c="XXX"></a:x>')
    ...     .unwrap()
    ...     .replace_path(prefix_def_0_path, DerivationTree("<letter>", None))
    ... )

    >>> print(tree)
    <b:x x:<letter>="XXX"></a:x>

    We declare two constraints: The first one, :code:`prefix_use_1 == prefix_def_0`
    stipulates that :code:`letter` equals :code:`b`. The second one,
    :code:`opid == clid` stipulates that the tag IDs of the opening and closing
    tags, currently :code:`b:x` and :code:`a:x`, are equal. The important part is
    that these constraints are not independent: The value of :code:`opid` depends
    on the value of :code:`prefix_use_1`. This dependency is a "structural constraint."

    >>> prefix_def_0 = BoundVariable("prefix_def_0", "<letter>")
    >>> prefix_use_1 = BoundVariable("prefix_use_1", "<letter_no_x>")
    >>> prefix_use_1_path = (0, 0, 1, 0)
    >>> opid = BoundVariable("opid", "<tag-id>")
    >>> opid_path = (0, 0, 1)
    >>> clid = BoundVariable("clid", "<tag-id>")
    >>> clid_path = (0, 2, 2)

    >>> smt_constraint_1 = SMTFormula(
    ...     z3_eq(prefix_use_1.to_smt(), prefix_def_0.to_smt()),
    ...     prefix_use_1,
    ...     prefix_def_0,
    ...     auto_eval=False,
    ...     auto_subst=False,
    ... ).substitute_expressions(
    ...     {
    ...         prefix_use_1: tree.get_subtree(prefix_use_1_path),
    ...         prefix_def_0: tree.get_subtree(prefix_def_0_path),
    ...     }
    ... )

    >>> print(smt_constraint_1)
    (prefix_use_1 == prefix_def_0, {'prefix_use_1': 'b', 'prefix_def_0': '<letter>'})

    >>> smt_constraint_2 = SMTFormula(
    ...     z3_eq(opid.to_smt(), clid.to_smt()),
    ...     opid,
    ...     clid,
    ...     auto_eval=False,
    ...     auto_subst=False,
    ... ).substitute_expressions(
    ...     {
    ...         opid: tree.get_subtree(opid_path),
    ...         clid: tree.get_subtree(clid_path),
    ...     }
    ... )

    >>> print(smt_constraint_2)
    (opid == clid, {'opid': 'b:x', 'clid': 'a:x'})

    >>> (
    ...     fresh_variables,
    ...     literal_constraints,
    ...     structural_constraints,
    ... ) = value_suggestion_constraints(tree, (smt_constraint_1, smt_constraint_2))

    We obtain two value constraints for :code:`prefix_use_1` and :code:`clid`,
    and one structural constraint for :code:`opid` and :code:`prefix_use_1`:

    >>> print(deep_str(fresh_variables))
    {letter}

    >>> print(deep_str(literal_constraints))
    (prefix_use_1 == "b", letter == "x", clid == "a:x")

    >>> print(deep_str(structural_constraints))
    (opid == Concat(prefix_use_1, Concat(":", letter)),)

    In constraint solving, the structural constraint should be given a higher
    priority than the value constraints.

    :param tree: The reference tree for the SMT constraints' substitutions.
    :param smt_constraints: The SMT constraints to extract value suggestions
        from.
    :return: A triple of a set of fresh variables, a sequence of value
        constraints, and a sequence of structural constraints.
    """

    (
        fresh_variables,
        structural_values,
        literal_values,
    ) = shape_relations_from_smt_constraints(tree, smt_constraints)

    value_constraints = tuple(
        z3_eq(var.to_smt(), z3.StringVal(value))
        for var, value in literal_values.items()
    )

    structural_constraints = tuple(
        z3_eq(
            var.to_smt(),
            z3_concat(
                tuple(
                    z3.StringVal(elem) if isinstance(elem, str) else elem.to_smt()
                    for elem in structure
                )
            ),
        )
        for var, structure in structural_values.items()
    )

    return fresh_variables, value_constraints, structural_constraints


def shape_relations_from_smt_constraints(
    tree: DerivationTree,
    smt_constraints: Iterable[SMTFormula],
    initial_fresh_variables: FrozenOrderedSet[Variable] = FrozenOrderedSet(),
) -> Tuple[
    FrozenOrderedSet[Variable],
    frozendict[Variable, Tuple[str | Variable, ...]],
    frozendict[Variable, str],
]:
    r"""
    This function extracts values and structures from the tree substitutions
    in the given SMT constraints. It returns a triple of

    1. A set of fresh variables use to generalize the structural constraints.
    2. A dictionary of "structural" relations describing the structure of
       substitutions that depend on other substitutions in terms of these
       other substitutions and string literals. To facilitate an as general
       usage of this class of constraints as possible, the structural
       constraints can contain fresh variables whose values appear in the
       "value relations."
    3. A sequence of "value" relations describing precise string values for
       substitution elements that are independent of the values of other
       substitutions.

    Example
    -------

    Consider the following simplificed XML grammar with namespaces that are
    declared by attributes prefixed with :code:`x:`:

    >>> simplified_xml_grammar = '''
    ...     <start> ::= <xml-tree>
    ...     <xml-tree> ::= "" | <xml-open-tag> <xml-tree> <xml-close-tag>
    ...     <xml-open-tag> ::= "<" <tag-id> <attrs> ">"
    ...     <xml-close-tag> ::= "</" <tag-id> ">"
    ...     <attrs> ::= "" | " " <attr> <attrs>
    ...     <attr> ::= <attr-id> "=\\"XXX\\""
    ...     <tag-id> ::= <letter-no-x> ":" <letter>
    ...     <attr-id> ::= <letter> ":" <letter>
    ...     <letter> ::= "a" | "b" | "c" | "x"
    ...     <letter-no-x> ::= "a" | "b" | "c"
    ... '''

    Our reference tree will be :code:`<b:x x:<letter>="XXX"></a:x>`.

    >>> solver = RepairSolver(simplified_xml_grammar)
    >>> prefix_def_0_path = (0, 0, 2, 1, 0, 2)
    >>> tree: DerivationTree = (
    ...     solver.parse('<b:x x:c="XXX"></a:x>')
    ...     .unwrap()
    ...     .replace_path(prefix_def_0_path, DerivationTree("<letter>", None))
    ... )

    >>> print(tree)
    <b:x x:<letter>="XXX"></a:x>

    We declare two constraints: The first one, :code:`prefix_use_1 == prefix_def_0`
    stipulates that :code:`letter` equals :code:`b`. The second one,
    :code:`opid == clid` stipulates that the tag IDs of the opening and closing
    tags, currently :code:`b:x` and :code:`a:x`, are equal. The important part is
    that these constraints are not independent: The value of :code:`opid` depends
    on the value of :code:`prefix_use_1`. This dependency is a "structural relation."

    >>> prefix_def_0 = BoundVariable("prefix_def_0", "<letter>")
    >>> prefix_use_1 = BoundVariable("prefix_use_1", "<letter_no_x>")
    >>> prefix_use_1_path = (0, 0, 1, 0)
    >>> opid = BoundVariable("opid", "<tag-id>")
    >>> opid_path = (0, 0, 1)
    >>> clid = BoundVariable("clid", "<tag-id>")
    >>> clid_path = (0, 2, 2)

    >>> smt_constraint_1 = SMTFormula(
    ...     z3_eq(prefix_use_1.to_smt(), prefix_def_0.to_smt()),
    ...     prefix_use_1,
    ...     prefix_def_0,
    ...     auto_eval=False,
    ...     auto_subst=False,
    ... ).substitute_expressions(
    ...     {
    ...         prefix_use_1: tree.get_subtree(prefix_use_1_path),
    ...         prefix_def_0: tree.get_subtree(prefix_def_0_path),
    ...     }
    ... )

    >>> print(smt_constraint_1)
    (prefix_use_1 == prefix_def_0, {'prefix_use_1': 'b', 'prefix_def_0': '<letter>'})

    >>> smt_constraint_2 = SMTFormula(
    ...     z3_eq(opid.to_smt(), clid.to_smt()),
    ...     opid,
    ...     clid,
    ...     auto_eval=False,
    ...     auto_subst=False,
    ... ).substitute_expressions(
    ...     {
    ...         opid: tree.get_subtree(opid_path),
    ...         clid: tree.get_subtree(clid_path),
    ...     }
    ... )

    >>> print(smt_constraint_2)
    (opid == clid, {'opid': 'b:x', 'clid': 'a:x'})

    >>> (
    ...     fresh_variables,
    ...     structural_values,
    ...     literal_values,
    ... ) = shape_relations_from_smt_constraints(tree, (smt_constraint_1, smt_constraint_2))

    We obtain two value relations for :code:`prefix_use_1` and :code:`clid`,
    and one structural relation for :code:`opid` and :code:`prefix_use_1`:

    >>> print(deep_str(fresh_variables))
    {letter}

    >>> print(deep_str(literal_values))
    {prefix_use_1: 'b', letter: 'x', clid: 'a:x'}

    >>> print(deep_str(structural_values))
    {opid: (prefix_use_1, ':', letter)}

    In constraint solving, the structural relation should be given a higher
    priority than the value relations.

    :param tree: The reference tree for the SMT constraints' substitutions.
    :param smt_constraints: The SMT constraints to extract value suggestions
        from.
    :param initial_fresh_variables: A dictionary of variables that will not be chosen
        as fresh variables.
    :return: A triple of a set of fresh variables, a sequence of structural
        relations, and a sequence of value relations.
    """

    bound_tree_paths = compute_bound_tree_paths(tree, smt_constraints)

    fresh_variables: frozendict[Variable, str] = frozendict(
        {var: "" for var in initial_fresh_variables}
    )
    structural_values: frozendict[Variable, Tuple[str | Variable, ...]] = frozendict({})
    literal_values: frozendict[Variable, str] = frozendict({})

    for path, var in bound_tree_paths.items():
        new_fresh_vars, structure = describe_subtree_structure(
            tree.get_subtree(path),
            bound_tree_paths,
            current_path=path,
            fresh_vars=fresh_variables,
        )

        assert structure or new_fresh_vars == fresh_variables
        if not structure:
            continue

        if initial_fresh_variables:
            new_fresh_vars = frozendict(
                {
                    var: val
                    for var, val in new_fresh_vars.items()
                    if var not in initial_fresh_variables
                }
            )

        fresh_variables = frozendict(fresh_variables | new_fresh_vars)

        if any(isinstance(elem, Variable) for elem in structure):
            structural_values = structural_values.set(var, structure)
            literal_values = frozendict(literal_values | new_fresh_vars)
        else:
            assert len(structure) == 1
            literal_values = literal_values.set(var, structure[0])

    return (
        FrozenOrderedSet(fresh_variables.keys()).difference(initial_fresh_variables),
        structural_values,
        literal_values,
    )


@typechecked
def extract_top_level_quantified_formulas(
    formula: Formula,
) -> FrozenOrderedSet[QuantifiedFormula]:
    """
    Returns all top-level quantified formulas in the given formula.

    :param formula: The formula to search in.
    :return: A tuple of all top-level quantified formulas.
    """

    if isinstance(formula, QuantifiedFormula):
        return FrozenOrderedSet({formula})

    if isinstance(formula, PropositionalCombinator):
        return FrozenOrderedSet(
            {
                f
                for arg in formula.args
                for f in extract_top_level_quantified_formulas(arg)
            }
        )

    return FrozenOrderedSet()


@typechecked
def set_auto_subst_and_eval(formula: Formula, value: bool) -> Formula:
    set_smt_auto_eval(formula, value)
    set_smt_auto_subst(formula, value)
    return formula


@typechecked
def evaluate_structural_predicates(
    constraint: Formula, context_tree: DerivationTree
) -> Formula:
    predicate_formula: StructuralPredicateFormula
    for predicate_formula in FilterVisitor(
        lambda f: (
            isinstance(f, StructuralPredicateFormula)
            and all(not isinstance(arg, Variable) for arg in f.args)
        )
    ).collect(constraint):
        instantiation = SMTFormula(z3.BoolVal(predicate_formula.evaluate(context_tree)))
        constraint = replace_formula(constraint, predicate_formula, instantiation)

    return constraint


class RepairSolver:
    @typechecked
    def __init__(
        self,
        grammar: FrozenGrammar | Grammar | str,
        maybe_constraint: Optional[Formula | str] = None,
        structural_predicates=frozenset(STANDARD_STRUCTURAL_PREDICATES),
        max_tries_existential_insertion: int = 4,
        enable_optimized_z3_queries: bool = True,
        timeout_seconds: Optional[int] = None,
    ):
        """
        An ISLa solver based on semantic repair of syntactically correct solutions.
        Its main methods are :meth:`~isla.repair_solver.RepairSolver.repair_tree`,
        :meth:`~isla.repair_solver.RepairSolver.solve`, and
        :meth:`~isla.repair_solver.RepairSolver.parse`.

        :param grammar: The grammar defining the syntactic constraints of the
            solutions to be produced.
        :param maybe_constraint: An optional constraint specifying the semantic
            restrictions of the solutions to be produced. It can be a string
            representing a formula in ISLa's syntax, a formula object, or None.
        :param structural_predicates: A set of structural predicates to be used
            when parsing the optional constraint if it is a string. This parameter
            is not required if no constraint is given, the constraint is a formula
            object, or it uses only standard structural predicates.
        :param max_tries_existential_insertion: The number of different insertions
            that are tried as solutions of an existential quantifier before giving
            up the repair process.
        :param enable_optimized_z3_queries: If true, SMT formulas are preprocessed
            before passing them to the SMT solver. This affects formulas with
            variables solely occurring in :code:`str.to.int` or :code:`str.len`
            contexts.
        :param timeout_seconds: The timeout in seconds for this solver. The solver's iterator
            will stop producing solutions after this time has passed, counting from
            the first :meth:`~isla.repair_solver.RepairSolver.solve` call.
        """

        self.enable_optimized_z3_queries: bool = enable_optimized_z3_queries
        self.max_tries_existential_insertion: int = max_tries_existential_insertion
        self.grammar_unwinding_threshold: int = 4

        self.grammar = grammar_to_frozen(
            parse_bnf(grammar) if isinstance(grammar, str) else grammar
        )
        self.canonical_grammar = frozen_canonical(self.grammar)
        self.graph = gg.GrammarGraph.from_grammar(self.grammar)
        self.solve_iterator = self.make_solve_iterator()
        self.fuzzer = GrammarCoverageFuzzer(self.grammar)

        self.constraint = (
            Maybe.from_optional(maybe_constraint)
            .map(
                lambda c: (
                    parse_isla(c, self.grammar, structural_predicates)
                    if isinstance(c, str)
                    else c
                )
            )
            .map(ensure_unique_bound_variables)
            .value_or(true())
        )

        top_constants = {
            c
            for c in VariablesCollector.collect(self.constraint)
            if isinstance(c, Constant) and not c.is_numeric()
        }

        assert len(top_constants) <= 1, (
            "ISLa only accepts up to one constant (free variable), "
            + f'found {len(top_constants)}: {", ".join(map(str, top_constants))}'
        )

        self.top_constant = Maybe.from_optional(next(iter(top_constants), None))

        self.timeout_seconds = timeout_seconds
        self.end_time: Optional[int] = None

    @safe
    @typechecked
    def parse(
        self,
        inp: str,
        nonterminal: str = "<start>",
        silent: bool = False,
    ) -> DerivationTree:
        """
        Parses the given input `inp`. Raises a `SyntaxError` if the input does not
        satisfy the grammar, and returns the parsed `DerivationTree` otherwise.

        :param inp: The input to parse.
        :param nonterminal: The nonterminal to start parsing with, if a string
          corresponding to a sub-grammar shall be parsed. We don't check semantic
          correctness in that case.
        :param silent: If True, no error is sent to the log stream in case of a
            failed parse.
        :return: A parsed `DerivationTree`.
        """

        grammar = self.grammar
        if nonterminal != "<start>":
            grammar = grammar.set("<start>", (nonterminal,))
            grammar = delete_unreachable(grammar)

        peg_parser = PEGParser(grammar)
        try:
            parse_tree = next(iter(peg_parser.parse(inp)))
            if nonterminal != "<start>":
                parse_tree = parse_tree[1][0]
        except SyntaxError as peg_err:
            if not silent:
                LOGGER.info(
                    f'PEGParser: Error parsing "{inp}" starting with "{nonterminal}":\n{peg_err}'
                )

            earley_parser = EarleyParser(grammar)
            try:
                parse_tree = next(earley_parser.parse(inp))
                if nonterminal != "<start>":
                    parse_tree = parse_tree[1][0]
            except SyntaxError as earley_err:
                if not silent:
                    LOGGER.error(
                        f'Error parsing "{inp}" starting with "{nonterminal}":\n{earley_err}'
                    )
                raise earley_err

        return DerivationTree.from_parse_tree(parse_tree)

    @typechecked
    def solve(self) -> DerivationTree:
        return next(self.solve_iterator)

    def init_end_time(self) -> None:
        if self.timeout_seconds is not None and self.end_time is None:
            self.end_time = time.time() + self.timeout_seconds

    def end_time_passed(self) -> bool:
        if self.end_time is None:
            return False

        return time.time() > self.end_time

    @typechecked
    def make_solve_iterator(self) -> Iterator[DerivationTree]:
        self.init_end_time()

        while True:
            if self.end_time_passed():
                return

            tree = self.fuzzer.fuzz_tree()

            maybe_repaired = self.repair_tree(
                self.instantiate_top_constant(tree),
                tree,
            )

            if is_successful(maybe_repaired):
                yield maybe_repaired.unwrap()

    @typechecked
    def instantiate_top_constant(self, tree: DerivationTree) -> Formula:
        return self.top_constant.map(
            lambda c: self.constraint.substitute_expressions({c: tree})
        ).value_or(self.constraint)

    @typechecked
    def repair_tree(
        self,
        constraint: Formula | Iterable[Formula],
        tree: DerivationTree,
    ) -> Maybe[DerivationTree]:
        if self.end_time_passed():
            return Nothing

        if not isinstance(constraint, Formula):
            constraint = conjunction(*constraint)

        LOGGER.debug(
            "%sRepairing tree '%s' with constraint '%s'",
            depth_indent(),
            tree,
            constraint,
        )
        constraint = set_auto_subst_and_eval(constraint, False)

        # 1. Instantiate all quantifiers.
        instantiated = self.instantiate_quantifiers(constraint)
        assert auto_subst_and_eval_is_false(instantiated)

        # 2. Evaluate all structural predicates.
        no_structural_predicates = evaluate_structural_predicates(instantiated, tree)
        if no_structural_predicates == false():
            # This can happen for unsatisfied structural predicates in a conjunction;
            # backtrack or fail.
            return Nothing

        # 3. Replace all valid SMT expressions with `true` (considering the
        #    negation scope); convert to DNF (in clause form).
        no_true_semantic_formulas: Tuple[Tuple[Formula, ...], ...] = to_dnf_clauses(
            self.eliminate_true_semantic_formulas(
                convert_to_nnf(no_structural_predicates), tree
            ),
        )

        # 4a. If the formula is a disjunction, recursively try to satisfy each disjunct.
        #     Return the first successfully repaired tree, or Nothing.
        if len(no_true_semantic_formulas) > 1:
            # TODO: Should we shuffle the disjuncts? Problem: We want to first address
            #       the instantiations *matching* an existential quantifier, and only
            #       later those where the quantifier is retained. In the original order,
            #       this property is retained; *naive* shuffling could destroy it.
            # TODO: Should we add a depth bound (e.g., based on the number of times an
            #       existential formula was solved by insertion) to avoid infinite loops?
            #       This is particularly critical if we add shuffling.
            # TODO: Make repair produce a *stream* of repaired trees.

            # To optimize the search, we first try to repair the disjuncts that
            # are most likely to be satisfiable. We estimate this by calculating
            # the proportion of unsatisfied conjuncts in each disjunct.

            return flow(
                no_true_semantic_formulas,
                partial(
                    map,
                    lambda conjuncts: self.repair_tree(
                        conjuncts,
                        tree,
                    ),
                ),
                lambda maybe_repaired_trees: next(
                    (
                        maybe_repaired_tree
                        for maybe_repaired_tree in maybe_repaired_trees
                        if is_successful(maybe_repaired_tree)
                    ),
                    Nothing,
                ),
                map_(tap(lambda t: isinstance(t, DerivationTree))),
            )

        assert len(no_true_semantic_formulas) == 1
        conjuncts = no_true_semantic_formulas[0]
        validate_structural_predicate_arguments(conjuncts, tree)
        validate_smt_formula_substitutions(conjuncts, tree)

        if not any(isinstance(c, ExistsFormula) for c in conjuncts):
            # 4c. If the formula is a single semantic formula or a conjunction of
            #     semantic formulas, repair all semantic formulas by making all
            #     constrained tree elements abstract and asking for a solution.
            #     If a solution exists, return the repaired tree. Otherwise,
            #     return Nothing.

            assert all(
                tree.find_node(subtree) is not None
                for smt_formula in conjuncts
                if isinstance(smt_formula, SMTFormula)
                for subtree in smt_formula.substitutions.values()
            )

            return self.repair_semantic_formulas(conjuncts, tree)

        return flow(
            self.eliminate_first_existential_formula(conjuncts, tree),
            partial(map, star(self.repair_tree)),
            partial(filter, is_successful),
            lambda maybe_repaired_trees: next(maybe_repaired_trees, Nothing),
        )

    def repair_semantic_formulas(
        self, conjuncts: Tuple[SMTFormula | ForallFormula, ...], tree: DerivationTree
    ) -> Maybe[DerivationTree]:
        """
        TODO: Document, test.

        :param conjuncts:
        :param tree:
        :return:
        """

        assert all(
            isinstance(conjunct, SMTFormula) or isinstance(conjunct, ForallFormula)
            for conjunct in conjuncts
        )

        smt_conjuncts = tuple(
            conjunct for conjunct in conjuncts if isinstance(conjunct, SMTFormula)
        )

        if not smt_conjuncts:
            # No SMT formulas => We can finish the tree by grammar fuzzing.
            # However, we must evaluate whether the such closed trees satisfy
            # the constraints.
            return self.try_to_finish(tree, conjunction(*conjuncts))

        def apply_smt_substitutions(
            substs: Mapping[DerivationTree, DerivationTree]
        ) -> Maybe[DerivationTree]:
            non_smt_formula = conjunction(
                *(c for c in conjuncts if not isinstance(c, SMTFormula))
            )

            if substs:
                return self.repair_tree(
                    non_smt_formula.substitute_expressions(substs),
                    tree.substitute(substs),
                )

            # No substitutions => We can finish the tree by grammar fuzzing.
            # However, we must evaluate whether the such closed trees satisfy
            # the constraints.
            return self.try_to_finish(tree, non_smt_formula)

        def log_solution(s: Mapping[DerivationTree, DerivationTree]):
            LOGGER.debug("SMT solution found: %s", lazystr(lambda: deep_str(s)))

        def log_no_solution(_: Nothing) -> Nothing:
            LOGGER.debug("No SMT solution found")
            return Nothing

        return (
            self.eliminate_all_semantic_formulas(smt_conjuncts, tree)
            .map(tap(log_solution))
            .lash(log_no_solution)
            .bind(apply_smt_substitutions)
        )

    def eliminate_first_existential_formula(
        self, conjuncts: Tuple[Formula, ...], tree: DerivationTree
    ) -> Iterator[Tuple[Tuple[Formula, ...], DerivationTree]]:
        r"""
        TODO

        >>> import string
        >>> grammar = frozendict({
        ...     "<start>": ("<stmt>",),
        ...     "<stmt>": ("<assgn> ; <stmt>", "<assgn>"),
        ...     "<assgn>": ("<var> := <rhs>",),
        ...     "<rhs>": ("<var>", "<digit>"),
        ...     "<var>": tuple(string.ascii_lowercase),
        ...     "<digit>": tuple(string.digits)
        ... })

        >>> solver = RepairSolver(grammar, max_tries_existential_insertion=3)
        >>> tree = solver.parse("a := 1 ; b := 2 ; c := 3").unwrap()

        >>> constraint_1 = parse_isla('exists <var> in start: <var> = "x"', grammar)
        >>> constraint_1 = constraint_1.substitute_expressions({constraint_1.in_variable: tree})

        >>> constraint_2 = parse_isla('exists <digit> in start: <digit> = "1"', grammar)
        >>> constraint_2 = constraint_2.substitute_expressions({constraint_2.in_variable: tree})

        >>> from isla.language import unparse_isla
        >>> def conjuncts_tree_pair_to_str(conjuncts, tree):
        ...     return (
        ...         f"{', '.join(unparse_isla(c).replace(chr(10), '') for c in conjuncts)} |- {tree}"
        ...     )

        >>> ten_solutions = tuple(itertools.islice(
        ...     solver.eliminate_first_existential_formula(
        ...         (constraint_1, constraint_2), tree
        ...     ),
        ...     10,
        ... ))

        >>> print("\n".join(map(star(conjuncts_tree_pair_to_str), ten_solutions)))
        (= var "x"), exists <digit> digit in <var> := <rhs> ; a := 1 ; b := 2 ; c := 3:  (= digit "1") |- <var> := <rhs> ; a := 1 ; b := 2 ; c := 3
        (= var "x"), exists <digit> digit in <var> := <var> ; a := 1 ; b := 2 ; c := 3:  (= digit "1") |- <var> := <var> ; a := 1 ; b := 2 ; c := 3
        (= var "x"), exists <digit> digit in a := 1 ; <var> := <rhs> ; b := 2 ; c := 3:  (= digit "1") |- a := 1 ; <var> := <rhs> ; b := 2 ; c := 3
        (= var "x"), exists <digit> digit in a := 1 ; <var> := <var> ; b := 2 ; c := 3:  (= digit "1") |- a := 1 ; <var> := <var> ; b := 2 ; c := 3
        (= var "x"), exists <digit> digit in a := 1 ; b := 2 ; <var> := <rhs> ; c := 3:  (= digit "1") |- a := 1 ; b := 2 ; <var> := <rhs> ; c := 3
        (= var "x"), exists <digit> digit in a := 1 ; b := 2 ; <var> := <var> ; c := 3:  (= digit "1") |- a := 1 ; b := 2 ; <var> := <var> ; c := 3

        >>> ten_subsequent_solutions = tuple(
        ...     (c, t)
        ...     for constraints, tree in ten_solutions
        ...     for c, t in itertools.islice(
        ...         solver.eliminate_first_existential_formula(constraints, tree), 2
        ...     )
        ... )

        >>> print("\n".join(map(star(conjuncts_tree_pair_to_str), ten_subsequent_solutions)))
        (= digit "1"), (= var "x") |- <var> := <digit> ; a := 1 ; b := 2 ; c := 3
        (= digit "1"), (= var "x") |- <var> := <digit> ; <var> := <rhs> ; a := 1 ; b := 2 ; c := 3
        (= digit "1"), (= var "x") |- <var> := <digit> ; <var> := <var> ; a := 1 ; b := 2 ; c := 3
        (= digit "1"), (= var "x") |- <var> := <var> ; <var> := <digit> ; a := 1 ; b := 2 ; c := 3
        (= digit "1"), (= var "x") |- a := 1 ; <var> := <digit> ; b := 2 ; c := 3
        (= digit "1"), (= var "x") |- <var> := <digit> ; a := 1 ; <var> := <rhs> ; b := 2 ; c := 3
        (= digit "1"), (= var "x") |- <var> := <digit> ; a := 1 ; <var> := <var> ; b := 2 ; c := 3
        (= digit "1"), (= var "x") |- a := 1 ; <var> := <digit> ; <var> := <var> ; b := 2 ; c := 3
        (= digit "1"), (= var "x") |- a := 1 ; b := 2 ; <var> := <digit> ; c := 3
        (= digit "1"), (= var "x") |- <var> := <digit> ; a := 1 ; b := 2 ; <var> := <rhs> ; c := 3
        (= digit "1"), (= var "x") |- <var> := <digit> ; a := 1 ; b := 2 ; <var> := <var> ; c := 3
        (= digit "1"), (= var "x") |- a := 1 ; <var> := <digit> ; b := 2 ; <var> := <var> ; c := 3

        :param conjuncts:
        :param tree:
        :return:
        """  # noqa: E501

        validate_structural_predicate_arguments(conjuncts, tree)
        validate_smt_formula_substitutions(conjuncts, tree)

        idx, first_existential_formula = Maybe.from_optional(
            next(
                filter(
                    star(lambda idx, f: isinstance(f, ExistsFormula)),
                    enumerate(conjuncts),
                ),
                None,
            )
        ).value_or((-1, None))

        if not first_existential_formula:
            yield conjuncts, tree, frozendict({})
            return

        other_conjuncts = conjuncts[:idx] + conjuncts[idx + 1 :]

        assert (
            not first_existential_formula.in_variable.value == "<start>"
            or first_existential_formula.in_variable == tree
        )

        for (
            instantiated_formula,
            resulting_tree,
            tree_substitutions,
        ) in self.eliminate_existential_formula(
            first_existential_formula,
            tree,
        ):
            updated_conjuncts = tuple(
                c.substitute_expressions(tree_substitutions) for c in other_conjuncts
            )

            validate_structural_predicate_arguments(
                instantiated_formula, resulting_tree
            )
            validate_structural_predicate_arguments(updated_conjuncts, resulting_tree)
            validate_smt_formula_substitutions(updated_conjuncts, tree)
            validate_smt_formula_substitutions(updated_conjuncts, resulting_tree)
            validate_smt_formula_substitutions(instantiated_formula, resulting_tree)

            yield (instantiated_formula,) + updated_conjuncts, resulting_tree

    def try_to_finish(
        self, tree: DerivationTree, validity_constraint: Formula, max_tries: int = 50
    ) -> Maybe[DerivationTree]:
        """
        TODO: Document & add test cases.

        :param tree:
        :param validity_constraint:
        :param max_tries:
        :return:
        """

        return next(
            (
                Some(closed_tree)
                for closed_tree, closing_substs in itertools.islice(
                    self.finish_unconstrained_tree(tree), max_tries
                )
                if evaluate(
                    validity_constraint.substitute_expressions(closing_substs),
                    closed_tree,
                    self.grammar,
                ).is_true()
            ),
            Nothing,
        )

    @typechecked
    def instantiate_quantifiers(
        self,
        formula: Formula,
        ignore: FrozenSet[Formula] = frozenset(),
    ) -> Formula:
        r"""
        TODO: Document.

        >>> grammar = {
        ...     "<start>": ["<digits>"],
        ...     "<digits>": ["<digit><digits>", "<digit>"],
        ...     "<digit>": ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"],
        ... }
        >>> constraint = '''
        ...     forall <digit> digit_1 in start: (
        ...         digit_1 = "0" or
        ...             exists <digit> digit_2 in start: (
        ...                 before(digit_2, digit_1) and digit_2 = "0"
        ...             )
        ...     )'''
        >>> solver = RepairSolver(grammar, constraint)
        >>> tree = solver.parse("012").unwrap()

        >>> from isla.language import split_conjunction
        >>> print(
        ...     "\n".join(
        ...         map(
        ...             str,
        ...             split_conjunction(
        ...                 solver.instantiate_quantifiers(
        ...                     solver.instantiate_top_constant(tree)
        ...                 )
        ...             ),
        ...         )
        ...     )
        ... )
        ((digit_1 == "0", {'digit_1': '0'}) ∨ ((((before(0, 0) ∧ (digit_2 == "0", {'digit_2': '0'})) ∨ (before(1, 0) ∧ (digit_2 == "0", {'digit_2': '1'}))) ∨ (before(2, 0) ∧ (digit_2 == "0", {'digit_2': '2'}))) ∨ ∃ digit_2 ∈ 012: ((before(digit_2, 0) ∧ digit_2 == "0"))))
        ((digit_1 == "0", {'digit_1': '1'}) ∨ ((((before(0, 1) ∧ (digit_2 == "0", {'digit_2': '0'})) ∨ (before(1, 1) ∧ (digit_2 == "0", {'digit_2': '1'}))) ∨ (before(2, 1) ∧ (digit_2 == "0", {'digit_2': '2'}))) ∨ ∃ digit_2 ∈ 012: ((before(digit_2, 1) ∧ digit_2 == "0"))))
        ((digit_1 == "0", {'digit_1': '2'}) ∨ ((((before(0, 2) ∧ (digit_2 == "0", {'digit_2': '0'})) ∨ (before(1, 2) ∧ (digit_2 == "0", {'digit_2': '1'}))) ∨ (before(2, 2) ∧ (digit_2 == "0", {'digit_2': '2'}))) ∨ ∃ digit_2 ∈ 012: ((before(digit_2, 2) ∧ digit_2 == "0"))))
        ∀ digit_1 ∈ 012: ((digit_1 == "0" ∨ ∃ digit_2 ∈ 012: ((before(digit_2, digit_1) ∧ digit_2 == "0"))))

        :param formula:
        :param ignore:
        :return:
        """  # noqa: E501

        # We disable the automatic evaluation and substitution of SMT expressions
        # because we want to use the # SMT expressions as-is in the formula (to
        # repair the invalid ones).
        formula = set_auto_subst_and_eval(formula, False)

        top_level_qfd_formulas = extract_top_level_quantified_formulas(
            formula
        ).difference(ignore)

        if not top_level_qfd_formulas:
            return formula

        for qfd_formula in top_level_qfd_formulas:
            matches = tuple(
                frozendict({var: tree for var, (_, tree) in match.items()})
                for match in matches_for_quantified_formula(
                    qfd_formula, self.grammar, in_tree=qfd_formula.in_variable
                )
                # if not qfd_formula.is_already_matched(
                #     match[qfd_formula.bound_variable][1]
                # )
                if hash(
                    (
                        match[qfd_formula.bound_variable][1].id,
                        match[qfd_formula.bound_variable][1].structural_hash(),
                    )
                )
                not in qfd_formula.already_matched
            )

            qfd_formula = add_already_matched(
                qfd_formula, [match[qfd_formula.bound_variable] for match in matches]
            )
            ignore = ignore | {qfd_formula}

            if isinstance(qfd_formula, ForallFormula):
                instantiations = conjunction(
                    *map(qfd_formula.inner_formula.substitute_expressions, matches),
                )

                formula = (
                    replace_formula(formula, qfd_formula, instantiations) & qfd_formula
                )
            elif isinstance(qfd_formula, ExistsFormula):
                instantiations = disjunction(
                    *map(qfd_formula.inner_formula.substitute_expressions, matches),
                )

                formula = replace_formula(
                    formula,
                    qfd_formula,
                    instantiations | qfd_formula,
                )

        return self.instantiate_quantifiers(formula, ignore)

    @typechecked
    def finish_unconstrained_tree(
        self,
        tree: DerivationTree,
    ) -> Iterator[Tuple[DerivationTree, frozendict[DerivationTree, DerivationTree]]]:
        while True:
            result_tree = tree
            result_substs: frozendict[DerivationTree, DerivationTree] = frozendict({})
            for path, leaf in tree.open_leaves():
                leaf_inst = self.fuzzer.expand_tree(DerivationTree(leaf.value, None))
                result_tree = result_tree.replace_path(path, leaf_inst)
                result_substs = result_substs.set(leaf, leaf_inst)

            yield result_tree, result_substs

    @typechecked
    def eliminate_true_semantic_formulas(
        self,
        constraint: Formula,
        context_tree: DerivationTree,
    ) -> Formula:
        for semantic_formula in FilterVisitor(
            lambda f: (
                isinstance(f, SMTFormula)
                and not f.free_variables()
                and evaluate(f, context_tree, self.grammar).is_true()
            )
        ).collect(constraint):
            constraint = replace_formula(constraint, semantic_formula, true())

        return constraint

    @typechecked
    def eliminate_existential_formula(
        self,
        existential_formula: ExistsFormula,
        context_tree: DerivationTree,
    ) -> Iterator[
        Tuple[Formula, DerivationTree, Mapping[DerivationTree, DerivationTree]]
    ]:
        """
        TODO: Document.

        >>> import string
        >>> grammar = frozendict({
        ...     "<start>": ("<stmt>",),
        ...     "<stmt>": ("<assgn> ; <stmt>", "<assgn>"),
        ...     "<assgn>": ("<var> := <rhs>",),
        ...     "<rhs>": ("<var>", "<digit>"),
        ...     "<var>": tuple(string.ascii_lowercase),
        ...     "<digit>": tuple(string.digits)
        ... })

        >>> solver = RepairSolver(grammar, max_tries_existential_insertion=3)
        >>> tree = solver.parse("a := 1 ; b := 2 ; c := 3").unwrap()

        >>> existential_formula = parse_isla(
        ...     'exists <var> var in start: (= var "x")', grammar
        ... ).substitute_expressions({Constant("start", "<start>"): tree})

        >>> f, t, m = next(solver.eliminate_existential_formula(existential_formula, tree))

        >>> print(f)
        (var == "x", {'var': '<var>'})

        >>> print(t)
        <var> := <rhs> ; a := 1 ; b := 2 ; c := 3

        :param existential_formula:
        :param context_tree:
        :return:
        """

        assert (
            not existential_formula.in_variable.value == "<start>"
            or existential_formula.in_variable == context_tree
        )

        inserted_trees_and_bind_paths: Tuple[
            Tuple[DerivationTree, Dict[BoundVariable, Path]], ...
        ] = tuple(
            Maybe.from_optional(existential_formula.bind_expression)
            .map(
                lambda bind_expr: bind_expr.to_tree_prefix(
                    existential_formula.bound_variable.n_type, self.grammar
                )
            )
            .value_or(
                [(DerivationTree(existential_formula.bound_variable.n_type, None), {})]
            )
        )

        inserted_tree: DerivationTree
        bind_expr_paths: Dict[BoundVariable, Path]
        for inserted_tree, bind_expr_paths in inserted_trees_and_bind_paths:
            insertion_results = insert_tree(
                existential_formula.in_variable,
                inserted_tree,
                self.graph,
                Some(self.canonical_grammar),
            )

            has_result = False
            for insertion_result in insertion_results:
                has_result = True
                assert len(insertion_result) == 2
                assert isinstance(insertion_result[0], DerivationTree)
                assert isinstance(insertion_result[1], tuple)
                yield self.process_insertion_result(
                    bind_expr_paths,
                    context_tree,
                    existential_formula,
                    *insertion_result,
                )

            if not has_result:
                LOGGER.debug(
                    "Could not insert tree '%s' (%s) into '%s' (%s)",
                    inserted_tree,
                    inserted_tree.value,
                    existential_formula.in_variable,
                    existential_formula.in_variable.value,
                )

    @typechecked
    def process_insertion_result(
        self,
        bind_expr_paths: Dict[BoundVariable, Path],
        context_tree: DerivationTree,
        existential_formula: ExistsFormula,
        inserted_tree: DerivationTree,
        path_to_inserted_tree: Path,
    ) -> Tuple[Formula, DerivationTree, Mapping[DerivationTree, DerivationTree]]:
        """
        TODO: Document.

        :param bind_expr_paths:
        :param context_tree:
        :param existential_formula:
        :param inserted_tree:
        :param path_to_inserted_tree:
        :return:
        """

        replaced_path = context_tree.find_node(existential_formula.in_variable)
        resulting_tree = context_tree.replace_path(replaced_path, inserted_tree)

        # TODO: Make this more efficient; only consider paths that can have changed.
        tree_substitutions = frozendict(
            {
                subtree: resulting_tree.get_subtree(resulting_tree.find_node(subtree))
                for _, subtree in context_tree.paths()
            }
        )

        inserted_tree_in_tree_after_insertion = inserted_tree.get_subtree(
            path_to_inserted_tree
        )

        variable_substitutions = frozendict(
            {existential_formula.bound_variable: inserted_tree_in_tree_after_insertion}
            | (
                {
                    var: inserted_tree_in_tree_after_insertion.get_subtree(path)
                    for var, path in bind_expr_paths.items()
                    if var in existential_formula.bind_expression.bound_variables()
                }
                if bind_expr_paths
                else {}
            )
        )

        instantiated_formula = flow(
            existential_formula.inner_formula,
            lambda f: f.substitute_expressions(variable_substitutions),
            lambda f: f.substitute_expressions(tree_substitutions),
        )

        validate_structural_predicate_arguments(instantiated_formula, resulting_tree)
        validate_smt_formula_substitutions(instantiated_formula, resulting_tree)

        return instantiated_formula, resulting_tree, tree_substitutions

    # TODO: Polish the functions below, which were copied from ISLaSolver
    @typechecked
    def eliminate_all_semantic_formulas(
        self,
        smt_formulas: Sequence[SMTFormula],
        tree: DerivationTree,
    ) -> Maybe[Mapping[DerivationTree, DerivationTree]]:
        """
        Eliminates all SMT-LIB formulas that appear in `state`'s constraint as conjunctive elements.
        If, e.g., an SMT-LIB formula occurs as a disjunction, no solution is computed.

        >>> solver = RepairSolver({"<start>": ["<a>"], "<a>": ["a"]})
        >>> solver.eliminate_all_semantic_formulas([true()], DerivationTree("<start>", None))
        <Some: frozendict.frozendict({})>

        >>> solver.eliminate_all_semantic_formulas([false()], DerivationTree("<start>", None))
        <Nothing>

        :param smt_formulas: A sequence of SMT-LIB formulas
            to solve and suggestions for the values of their variables.
        :param tree: The reference tree.
        :return: A mapping from old to new trees, if a solution exists.
        """

        if not smt_formulas:
            return Some(tree)

        LOGGER.debug("Eliminating semantic formulas [%s]", lazyjoin(", ", smt_formulas))

        # NOTE: We need to cluster SMT formulas by tree substitutions. If there are two
        # formulas with a variable $var which is instantiated to different trees, we
        # need two separate solutions. If, however, $var is instantiated with the
        # *same* tree, we need one solution to both formulas together.
        smt_formulas = rename_instantiated_variables_in_smt_formulas(smt_formulas)

        # Now, we also cluster formulas by common variables (and instantiated subtrees:
        # One formula might yield an instantiation of a subtree of the instantiation of
        # another formula. They need to appear in the same cluster). The solver can
        # better handle smaller constraints, and those which do not have variables in
        # common can be handled independently.

        @typechecked
        def cluster_keys(smt_formula: SMTFormula):
            return (
                smt_formula.free_variables()
                | smt_formula.instantiated_variables
                | set(
                    [
                        subtree
                        for tree in smt_formula.substitutions.values()
                        for _, subtree in tree.paths()
                    ]
                )
            )

        formula_clusters: Tuple[Tuple[SMTFormula, ...], ...] = tuple(
            filter(None, cluster_by_common_elements(smt_formulas, cluster_keys))
        )

        assert all(
            not cluster_keys(smt_formula)
            or any(smt_formula in cluster for cluster in formula_clusters)
            for smt_formula in smt_formulas
        )

        match tuple(
            smt_formula for smt_formula in smt_formulas if not cluster_keys(smt_formula)
        ):
            case ():
                pass
            case remaining_smt_formulas_cluster:
                formula_clusters += (remaining_smt_formulas_cluster,)

        # These solutions are all independent, such that we can combine each solution
        # with all others.
        maybe_solution: Maybe[frozendict[DerivationTree, DerivationTree]] = reduce(
            lambda maybe_combined_solution, maybe_cluster_solution: (
                maybe_combined_solution.bind(
                    lambda combined_solution: maybe_cluster_solution.map(
                        lambda cluster_solution: frozendict(
                            combined_solution | cluster_solution
                        )
                    )
                )
            ),
            map(partial(self.solve_quantifier_free_formula, tree), formula_clusters),
            Some(frozendict()),
        )

        # We also have to instantiate all subtrees of the substituted element.
        return maybe_solution.map(subtree_solutions)

    @typechecked
    def solve_quantifier_free_formula(
        self,
        tree: DerivationTree,
        smt_formulas: Tuple[SMTFormula, ...],
    ) -> Maybe[frozendict[DerivationTree, DerivationTree]]:
        """
        Attempts to solve the given SMT-LIB formulas by calling Z3.

        Note that this function does not unify variables pointing to the same derivation
        trees. E.g., a solution may be returned for the formula `var_1 = "a" and
        var_2 = "b"`, though `var_1` and `var_2` point to the same `<var>` tree as
        defined by their substitutions maps. Unification is performed in
        `eliminate_all_semantic_formulas`.

        :param smt_formulas: The SMT-LIB formulas to solve.
        :return: A (possibly empty) list of solutions.
        """

        (
            solver_result,
            maybe_model,
        ) = self.solve_smt_formulas_with_language_constraints(tree, smt_formulas)

        if solver_result != z3.sat:
            return Nothing

        tree_substitutions_in_smt_formulas = collect_tree_substitutions_in_smt_formulas(
            smt_formulas
        )
        variables_in_smt_formulas = collect_variables_in_smt_formulas(smt_formulas)

        def integrate_model_for_variable(
            model: frozendict[Variable, DerivationTree],
            variable: Variable,
            solution: frozendict[Variable, DerivationTree],
        ) -> frozendict[Variable, DerivationTree]:
            return solution.set(
                tree_substitutions_in_smt_formulas.get(variable, variable),
                model[variable],
            )

        result: Maybe[frozendict[DerivationTree, DerivationTree]] = maybe_model.bind(
            lambda model: reduce(
                lambda maybe_solution, variable: maybe_solution.map(
                    partial(integrate_model_for_variable, model, variable)
                ),
                variables_in_smt_formulas,
                Some(frozendict({})),
            )
        )

        assert result.map(
            lambda r: isinstance(r, frozendict)
            and all(
                isinstance(k, DerivationTree) and isinstance(v, DerivationTree)
                for k, v in r.items()
            )
        ).value_or(False)

        return result

    @typechecked
    def solve_smt_formulas_with_language_constraints(
        self,
        tree: DerivationTree,
        smt_formulas: Tuple[SMTFormula, ...],
    ) -> Tuple[z3.CheckSatResult, Maybe[frozendict[Variable, DerivationTree]]]:
        """
        Attempts to solve the given SMT-LIB formulas by calling Z3.

        """

        variables = collect_variables_in_smt_formulas(smt_formulas)

        if self.enable_optimized_z3_queries:
            (
                length_vars,
                int_vars,
                fresh_var_map,
                sat_result,
                maybe_model,
            ) = self.compute_solution_optimized(smt_formulas, tree, variables)
        else:
            (
                length_vars,
                int_vars,
                fresh_var_map,
                sat_result,
                maybe_model,
            ) = self.compute_solution_vanilla(smt_formulas, tree, variables)

        if sat_result != z3.sat:
            return sat_result, Nothing

        assert maybe_model is not None
        return sat_result, self.extract_model_values(
            variables, maybe_model, fresh_var_map, length_vars, int_vars
        )

    def compute_solution_vanilla(
        self,
        smt_formulas: Tuple[SMTFormula, ...],
        tree: DerivationTree,
        variables: Optional[FrozenOrderedSet[Variable]] = None,
    ) -> Tuple[
        FrozenOrderedSet[Variable],
        FrozenOrderedSet[Variable],
        frozendict[Variable, z3.ExprRef],
        z3.CheckSatResult,
        Optional[z3.ModelRef],
    ]:
        r"""
        This function computes a solution to the given SMT-LIB formulas using the
        Z3 SMT solver. It does not perform any optimizations (e.g., for numeric
        variables).

        Example
        -------

        >>> simplified_xml_grammar = '''
        ...     <start> ::= <xml-tree>
        ...     <xml-tree> ::= "" | <xml-open-tag> <xml-tree> <xml-close-tag>
        ...     <xml-open-tag> ::= "<" <tag-id> <attrs> ">"
        ...     <xml-close-tag> ::= "</" <tag-id> ">"
        ...     <attrs> ::= "" | " " <attr> <attrs>
        ...     <attr> ::= <attr-id> "=\\"XXX\\""
        ...     <tag-id> ::= <letter-no-x> ":" <letter>
        ...     <attr-id> ::= <letter> ":" <letter>
        ...     <letter> ::= "a" | "b" | "c" | "x"
        ...     <letter-no-x> ::= "a" | "b" | "c"
        ... '''

        >>> solver = RepairSolver(simplified_xml_grammar)

        >>> tree = solver.parse('<a:b x:c="XXX" x:c="XXX"><b:x></c:a></a:b>').unwrap()
        >>> tree = tree.replace_path((0, 0, 2, 1, 0, 2), DerivationTree("<letter>"))
        >>> tree = tree.replace_path((0, 0, 2, 2, 1, 0, 2), DerivationTree("<letter>"))
        >>> print(tree)
        <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>

        >>> letter_no_x_1 = Variable("letter_no_x_1", "<letter-no-x>")
        >>> letter_no_x_2 = Variable("letter_no_x_2", "<letter-no-x>")
        >>> letter_1 = Variable("letter_1", "<letter>")
        >>> letter_2 = Variable("letter_2", "<letter>")
        >>> attr_id_1 = Variable("attr_id_1", "<attr-id>")
        >>> attr_id_2 = Variable("attr_id_2", "<attr-id>")
        >>> tag_id_1 = Variable("tag_id_1", "<tag-id>")
        >>> tag_id_2 = Variable("tag_id_2", "<tag-id>")

        <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>
                                                ^
        >>> letter_no_x_1_tree = tree.get_subtree((0, 1, 0, 1, 0))

        <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>
         ^
        >>> letter_no_x_2_tree = tree.get_subtree((0, 0, 1, 0))

        <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>
               ^
        >>> letter_1_tree = tree.get_subtree((0, 0, 2, 1, 0, 2))

        <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>
                                ^
        >>> letter_2_tree = tree.get_subtree((0, 0, 2, 2, 1, 0, 2))

        <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>
             ^
        >>> attr_id_1_tree = tree.get_subtree((0, 0, 2, 1, 0))

        <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>
                              ^
        >>> attr_id_2_tree = tree.get_subtree((0, 0, 2, 2, 1, 0))

        <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>
         ^
        >>> tag_id_1_tree = tree.get_subtree((0, 1, 0, 1))

        <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>
                                                            ^
        >>> tag_id_2_tree = tree.get_subtree((0, 1, 2, 2))

        - letter_no_x_1 == letter_1
        - Not(attr_id_2 == attr_id_1)
        - Not(letter_1 == "x")
        - letter_no_x_2 == letter_2
        - Not(letter_2 == "x")
        - tag_id_1 == tag_id_2

        >>> formula_1 = SMTFormula(
        ...     z3_eq(letter_no_x_1.to_smt(), letter_1.to_smt()),
        ...     letter_no_x_1, letter_1,
        ...     auto_eval=False, auto_subst=False,
        ... ).substitute_expressions(
        ...     {letter_no_x_1: letter_no_x_1_tree, letter_1: letter_1_tree}
        ... )

        >>> formula_2 = SMTFormula(
        ...     z3.Not(z3_eq(attr_id_2.to_smt(), attr_id_1.to_smt())),
        ...     attr_id_2, attr_id_1,
        ...     auto_eval=False, auto_subst=False,
        ... ).substitute_expressions({attr_id_2: attr_id_2_tree, attr_id_1: attr_id_1_tree})

        >>> formula_3 = SMTFormula(
        ...     z3.Not(z3_eq(letter_1.to_smt(), z3.StringVal("x"))),
        ...     letter_1,
        ...     auto_eval=False, auto_subst=False,
        ... ).substitute_expressions({letter_1: letter_1_tree})

        >>> formula_4 = SMTFormula(
        ...     z3_eq(letter_no_x_2.to_smt(), letter_2.to_smt()),
        ...     letter_no_x_2, letter_2,
        ...     auto_eval=False, auto_subst=False,
        ... ).substitute_expressions(
        ...     {letter_no_x_2: letter_no_x_2_tree, letter_2: letter_2_tree}
        ... )

        >>> formula_5 = SMTFormula(
        ...     z3.Not(z3_eq(letter_2.to_smt(), z3.StringVal("x"))),
        ...     letter_2,
        ...     auto_eval=False, auto_subst=False,
        ... ).substitute_expressions({letter_2: letter_2_tree})

        >>> formula_6 = SMTFormula(
        ...     z3_eq(tag_id_1.to_smt(), tag_id_2.to_smt()),
        ...     tag_id_1, tag_id_2,
        ...     auto_eval=False, auto_subst=False,
        ... ).substitute_expressions({tag_id_1: tag_id_1_tree, tag_id_2: tag_id_2_tree})

        >>> random.seed(0)
        >>> z3.set_param("smt.random_seed", 0)

        >>> _1, _2, _3, res, model = solver.compute_solution_vanilla(
        ...     (formula_1, formula_2, formula_3, formula_4, formula_5, formula_6), tree
        ... )

        >>> res
        sat

        >>> model[attr_id_1.to_smt()]
        "x:b"

        >>> model[attr_id_2.to_smt()]
        "x:a"

        >>> model[tag_id_1.to_smt()]
        "b:x"

        >>> model[tag_id_2.to_smt()]
        "b:x"

        :param smt_formulas: The SMT-LIB formulas to solve.
        :param tree: The reference tree.
        :param variables: The variables occurring in the SMT-LIB formulas. If not
            provided, they are computed from the formulas.
        :return: A tuple containing the set of length variables (here empty), the
            set of integer variables (here empty), a mapping from fresh variables
            to their Z3 expressions (here empty), the result of the Z3 solver, and
            the model returned by the Z3 solver.
        """

        if variables is None:
            variables = collect_variables_in_smt_formulas(smt_formulas)

        (
            fresh_variables,
            value_suggestions,
            structural_suggestions,
        ) = value_suggestion_constraints(tree, smt_formulas)

        sat_result, maybe_model = z3_solve(
            self.generate_language_constraints(
                variables | fresh_variables,
            )
            + tuple(map(lambda f: f.formula, smt_formulas)),
            structural_suggestions,
            value_suggestions,
        )

        return (
            FrozenOrderedSet(),
            FrozenOrderedSet(),
            frozendict({}),
            sat_result,
            maybe_model,
        )

    def compute_solution_optimized(
        self,
        smt_formulas: Tuple[SMTFormula, ...],
        tree: DerivationTree,
        variables: Optional[FrozenOrderedSet[Variable]] = None,
    ) -> Tuple[
        FrozenOrderedSet[Variable],
        FrozenOrderedSet[Variable],
        frozendict[Variable, z3.ExprRef],
        z3.CheckSatResult,
        Optional[z3.ModelRef],
    ]:
        """
        This function attempts to solve the given SMT-LIB formulas. It contains
        optimizations for variables occurring exclusively in :code:`str.len` and
        :code:`str.to.int` contexts, which it passes to the SMT solver as integer
        variables. The returned model will then provide assignments for these
        fresh integer variables, that then must be converted to suitable strings.

        Example
        -------

        Consider the following grammar of a TLS heartbeat request:

        >>> heartbeat_request_grammar = {
        ...     "<start>": ["<heartbeat-request>"],
        ...     "<heartbeat-request>": ["\x01<payload-length><payload><padding>"],
        ...     "<payload-length>": ["<byte><byte>"],
        ...     "<payload>": ["<bytes>"],
        ...     "<padding>": ["<bytes>"],
        ...     "<bytes>": ["<byte><bytes>", "<byte>"],
        ...     "<byte>": [chr(i) for i in range(256)],
        ... }

        >>> solver = RepairSolver(heartbeat_request_grammar)

        We regard a heartbeat request an invalid combination of the length and payload fields.

        >>> tree = DerivationTree.from_parse_tree((
        ...     "<start>",
        ...     [
        ...         (
        ...             "<heartbeat-request>",
        ...             [
        ...                 ("\x01", []),
        ...                 (
        ...                     "<payload-length>",
        ...                     [("<byte>", [("î", [])]), ("<byte>", [("¶", [])])],
        ...                 ),
        ...                 ("<payload>", [("<bytes>", [("<byte>", [("¼", [])])])]),
        ...                 (
        ...                     "<padding>",
        ...                     [
        ...                         (
        ...                             "<bytes>",
        ...                             [
        ...                                 ("<byte>", [("Ï", [])]),
        ...                                 ("<bytes>", [("<byte>", [("µ", [])])]),
        ...                             ],
        ...                         )
        ...                     ],
        ...                 ),
        ...             ],
        ...         )
        ...     ],
        ... ))

        >>> byte_1 = BoundVariable("byte_1", "<byte>")
        >>> byte_2 = BoundVariable("byte_2", "<byte>")
        >>> payload = BoundVariable("payload", "<payload>")

        >>> byte_1_tree = tree.get_subtree((0, 1, 0))
        >>> byte_2_tree = tree.get_subtree((0, 1, 1))
        >>> payload_tree = tree.get_subtree((0, 2))

        We stipulate the constraints that (1) the most significant byte must be
        equal to 1 and (2) the length of the payload must be equal to 256 times
        the most significant byte plus the least significant byte.

        >>> formula_1 = SMTFormula(
        ...     z3_eq(byte_1.to_smt(), z3.StringVal("\x01")),
        ...     byte_1,
        ...     auto_eval=False,
        ...     auto_subst=False,
        ... ).substitute_expressions({byte_1: byte_1_tree})

        >>> formula_2 = SMTFormula(
        ...     z3_eq(
        ...         z3.IntVal(256) * z3.StrToCode(byte_1.to_smt()) + z3.StrToCode(byte_2.to_smt()),
        ...         z3.Length(payload.to_smt())
        ...     ),
        ...     byte_1,
        ...     byte_2,
        ...     payload,
        ...     auto_eval=False,
        ...     auto_subst=False,
        ... ).substitute_expressions({
        ...     byte_1: byte_1_tree,
        ...     byte_2: byte_2_tree,
        ...     payload: payload_tree
        ... })

        We see that in the returned result, (1) the value of the most significant byte is
        chosen as defined, (2) the value of the least significant byte from the substitutions
        in second formula is retained, and (3) the payload is represented as an integer variable
        of value 438 (256 * 1 + 182).

        >>> print(deep_str(
        ...     solver.compute_solution_optimized(
        ...         (formula_1, formula_2),
        ...         tree,
        ...         FrozenOrderedSet((byte_1, byte_2, payload)),
        ...     )
        ... ))
        ({payload}, {}, {payload: payload_0}, sat, [byte_2 = "¶", payload_0 = 438, byte_1 = ""])

        :param smt_formulas: The SMT-LIB formulas to solve.
        :param tree: The reference tree.
        :param variables: The variables to consider. If not given, all variables in
            `smt_formulas` are considered.
        :return:
        """

        if variables is None:
            variables = collect_variables_in_smt_formulas(smt_formulas)

        vars_in_context = infer_variable_contexts(variables, smt_formulas)
        length_vars = vars_in_context["length"]
        int_vars = vars_in_context["int"]
        flexible_vars = vars_in_context["flexible"]

        # Add language constraints for "flexible" variables
        flex_language_constraints: Tuple[z3.BoolRef, ...] = (
            self.generate_language_constraints(flexible_vars)
        )

        fresh_var_map: frozendict[Variable, z3.ExprRef] = frozendict({})

        # Create fresh variables for `str.len` and `str.to.int` variables.
        all_variables = variables
        for var in length_vars | int_vars:
            fresh = fresh_constant(
                all_variables,
                Constant(var.name, "NOT-NEEDED"),
                add=False,
            )
            fresh_var_map = fresh_var_map.set(var, z3.Int(fresh.name))
            all_variables = all_variables.union((fresh,))

        # In `smt_formulas`, we replace all `length(...)` terms for "length
        # variables" with the corresponding fresh variable.
        replacement_map: Dict[z3.ExprRef, z3.ExprRef] = {
            expr: fresh_var_map[
                get_elem_by_equivalence(
                    expr.children()[0],
                    length_vars | int_vars,
                    lambda e1, e2: e1 == e2.to_smt(),
                )
            ]
            for formula in smt_formulas
            for expr in visit_z3_expr(formula.formula)
            if expr.decl().kind() in {z3.Z3_OP_SEQ_LENGTH, z3.Z3_OP_STR_TO_INT}
            and expr.children()[0] in {var.to_smt() for var in length_vars | int_vars}
        }

        # Perform substitution, add formulas
        smt_formulas_no_seq_and_strtoint: Tuple[z3.BoolRef, ...] = tuple(
            cast(z3.BoolRef, z3_subst(formula.formula, replacement_map))
            for formula in smt_formulas
        )

        # Lengths must be positive
        length_constraints = tuple(
            cast(
                z3.BoolRef,
                replacement_map[z3.Length(length_var.to_smt())] >= z3.IntVal(0),
            )
            for length_var in length_vars
        )

        # Add custom intervals for int variables
        interval_constraints = self.compute_interval_constraints(
            int_vars, replacement_map
        )

        # Compute constraints on existing values
        (
            fresh_variables,
            structural_relations,
            value_relations,
        ) = shape_relations_from_smt_constraints(
            tree, smt_formulas, initial_fresh_variables=all_variables
        )

        assert all(int_var not in structural_relations for int_var in int_vars)
        assert all(length_var not in structural_relations for length_var in length_vars)

        structural_constraints: Tuple[z3.BoolRef, ...] = tuple(
            z3_eq(
                var.to_smt(),
                z3_concat(
                    tuple(
                        z3.StringVal(elem) if isinstance(elem, str) else elem.to_smt()
                        for elem in structure
                    )
                ),
            )
            for var, structure in structural_relations.items()
        )

        value_constraints: Tuple[z3.BoolRef, ...] = (
            tuple(
                z3_eq(var.to_smt(), z3.StringVal(value))
                for var, value in value_relations.items()
                if var in flexible_vars or var in fresh_variables
            )
            + tuple(
                z3_eq(fresh_var_map[var], z3.IntVal(int(value)))
                for var, value in value_relations.items()
                if var in int_vars
            )
            + tuple(
                z3_eq(fresh_var_map[var], z3.IntVal(len(value)))
                for var, value in value_relations.items()
                if var in length_vars
            )
        )

        sat_result, maybe_model = z3_solve(
            flex_language_constraints
            + length_constraints
            + interval_constraints
            + smt_formulas_no_seq_and_strtoint,
            medium_constraints=structural_constraints,
            soft_constraints=value_constraints,
        )

        return length_vars, int_vars, fresh_var_map, sat_result, maybe_model

    def compute_interval_constraints(
        self,
        int_vars: Iterable[Variable],
        replacement_map: Mapping[z3.ExprRef, z3.ExprRef],
    ) -> Tuple[z3.BoolRef, ...]:
        """
        TODO: Document, test.

        :param int_vars:
        :param replacement_map:
        :return:
        """

        interval_constraints: Tuple[z3.BoolRef, ...] = ()
        for int_var in int_vars:
            regex = self.extract_regular_expression(int_var.n_type)
            maybe_intervals = numeric_intervals_from_regex(regex)
            repl_var = replacement_map[z3.StrToInt(int_var.to_smt())]
            interval_constraints += maybe_intervals.map(
                lambda intervals: (
                    z3_or(
                        [
                            z3.And(
                                (
                                    repl_var >= z3.IntVal(interval[0])
                                    if interval[0] > -sys.maxsize
                                    else z3.BoolVal(True)
                                ),
                                (
                                    repl_var <= z3.IntVal(interval[1])
                                    if interval[1] < sys.maxsize
                                    else z3.BoolVal(True)
                                ),
                            )
                            for interval in intervals
                        ]
                    ),
                )
            ).value_or(())

        return interval_constraints

    def extract_model_values(
        self, variables, maybe_model, fresh_var_map, length_vars, int_vars
    ):
        """
        TODO: Test, Document.

        :param variables:
        :param maybe_model:
        :param fresh_var_map:
        :param length_vars:
        :param int_vars:
        :return:
        """

        model_values: Maybe[frozendict[Variable, DerivationTree]] = flow(
            variables,
            partial(
                map,
                lambda var: (
                    self.extract_model_value(
                        var, maybe_model, fresh_var_map, length_vars, int_vars
                    ).map(lambda model_value: ((var, model_value),))
                ),
            ),
            partial(sum_of_maybes, neutral=()),
            map_(frozendict),
        )

        assert model_values.map(
            lambda r: isinstance(r, frozendict)
            and all(
                isinstance(k, Variable) and isinstance(v, DerivationTree)
                for k, v in r.items()
            )
        ).value_or(False)

        return model_values

    @typechecked
    def generate_language_constraints(
        self,
        variables_in_smt_formulas: Iterable[Variable],
    ) -> Tuple[z3.BoolRef, ...]:
        return tuple(
            z3.InRe(var.to_smt(), self.extract_regular_expression(var.n_type))
            for var in variables_in_smt_formulas
        )

    @lru_cache(maxsize=128)
    @typechecked
    def extract_regular_expression(self, nonterminal: str) -> z3.ReRef:
        # For definitions like `<a> ::= <b>`, we only compute the regular expression
        # for `<b>`. That way, we might save some calls if `<b>` is used multiple times
        # (e.g., as in `<byte>`).
        canonical_expansions = self.canonical_grammar[nonterminal]

        if (
            len(canonical_expansions) == 1
            and len(canonical_expansions[0]) == 1
            and is_nonterminal(canonical_expansions[0][0])
        ):
            sub_nonterminal = canonical_expansions[0][0]
            assert (
                nonterminal != sub_nonterminal
            ), f"Expansion {nonterminal} => {sub_nonterminal}: Infinite recursion!"
            return self.extract_regular_expression(sub_nonterminal)

        # Similarly, for definitions like `<a> ::= <b> " x " <c>`, where `<b>` and `<c>`
        # don't reach `<a>`, we only compute the regular expressions for `<b>` and `<c>`
        # and return a concatenation. This also saves us expensive conversions (e.g.,
        # for `<seq> ::= <byte> <byte>`).
        if (
            len(canonical_expansions) == 1
            and any(is_nonterminal(elem) for elem in canonical_expansions[0])
            and all(
                not is_nonterminal(elem)
                or elem != nonterminal
                and not self.graph.reachable(elem, nonterminal)
                for elem in canonical_expansions[0]
            )
        ):
            result_elements: List[z3.ReRef] = [
                (
                    z3.Re(elem)
                    if not is_nonterminal(elem)
                    else self.extract_regular_expression(elem)
                )
                for elem in canonical_expansions[0]
            ]
            return z3.Concat(*result_elements)

        regex_conv = RegexConverter(
            grammar_to_unfrozen(
                self.grammar
            ),  # TODO: Make RegexConverter work with immutable grammars
            compress_unions=True,
            max_num_expansions=self.grammar_unwinding_threshold,
        )

        regex = regex_conv.to_regex(nonterminal, convert_to_z3=False)

        LOGGER.debug(
            f"Computed regular expression for nonterminal {nonterminal}:\n{regex}"
        )

        return regex_to_z3(regex)

    @typechecked
    def extract_model_value(
        self,
        var: Variable,
        model: z3.ModelRef,
        fresh_var_map: Mapping[Variable, z3.ExprRef],
        length_vars: Set[Variable],
        int_vars: Set[Variable],
    ) -> Maybe[DerivationTree]:
        r"""
        Extracts a value for :code:`var` from :code:`model`. Considers the following
        special cases:

        Numeric Variables
            Returns a closed derivation tree of one node with a string representation
            of the numeric solution.

        "Length" Variables
            Returns a string of the length corresponding to the model and
            :code:`fresh_var_map`, see also
            :meth:`~isla.repair_solver.safe_create_fixed_length_tree()`.

        "Int" Variables
            Tries to parse the numeric solution from the model (obtained via
            :code:`fresh_var_map`) into the type of :code:`var` and returns the
            corresponding derivation tree.

        >>> grammar = {
        ...     "<start>": ["<A>"],
        ...     "<A>": ["<X><Y>"],
        ...     "<X>": ["x", "x<X>"],
        ...     "<Y>": ["<digit>", "<digit><Y>"],
        ...     "<digit>": ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"],
        ... }
        >>> solver = RepairSolver(grammar)

        **"Length" Variables:**

        >>> from isla.z3_helpers import z3_eq
        >>> x = Variable("x", "<X>")
        >>> x_0 = z3.Int("x_0")
        >>> f = z3_eq(x_0, z3.IntVal(3))
        >>> z3_solver = z3.Solver()
        >>> z3_solver.add(f)
        >>> z3_solver.check()
        sat
        >>> model = z3_solver.model()
        >>> result = solver.extract_model_value(x, model, {x: x_0}, {x}, set()).unwrap()
        >>> result.value
        '<X>'
        >>> str(result)
        'xxx'

        **"Int" Variables:**

        >>> y = Variable("y", "<Y>")
        >>> y_0 = z3.Int("y_0")
        >>> f = z3_eq(y_0, z3.IntVal(5))
        >>> z3_solver = z3.Solver()
        >>> z3_solver.add(f)
        >>> z3_solver.check()
        sat
        >>> model = z3_solver.model()
        >>> DerivationTree.next_id = 1
        >>> solver.extract_model_value(y, model, {y: y_0}, set(), {y}).unwrap()
        DerivationTree('<Y>', (DerivationTree('<digit>', (DerivationTree('5', (), id=1),), id=2),), id=3)

        **"Flexible" Variables:**

        >>> f = z3_eq(x.to_smt(), z3.StringVal("xxxxx"))
        >>> z3_solver = z3.Solver()
        >>> z3_solver.add(f)
        >>> z3_solver.check()
        sat
        >>> model = z3_solver.model()
        >>> result = solver.extract_model_value(x, model, {}, set(), set()).unwrap()
        >>> result.value
        '<X>'
        >>> str(result)
        'xxxxx'

        **Special Number Formats**

        It may happen that the solver returns, e.g., "1" as a solution for an int
        variable, but the grammar only recognizes "+001". We support this case, i.e.,
        an optional "+" and optional 0 padding; an optional 0 padding for negative
        numbers is also supported.

        >>> grammar = {
        ...     "<start>": ["<int>"],
        ...     "<int>": ["<sign>00<leaddigit><digits>"],
        ...     "<sign>": ["-", "+"],
        ...     "<digits>": ["", "<digit><digits>"],
        ...     "<digit>": list("0123456789"),
        ...     "<leaddigit>": list("123456789"),
        ... }
        >>> solver = RepairSolver(grammar)

        >>> i = Variable("i", "<int>")
        >>> i_0 = z3.Int("i_0")
        >>> f = z3_eq(i_0, z3.IntVal(5))

        >>> z3_solver = z3.Solver()
        >>> z3_solver.add(f)
        >>> z3_solver.check()
        sat

        The following test works when run from the IDE, but unfortunately not when
        started from CI/the `test_doctests.py` script. Thus, we only show it as code
        block (we added a unit test as a replacement)::

            model = z3_solver.model()
            print(solver.extract_model_value(i, model, {i: i_0}, set(), {i}))
            # Prints: +005

        :param var: The variable for which to extract a solution from the model.
        :param model: The model containing the solution.
        :param fresh_var_map: A map from variables to fresh symbols for "length" and
                              "int" variables.
        :param length_vars: The set of "length" variables.
        :param int_vars: The set of "int" variables.
        :return: A :class:`~isla.derivation_tree.DerivationTree` object corresponding
                 to the solution in :code:`model`.
        """

        f_flex_vars = self.extract_model_value_flexible_var
        f_int_vars = partial(self.extract_model_value_int_var, f_flex_vars)
        f_length_vars = partial(self.extract_model_value_length_var, f_int_vars)

        return f_length_vars(var, model, fresh_var_map, length_vars, int_vars)

    @typechecked
    def extract_model_value_length_var(
        self,
        fallback: ExtractModelValueFallbackType,
        var: Variable,
        model: z3.ModelRef,
        fresh_var_map: Mapping[Variable, z3.ExprRef],
        length_vars: Set[Variable],
        int_vars: Set[Variable],
    ) -> Maybe[DerivationTree]:
        """
        Addresses the case of length variables from
        :meth:`~isla.repair_solver.RepairSolver.extract_model_value`.

        :param fallback: The function to call if this function is not responsible.
        :param var: See :meth:`~isla.repair_solver.RepairSolver.extract_model_value`.
        :param model: See :meth:`~isla.repair_solver.RepairSolver.extract_model_value`.
        :param fresh_var_map: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :param length_vars: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :param int_vars: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :return: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        """
        if var not in length_vars:
            return fallback(var, model, fresh_var_map, length_vars, int_vars)

        return create_fixed_length_tree(
            start=var.n_type,
            canonical_grammar=self.canonical_grammar,
            target_length=model[fresh_var_map[var]].as_long(),
        )

    @typechecked
    def extract_model_value_int_var(
        self,
        fallback: ExtractModelValueFallbackType,
        var: Variable,
        model: z3.ModelRef,
        fresh_var_map: Mapping[Variable, z3.ExprRef],
        length_vars: Set[Variable],
        int_vars: Set[Variable],
    ) -> Maybe[DerivationTree]:
        """
        Addresses the case of int variables from
        :meth:`~isla.solver.RepairSolver.extract_model_value`.

        :param fallback: The function to call if this function is not responsible.
        :param var: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :param model: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :param fresh_var_map: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :param length_vars: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :param int_vars: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :return: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        """
        if var not in int_vars:
            return fallback(var, model, fresh_var_map, length_vars, int_vars)

        str_model_value = model[fresh_var_map[var]].as_string()

        try:
            int_model_value = int(str_model_value)
        except ValueError:
            raise RuntimeError(f"Value {str_model_value} for {var} is not a number")

        var_type = var.n_type

        try:
            return result_to_maybe(
                self.parse(
                    str(int_model_value),
                    var_type,
                    silent=True,
                )
            )
        except SyntaxError:
            # This may happen, e.g, with padded values: Only "01" is a valid
            # solution, but not "1". Similarly, a grammar may expect "+1", but
            # "1" is returned by the solver. We support the number format
            # `[+-]0*<digits>`. Whenever the grammar recognizes at least this
            # set for the nonterminal in question, we return a derivation tree.
            # Otherwise, a RuntimeError is raised.

            z3_solver = z3.Solver()
            z3_solver.set("timeout", 300)

            maybe_plus_re = z3.Option(z3.Re("+"))
            zeroes_padding_re = z3.Star(z3.Re("0"))

            # TODO: Ensure symbols are fresh
            maybe_plus_var = z3.String("__plus")
            zeroes_padding_var = z3.String("__padding")

            z3_solver.add(z3.InRe(maybe_plus_var, maybe_plus_re))
            z3_solver.add(z3.InRe(zeroes_padding_var, zeroes_padding_re))

            z3_solver.add(
                z3.InRe(
                    z3.Concat(
                        maybe_plus_var if int_model_value >= 0 else z3.StringVal("-"),
                        zeroes_padding_var,
                        z3.StringVal(
                            str_model_value
                            if int_model_value >= 0
                            else str(-int_model_value)
                        ),
                    ),
                    self.extract_regular_expression(var.n_type),
                )
            )

            if z3_solver.check() != z3.sat:
                LOGGER.warning(
                    RuntimeError(
                        "Could not parse a numeric solution "
                        + f"({str_model_value}) for variable "
                        + f"{var} of type '{var.n_type}'; try "
                        + "running the solver without optimized Z3 queries or make "
                        + "sure that ranges are restricted to syntactically valid "
                        + "ones (according to the grammar).",
                    )
                )

            return result_to_maybe(
                self.parse(
                    (
                        z3_solver.model()[maybe_plus_var].as_string()
                        if int_model_value >= 0
                        else "-"
                    )
                    + z3_solver.model()[zeroes_padding_var].as_string()
                    + (
                        str_model_value
                        if int_model_value >= 0
                        else str(-int_model_value)
                    ),
                    var.n_type,
                )
            )

    @typechecked
    def extract_model_value_flexible_var(
        self,
        var: Variable,
        model: z3.ModelRef,
        _fresh_var_map,
        _length_vars,
        _int_vars,
    ) -> Maybe[DerivationTree]:
        """
        Addresses the case of "flexible" variables from
        :meth:`~isla.solver.RepairSolver.extract_model_value`.

        :param var: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :param model: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        :param _fresh_var_map: Not needed.
        :param _length_vars: Not needed.
        :param _int_vars: Not needed.
        :return: See :meth:`~isla.solver.RepairSolver.extract_model_value`.
        """

        return result_to_maybe(
            self.parse(
                smt_string_val_to_string(model[z3.String(var.name)]),
                var.n_type,
            )
        )


@typechecked
def rename_instantiated_variables_in_smt_formulas(
    smt_formulas: Iterable[SMTFormula],
) -> Tuple[SMTFormula, ...]:
    """
    TODO: Document, polish.

    :param smt_formulas:
    :param value_suggestions:
    :return:
    """

    resulting_smt_formulas = ()

    for smt_formula in smt_formulas:
        variable_substitution: frozendict[Variable, BoundVariable] = frozendict(
            {
                var: BoundVariable(
                    f"{tree.value}_{tree.id}",
                    eassert(var.n_type, var.n_type == tree.value),
                )
                for var, tree in smt_formula.substitutions.items()
            }
        )

        def apply_substitution(formula: SMTFormula) -> SMTFormula:
            new_smt_formula = cast(
                z3.BoolRef,
                z3_subst(
                    formula.formula,
                    {
                        var.to_smt(): new_var.to_smt()
                        for var, new_var in variable_substitution.items()
                    },
                ),
            )

            new_substitutions = {
                variable_substitution.get(var, var): val
                for var, val in formula.substitutions.items()
            }

            new_instantiated_variables = FrozenOrderedSet(
                tuple(
                    variable_substitution.get(v, v)
                    for v in formula.instantiated_variables
                )
            )

            new_free_variables = {
                variable_substitution.get(v, v) for v in formula.free_variables_
            }

            return SMTFormula(
                new_smt_formula,
                *new_free_variables,
                instantiated_variables=new_instantiated_variables,
                substitutions=new_substitutions,
            )

        resulting_smt_formulas += (apply_substitution(smt_formula),)

    return resulting_smt_formulas


@typechecked
def infer_variable_contexts(
    variables: FrozenOrderedSet[Variable], smt_formulas: Sequence[SMTFormula]
) -> frozendict[str, FrozenOrderedSet[Variable]]:
    """
    Divides the given variables into

    1. those that occur only in :code:`length(...)` contexts,
    2. those that occur only in :code:`str.to.int(...)` contexts, and
    3. "flexible" constants occurring in other/various contexts.

    >>> x = Variable("x", "<X>")
    >>> y = Variable("y", "<Y>")

    Two variables in an arbitrary context.

    >>> from isla.z3_helpers import z3_eq
    >>> f = SMTFormula(z3_eq(x.to_smt(), y.to_smt()), x, y)
    >>> contexts = infer_variable_contexts(FrozenOrderedSet((x, y)), (f,))
    >>> deep_str(contexts["length"])
    '{}'
    >>> deep_str(contexts["int"])
    '{}'
    >>> contexts["flexible"] == {Variable("x", "<X>"), Variable("y", "<Y>")}
    True

    Variable x occurs in a length context, variable y in an arbitrary one.

    >>> f = SMTFormula(
    ...     z3.And(
    ...         z3.Length(x.to_smt()) > z3.IntVal(10),
    ...         z3_eq(y.to_smt(), z3.StringVal("y"))),
    ...     x, y)
    >>> print(deep_str(infer_variable_contexts(FrozenOrderedSet((x, y)), (f,))))
    {'length': {x}, 'int': {}, 'flexible': {y}}

    Variable x occurs in a length context, y does not occur.

    >>> f = SMTFormula(z3.Length(x.to_smt()) > z3.IntVal(10), x)
    >>> print(deep_str(infer_variable_contexts(FrozenOrderedSet((x, y)), (f,))))
    {'length': {x}, 'int': {}, 'flexible': {y}}

    Variables x and y both occur in a length context.

    >>> f = SMTFormula(z3.Length(x.to_smt()) > z3.Length(y.to_smt()), x, y)
    >>> contexts = infer_variable_contexts(FrozenOrderedSet((x, y)), (f,))
    >>> contexts["length"] == {Variable("x", "<X>"), Variable("y", "<Y>")}
    True
    >>> deep_str(contexts["int"])
    '{}'
    >>> deep_str(contexts["flexible"])
    '{}'

    Variable x occurs in a :code:`str.to.int` context.

    >>> f = SMTFormula(z3.StrToInt(x.to_smt()) > z3.IntVal(17), x)
    >>> print(deep_str(infer_variable_contexts(FrozenOrderedSet((x,)), (f,))))
    {'length': {}, 'int': {x}, 'flexible': {}}

    Now, x also occurs in a different context; it's "flexible" now.

    >>> f = SMTFormula(
    ...     z3.And(
    ...         z3.StrToInt(x.to_smt()) > z3.IntVal(17),
    ...         z3_eq(x.to_smt(), z3.StringVal("17"))),
    ...     x)
    >>> print(deep_str(infer_variable_contexts(FrozenOrderedSet((x,)), (f,))))
    {'length': {}, 'int': {}, 'flexible': {x}}

    :param variables: The constants to divide/filter from.
    :param smt_formulas: The SMT formulas to consider in the filtering.
    :return: A pair of constants occurring in `str.len` contexts, and the
    remaining ones. The union of both sets equals `variables`, and both sets
    are disjoint.
    """

    parent_relationships = reduce(
        merge_dict_of_sets,
        [parent_relationships_in_z3_expr(formula.formula) for formula in smt_formulas],
        {},
    )

    contexts: frozendict[Variable, FrozenOrderedSet[int]] = frozendict(
        {
            var: FrozenOrderedSet(
                tuple(
                    expr.decl().kind()
                    for expr in parent_relationships.get(var.to_smt(), set())
                )
            )
            or {-1}
            for var in variables
        }
    )

    # The set `length_vars` consists of all variables that only occur in
    # `str.len(...)` context.
    length_vars: FrozenOrderedSet[Variable] = FrozenOrderedSet(
        tuple(
            var
            for var in variables
            if all(context == z3.Z3_OP_SEQ_LENGTH for context in contexts[var])
        )
    )

    # The set `int_vars` consists of all variables that only occur in
    # `str.to.int(...)` context.
    int_vars: FrozenOrderedSet[Variable] = FrozenOrderedSet(
        tuple(
            var
            for var in variables
            if all(context == z3.Z3_OP_STR_TO_INT for context in contexts[var])
        )
    )

    # "Flexible" variables are the remaining ones.
    flexible_vars = variables.difference(length_vars).difference(int_vars)

    return frozendict(
        {"length": length_vars, "int": int_vars, "flexible": flexible_vars}
    )


@typechecked
def create_fixed_length_tree(
    start: DerivationTree | str,
    canonical_grammar: FrozenCanonicalGrammar,
    target_length: int,
) -> Maybe[DerivationTree]:
    """
    TODO: Document, polish.

    >>> grammar = {
    ...     "<start>": ["<X>"],
    ...     "<X>": ["x", "x<X>"],
    ... }
    >>> tree = create_fixed_length_tree("<X>", frozen_canonical(grammar), 5)
    >>> tree
    <Some: xxxxx>
    >>> tree.map(lambda t: t.value)
    <Some: <X>>

    :param start:
    :param canonical_grammar:
    :param target_length:
    :return:
    """

    nullable = compute_nullable_nonterminals(canonical_grammar)
    start = DerivationTree(start) if isinstance(start, str) else start
    stack: List[Tuple[DerivationTree, int, Tuple[Tuple[Path, DerivationTree], ...]]] = [
        (start, int(start.value not in nullable), (((), start),)),
    ]

    while stack:
        tree, curr_len, open_leaves = stack.pop()

        if not open_leaves:
            if curr_len == target_length:
                return Some(tree)
            else:
                continue

        if curr_len > target_length:
            continue

        idx: int
        path: Path
        leaf: DerivationTree
        for idx, (path, leaf) in reversed(list(enumerate(open_leaves))):
            terminal_expansions, expansions = get_expansions(
                leaf.value, canonical_grammar
            )

            if terminal_expansions:
                expansions.append(random.choice(terminal_expansions))

            # Only choose one random terminal expansion; keep all nonterminal expansions
            expansions = sorted(
                expansions,
                key=lambda expansion: len(
                    [elem for elem in expansion if is_nonterminal(elem)]
                ),
            )

            for expansion in reversed(expansions):
                new_children = tuple(
                    [
                        DerivationTree(elem, None if is_nonterminal(elem) else ())
                        for elem in expansion
                    ]
                )

                expanded_tree = tree.replace_path(
                    path,
                    DerivationTree(
                        leaf.value,
                        new_children,
                    ),
                )

                stack.append(
                    (
                        expanded_tree,
                        curr_len
                        + sum(
                            [
                                (
                                    len(child.value)
                                    if child.children == ()
                                    else (1 if child.value not in nullable else 0)
                                )
                                for child in new_children
                            ]
                        )
                        - int(leaf.value not in nullable),
                        open_leaves[:idx]
                        + tuple(
                            [
                                (path + (child_idx,), new_child)
                                for child_idx, new_child in enumerate(new_children)
                                if is_nonterminal(new_child.value)
                            ]
                        )
                        + open_leaves[idx + 1 :],
                    )
                )

    LOGGER.warning(
        "Could not create a tree of length %d with start nonterminal/tree %s",
        target_length,
        start,
    )
    return Nothing


@typechecked
def subtree_solutions(
    solution: Mapping[DerivationTree, DerivationTree]
) -> frozendict[DerivationTree, DerivationTree]:
    """
    TODO: Polish, document.

    :param solution:
    :return:
    """

    solution_with_subtrees: frozendict[DerivationTree, DerivationTree] = frozendict({})

    for orig, subst in solution.items():
        assert isinstance(
            orig, DerivationTree
        ), f"Expected a DerivationTree, given: {type(orig).__name__}"

        # Note: It can happen that a path in the original tree is not valid in the
        #       substitution, e.g., if we happen to replace a larger with a smaller
        #       tree.
        for path, tree in [
            (p, t)
            for p, t in orig.paths()
            if t not in solution_with_subtrees and subst.is_valid_path(p)
        ]:
            solution_with_subtrees = solution_with_subtrees.set(
                tree, subst.get_subtree(path)
            )

    return solution_with_subtrees


def collect_tree_substitutions_in_smt_formulas(
    smt_formulas: Iterable[SMTFormula],
) -> frozendict[Variable, DerivationTree]:
    """
    Collects all tree substitutions from the given SMT formulas.

    :param smt_formulas: The SMT formulas to collect the substitutions from.
    :return: A mapping from variables to their corresponding derivation
        trees collected from the given SMT formulas.
    """

    return reduce(
        operator.or_,
        (smt_formula.substitutions for smt_formula in smt_formulas),
        frozendict({}),
    )


def collect_variables_in_smt_formulas(
    smt_formulas: Iterable[SMTFormula],
) -> FrozenOrderedSet[Variable]:
    """
    Collects all (free and instantiated) variables in the given SMT formulas.

    :param smt_formulas: The SMT formulas to collect the variables from.
    :return: A set of variables collected from the given SMT formulas.
    """

    return reduce(
        operator.or_,
        (
            smt_formula.free_variables() | smt_formula.instantiated_variables
            for smt_formula in smt_formulas
        ),
        FrozenOrderedSet(),
    )


@typechecked
def auto_subst_and_eval_is_false(formula: Formula) -> bool:
    class AutoSubstEvalVisitor(FormulaVisitor):
        @typechecked
        def __init__(self):
            super().__init__()
            self.problems: Tuple[SMTFormula, ...] = ()

        @typechecked
        def visit_smt_formula(self, formula: SMTFormula):
            if formula.auto_eval or formula.auto_subst:
                self.problems += (formula,)

    visitor = AutoSubstEvalVisitor()
    formula.accept(visitor)

    if visitor.problems:
        LOGGER.warning(
            "Found formulas with auto_eval or auto_subst set to True:\n%s",
            "\n".join(map(str, visitor.problems)),
        )

    return not len(visitor.problems)


def add_already_matched(
    f: QuantifiedFormula, trees: DerivationTree | Iterable[DerivationTree]
) -> QuantifiedFormula:
    # TODO this is a hack: We unify trees by the root's ID and structure.
    #      The implemented standard is to register tree IDs. Either, we
    #      don't need this hack, or we should investigate if we should
    #      change something so that we no longer need this hack, or we
    #      should consider turning the hack into the proper standard.

    return type(f)(
        f.bound_variable,
        f.in_variable,
        f.inner_formula,
        f.bind_expression,
        (
            f.already_matched
            | (
                FrozenOrderedSet([trees.structural_hash()])
                if isinstance(trees, DerivationTree)
                else FrozenOrderedSet(
                    [hash((tree.id, tree.structural_hash())) for tree in trees]
                )
            )
        ),
    )
