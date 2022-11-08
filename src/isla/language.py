# Copyright © 2022 CISPA Helmholtz Center for Information Security.
# Author: Dominic Steinhöfel.
#
# This file is part of ISLa.
#
# ISLa is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# ISLa is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with ISLa.  If not, see <http://www.gnu.org/licenses/>.

import copy
import dataclasses
import functools
import itertools
import logging
import operator
import pickle
import re
import string
from abc import ABC, abstractmethod
from dataclasses import dataclass
from functools import reduce, lru_cache
from typing import (
    Union,
    List,
    Optional,
    Dict,
    Tuple,
    Callable,
    cast,
    Set,
    Iterable,
    Sequence,
    Protocol,
    TypeVar,
    MutableSet,
)

import antlr4
import z3
from antlr4 import InputStream, RuleContext, ParserRuleContext
from antlr4.Token import CommonToken
from grammar_graph import gg
from orderedset import OrderedSet
from z3 import Z3Exception

import isla.mexpr_parser.MexprParserListener as MexprParserListener
from isla.bnf import bnfListener
from isla.bnf.bnfLexer import bnfLexer
from isla.bnf.bnfParser import bnfParser
from isla.derivation_tree import DerivationTree
from isla.fuzzer import GrammarCoverageFuzzer
from isla.helpers import (
    RE_NONTERMINAL,
    is_nonterminal,
    assertions_activated,
    canonical,
    nth_occ,
    srange,
    grammar_to_mutable,
    list_set,
    is_prefix,
    Maybe,
    chain_functions,
    eassert,
    Exceptional,
    instantiate_escaped_symbols,
)
from isla.helpers import (
    replace_line_breaks,
    delete_unreachable,
    powerset,
    grammar_to_immutable,
    nested_list_to_tuple,
)
from isla.isla_language import IslaLanguageListener
from isla.isla_language.IslaLanguageLexer import IslaLanguageLexer
from isla.isla_language.IslaLanguageParser import IslaLanguageParser
from isla.mexpr_lexer.MexprLexer import MexprLexer
from isla.mexpr_parser.MexprParser import MexprParser
from isla.parser import EarleyParser, PEGParser
from isla.type_defs import Path, Grammar, ImmutableGrammar, ImmutableList, Pair
from isla.z3_helpers import (
    is_valid,
    z3_push_in_negations,
    z3_subst,
    get_symbols,
    smt_expr_to_str,
)

SolutionState = List[Tuple["Constant", "Formula", "DerivationTree"]]
Assignment = Tuple["Constant", "Formula", "DerivationTree"]

language_core_logger = logging.getLogger("isla-language-core")

# The below is an important optimization: In Z3's ExprRef, __eq__ is overloaded
# to return a *formula* (an equation). This is quite costly, and automatically
# called when putting ExprRefs into hash tables. To resort to a structural
# comparison, we replace the __eq__ method by AstRef's __eq__, which does perform
# a structural comparison.
z3.ExprRef.__eq__ = z3.AstRef.__eq__


class Variable:
    NUMERIC_NTYPE = "NUM"

    def __init__(self, name: str, n_type: str):
        self.name = name
        self.n_type = n_type

    def to_smt(self):
        return z3.String(self.name)

    def is_numeric(self):
        return self.n_type == Constant.NUMERIC_NTYPE

    def __eq__(self, other):
        return type(self) is type(other) and (self.name, self.n_type) == (
            other.name,
            other.n_type,
        )

    def __hash__(self):
        return hash((type(self).__name__, self.name, self.n_type))

    def __repr__(self):
        return f'{type(self).__name__}("{self.name}", "{self.n_type}")'

    def __str__(self):
        return self.name


class Constant(Variable):
    def __init__(self, name: str, n_type: str):
        """
        A constant is a "free variable" in a formula.

        :param name: The name of the constant.
        :param n_type: The nonterminal type of the constant, e.g., "<var>".
        """
        super().__init__(name, n_type)


class BoundVariable(Variable):
    def __init__(self, name: str, n_type: str):
        """
        A variable bound by a quantifier.

        :param name: The name of the variable.
        :param n_type: The nonterminal type of the variable, e.g., "<var>".
        """
        super().__init__(name, n_type)

    def __add__(self, other: Union[str, "BoundVariable"]) -> "BindExpression":
        assert isinstance(other, str) or isinstance(other, BoundVariable)
        return BindExpression(self, other)


class DummyVariable(BoundVariable):
    """A variable of which only its nonterminal is of interest (primarily for BindExpressions)."""

    cnt = 0

    def __init__(self, n_type: str):
        super().__init__(f"DUMMY_{DummyVariable.cnt}", n_type)
        self.is_nonterminal = bool(is_nonterminal(n_type))
        DummyVariable.cnt += 1

    def __str__(self):
        return self.n_type


class BindExpression:
    def __init__(self, *bound_elements: Union[str, BoundVariable, List[str]]):
        self.bound_elements: List[BoundVariable | List[BoundVariable]] = []
        for bound_elem in bound_elements:
            if isinstance(bound_elem, BoundVariable):
                self.bound_elements.append(bound_elem)
                continue

            if isinstance(bound_elem, list):
                if all(isinstance(list_elem, Variable) for list_elem in bound_elem):
                    self.bound_elements.append(bound_elem)
                    continue

                assert all(isinstance(list_elem, str) for list_elem in bound_elem)

                self.bound_elements.append(
                    [
                        DummyVariable(token)
                        for token in re.split(RE_NONTERMINAL, "".join(bound_elem))
                        if token
                    ]
                )
                continue

            self.bound_elements.extend(
                [
                    DummyVariable(token)
                    for token in re.split(RE_NONTERMINAL, bound_elem)
                    if token
                ]
            )

        self.prefixes: Dict[
            str, List[Tuple[DerivationTree, Dict[BoundVariable, Path]]]
        ] = {}
        self.__flattened_elements: Dict[str, Tuple[Tuple[BoundVariable, ...], ...]] = {}

    def __add__(self, other: Union[str, "BoundVariable"]) -> "BindExpression":
        assert type(other) == str or type(other) == BoundVariable
        result = BindExpression(*self.bound_elements)
        result.bound_elements.append(other)
        return result

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return BindExpression(
            *[
                elem if isinstance(elem, list) else subst_map.get(elem, elem)
                for elem in self.bound_elements
            ]
        )

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        # Not isinstance(var, BoundVariable) since we want to exclude dummy variables
        return OrderedSet(
            [var for var in self.bound_elements if type(var) is BoundVariable]
        )

    def all_bound_variables(self, grammar: Grammar) -> OrderedSet[BoundVariable]:
        # Includes dummy variables
        return OrderedSet(
            [
                var
                for alternative in flatten_bound_elements(
                    nested_list_to_tuple(self.bound_elements),
                    grammar_to_immutable(grammar),
                    in_nonterminal=None,
                )
                for var in alternative
                if isinstance(var, BoundVariable)
            ]
        )

    def to_tree_prefix(
        self, in_nonterminal: str, grammar: Grammar
    ) -> List[Tuple[DerivationTree, Dict[BoundVariable, Path]]]:
        if in_nonterminal in self.prefixes:
            cached = self.prefixes[in_nonterminal]
            return [(opt[0].new_ids(), opt[1]) for opt in cached]

        result: List[Tuple[DerivationTree, Dict[BoundVariable, Path]]] = []
        immutable_grammar = grammar_to_immutable(grammar)

        for bound_elements in flatten_bound_elements(
            nested_list_to_tuple(self.bound_elements),
            immutable_grammar,
            in_nonterminal=in_nonterminal,
        ):
            BindExpression.__combination_to_tree_prefix(
                bound_elements, in_nonterminal, immutable_grammar
            ).if_present(lambda r: result.append(r))

        self.prefixes[in_nonterminal] = result
        return result

    @staticmethod
    def __combination_to_tree_prefix(
        bound_elements: Tuple[BoundVariable, ...],
        in_nonterminal: str,
        immutable_grammar: ImmutableGrammar,
    ) -> Maybe[Tuple[DerivationTree, Dict[BoundVariable, Path]]]:
        flattened_bind_expr_str = "".join(
            map(
                lambda elem: f"{{{elem.n_type} {elem.name}}}"
                if type(elem) == BoundVariable
                else str(elem),
                bound_elements,
            )
        )

        maybe_tree = parse(flattened_bind_expr_str, in_nonterminal, immutable_grammar)
        if not maybe_tree.is_present():
            language_core_logger.warning(
                'Parsing match expression string "%s" caused a syntax error. If this is'
                + " not a test case where this behavior is intended, it should probably"
                + " be investigated.",
                flattened_bind_expr_str,
            )
            return Maybe.nothing()

        tree = maybe_tree.get()

        assert tree.value == in_nonterminal

        split_bound_elements = []
        dummy_var_map: Dict[DummyVariable, List[DummyVariable]] = {}
        for elem in bound_elements:
            if not isinstance(elem, DummyVariable) or is_nonterminal(elem.n_type):
                split_bound_elements.append(elem)
                continue

            new_dummies = (
                [DummyVariable(char) for char in elem.n_type] if elem.n_type else [elem]
            )
            split_bound_elements.extend(new_dummies)
            dummy_var_map[elem] = new_dummies

        match_expr_tree = tree
        match_expr_matches: Dict[BoundVariable, Path] = {}
        skip_paths_below = set()
        remaining_bound_elements = list(split_bound_elements)

        def search(path: Path, child: DerivationTree):
            nonlocal match_expr_tree
            if any(
                len(path) > len(skip_path) and path[: len(skip_path)] == skip_path
                for skip_path in skip_paths_below
            ):
                return

            if (
                len(child.children) == 7
                and child.children[0].value == "{"
                and child.children[1].value == "<LANGLE>"
            ):
                assert is_nonterminal(child.value)
                skip_paths_below.add(path)
                match_expr_tree = match_expr_tree.replace_path(
                    path, DerivationTree(child.value, None)
                )
                var_n_type = "<" + child.children[2].value + ">"
                var_name = str(child.children[5])

                var = next(
                    var for var in remaining_bound_elements if var.name == var_name
                )
                assert var.n_type == var_n_type
                remaining_bound_elements.remove(var)
                match_expr_matches[var] = path
            elif len(child.children) == 3 and child.children[0].value == "<LANGLE>":
                assert is_nonterminal(child.value)
                skip_paths_below.add(path)
                match_expr_tree = match_expr_tree.replace_path(
                    path, DerivationTree(child.value, None)
                )
                var_n_type = "<" + child.children[1].value + ">"

                var = next(
                    var for var in remaining_bound_elements if var.n_type == var_n_type
                )
                remaining_bound_elements.remove(var)
                match_expr_matches[var] = path
            elif str(child) == child.value or not str(child):
                # TODO: Check if `()` is always the right choice for the children
                match_expr_tree = match_expr_tree.replace_path(
                    path,
                    DerivationTree(
                        child.value,
                        ()
                        # None if is_nonterminal(child.value) else ()
                    ),
                )
                skip_paths_below.add(path)

                for char in (
                    [""]
                    if not str(child)
                    else (
                        [child.value]
                        if is_nonterminal(child.value)
                        else list(child.value)
                    )
                ):
                    var = (
                        Maybe.from_iterator(
                            var
                            for var in remaining_bound_elements
                            if var.n_type == char
                        )
                        .if_present(
                            lambda var: eassert(var, isinstance(var, DummyVariable))
                        )
                        .if_present(remaining_bound_elements.remove)
                        .orelse(lambda: DummyVariable(""))
                        .get()
                    )

                    match_expr_matches[var] = path

        tree.traverse(
            search,
            # abort_condition=lambda p, t: not remaining_bound_elements
        )

        # In the result, we have to combine all terminals that point to the same path.
        consolidated_matches = consolidate_match_expression_matches(match_expr_matches)

        assert all(
            var in consolidated_matches
            for var in bound_elements
            if not isinstance(var, DummyVariable)
        )
        assert all(
            any(
                len(match_path) <= len(leaf_path)
                and leaf_path[: len(match_path)] == match_path
                for match_path in consolidated_matches.values()
            )
            for leaf_path, _ in tree.leaves()
        )

        return Maybe((match_expr_tree, consolidated_matches))

    def match(
        self, tree: DerivationTree, grammar: Grammar
    ) -> Optional[Dict[BoundVariable, Tuple[Path, DerivationTree]]]:
        for mexpr_tree, mexpr_var_matches in self.to_tree_prefix(tree.value, grammar):
            possible_match = match(tree, mexpr_tree, mexpr_var_matches)
            if possible_match:
                return possible_match

        return None

    def __repr__(self):
        return f'BindExpression({", ".join(map(repr, self.bound_elements))})'

    def __str__(self):
        return "".join(
            map(
                lambda e: f"{str(e)}"
                if isinstance(e, str)
                else ("[" + "".join(map(str, e)) + "]")
                if isinstance(e, list)
                else (
                    f"{{{e.n_type} {str(e)}}}"
                    if not isinstance(e, DummyVariable)
                    else str(e)
                ),
                self.bound_elements,
            )
        )

    @staticmethod
    def __dummy_vars_to_str(
        elem: BoundVariable | List[BoundVariable],
    ) -> str | BoundVariable | List[str | BoundVariable]:
        if isinstance(elem, DummyVariable):
            return elem.n_type

        if isinstance(elem, list):
            return list(map(BindExpression.__dummy_vars_to_str, elem))

        return elem

    def __hash__(self):
        return hash(
            tuple(
                [
                    tuple(e) if isinstance(e, list) else e
                    for e in map(
                        BindExpression.__dummy_vars_to_str, self.bound_elements
                    )
                ]
            )
        )

    def __eq__(self, other):
        return isinstance(other, BindExpression) and list(
            map(BindExpression.__dummy_vars_to_str, self.bound_elements)
        ) == list(map(BindExpression.__dummy_vars_to_str, other.bound_elements))


def consolidate_match_expression_matches(
    match_expr_matches: Dict[BoundVariable, Path]
) -> Dict[BoundVariable, Path]:
    """
    Groups together `DummyVariable`s in `match_expr_matches` that point to the same path.
    This is needed since we have tosplit dummy variables into individual characters when
    creating prefix trees for match expressions.

    :param match_expr_matches: The matches to consolidate.
    :return: The consolidated matches; all paths are unique.
    """
    consolidated_matches: Dict[BoundVariable, Path] = {}
    last_dummy_elem = None
    last_dummy_path = None
    for var, path in match_expr_matches.items():
        if not isinstance(var, DummyVariable) or is_nonterminal(var.n_type):
            consolidated_matches[var] = path
            continue

        if last_dummy_path is None or last_dummy_path != path:
            last_dummy_path = path
            last_dummy_elem = var
            consolidated_matches[var] = path
            continue

        del consolidated_matches[last_dummy_elem]
        new_dummy = DummyVariable(last_dummy_elem.n_type + var.n_type)
        consolidated_matches[new_dummy] = path
        last_dummy_elem = new_dummy
    return consolidated_matches


@functools.lru_cache(10)
def grammar_to_match_expr_grammar(
    start_symbol: str, grammar: ImmutableGrammar
) -> Grammar:
    new_grammar = grammar_to_mutable(grammar)
    if start_symbol != "<start>":
        new_grammar["<start>"] = [start_symbol]
        delete_unreachable(new_grammar)

    def fresh_nonterminal(suggestion: str) -> str:
        if suggestion[1:-1] not in new_grammar:
            return suggestion
        idx = 0
        while f"<{suggestion[1:-1]}_{idx}>" in new_grammar:
            idx += 1
        return f"<{suggestion[1:-1]}_{idx}>"

    id_nonterminal = fresh_nonterminal("<ID>")
    letter_nonterminal = fresh_nonterminal("<LETTER>")
    letter_or_digit_nonterminal = fresh_nonterminal("<LETTER_OR_DIGIT>")
    id_chars = fresh_nonterminal("<id_chars>")
    langle_nonterminal = fresh_nonterminal("<LANGLE>")
    rangle_nonterminal = fresh_nonterminal("<RANGLE>")

    for nonterminal in new_grammar:
        if nonterminal == "<start>":
            continue
        new_grammar[nonterminal].insert(
            0, f"{{{langle_nonterminal}{nonterminal[1:-1]}{rangle_nonterminal} <ID>}}"
        )
        new_grammar[nonterminal].insert(
            0, f"{langle_nonterminal}{nonterminal[1:-1]}{rangle_nonterminal}"
        )

    new_grammar[langle_nonterminal] = ["<"]
    new_grammar[rangle_nonterminal] = [">"]
    new_grammar[letter_nonterminal] = srange(string.ascii_letters)
    new_grammar[letter_or_digit_nonterminal] = srange(string.digits) + srange(
        string.ascii_letters
    )
    new_grammar[id_chars] = [
        f"{letter_or_digit_nonterminal}{id_chars}",
        f"_{id_chars}",
        f"-{id_chars}",
        "",
    ]
    new_grammar[id_nonterminal] = [
        f"${letter_nonterminal}{id_chars}",
        f"{letter_nonterminal}{id_chars}",
    ]

    return new_grammar


class FormulaVisitor:
    def __init__(self):
        self.in_negation_scope = False

    def do_continue(self, formula: "Formula") -> bool:
        """If this returns False, this formula should not call the visit methods for
        its children."""
        return True

    def toggle_negation_scope(self) -> None:
        self.in_negation_scope = not self.in_negation_scope

    def visit_predicate_formula(self, formula: "StructuralPredicateFormula"):
        pass

    def visit_semantic_predicate_formula(self, formula: "SemanticPredicateFormula"):
        pass

    def visit_negated_formula(self, formula: "NegatedFormula"):
        pass

    def visit_conjunctive_formula(self, formula: "ConjunctiveFormula"):
        pass

    def visit_disjunctive_formula(self, formula: "DisjunctiveFormula"):
        pass

    def visit_smt_formula(self, formula: "SMTFormula"):
        pass

    def visit_exists_formula(self, formula: "ExistsFormula"):
        pass

    def visit_forall_formula(self, formula: "ForallFormula"):
        pass

    def visit_exists_int_formula(self, formula: "ExistsIntFormula"):
        pass

    def visit_forall_int_formula(self, formula: "ForallIntFormula"):
        pass


class FormulaTransformer(ABC):
    def __init__(self):
        self.in_negation_scope = False

    def toggle_negation_scope(self) -> None:
        self.in_negation_scope = not self.in_negation_scope

    @abstractmethod
    def transform_predicate_formula(
        self, formula: "StructuralPredicateFormula"
    ) -> "Formula":
        raise NotImplementedError()

    @abstractmethod
    def transform_semantic_predicate_formula(
        self, formula: "SemanticPredicateFormula"
    ) -> "Formula":
        raise NotImplementedError()

    @abstractmethod
    def transform_negated_formula(self, formula: "NegatedFormula") -> "Formula":
        raise NotImplementedError()

    @abstractmethod
    def transform_conjunctive_formula(self, formula: "ConjunctiveFormula") -> "Formula":
        raise NotImplementedError()

    @abstractmethod
    def transform_disjunctive_formula(self, formula: "DisjunctiveFormula") -> "Formula":
        raise NotImplementedError()

    @abstractmethod
    def transform_smt_formula(self, formula: "SMTFormula") -> "Formula":
        raise NotImplementedError()

    @abstractmethod
    def transform_exists_formula(self, formula: "ExistsFormula") -> "Formula":
        raise NotImplementedError()

    @abstractmethod
    def transform_forall_formula(self, formula: "ForallFormula") -> "Formula":
        raise NotImplementedError()

    @abstractmethod
    def transform_exists_int_formula(self, formula: "ExistsIntFormula") -> "Formula":
        raise NotImplementedError()

    @abstractmethod
    def transform_forall_int_formula(self, formula: "ForallIntFormula") -> "Formula":
        raise NotImplementedError()


class NoopFormulaTransformer(FormulaTransformer):
    def transform_predicate_formula(
        self, formula: "StructuralPredicateFormula"
    ) -> "Formula":
        return formula

    def transform_semantic_predicate_formula(
        self, formula: "SemanticPredicateFormula"
    ) -> "Formula":
        return formula

    def transform_negated_formula(self, formula: "NegatedFormula") -> "Formula":
        return formula

    def transform_conjunctive_formula(self, formula: "ConjunctiveFormula") -> "Formula":
        return formula

    def transform_disjunctive_formula(self, formula: "DisjunctiveFormula") -> "Formula":
        return formula

    def transform_smt_formula(self, formula: "SMTFormula") -> "Formula":
        return formula

    def transform_exists_formula(self, formula: "ExistsFormula") -> "Formula":
        return formula

    def transform_forall_formula(self, formula: "ForallFormula") -> "Formula":
        return formula

    def transform_exists_int_formula(self, formula: "ExistsIntFormula") -> "Formula":
        return formula

    def transform_forall_int_formula(self, formula: "ForallIntFormula") -> "Formula":
        return formula


class Formula(ABC):
    # def __getstate__(self):
    #     return {f: pickle.dumps(v) for f, v in self.__dict__.items()} | {"cls": type(self).__name__}
    #
    # def __setstate__(self, state):
    #     pass

    @abstractmethod
    def bound_variables(self) -> OrderedSet[BoundVariable]:
        """Non-recursive: Only non-empty for quantified formulas"""
        raise NotImplementedError()

    @abstractmethod
    def free_variables(self) -> OrderedSet[Variable]:
        """Recursive."""
        raise NotImplementedError()

    @abstractmethod
    def tree_arguments(self) -> OrderedSet[DerivationTree]:
        """Trees that were substituted for variables."""
        raise NotImplementedError()

    @abstractmethod
    def substitute_variables(self, subst_map: Dict[Variable, Variable]) -> "Formula":
        raise NotImplementedError()

    @abstractmethod
    def substitute_expressions(
        self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]
    ) -> "Formula":
        raise NotImplementedError()

    @abstractmethod
    def accept(self, visitor: FormulaVisitor):
        raise NotImplementedError()

    @abstractmethod
    def transform(self, transformer: FormulaTransformer) -> "Formula":
        raise NotImplementedError()

    @abstractmethod
    def __len__(self):
        raise NotImplementedError()

    @abstractmethod
    def __hash__(self):
        raise NotImplementedError()

    @abstractmethod
    def __eq__(self, other: "Formula"):
        raise NotImplementedError()

    def __and__(self, other: "Formula"):
        if self == other:
            return self

        if isinstance(self, SMTFormula) and self.is_false:
            return self

        if isinstance(other, SMTFormula) and other.is_false:
            return other

        if isinstance(self, SMTFormula) and self.is_true:
            return other

        if isinstance(other, SMTFormula) and other.is_true:
            return self

        if isinstance(self, NegatedFormula) and self.args[0] == other:
            return SMTFormula(z3.BoolVal(False))

        if isinstance(other, NegatedFormula) and other.args[0] == self:
            return SMTFormula(z3.BoolVal(False))

        return ConjunctiveFormula(self, other)

    def __or__(self, other: "Formula"):
        if self == other:
            return self

        if isinstance(self, SMTFormula) and z3.is_true(self.formula):
            return self

        if isinstance(other, SMTFormula) and z3.is_true(other.formula):
            return other

        if isinstance(self, SMTFormula) and z3.is_false(self.formula):
            return other

        if isinstance(other, SMTFormula) and z3.is_false(other.formula):
            return self

        if isinstance(self, NegatedFormula) and self.args[0] == other:
            return SMTFormula(z3.BoolVal(True))

        if isinstance(other, NegatedFormula) and other.args[0] == self:
            return SMTFormula(z3.BoolVal(True))

        return DisjunctiveFormula(self, other)

    def __neg__(self):
        assert not isinstance(self, SMTFormula)  # Overloaded in SMTFormula

        if isinstance(self, NegatedFormula):
            return self.args[0]
        elif isinstance(self, ConjunctiveFormula):
            return reduce(lambda a, b: a | b, [-arg for arg in self.args])
        elif isinstance(self, DisjunctiveFormula):
            return reduce(lambda a, b: a & b, [-arg for arg in self.args])
        elif isinstance(self, ForallFormula):
            return ExistsFormula(
                self.bound_variable,
                self.in_variable,
                -self.inner_formula,
                self.bind_expression,
            )
        elif isinstance(self, ExistsFormula):
            return ForallFormula(
                self.bound_variable,
                self.in_variable,
                -self.inner_formula,
                self.bind_expression,
            )
        elif isinstance(self, ForallIntFormula):
            return ExistsIntFormula(self.bound_variable, -self.inner_formula)
        elif isinstance(self, ExistsIntFormula):
            return ForallIntFormula(self.bound_variable, -self.inner_formula)

        return NegatedFormula(self)


def substitute(
    formula: Formula,
    subst_map: Dict[Variable | DerivationTree, str | int | Variable | DerivationTree],
) -> Formula:
    assert not any(
        isinstance(subst, DerivationTree) and isinstance(value, Variable)
        for subst, value in subst_map.items()
    )

    subst_map = {
        to_subst: (
            DerivationTree(str(value), [])
            if isinstance(value, str) or isinstance(value, int)
            else value
        )
        for to_subst, value in subst_map.items()
    }

    result = formula.substitute_variables(
        {
            to_subst: value
            for to_subst, value in subst_map.items()
            if isinstance(to_subst, Variable) and isinstance(value, Variable)
        }
    )

    result = result.substitute_expressions(
        {
            to_subst: value
            for to_subst, value in subst_map.items()
            if isinstance(value, DerivationTree)
        }
    )

    return result


@dataclass(frozen=True)
class StructuralPredicate:
    name: str
    arity: int
    eval_fun: Callable[[DerivationTree, Union[Path, str], ...], bool]

    def evaluate(self, context_tree: DerivationTree, *instantiations: Union[Path, str]):
        return self.eval_fun(context_tree, *instantiations)

    def __str__(self):
        return self.name


class StructuralPredicateFormula(Formula):
    def __init__(
        self, predicate: StructuralPredicate, *args: Variable | str | DerivationTree
    ):
        assert len(args) == predicate.arity
        self.predicate = predicate
        self.args: List[Variable | str | DerivationTree] = list(args)

    def evaluate(self, context_tree: DerivationTree) -> bool:
        args_with_paths: List[Union[str, Tuple[Path, DerivationTree]]] = [
            arg if isinstance(arg, str) else (context_tree.find_node(arg), arg)
            for arg in self.args
        ]

        if any(arg[0] is None for arg in args_with_paths if isinstance(arg, tuple)):
            raise RuntimeError(
                "Could not find paths for all predicate arguments in context tree:\n"
                + str([str(tree) for path, tree in args_with_paths if path is None])
                + f"\nContext tree:\n{context_tree}"
            )

        return self.predicate.eval_fun(
            context_tree,
            *[arg if isinstance(arg, str) else arg[0] for arg in args_with_paths],
        )

    def substitute_variables(
        self, subst_map: Dict[Variable, Variable]
    ) -> "StructuralPredicateFormula":
        return StructuralPredicateFormula(
            self.predicate,
            *[arg if arg not in subst_map else subst_map[arg] for arg in self.args],
        )

    def substitute_expressions(
        self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]
    ) -> "StructuralPredicateFormula":
        new_args = []
        for arg in self.args:
            if isinstance(arg, Variable):
                if arg in subst_map:
                    new_args.append(subst_map[arg])
                else:
                    new_args.append(arg)
                continue

            if isinstance(arg, str):
                new_args.append(arg)
                continue

            assert isinstance(arg, DerivationTree)
            tree: DerivationTree = arg
            if tree in subst_map:
                new_args.append(subst_map[tree])
                continue

            new_args.append(tree.substitute({k: v for k, v in subst_map.items()}))

        return StructuralPredicateFormula(self.predicate, *new_args)

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return OrderedSet([])

    def free_variables(self) -> OrderedSet[Variable]:
        return OrderedSet([arg for arg in self.args if isinstance(arg, Variable)])

    def tree_arguments(self) -> OrderedSet[DerivationTree]:
        return OrderedSet([arg for arg in self.args if isinstance(arg, DerivationTree)])

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_predicate_formula(self)

    def transform(self, visitor: FormulaTransformer) -> Formula:
        return visitor.transform_predicate_formula(self)

    def __len__(self):
        return 1

    def __hash__(self):
        return hash((type(self).__name__, self.predicate, tuple(self.args)))

    def __eq__(self, other):
        return type(self) is type(other) and (self.predicate, self.args) == (
            other.predicate,
            other.args,
        )

    def __str__(self):
        arg_strings = [
            f'"{arg}"' if isinstance(arg, str) else str(arg) for arg in self.args
        ]

        return f"{self.predicate}({', '.join(arg_strings)})"

    def __repr__(self):
        return (
            f'PredicateFormula({repr(self.predicate), ", ".join(map(repr, self.args))})'
        )


@dataclasses.dataclass(frozen=True)
class SemPredEvalResult:
    result: Optional[bool | Dict[Variable | DerivationTree, DerivationTree]]

    def is_boolean(self) -> bool:
        return self.true() or self.false()

    def true(self) -> bool:
        return self.result is True

    def false(self) -> bool:
        return self.result is False

    def ready(self) -> bool:
        return self.result is not None

    def __str__(self):
        if self.ready():
            if self.true() or self.false():
                return str(self.result)
            else:
                return (
                    "{"
                    + ", ".join(
                        [
                            str(key) + ": " + str(value)
                            for key, value in self.result.items()
                        ]
                    )
                    + "}"
                )
        else:
            return "UNKNOWN"


SemPredArg = Union[DerivationTree, Variable, str, int]


class SemanticPredicateEvalFun(Protocol):
    @abstractmethod
    def __call__(
        self,
        graph: Optional[gg.GrammarGraph],
        *args: DerivationTree | Constant | str | int,
        negate=False,
    ) -> SemPredEvalResult:
        raise NotImplementedError()


class SemanticPredicate:
    def __init__(
        self,
        name: str,
        arity: int,
        eval_fun: SemanticPredicateEvalFun,
        binds_tree: Optional[
            Callable[[DerivationTree, Tuple[SemPredArg, ...]], bool] | bool
        ] = None,
    ):
        """
        :param name:
        :param arity:
        :param eval_fun:
        :param binds_tree: Given a derivation tree and the arguments for the predicate, this function tests whether
        the tree is bound by the predicate formula. The effect of this is that bound trees cannot be freely expanded,
        similarly to nonterminals bound by a universal quantifier. A semantic predicate may also not bind any of its
        arguments; in that case, we can freely instantiate the arguments and then ask the predicate for a "fix" if
        the instantiation is non-conformant. Most semantic predicates do not bind their arguments. Pass nothing or
        True for this parameter for predicates binding all trees in all their arguments. Pass False for predicates
        binding no trees at all. Pass a custom function for anything special.
        """
        self.name = name
        self.arity = arity
        self.eval_fun = eval_fun

        if binds_tree is not None and binds_tree is not True:
            if binds_tree is False:
                self.binds_tree = lambda tree, args: False
            else:
                self.binds_tree = binds_tree
        else:
            self.binds_tree = lambda tree, args: any(
                tree_arg.find_node(tree) is not None
                for tree_arg in args
                if isinstance(tree_arg, DerivationTree)
            )

    def evaluate(
        self, graph: gg.GrammarGraph, *instantiations: SemPredArg, negate: bool = False
    ):
        if negate:
            return self.eval_fun(graph, *instantiations, negate=True)
        else:
            return self.eval_fun(graph, *instantiations)

    def __eq__(self, other):
        return isinstance(other, SemanticPredicate) and (self.name, self.arity) == (
            other.name,
            other.arity,
        )

    def __hash__(self):
        return hash((self.name, self.arity))

    def __repr__(self):
        return f"SemanticPredicate({self.name}, {self.arity})"

    def __str__(self):
        return self.name


class SemanticPredicateFormula(Formula):
    def __init__(self, predicate: SemanticPredicate, *args: SemPredArg, order: int = 0):
        assert len(args) == predicate.arity
        self.predicate = predicate
        self.args: Tuple[SemPredArg, ...] = args
        self.order = order

    def evaluate(
        self, graph: gg.GrammarGraph, negate: bool = False
    ) -> SemPredEvalResult:
        return self.predicate.evaluate(graph, *self.args, negate=negate)

    def binds_tree(self, tree: DerivationTree) -> bool:
        return self.predicate.binds_tree(tree, self.args)

    def substitute_variables(
        self, subst_map: Dict[Variable, Variable]
    ) -> "SemanticPredicateFormula":
        return SemanticPredicateFormula(
            self.predicate,
            *[arg if arg not in subst_map else subst_map[arg] for arg in self.args],
            order=self.order,
        )

    def substitute_expressions(
        self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]
    ) -> "SemanticPredicateFormula":
        tree_id_subst_map = {
            tree.id: repl
            for tree, repl in subst_map.items()
            if isinstance(tree, DerivationTree)
        }

        new_args = []
        for arg in self.args:
            if isinstance(arg, str) or isinstance(arg, int):
                new_args.append(arg)
                continue

            if isinstance(arg, Variable):
                if arg in subst_map:
                    new_args.append(subst_map[arg])
                else:
                    new_args.append(arg)
                continue

            tree: DerivationTree = arg
            if tree.id in tree_id_subst_map:
                new_args.append(tree_id_subst_map[tree.id])
                continue

            new_args.append(tree.substitute({k: v for k, v in subst_map.items()}))

        return SemanticPredicateFormula(self.predicate, *new_args, order=self.order)

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return OrderedSet([])

    def free_variables(self) -> OrderedSet[Variable]:
        return OrderedSet([arg for arg in self.args if isinstance(arg, Variable)])

    def tree_arguments(self) -> OrderedSet[DerivationTree]:
        return OrderedSet([arg for arg in self.args if isinstance(arg, DerivationTree)])

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_semantic_predicate_formula(self)

    def transform(self, visitor: FormulaTransformer) -> Formula:
        return visitor.transform_semantic_predicate_formula(self)

    def __len__(self):
        return 1

    def __hash__(self):
        return hash((type(self).__name__, self.predicate, self.args))

    def __eq__(self, other):
        return (
            isinstance(other, SemanticPredicateFormula)
            and self.predicate == other.predicate
            and self.args == other.args
        )

    def __str__(self):
        arg_strings = [
            f'"{arg}"'
            if isinstance(arg, str)
            else (
                arg.to_string(show_open_leaves=True, show_ids=True)
                if isinstance(arg, DerivationTree)
                else str(arg)
            )
            for arg in self.args
        ]

        return f"{self.predicate}({', '.join(arg_strings)})"

    def __repr__(self):
        return f'SemanticPredicateFormula({repr(self.predicate), ", ".join(map(repr, self.args))})'


class PropositionalCombinator(Formula, ABC):
    def __init__(self, *args: Formula):
        self.args = args

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return reduce(operator.or_, [arg.bound_variables() for arg in self.args])

    def free_variables(self) -> OrderedSet[Variable]:
        result: OrderedSet[Variable] = OrderedSet([])
        for arg in self.args:
            result |= arg.free_variables()
        return result

    def tree_arguments(self) -> OrderedSet[DerivationTree]:
        result: OrderedSet[DerivationTree] = OrderedSet([])
        for arg in self.args:
            result |= arg.tree_arguments()
        return result

    def __len__(self):
        return 1 + len(self.args)

    def __repr__(self):
        return f"{type(self).__name__}({', '.join(map(repr, self.args))})"

    def __hash__(self):
        return hash((type(self).__name__, self.args))

    def __eq__(self, other):
        return type(self) == type(other) and self.args == other.args


class NegatedFormula(PropositionalCombinator):
    def __init__(self, arg: Formula):
        super().__init__(arg)

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_negated_formula(self)

        visitor.toggle_negation_scope()
        if visitor.do_continue(self):
            for formula in self.args:
                formula.accept(visitor)
        visitor.toggle_negation_scope()

    def transform(self, transformer: FormulaTransformer) -> "Formula":
        return transformer.transform_negated_formula(
            NegatedFormula(self.args[0].transform(transformer))
        )

    def substitute_variables(
        self, subst_map: Dict[Variable, Variable]
    ) -> "NegatedFormula":
        return NegatedFormula(
            *[arg.substitute_variables(subst_map) for arg in self.args]
        )

    def substitute_expressions(
        self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]
    ) -> "NegatedFormula":
        return NegatedFormula(
            *[arg.substitute_expressions(subst_map) for arg in self.args]
        )

    def __hash__(self):
        return hash((type(self).__name__, self.args))

    def __str__(self):
        return f"¬({self.args[0]})"


class ConjunctiveFormula(PropositionalCombinator):
    def __init__(self, *args: Formula):
        if len(args) < 2:
            raise RuntimeError(
                f"Conjunction needs at least two arguments, {len(args)} given."
            )
        super().__init__(*args)

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return reduce(
            lambda a, b: a & b,
            [arg.substitute_variables(subst_map) for arg in self.args],
        )

    def substitute_expressions(
        self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]
    ) -> Formula:
        return reduce(
            lambda a, b: a & b,
            [arg.substitute_expressions(subst_map) for arg in self.args],
        )

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_conjunctive_formula(self)
        if visitor.do_continue(self):
            for formula in self.args:
                formula.accept(visitor)

    def transform(self, transformer: FormulaTransformer) -> "Formula":
        return transformer.transform_conjunctive_formula(
            ConjunctiveFormula(*[arg.transform(transformer) for arg in self.args])
        )

    def __hash__(self):
        return hash((type(self).__name__, self.args))

    def __eq__(self, other):
        return split_conjunction(self) == split_conjunction(other)

    def __str__(self):
        return f"({' ∧ '.join(map(str, self.args))})"


class DisjunctiveFormula(PropositionalCombinator):
    def __init__(self, *args: Formula):
        if len(args) < 2:
            raise RuntimeError(
                f"Disjunction needs at least two arguments, {len(args)} given."
            )
        super().__init__(*args)

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return reduce(
            lambda a, b: a | b,
            [arg.substitute_variables(subst_map) for arg in self.args],
        )

    def substitute_expressions(
        self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]
    ) -> Formula:
        return reduce(
            lambda a, b: a | b,
            [arg.substitute_expressions(subst_map) for arg in self.args],
        )

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_disjunctive_formula(self)
        if visitor.do_continue(self):
            for formula in self.args:
                formula.accept(visitor)

    def transform(self, transformer: FormulaTransformer) -> "Formula":
        return transformer.transform_disjunctive_formula(
            DisjunctiveFormula(*[arg.transform(transformer) for arg in self.args])
        )

    def __hash__(self):
        return hash((type(self).__name__, self.args))

    def __eq__(self, other):
        return split_disjunction(self) == split_disjunction(other)

    def __str__(self):
        return f"({' ∨ '.join(map(str, self.args))})"


class SMTFormula(Formula):
    def __init__(
        self,
        formula: z3.BoolRef,
        *free_variables: Variable,
        instantiated_variables: Optional[OrderedSet[Variable]] = None,
        substitutions: Optional[Dict[Variable, DerivationTree]] = None,
        auto_eval: bool = True,
        auto_subst: bool = True,
    ):
        """
        Encapsulates an SMT formula.
        :param formula: The SMT formula.
        :param free_variables: Free variables in this formula.
        """
        self.formula = formula
        self.is_false = z3.is_false(formula)
        self.is_true = z3.is_true(formula)

        self.free_variables_ = OrderedSet(free_variables)
        self.instantiated_variables = instantiated_variables or OrderedSet([])
        self.substitutions: Dict[Variable, DerivationTree] = substitutions or {}

        if assertions_activated():
            actual_symbols = get_symbols(formula)
            assert len(self.free_variables_) + len(self.instantiated_variables) == len(
                actual_symbols
            ), (
                f"Supplied number of {len(free_variables)} symbols does not match "
                + f"actual number of symbols {len(actual_symbols)} in formula '{formula}'"
            )

        # When substituting expressions, the formula is automatically evaluated if this flag
        # is set to True and all substituted expressions are closed trees, i.e., the formula
        # is ground. Deactivate only for special purposes, e.g., vacuity checking.
        self.auto_eval = auto_eval
        # self.auto_eval = False

        self.auto_subst = auto_subst

    def __getstate__(self) -> Dict[str, bytes]:
        result: Dict[str, bytes] = {
            f: pickle.dumps(v) for f, v in self.__dict__.items() if f != "formula"
        }
        # result["formula"] = self.formula.sexpr().encode("utf-8")
        result["formula"] = smt_expr_to_str(self.formula).encode("utf-8")
        return result

    def __setstate__(self, state: Dict[str, bytes]) -> None:
        inst = {f: pickle.loads(v) for f, v in state.items() if f != "formula"}
        free_variables: OrderedSet[Variable] = inst["free_variables_"]
        instantiated_variables: OrderedSet[Variable] = inst["instantiated_variables"]

        formula = state["formula"].decode("utf-8")
        formula = formula.replace(r"\"", r"\"")
        z3_constr = z3.parse_smt2_string(
            f"(assert {formula})",
            decls={
                var.name: z3.String(var.name)
                for var in free_variables | instantiated_variables
            },
        )[0]

        self.__dict__ = inst
        self.formula = z3_constr

    def substitute_variables(self, subst_map: Dict[Variable, Variable]) -> "SMTFormula":
        new_smt_formula = z3_subst(
            self.formula, {v1.to_smt(): v2.to_smt() for v1, v2 in subst_map.items()}
        )

        new_free_variables = [
            variable if variable not in subst_map else subst_map[variable]
            for variable in self.free_variables_
        ]

        assert all(
            inst_var not in subst_map for inst_var in self.instantiated_variables
        )
        assert all(inst_var not in subst_map for inst_var in self.substitutions.keys())

        return SMTFormula(
            cast(z3.BoolRef, new_smt_formula),
            *new_free_variables,
            instantiated_variables=self.instantiated_variables,
            substitutions=self.substitutions,
            auto_eval=self.auto_eval,
            auto_subst=self.auto_subst,
        )

    def substitute_expressions(
        self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]
    ) -> "SMTFormula":
        tree_subst_map = {
            k: v
            for k, v in subst_map.items()
            if isinstance(k, DerivationTree)
            and (
                k in self.substitutions.values()
                or any(t.find_node(k) is not None for t in self.substitutions.values())
            )
        }
        var_subst_map: Dict[Variable:DerivationTree] = {
            k: v for k, v in subst_map.items() if k in self.free_variables_
        }

        updated_substitutions: Dict[Variable, DerivationTree] = {
            var: tree.substitute(tree_subst_map)
            for var, tree in self.substitutions.items()
        }

        new_substitutions: Dict[Variable, DerivationTree] = (
            updated_substitutions | var_subst_map
        )

        complete_substitutions = {
            k: v
            for k, v in new_substitutions.items()
            if v.is_complete() and self.auto_subst
        }
        new_substitutions = {
            k: v
            for k, v in new_substitutions.items()
            if not v.is_complete() or not self.auto_subst
        }

        assert set(complete_substitutions.keys()).isdisjoint(
            set(new_substitutions.keys())
        )

        new_instantiated_variables = OrderedSet(
            [
                var
                for var in self.instantiated_variables
                | OrderedSet(new_substitutions.keys())
                if var not in complete_substitutions
            ]
        )

        new_smt_formula: z3.BoolRef = cast(
            z3.BoolRef,
            z3_subst(
                self.formula,
                {
                    variable.to_smt(): z3.StringVal(str(tree))
                    for variable, tree in complete_substitutions.items()
                },
            ),
        )

        new_free_variables: OrderedSet[Variable] = OrderedSet(
            [
                variable
                for variable in self.free_variables_
                if variable not in var_subst_map
            ]
        )

        if (
            self.auto_eval
            and len(new_free_variables) + len(new_instantiated_variables) == 0
        ):
            # Formula is ground, we can evaluate it!
            return SMTFormula(z3.BoolVal(is_valid(new_smt_formula).to_bool()))

        return SMTFormula(
            cast(z3.BoolRef, new_smt_formula),
            *new_free_variables,
            instantiated_variables=new_instantiated_variables,
            substitutions=new_substitutions,
            auto_eval=self.auto_eval,
            auto_subst=self.auto_subst,
        )

    def tree_arguments(self) -> OrderedSet[DerivationTree]:
        return OrderedSet(self.substitutions.values())

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return OrderedSet([])

    def free_variables(self) -> OrderedSet[Variable]:
        return self.free_variables_

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_smt_formula(self)

    def transform(self, transformer: FormulaTransformer) -> Formula:
        return transformer.transform_smt_formula(
            SMTFormula(
                self.formula,
                *self.free_variables_,
                instantiated_variables=self.instantiated_variables,
                substitutions=self.substitutions,
                auto_eval=self.auto_eval,
                auto_subst=self.auto_subst,
            )
        )

    # NOTE: Combining SMT formulas with and/or is not that easy due to tree substitutions, see
    #       function "eliminate_semantic_formula" in solver.py. Problems: Name collisions, plus
    #       impedes clustering which improves solver efficiency. The conjunction and disjunction
    #       functions contain assertions preventing name collisions.
    def disjunction(self, other: "SMTFormula") -> "SMTFormula":
        assert self.free_variables().isdisjoint(other.free_variables()) or not any(
            (var in self.substitutions and var not in other.substitutions)
            or (var in other.substitutions and var not in self.substitutions)
            or (
                var in self.substitutions
                and var in other.substitutions
                and self.substitutions[var].id != other.substitutions[var].id
            )
            for var in self.free_variables().intersection(other.free_variables())
        )
        return SMTFormula(
            z3.Or(self.formula, other.formula),
            *(self.free_variables() | other.free_variables()),
            instantiated_variables=self.instantiated_variables
            | other.instantiated_variables,
            substitutions=self.substitutions | other.substitutions,
            auto_eval=self.auto_eval and other.auto_eval,
            auto_subst=self.auto_subst and other.auto_subst,
        )

    def conjunction(self, other: "SMTFormula") -> "SMTFormula":
        assert self.free_variables().isdisjoint(other.free_variables()) or not any(
            (var in self.substitutions and var not in other.substitutions)
            or (var in other.substitutions and var not in self.substitutions)
            or (
                var in self.substitutions
                and var in other.substitutions
                and self.substitutions[var].id != other.substitutions[var].id
            )
            for var in self.free_variables().intersection(other.free_variables())
        )

        return SMTFormula(
            z3.And(self.formula, other.formula),
            *(self.free_variables() | other.free_variables()),
            instantiated_variables=self.instantiated_variables
            | other.instantiated_variables,
            substitutions=self.substitutions | other.substitutions,
            auto_eval=self.auto_eval and other.auto_eval,
            auto_subst=self.auto_subst and other.auto_subst,
        )

    def __len__(self):
        return 1

    def __neg__(self) -> "SMTFormula":
        return SMTFormula(
            z3_push_in_negations(self.formula, negate=True),
            *self.free_variables(),
            instantiated_variables=self.instantiated_variables,
            substitutions=self.substitutions,
            auto_eval=self.auto_eval,
            auto_subst=self.auto_subst,
        )

    def __repr__(self):
        return (
            f"SMTFormula({repr(self.formula)}, {', '.join(map(repr, self.free_variables_))}, "
            f"instantiated_variables={repr(self.instantiated_variables)}, "
            f"substitutions={repr(self.substitutions)})"
        )

    def __str__(self):
        if not self.substitutions:
            return str(self.formula)
        else:
            subst_string = str(
                {str(var): str(tree) for var, tree in self.substitutions.items()}
            )
            return f"({self.formula}, {subst_string})"

    def __eq__(self, other):
        return (
            isinstance(other, SMTFormula)
            and self.formula == other.formula
            and self.substitutions == other.substitutions
        )

    def __hash__(self):
        return hash(
            (type(self).__name__, self.formula, tuple(self.substitutions.items()))
        )


class NumericQuantifiedFormula(Formula, ABC):
    def __init__(self, bound_variable: BoundVariable, inner_formula: Formula):
        self.bound_variable = bound_variable
        self.inner_formula = inner_formula

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        """Non-recursive: Only non-empty for quantified formulas"""
        return OrderedSet([self.bound_variable])

    def free_variables(self) -> OrderedSet[Variable]:
        """Recursive."""
        return self.inner_formula.free_variables().difference(self.bound_variables())

    def tree_arguments(self) -> OrderedSet[DerivationTree]:
        return self.inner_formula.tree_arguments()

    def __len__(self):
        return 1 + len(self.inner_formula)


class ExistsIntFormula(NumericQuantifiedFormula):
    def __init__(self, bound_variable: BoundVariable, inner_formula: Formula):
        super().__init__(bound_variable, inner_formula)

    def substitute_variables(self, subst_map: Dict[Variable, Variable]) -> "Formula":
        return ExistsIntFormula(
            subst_map.get(self.bound_variable, self.bound_variable),
            self.inner_formula.substitute_variables(subst_map),
        )

    def substitute_expressions(
        self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]
    ) -> "Formula":
        assert self.bound_variable not in subst_map
        return ExistsIntFormula(
            self.bound_variable, self.inner_formula.substitute_expressions(subst_map)
        )

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_exists_int_formula(self)
        if visitor.do_continue(self):
            self.inner_formula.accept(visitor)

    def transform(self, transformer: FormulaTransformer) -> Formula:
        return transformer.transform_exists_int_formula(
            ExistsIntFormula(
                self.bound_variable, self.inner_formula.transform(transformer)
            )
        )

    def __hash__(self):
        return hash((type(self).__name__, self.bound_variable, self.inner_formula))

    def __eq__(self, other):
        return (
            isinstance(other, ExistsIntFormula)
            and self.bound_variable == other.bound_variable
            and self.inner_formula == other.inner_formula
        )

    def __str__(self):
        return f"∃ int {self.bound_variable.name}: {str(self.inner_formula)}"

    def __repr__(self):
        return (
            f"ExistsIntFormula({repr(self.bound_variable)}, {repr(self.inner_formula)})"
        )


class ForallIntFormula(NumericQuantifiedFormula):
    def __init__(self, bound_variable: BoundVariable, inner_formula: Formula):
        super().__init__(bound_variable, inner_formula)

    def substitute_variables(self, subst_map: Dict[Variable, Variable]) -> "Formula":
        return ForallIntFormula(
            subst_map.get(self.bound_variable, self.bound_variable),
            self.inner_formula.substitute_variables(subst_map),
        )

    def substitute_expressions(
        self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]
    ) -> "Formula":
        assert self.bound_variable not in subst_map
        return ForallIntFormula(
            self.bound_variable, self.inner_formula.substitute_expressions(subst_map)
        )

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_forall_int_formula(self)
        if visitor.do_continue(self):
            self.inner_formula.accept(visitor)

    def transform(self, transformer: FormulaTransformer) -> Formula:
        return transformer.transform_forall_int_formula(
            ForallIntFormula(
                self.bound_variable, self.inner_formula.transform(transformer)
            )
        )

    def __hash__(self):
        return hash((type(self).__name__, self.bound_variable, self.inner_formula))

    def __eq__(self, other):
        return (
            isinstance(other, ForallIntFormula)
            and self.bound_variable == other.bound_variable
            and self.inner_formula == other.inner_formula
        )

    def __str__(self):
        return f"∀ int {self.bound_variable.name}: {str(self.inner_formula)}"

    def __repr__(self):
        return (
            f"ForallIntFormula({repr(self.bound_variable)}, {repr(self.inner_formula)})"
        )


class QuantifiedFormula(Formula, ABC):
    def __init__(
        self,
        bound_variable: Union[BoundVariable, str],
        in_variable: Union[Variable, DerivationTree],
        inner_formula: Formula,
        bind_expression: Optional[Union[BindExpression, BoundVariable]] = None,
    ):
        assert inner_formula is not None
        assert isinstance(bound_variable, BoundVariable) or bind_expression is not None

        if isinstance(bound_variable, str):
            assert is_nonterminal(bound_variable)
            self.bound_variable = DummyVariable(bound_variable)
        else:
            self.bound_variable = bound_variable

        self.in_variable = in_variable
        self.inner_formula = inner_formula

        if isinstance(bind_expression, BoundVariable):
            self.bind_expression = BindExpression(bind_expression)
        else:
            self.bind_expression = bind_expression

    def bound_variables(self) -> OrderedSet[BoundVariable]:
        return OrderedSet([self.bound_variable]) | (
            OrderedSet([])
            if self.bind_expression is None
            else self.bind_expression.bound_variables()
        )

    def free_variables(self) -> OrderedSet[Variable]:
        return (
            OrderedSet(
                [self.in_variable] if isinstance(self.in_variable, Variable) else []
            )
            | self.inner_formula.free_variables()
        ) - self.bound_variables()

    def tree_arguments(self) -> OrderedSet[DerivationTree]:
        result = OrderedSet([])
        if isinstance(self.in_variable, DerivationTree):
            result.add(self.in_variable)
        result.update(self.inner_formula.tree_arguments())
        return result

    def is_already_matched(self, tree: DerivationTree) -> bool:
        return False

    def __len__(self):
        result = 1 + len(self.inner_formula)
        if self.bind_expression:
            result += len(self.bind_expression.bound_elements)
        return result

    def __repr__(self):
        return (
            f"{type(self).__name__}({repr(self.bound_variable)}, {repr(self.in_variable)}, "
            f'{repr(self.inner_formula)}{"" if self.bind_expression is None else ", " + repr(self.bind_expression)})'
        )

    def __hash__(self):
        return hash(
            (
                type(self).__name__,
                self.bound_variable,
                self.in_variable,
                self.inner_formula,
                self.bind_expression or 0,
            )
        )

    def __eq__(self, other):
        return type(self) == type(other) and (
            self.bound_variable,
            self.in_variable,
            self.inner_formula,
            self.bind_expression,
        ) == (
            other.bound_variable,
            other.in_variable,
            other.inner_formula,
            other.bind_expression,
        )


class ForallFormula(QuantifiedFormula):
    __next_id = 0

    def __init__(
        self,
        bound_variable: Union[BoundVariable, str],
        in_variable: Union[Variable, DerivationTree],
        inner_formula: Formula,
        bind_expression: Optional[BindExpression] = None,
        already_matched: Optional[Set[int]] = None,
        id: Optional[int] = None,
    ):
        super().__init__(bound_variable, in_variable, inner_formula, bind_expression)
        self.already_matched: Set[int] = (
            set() if not already_matched else set(already_matched)
        )

        # The id field is used by eliminate_quantifiers to avoid counting universal
        # formulas twice when checking for vacuous satisfaction.
        if id is None:
            self.id = ForallFormula.__next_id
            ForallFormula.__next_id += 1
        else:
            self.id = id

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        assert not self.already_matched

        return ForallFormula(
            self.bound_variable
            if self.bound_variable not in subst_map
            else subst_map[self.bound_variable],
            self.in_variable
            if self.in_variable not in subst_map
            else subst_map[self.in_variable],
            self.inner_formula.substitute_variables(subst_map),
            None
            if not self.bind_expression
            else self.bind_expression.substitute_variables(subst_map),
            self.already_matched,
            id=self.id,
        )

    def substitute_expressions(
        self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]
    ) -> Formula:
        new_in_variable = self.in_variable
        if self.in_variable in subst_map:
            new_in_variable = subst_map[new_in_variable]
        elif isinstance(new_in_variable, DerivationTree):
            new_in_variable = new_in_variable.substitute(subst_map)

        new_inner_formula = self.inner_formula.substitute_expressions(subst_map)

        if (
            self.bound_variable not in new_inner_formula.free_variables()
            and self.bind_expression is None
        ):
            # NOTE: We cannot remove the quantifier if there is a bind expression, not even if
            #       the variables in the bind expression do not occur in the inner formula,
            #       since there might be multiple expansion alternatives of the bound variable
            #       nonterminal and it makes a difference whether a particular expansion has been
            #       chosen. Consider, e.g., an inner formula "false". Then, this formula evaluates
            #       to false IF, AND ONLY IF, the defined expansion alternative is chosen, and
            #       NOT always.
            return new_inner_formula

        return ForallFormula(
            self.bound_variable,
            new_in_variable,
            new_inner_formula,
            self.bind_expression,
            self.already_matched,
            id=self.id,
        )

    def add_already_matched(
        self, trees: Union[DerivationTree, Iterable[DerivationTree]]
    ) -> "ForallFormula":
        return ForallFormula(
            self.bound_variable,
            self.in_variable,
            self.inner_formula,
            self.bind_expression,
            self.already_matched
            | (
                {trees.id}
                if isinstance(trees, DerivationTree)
                else {tree.id for tree in trees}
            ),
            id=self.id,
        )

    def is_already_matched(self, tree: DerivationTree) -> bool:
        return tree.id in self.already_matched

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_forall_formula(self)
        if visitor.do_continue(self):
            self.inner_formula.accept(visitor)

    def transform(self, transformer: FormulaTransformer) -> Formula:
        return transformer.transform_forall_formula(
            ForallFormula(
                self.bound_variable,
                self.in_variable,
                self.inner_formula.transform(transformer),
                self.bind_expression,
                self.already_matched,
                id=self.id,
            )
        )

    def __str__(self):
        quote = '"'
        return (
            f'∀ {"" if not self.bind_expression else quote + str(self.bind_expression) + quote + " = "}'
            f"{str(self.bound_variable)} ∈ {replace_line_breaks(str(self.in_variable))}: ({str(self.inner_formula)})"
        )


class ExistsFormula(QuantifiedFormula):
    def __init__(
        self,
        bound_variable: Union[BoundVariable, str],
        in_variable: Union[Variable, DerivationTree],
        inner_formula: Formula,
        bind_expression: Optional[BindExpression] = None,
    ):
        super().__init__(bound_variable, in_variable, inner_formula, bind_expression)

    def substitute_variables(self, subst_map: Dict[Variable, Variable]):
        return ExistsFormula(
            self.bound_variable
            if self.bound_variable not in subst_map
            else subst_map[self.bound_variable],
            self.in_variable
            if self.in_variable not in subst_map
            else subst_map[self.in_variable],
            self.inner_formula.substitute_variables(subst_map),
            None
            if not self.bind_expression
            else self.bind_expression.substitute_variables(subst_map),
        )

    def substitute_expressions(
        self, subst_map: Dict[Union[Variable, DerivationTree], DerivationTree]
    ) -> Formula:
        new_in_variable = self.in_variable
        if self.in_variable in subst_map:
            new_in_variable = subst_map[new_in_variable]
        elif isinstance(new_in_variable, DerivationTree):
            new_in_variable = new_in_variable.substitute(subst_map)

        new_inner_formula = self.inner_formula.substitute_expressions(subst_map)

        if self.bound_variable not in new_inner_formula.free_variables() and (
            self.bind_expression is None
            or not any(
                bv in new_inner_formula.free_variables()
                for bv in self.bind_expression.bound_variables()
            )
        ):
            return new_inner_formula

        return ExistsFormula(
            self.bound_variable,
            new_in_variable,
            self.inner_formula.substitute_expressions(subst_map),
            self.bind_expression,
        )

    def accept(self, visitor: FormulaVisitor):
        visitor.visit_exists_formula(self)
        if visitor.do_continue(self):
            self.inner_formula.accept(visitor)

    def transform(self, transformer: FormulaTransformer) -> Formula:
        return transformer.transform_exists_formula(
            ExistsFormula(
                self.bound_variable,
                self.in_variable,
                self.inner_formula.transform(transformer),
                self.bind_expression,
            )
        )

    def __str__(self):
        quote = "'"
        return (
            f'∃ {"" if not self.bind_expression else quote + str(self.bind_expression) + quote + " = "}'
            f"{str(self.bound_variable)} ∈ {replace_line_breaks(str(self.in_variable))}: ({str(self.inner_formula)})"
        )


class VariablesCollector(FormulaVisitor):
    def __init__(self):
        super().__init__()
        self.result: OrderedSet[Variable] = OrderedSet()

    @staticmethod
    def collect(formula: Formula) -> OrderedSet[Variable]:
        c = VariablesCollector()
        formula.accept(c)
        return c.result

    def visit_exists_formula(self, formula: ExistsFormula):
        self.visit_quantified_formula(formula)

    def visit_forall_formula(self, formula: ForallFormula):
        self.visit_quantified_formula(formula)

    def visit_quantified_formula(self, formula: QuantifiedFormula):
        if isinstance(formula.in_variable, Variable):
            self.result.add(formula.in_variable)
        self.result.add(formula.bound_variable)
        if formula.bind_expression is not None:
            self.result.update(formula.bind_expression.bound_variables())

    def visit_exists_int_formula(self, formula: ExistsIntFormula):
        self.result.add(formula.bound_variable)

    def visit_forall_int_formula(self, formula: ForallIntFormula):
        self.result.add(formula.bound_variable)

    def visit_predicate_formula(self, formula: StructuralPredicateFormula):
        self.result.update([arg for arg in formula.args if isinstance(arg, Variable)])

    def visit_semantic_predicate_formula(self, formula: SemanticPredicateFormula):
        self.result.update([arg for arg in formula.args if isinstance(arg, Variable)])

    def visit_smt_formula(self, formula: SMTFormula):
        self.result.update(formula.free_variables())


class BoundVariablesCollector(FormulaVisitor):
    def __init__(self):
        super().__init__()
        self.result: OrderedSet[BoundVariable] = OrderedSet()

    @staticmethod
    def collect(formula: Formula) -> OrderedSet[BoundVariable]:
        c = BoundVariablesCollector()
        formula.accept(c)
        return c.result

    def visit_exists_formula(self, formula: ExistsFormula):
        self.visit_quantified_formula(formula)

    def visit_forall_formula(self, formula: ForallFormula):
        self.visit_quantified_formula(formula)

    def visit_quantified_formula(self, formula: QuantifiedFormula):
        self.result.add(formula.bound_variable)
        if formula.bind_expression is not None:
            self.result.update(formula.bind_expression.bound_variables())

    def visit_exists_int_formula(self, formula: ExistsIntFormula):
        self.result.add(formula.bound_variable)

    def visit_forall_int_formula(self, formula: ForallIntFormula):
        self.result.add(formula.bound_variable)


class FilterVisitor(FormulaVisitor):
    def __init__(
        self,
        filter_fun: Callable[[Formula], bool],
        do_continue: Callable[[Formula], bool] = lambda f: True,
    ):
        super().__init__()
        self.filter = filter_fun
        self.result: List[Formula] = []
        self.do_continue = do_continue

    def collect(self, formula: Formula) -> List[Formula]:
        self.result = []
        formula.accept(self)
        return self.result

    def do_continue(self, formula: Formula) -> bool:
        return self.do_continue(formula)

    def visit_forall_formula(self, formula: ForallFormula):
        if self.filter(formula):
            self.result.append(formula)

    def visit_exists_formula(self, formula: ExistsFormula):
        if self.filter(formula):
            self.result.append(formula)

    def visit_exists_int_formula(self, formula: ExistsIntFormula):
        if self.filter(formula):
            self.result.append(formula)

    def visit_forall_int_formula(self, formula: ForallIntFormula):
        if self.filter(formula):
            self.result.append(formula)

    def visit_negated_formula(self, formula: NegatedFormula):
        if self.filter(formula):
            self.result.append(formula)

    def visit_smt_formula(self, formula: SMTFormula):
        if self.filter(formula):
            self.result.append(formula)

    def visit_predicate_formula(self, formula: StructuralPredicateFormula):
        if self.filter(formula):
            self.result.append(formula)

    def visit_semantic_predicate_formula(self, formula: SemanticPredicateFormula):
        if self.filter(formula):
            self.result.append(formula)

    def visit_disjunctive_formula(self, formula: DisjunctiveFormula):
        if self.filter(formula):
            self.result.append(formula)

    def visit_conjunctive_formula(self, formula: ConjunctiveFormula):
        if self.filter(formula):
            self.result.append(formula)


def replace_formula(  # noqa: C901
    in_formula: Formula,
    to_replace: Union[Formula, Callable[[Formula], bool | Formula]],
    replace_with: Optional[Formula] = None,
) -> Formula:
    """
    Replaces a formula inside a conjunction or disjunction.
    to_replace is either (1) a formula to replace, or (2) a predicate which holds if the given formula
    should been replaced (if it returns True, replace_with must not be None), or (3) a function returning
    the formula to replace if the subformula should be replaced, or False otherwise. For (3), replace_with
    may be None (it is irrelevant).
    """

    if callable(to_replace):
        result = to_replace(in_formula)
        if isinstance(result, Formula):
            return replace_formula(result, to_replace, replace_with)

        assert isinstance(result, bool)
        if result:
            assert replace_with is not None
            return replace_with
    elif in_formula == to_replace:
        return replace_with

    if isinstance(in_formula, ConjunctiveFormula):
        return reduce(
            lambda a, b: a & b,
            [
                replace_formula(child, to_replace, replace_with)
                for child in in_formula.args
            ],
        )
    elif isinstance(in_formula, DisjunctiveFormula):
        return reduce(
            lambda a, b: a | b,
            [
                replace_formula(child, to_replace, replace_with)
                for child in in_formula.args
            ],
        )
    elif isinstance(in_formula, NegatedFormula):
        child_result = replace_formula(in_formula.args[0], to_replace, replace_with)

        if child_result == SMTFormula(z3.BoolVal(False)):
            return SMTFormula(z3.BoolVal(True))
        elif child_result == SMTFormula(z3.BoolVal(True)):
            return SMTFormula(z3.BoolVal(False))

        return NegatedFormula(child_result)
    elif isinstance(in_formula, ForallFormula):
        return ForallFormula(
            in_formula.bound_variable,
            in_formula.in_variable,
            replace_formula(in_formula.inner_formula, to_replace, replace_with),
            in_formula.bind_expression,
            in_formula.already_matched,
            id=in_formula.id,
        )
    elif isinstance(in_formula, ExistsFormula):
        return ExistsFormula(
            in_formula.bound_variable,
            in_formula.in_variable,
            replace_formula(in_formula.inner_formula, to_replace, replace_with),
            in_formula.bind_expression,
        )
    elif isinstance(in_formula, ExistsIntFormula):
        return ExistsIntFormula(
            in_formula.bound_variable,
            replace_formula(in_formula.inner_formula, to_replace, replace_with),
        )
    elif isinstance(in_formula, ForallIntFormula):
        return ForallIntFormula(
            in_formula.bound_variable,
            replace_formula(in_formula.inner_formula, to_replace, replace_with),
        )

    return in_formula


def convert_to_nnf(formula: Formula, negate=False) -> Formula:
    """Pushes negations inside the formula."""

    def close(evaluation_function: callable) -> callable:
        return lambda f: evaluation_function(f, negate)

    return (
        chain_functions(
            map(
                close,
                [
                    convert_negated_formula_to_nnf,
                    convert_conjunctive_formula_to_nnf,
                    convert_disjunctive_formula_to_nnf,
                    convert_structural_predicate_formula_to_nnf,
                    convert_smt_formula_to_nnf,
                    convert_exists_int_formula_to_nnf,
                    convert_quantified_formula_to_nnf,
                ],
            ),
            formula,
        )
        .raise_if_not_present(
            lambda: NotImplementedError(
                f"Unexpected formula type {type(formula).__name__}"
            )
        )
        .get()
    )


def convert_negated_formula_to_nnf(formula: Formula, negate: bool) -> Maybe[Formula]:
    if not isinstance(formula, NegatedFormula):
        return Maybe.nothing()

    return Maybe(convert_to_nnf(formula.args[0], not negate))


def convert_conjunctive_formula_to_nnf(
    formula: Formula, negate: bool
) -> Maybe[Formula]:
    if not isinstance(formula, ConjunctiveFormula):
        return Maybe.nothing()

    args = [convert_to_nnf(arg, negate) for arg in formula.args]
    if negate:
        return Maybe(reduce(lambda a, b: a | b, args))
    else:
        return Maybe(reduce(lambda a, b: a & b, args))


def convert_disjunctive_formula_to_nnf(
    formula: Formula, negate: bool
) -> Maybe[Formula]:
    if not isinstance(formula, DisjunctiveFormula):
        return Maybe.nothing()

    args = [convert_to_nnf(arg, negate) for arg in formula.args]
    if negate:
        return Maybe(reduce(lambda a, b: a & b, args))
    else:
        return Maybe(reduce(lambda a, b: a | b, args))


def convert_structural_predicate_formula_to_nnf(
    formula: Formula, negate: bool
) -> Maybe[Formula]:
    if not isinstance(formula, StructuralPredicateFormula) and not isinstance(
        formula, SemanticPredicateFormula
    ):
        return Maybe.nothing()

    return Maybe(-formula if negate else formula)


def convert_smt_formula_to_nnf(formula: Formula, negate: bool) -> Maybe[Formula]:
    if not isinstance(formula, SMTFormula):
        return Maybe.nothing()

    negated_smt_formula = z3_push_in_negations(formula.formula, negate)
    # Automatic simplification can remove free variables from the formula!
    actual_symbols = get_symbols(negated_smt_formula)
    free_variables = [
        var for var in formula.free_variables() if var.to_smt() in actual_symbols
    ]
    instantiated_variables = OrderedSet(
        [
            var
            for var in formula.instantiated_variables
            if var.to_smt() in actual_symbols
        ]
    )
    substitutions = {
        var: repl
        for var, repl in formula.substitutions.items()
        if var.to_smt() in actual_symbols
    }

    return Maybe(
        SMTFormula(
            negated_smt_formula,
            *free_variables,
            instantiated_variables=instantiated_variables,
            substitutions=substitutions,
            auto_eval=formula.auto_eval,
            auto_subst=formula.auto_subst,
        )
    )


def convert_exists_int_formula_to_nnf(formula: Formula, negate: bool) -> Maybe[Formula]:
    if not isinstance(formula, ExistsIntFormula) and not isinstance(
        formula, ForallIntFormula
    ):
        return Maybe.nothing()

    inner_formula = (
        convert_to_nnf(formula.inner_formula, negate)
        if negate
        else formula.inner_formula
    )

    if (isinstance(formula, ForallIntFormula) and negate) or (
        isinstance(formula, ExistsIntFormula) and not negate
    ):
        return Maybe(ExistsIntFormula(formula.bound_variable, inner_formula))
    else:
        return Maybe(ForallIntFormula(formula.bound_variable, inner_formula))


def convert_quantified_formula_to_nnf(formula: Formula, negate: bool) -> Maybe[Formula]:
    if not isinstance(formula, QuantifiedFormula):
        return Maybe.nothing()

    inner_formula = (
        convert_to_nnf(formula.inner_formula, negate)
        if negate
        else formula.inner_formula
    )
    already_matched: Set[int] = (
        formula.already_matched if isinstance(formula, ForallFormula) else set()
    )

    if (isinstance(formula, ForallFormula) and negate) or (
        isinstance(formula, ExistsFormula) and not negate
    ):
        return Maybe(
            ExistsFormula(
                formula.bound_variable,
                formula.in_variable,
                inner_formula,
                formula.bind_expression,
            )
        )
    else:
        return Maybe(
            ForallFormula(
                formula.bound_variable,
                formula.in_variable,
                inner_formula,
                formula.bind_expression,
                already_matched,
            )
        )


def convert_to_dnf(formula: Formula) -> Formula:
    assert not isinstance(formula, NegatedFormula) or not isinstance(
        formula.args[0], PropositionalCombinator
    ), "Convert to NNF before converting to DNF"

    if isinstance(formula, ConjunctiveFormula):
        disjuncts_list = [
            split_disjunction(convert_to_dnf(arg)) for arg in formula.args
        ]
        return reduce(
            lambda a, b: a | b,
            [
                reduce(
                    lambda a, b: a & b,
                    OrderedSet(split_conjunction(left & right)),
                    SMTFormula(z3.BoolVal(True)),
                )
                for left, right in itertools.product(*disjuncts_list)
            ],
            SMTFormula(z3.BoolVal(False)),
        )
    elif isinstance(formula, DisjunctiveFormula):
        return reduce(
            lambda a, b: a | b,
            [convert_to_dnf(subformula) for subformula in formula.args],
            SMTFormula(z3.BoolVal(False)),
        )
    elif isinstance(formula, ForallFormula):
        return ForallFormula(
            formula.bound_variable,
            formula.in_variable,
            convert_to_dnf(formula.inner_formula),
            formula.bind_expression,
            formula.already_matched,
        )
    elif isinstance(formula, ExistsFormula):
        return ExistsFormula(
            formula.bound_variable,
            formula.in_variable,
            convert_to_dnf(formula.inner_formula),
            formula.bind_expression,
        )
    else:
        return formula


def fresh_vars(
    orig_vars: OrderedSet[BoundVariable], used_names: Set[str]
) -> Dict[BoundVariable, BoundVariable]:
    result: Dict[BoundVariable, BoundVariable] = {}

    for variable in orig_vars:
        proposal = variable.name
        if proposal not in used_names:
            used_names.add(proposal)
            result[variable] = variable
            continue

        maybe_match = re.match(r"^(.*)_[0-9]+$", proposal)
        if maybe_match:
            proposal = maybe_match.group(1)

        idx = 0
        while f"{proposal}_{idx}" in used_names:
            idx += 1

        new_name = f"{proposal}_{idx}"
        used_names.add(new_name)
        result[variable] = BoundVariable(new_name, variable.n_type)

    return result


def ensure_unique_bound_variables(  # noqa: C901
    formula: Formula, used_names: Optional[Set[str]] = None
) -> Formula:
    used_names: Set[str] = set() if used_names is None else used_names

    if isinstance(formula, QuantifiedFormula):
        orig_used_names = set(used_names)

        used_names |= {
            var.name
            for var in BoundVariablesCollector()
            .collect(formula)
            .difference(formula.bound_variables())
        }

        old_used_names = set(used_names)
        formula = formula.substitute_variables(
            fresh_vars(
                formula.bound_variables(),
                used_names,
            )
        )

        used_names = orig_used_names | used_names.difference(old_used_names)

        if isinstance(formula, ForallFormula):
            return ForallFormula(
                formula.bound_variable,
                formula.in_variable,
                ensure_unique_bound_variables(formula.inner_formula, used_names),
                formula.bind_expression,
                formula.already_matched,
            )
        else:
            return ExistsFormula(
                formula.bound_variable,
                formula.in_variable,
                ensure_unique_bound_variables(formula.inner_formula, used_names),
                formula.bind_expression,
            )
    elif isinstance(formula, NegatedFormula):
        return NegatedFormula(
            ensure_unique_bound_variables(formula.args[0], used_names)
        )
    elif isinstance(formula, ConjunctiveFormula):
        return reduce(
            lambda a, b: a & b,
            [ensure_unique_bound_variables(arg, used_names) for arg in formula.args],
        )
    elif isinstance(formula, DisjunctiveFormula):
        return reduce(
            lambda a, b: a | b,
            [ensure_unique_bound_variables(arg, used_names) for arg in formula.args],
        )
    else:
        return formula


def split_conjunction(formula: Formula) -> List[Formula]:
    if not type(formula) is ConjunctiveFormula:
        return [formula]
    else:
        formula: ConjunctiveFormula
        return [elem for arg in formula.args for elem in split_conjunction(arg)]


def split_disjunction(formula: Formula) -> List[Formula]:
    if not type(formula) is DisjunctiveFormula:
        return [formula]
    else:
        formula: DisjunctiveFormula
        return [elem for arg in formula.args for elem in split_disjunction(arg)]


class VariableManager:
    def __init__(self, grammar: Optional[Grammar] = None):
        self.placeholders: Dict[str, Variable] = {}
        self.variables: Dict[str, Variable] = {}
        self.grammar = grammar

    def _var(
        self,
        name: str,
        n_type: Optional[str],
        constr: Optional[Callable[[str, Optional[str]], Variable]] = None,
    ) -> Variable:
        if self.grammar is not None and n_type is not None:
            assert (
                n_type == Variable.NUMERIC_NTYPE or n_type in self.grammar
            ), f"Unknown nonterminal type {n_type} for variable {name}"

        matching_variables = [
            var for var_name, var in self.variables.items() if var_name == name
        ]
        if matching_variables:
            return matching_variables[0]

        if constr is not None and n_type:
            return self.variables.setdefault(name, constr(name, n_type))

        matching_placeholders = [
            var for var_name, var in self.placeholders.items() if var_name == name
        ]
        if matching_placeholders:
            return matching_placeholders[0]

        assert constr is not None
        return self.placeholders.setdefault(name, constr(name, None))

    def var_declared(self, name: str) -> bool:
        return name in self.variables.keys()

    def all_var_names(self) -> Set[str]:
        return set(self.variables.keys()) | set(self.placeholders.keys())

    def const(self, name: str, n_type: Optional[str] = None) -> Constant:
        return cast(Constant, self._var(name, n_type, Constant))

    def num_var(self, name: str) -> BoundVariable:
        return cast(
            BoundVariable, self._var(name, BoundVariable.NUMERIC_NTYPE, BoundVariable)
        )

    def bv(self, name: str, n_type: Optional[str] = None) -> BoundVariable:
        return cast(BoundVariable, self._var(name, n_type, BoundVariable))

    def smt(self, formula) -> SMTFormula:
        assert isinstance(formula, z3.BoolRef)
        z3_symbols = get_symbols(formula)
        isla_variables = [self._var(str(z3_symbol), None) for z3_symbol in z3_symbols]
        return SMTFormula(formula, *isla_variables)

    def create(self, formula: Formula, safe=True) -> Formula:
        if safe:
            undeclared_variables = [
                ph_name
                for ph_name in self.placeholders
                if all(var_name != ph_name for var_name in self.variables)
            ]

            if undeclared_variables:
                raise RuntimeError(
                    "Undeclared variables: " + ", ".join(undeclared_variables)
                )

        return formula.substitute_variables(
            {
                ph_var: (
                    Maybe.from_iterator(
                        var
                        for var_name, var in self.variables.items()
                        if var_name == ph_name
                    )
                    + Maybe(ph_var)
                ).get()
                for ph_name, ph_var in self.placeholders.items()
            }
        )


def antlr_get_text_with_whitespace(ctx) -> str:
    if isinstance(ctx, antlr4.TerminalNode):
        return ctx.getText()

    a = ctx.start.start
    b = ctx.stop.stop
    assert isinstance(a, int)
    assert isinstance(b, int)
    stream = ctx.start.source[1]
    assert isinstance(stream, antlr4.InputStream)
    return stream.getText(start=a, stop=b)


def parse_tree_text(elem: RuleContext | CommonToken) -> str:
    if isinstance(elem, CommonToken):
        return elem.text
    else:
        return elem.getText()


class MExprEmitter(MexprParserListener.MexprParserListener):
    def __init__(self, mgr: VariableManager):
        self.result: List[Union[str, BoundVariable, List[str]]] = []
        self.mgr = mgr

    def exitMatchExprOptional(self, ctx: MexprParser.MatchExprOptionalContext):
        self.result.append([antlr_get_text_with_whitespace(ctx)[1:-1]])

    def exitMatchExprChars(self, ctx: MexprParser.MatchExprCharsContext):
        text = antlr_get_text_with_whitespace(ctx)
        text = text.replace("{{", "{").replace("}}", "}")
        self.result.append(instantiate_escaped_symbols(text))

    def exitMatchExprVar(self, ctx: MexprParser.MatchExprVarContext):
        self.result.append(
            self.mgr.bv(parse_tree_text(ctx.ID()), parse_tree_text(ctx.varType()))
        )


class ConcreteSyntaxMexprUsedVariablesCollector(
    MexprParserListener.MexprParserListener
):
    def __init__(self):
        self.used_variables: OrderedSet[str] = OrderedSet()

    def enterMatchExprVar(self, ctx: MexprParser.MatchExprVarContext):
        self.used_variables.add(parse_tree_text(ctx.ID()))


class ConcreteSyntaxUsedVariablesCollector(IslaLanguageListener.IslaLanguageListener):
    def __init__(self):
        self.used_variables: OrderedSet[str] = OrderedSet()

    def collect_used_variables_in_mexpr(self, inp: str) -> None:
        lexer = MexprLexer(InputStream(inp))
        parser = MexprParser(antlr4.CommonTokenStream(lexer))
        parser._errHandler = BailPrintErrorStrategy()
        collector = ConcreteSyntaxMexprUsedVariablesCollector()
        antlr4.ParseTreeWalker().walk(collector, parser.matchExpr())
        self.used_variables.update(collector.used_variables)

    def enterForall(self, ctx: IslaLanguageParser.ForallContext):
        if ctx.varId:
            self.used_variables.add(parse_tree_text(ctx.varId))

    def enterForallMexpr(self, ctx: IslaLanguageParser.ForallMexprContext):
        if ctx.varId:
            self.used_variables.add(parse_tree_text(ctx.varId))
        self.collect_used_variables_in_mexpr(
            antlr_get_text_with_whitespace(ctx.STRING())[1:-1]
        )

    def enterExists(self, ctx: IslaLanguageParser.ExistsContext):
        if ctx.varId:
            self.used_variables.add(parse_tree_text(ctx.varId))

    def enterExistsMexpr(self, ctx: IslaLanguageParser.ExistsMexprContext):
        if ctx.varId:
            self.used_variables.add(parse_tree_text(ctx.varId))
        self.collect_used_variables_in_mexpr(
            antlr_get_text_with_whitespace(ctx.STRING())[1:-1]
        )


class BailPrintErrorStrategy(antlr4.BailErrorStrategy):
    def recover(self, recognizer: antlr4.Parser, e: antlr4.RecognitionException):
        recognizer._errHandler.reportError(recognizer, e)
        super().recover(recognizer, e)


def used_variables_in_concrete_syntax(
    inp: str | IslaLanguageParser.StartContext,
) -> OrderedSet[str]:
    if isinstance(inp, str):
        lexer = IslaLanguageLexer(InputStream(inp))
        parser = IslaLanguageParser(antlr4.CommonTokenStream(lexer))
        parser._errHandler = BailPrintErrorStrategy()
        context = parser.start()
    else:
        assert isinstance(inp, IslaLanguageParser.StartContext)
        context = inp

    collector = ConcreteSyntaxUsedVariablesCollector()
    antlr4.ParseTreeWalker().walk(collector, context)
    return collector.used_variables


def start_constant():
    return Constant("start", "<start>")


def univ_close_over_var_push_in(
    formula: Formula,
    var: BoundVariable,
    in_var: Variable = start_constant(),
    mexpr: Optional[BindExpression] = None,
    qfd_vars: Optional[BoundVariable | Iterable[BoundVariable]] = None,
) -> Formula:
    """
    Adds a universal quantifier over `var` with match expression `mexpr` and "in" variable `in_var`
    in `formula`, such that, if `formula` is a propositional combination or a universal quantifier,
    the new quantifier is pushed inside as much as possible.

    We consider pushing in possible if:
    1. `formula` is a propositional combination and
    1a. it has one argument in which `qfd_var` does not occur, *or*
    1b. `in_var` is bound by a quantifier inside one of the arguments; or
    2. `formula` is a universal formula that does not use `var` as container ("in") variable.

    :param formula: The formula into which to push in a new universal quantifier.
    :param var: The bound variable of the new universal quantifier.
    :param in_var: The container ("in") variable of the new universal quantifier.
    :param mexpr: The match expression of the new universal quantifier.
    :param qfd_vars: A variable to decide whether pushing in is possible or not. Defaults to `var`.
    :return: A formula with an added quantifier, or the original formula if `qfd_var` does
    not occur freely in `formula`.
    """

    if qfd_vars is None:
        qfd_vars = {var}
    elif isinstance(qfd_vars, BoundVariable):
        qfd_vars = {qfd_vars}
    else:
        qfd_vars = set(qfd_vars)

    mexpr_vars = set() if not mexpr else mexpr.bound_variables()
    all_new_bound_vars = qfd_vars | mexpr_vars

    if not all_new_bound_vars.intersection(formula.free_variables()):
        return formula

    if isinstance(formula, PropositionalCombinator):
        if any(
            not qfd_vars.intersection(arg.free_variables()) for arg in formula.args
        ) or any(
            in_var in BoundVariablesCollector().collect(arg) for arg in formula.args
        ):
            return type(formula)(
                *map(
                    lambda arg: univ_close_over_var_push_in(
                        arg, var, in_var, mexpr, qfd_vars
                    ),
                    formula.args,
                )
            )

    if isinstance(formula, ForallFormula) and var != formula.in_variable:
        return ForallFormula(
            formula.bound_variable,
            formula.in_variable,
            univ_close_over_var_push_in(
                formula.inner_formula, var, in_var, mexpr, qfd_vars
            ),
            formula.bind_expression,
        )

    return ForallFormula(var, in_var, formula, bind_expression=mexpr)


class AddMexprTransformer(NoopFormulaTransformer):
    def __init__(
        self,
        qfd_var: BoundVariable,
        mexprs: Iterable[BindExpression],
        grammar: Grammar,
    ):
        super().__init__()
        self.qfd_var: BoundVariable = qfd_var
        self.mexprs: Iterable[BindExpression] = mexprs
        self.grammar = grammar

    def transform_quantified_formula(self, formula: QuantifiedFormula) -> Formula:
        if formula.bound_variable != self.qfd_var:
            return formula

        if formula.bind_expression is not None:
            mexprs = self.__add_mexprs_to_qfr_with_existing_mexpr(formula)
        else:
            mexprs = self.mexprs

        return reduce(
            Formula.__and__ if isinstance(formula, ForallFormula) else Formula.__or__,
            [
                type(formula)(
                    formula.bound_variable,
                    formula.in_variable,
                    formula.inner_formula,
                    mexpr,
                )
                for mexpr in mexprs
            ],
        )

    def __add_mexprs_to_qfr_with_existing_mexpr(
        self, formula: QuantifiedFormula
    ) -> List[BindExpression]:
        orig_trees_and_paths = formula.bind_expression.to_tree_prefix(
            formula.bound_variable.n_type, self.grammar
        )

        mexprs = [
            self.__add_mexpr_to_qfr_with_existing_mexpr(
                formula, mexpr, orig_trees_and_paths
            )
            for mexpr in self.mexprs
        ]

        if not mexprs:
            raise RuntimeError(
                "Could not merge the match expression of a formula with new match expressions "
                + f"(there were conflicts), formula: {formula}, match expressions: {self.mexprs}"
            )

        return mexprs

    def __add_mexpr_to_qfr_with_existing_mexpr(
        self,
        formula: QuantifiedFormula,
        mexpr: BindExpression,
        orig_trees_and_paths: List[Tuple[DerivationTree, Dict[BoundVariable, Path]]],
    ) -> BindExpression:
        new_trees_and_paths = mexpr.to_tree_prefix(
            formula.bound_variable.n_type, self.grammar
        )

        product: List[
            Tuple[
                Tuple[DerivationTree, Dict[BoundVariable, Path]],
                Tuple[DerivationTree, Dict[BoundVariable, Path]],
            ]
        ] = [
            ((orig_tree, orig_paths), (new_tree, new_paths))
            for (orig_tree, orig_paths), (new_tree, new_paths) in itertools.product(
                orig_trees_and_paths, new_trees_and_paths
            )
            # The two paths maps conflict if (1) two paths bind different variables or
            # (2) one path to a bound variable is the prefix of another one.
            if not any(
                is_prefix(path, other_path)
                or is_prefix(other_path, path)
                or (path == other_path and var != other_var)
                for var, path in orig_paths.items()
                if not isinstance(var, DummyVariable)
                for other_var, other_path in new_paths.items()
                if not isinstance(other_var, DummyVariable)
            )
        ]

        for (orig_tree, orig_paths), (
            new_tree,
            new_paths,
        ) in product:
            # Merge the trees
            resulting_tree = orig_tree
            resulting_paths: Dict[Path, BoundVariable] = {
                path: var
                for var, path in orig_paths.items()
                if not isinstance(var, DummyVariable)
            }

            conflict = False
            for new_var, new_path in new_paths.items():
                monad = AddMexprTransformer.__merge_trees_at_path(
                    resulting_tree, new_tree, new_var, new_path
                )
                if not monad.is_present():
                    conflict = True
                    break

                resulting_tree = monad.get()
                if not isinstance(new_var, DummyVariable):
                    resulting_paths[new_path] = new_var

            if conflict:
                continue

            mexpr_elems = [
                resulting_paths[path] if path in resulting_paths else leaf.value
                for path, leaf in resulting_tree.leaves()
            ]

            return BindExpression(*mexpr_elems)

    @staticmethod
    def __merge_trees_at_path(
        merged_tree: DerivationTree,
        new_tree: DerivationTree,
        new_var: BoundVariable,
        new_path: Path,
    ) -> Maybe[Tuple[DerivationTree]]:
        # Take the more specific path. They should not conflict,
        # i.e., have a common sub-path pointing to the same nonterminal.

        if merged_tree.is_valid_path(new_path):
            # `resulting_tree` has a longer (or as long) path.
            if any(
                merged_tree.get_subtree(new_path[:idx]).value
                != new_tree.get_subtree(new_path[:idx]).value
                for idx in range(len(new_path))
            ):
                return Maybe.nothing()

            if not isinstance(new_var, DummyVariable):
                if merged_tree.get_subtree(new_path).children:
                    return Maybe.nothing()

            return Maybe(merged_tree)
        else:
            # `new_tree` has a longer (or as long) path.
            # First, find the valid prefix in `resulting_tree`.
            assert new_path
            valid_path = new_path[:-1]
            while valid_path and not merged_tree.is_valid_path(valid_path):
                valid_path = valid_path[:-1]

            if any(
                merged_tree.get_subtree(valid_path[:idx]).value
                != new_tree.get_subtree(valid_path[:idx]).value
                for idx in range(len(valid_path))
            ):
                return Maybe.nothing()

            return Maybe(
                merged_tree.replace_path(valid_path, new_tree.get_subtree(valid_path))
            )

    def transform_forall_formula(self, formula: ForallFormula) -> Formula:
        return self.transform_quantified_formula(formula)

    def transform_exists_formula(self, formula: ExistsFormula) -> Formula:
        return self.transform_quantified_formula(formula)


def add_mexpr_to_qfr_over_var(
    formula: Formula,
    qfd_var: BoundVariable,
    mexprs: Iterable[BindExpression],
    grammar: Grammar,
) -> Formula:
    return formula.transform(AddMexprTransformer(qfd_var, mexprs, grammar))


ParsedXPathExpr = ImmutableList[ImmutableList[Pair[str, int]]]


class ISLaEmitter(IslaLanguageListener.IslaLanguageListener):
    def __init__(
        self,
        grammar: Optional[Grammar | str] = None,
        structural_predicates: Optional[Set[StructuralPredicate]] = None,
        semantic_predicates: Optional[Set[SemanticPredicate]] = None,
    ):
        self.structural_predicates_map = (
            {}
            if not structural_predicates
            else {p.name: p for p in structural_predicates}
        )
        self.semantic_predicates_map = (
            {} if not semantic_predicates else {p.name: p for p in semantic_predicates}
        )

        self.result: Optional[Formula] = None
        self.constant: Constant = Constant("start", "<start>")
        self.formulas = {}
        self.smt_expressions: Dict[ParserRuleContext, str] = {}
        self.predicate_args = {}

        if grammar:
            if isinstance(grammar, str):
                self.grammar = parse_bnf(grammar)
            else:
                self.grammar = grammar

            self.canonical_grammar = canonical(self.grammar)
        else:
            self.grammar = None

        self.mgr = VariableManager(self.grammar)
        self.used_variables: Optional[OrderedSet[str]] = None

        self.vars_for_free_nonterminals: Dict[str, BoundVariable] = {}
        self.vars_for_xpath_expressions: Dict[ParsedXPathExpr, BoundVariable] = {}

    def parse_mexpr(self, inp: str, mgr: VariableManager) -> BindExpression:
        lexer = MexprLexer(InputStream(inp))
        parser = MexprParser(antlr4.CommonTokenStream(lexer))
        parser._errHandler = BailPrintErrorStrategy()
        mexpr_emitter = MExprEmitter(mgr)
        antlr4.ParseTreeWalker().walk(mexpr_emitter, parser.matchExpr())
        return BindExpression(*mexpr_emitter.result)

    def register_var_for_free_nonterminal(self, nonterminal: str) -> BoundVariable:
        if nonterminal in self.vars_for_free_nonterminals:
            return self.vars_for_free_nonterminals[nonterminal]

        assert nonterminal[0] == "<"
        assert nonterminal[-1] == ">"
        assert len(nonterminal) > 2

        fresh_var = fresh_bound_variable(
            self.used_variables | self.vars_for_free_nonterminals,
            BoundVariable(nonterminal[1:-1], nonterminal),
            add=False,
        )

        self.mgr.bv(fresh_var.name, fresh_var.n_type)
        self.vars_for_free_nonterminals[nonterminal] = fresh_var

        return fresh_var

    def register_var_for_xpath_expression(self, xpath_expr: str) -> BoundVariable:
        parsed_xpath_expr = self.parse_xpath_expr(xpath_expr)
        if parsed_xpath_expr in self.vars_for_xpath_expressions:
            return self.vars_for_xpath_expressions[parsed_xpath_expr]

        last_nonterminal: str = parsed_xpath_expr[-1][-1][0]
        assert is_nonterminal(last_nonterminal)

        fresh_var = fresh_bound_variable(
            self.used_variables
            | {var.name for var in self.vars_for_free_nonterminals.values()}
            | {var.name for var in self.vars_for_xpath_expressions.values()},
            BoundVariable(last_nonterminal[1:-1], last_nonterminal),
            add=False,
        )

        self.mgr.bv(fresh_var.name, fresh_var.n_type)
        self.vars_for_xpath_expressions[parsed_xpath_expr] = fresh_var

        return fresh_var

    @staticmethod
    @lru_cache(100)
    def parse_xpath_expr(xpath_expr: str) -> ParsedXPathExpr:
        """
        The returned list contains one element per XPath "segment," i.e., a chain
        that is not interrupted by `..`. Each sub list contains one element for
        each `.`-separated chain of an XPath expression consisting of the name of
        the accessed element and an index. Indices are counted from 0, as opposed
        to 1 in the concrete syntax.

        :param xpath_expr:  The XPath expression to process.
        :return: The result of parsing the XPath expression.
        """
        return tuple(
            [
                tuple(
                    [
                        (elem, 0)
                        if "[" not in elem
                        else (elem.split("[")[0], int(elem.split("[")[1][:-1]) - 1)
                        for elem in seg.split(".")
                    ]
                )
                for seg in xpath_expr.split("..")
            ]
        )

    def close_over_free_nonterminals(self, formula: Formula) -> Formula:
        # When closing over "free nonterminals", we exclude those (for the simple first run)
        # who appear as a first element in an XPath expression. Those are quantified over
        # afterward; else we'd obtain spurious quantifiers.
        free_nonterminal_vars = [
            var
            for nonterminal, var in self.vars_for_free_nonterminals.items()
            if all(
                not segments or not segments[0] or segments[0][0][0] != nonterminal
                for segments in self.vars_for_xpath_expressions.keys()
            )
        ]

        free_nonterminal_vars_also_in_xpath_expr = {
            nonterminal: var
            for nonterminal, var in self.vars_for_free_nonterminals.items()
            if var not in free_nonterminal_vars
        }

        for var in reversed(free_nonterminal_vars):
            formula = univ_close_over_var_push_in(formula, var)

        # We group segments by their first element such that we introduce quantifiers
        # correctly. For example, if we have expressions `<string>.<length>.<low-byte>`
        # and `<string>.<length>.<high-byte>` in different atoms, both need to be put
        # into the scope of a single new quantifier over `<string>`. For this, we have
        # to collect the fresh variables introduced for both expressions.
        # [(k, list(g)) for k, g in itertools.groupby(
        #     sorted(tuple(self.vars_for_xpath_expressions.items())),
        #     lambda p: p[0][0][0]
        # )]

        # fresh_vars: Dict[str, BoundVariable] = {}

        # for segments, bound_variable in list(self.vars_for_xpath_expressions.items()):
        for first_segment_elem, group in itertools.groupby(
            sorted(tuple(self.vars_for_xpath_expressions.items())), lambda p: p[0][0][0]
        ):
            if is_nonterminal(first_segment_elem[0]):
                var_type = first_segment_elem[0]
                var = fresh_bound_variable(
                    self.used_variables,
                    BoundVariable(var_type[1:-1], var_type),
                    add=False,
                )
                self.used_variables.add(var.name)

                if var_type in free_nonterminal_vars_also_in_xpath_expr:
                    formula = formula.substitute_variables(
                        {free_nonterminal_vars_also_in_xpath_expr[var_type]: var}
                    )

                group_xpath_exprs = list(group)
                qfd_vars = {var for _, var in group_xpath_exprs}
                formula = univ_close_over_var_push_in(formula, var, qfd_vars=qfd_vars)

                for segments, bound_variable in group_xpath_exprs:
                    new_segments = list_set(
                        segments, 0, list_set(segments[0], 0, (var.name, 0))
                    )
                    del self.vars_for_xpath_expressions[segments]
                    self.vars_for_xpath_expressions[new_segments] = bound_variable

        return formula

    def close_over_xpath_expressions(self, formula: Formula) -> Formula:
        if not self.vars_for_xpath_expressions:
            return formula

        assert (
            self.grammar is not None
        ), 'You need to pass a grammar to process "XPath" expressions in formulas.'

        # We assume all XPath expressions start with a variable, e.g., `var.nt1[1].nt2[1]..nt3.nt4[0]`.
        # If one started with a nonterminal, it should have been existentially quantified over.
        assert all(
            not is_nonterminal(parsed_xpath_expr[0][0][0])
            for parsed_xpath_expr in self.vars_for_xpath_expressions
        )

        # We reduce the first XPath expression and proceed recursively until `self.var_for_xpath_expressions`
        # is empty. Consequently, it's crucial that we update this map as we proceed.

        xpath_expr: ParsedXPathExpr = next(iter(self.vars_for_xpath_expressions))
        assert xpath_expr
        final_bound_variable = self.vars_for_xpath_expressions[xpath_expr]
        del self.vars_for_xpath_expressions[xpath_expr]

        # Either, the first XPath segment consists of multiple elements, or we have more than one segment.
        assert len(xpath_expr) > 1 or len(xpath_expr[0]) > 1

        if len(xpath_expr) > 1 and len(xpath_expr[0]) == 1:
            # If the first of more than one XPath segments is a variable, we can eliminate
            # that segment by introducing a quantifier.
            in_var_name = xpath_expr[0][0][0]
            assert not is_nonterminal(in_var_name)
            in_var = next(
                var
                for var in VariablesCollector().collect(formula)
                if var.name == in_var_name
            )
            bound_var_type = xpath_expr[1][0][0]
            assert is_nonterminal(bound_var_type)

            assert (
                len(xpath_expr) == 2 and len(xpath_expr[1]) == 1
            ), "If this fails, uncomment the else branch in the source code."

            # NOTE: Previously, the following else branch was in place here, but it was
            #       never executed. Leaving this here for the moment in case it covers
            #       an edge case that was not explicitly tested (2022-09-27).
            # else:
            #     assert False
            #     bound_var = fresh_bound_variable(
            #         self.used_variables,
            #         BoundVariable(bound_var_type[1:-1], bound_var_type),
            #         add=False,
            #     )
            #     self.used_variables.add(bound_var.name)
            #
            #     xpath_expr = list_set(
            #         xpath_expr[1:], 0, list_set(xpath_expr[1], 0, (bound_var.name, 0))
            #     )
            #     self.vars_for_xpath_expressions[xpath_expr] = final_bound_variable

            formula = univ_close_over_var_push_in(
                formula,
                final_bound_variable,
                in_var=in_var,
                qfd_vars=final_bound_variable,
            )

            return self.close_over_xpath_expressions(formula)

        def find_var(var_name: str, error_message: str) -> Variable:
            return (
                Maybe.from_iterator(
                    var
                    for var in VariablesCollector.collect(formula)
                    if var.name == var_name
                )
                .raise_if_not_present(lambda: RuntimeError(error_message))
                .get()
            )

        first_var = cast(
            BoundVariable,
            find_var(
                xpath_expr[0][0][0],
                f"Unknown variable {xpath_expr[0][0][0]} in XPath expression.",
            ),
        )

        # We eliminate the first XPath segment by
        #
        # 1. Creating a suitable match expression. If there is only one XPath segment,
        #    the match expression binds `final_bound_variable`; otherwise, it binds
        #    a fresh variable.
        # 2. We attach the match expression to the corresponding quantifier, which might
        #    involve "merging" match expressions.
        # 3. We update `self.vars_for_xpath_expressions if more XPath segments remain.
        #    Then, we replace the first remaining segment to point by the new bound variable.
        # 4. Finally, we proceed recursively until `self.vars_for_xpath_expressions` is empty.

        # 1. Create a suitable match expression.
        bound_var, match_expressions = self.__create_match_expr_for_first_xpath_segment(
            xpath_expr, final_bound_variable, first_var
        )

        # 2. Attach match expression to existing quantifier
        formula = add_mexpr_to_qfr_over_var(
            formula, first_var, match_expressions, self.grammar
        )

        # 3. Update `self.vars_for_xpath_expressions if more XPath segments remain.
        if len(xpath_expr) > 1:
            self.vars_for_xpath_expressions[
                list_set(xpath_expr, 0, ((bound_var.name, 0),))
            ] = final_bound_variable

        # 4. Proceed recursively.
        return self.close_over_xpath_expressions(formula)

    def __create_match_expr_for_first_xpath_segment(
        self,
        xpath_expr: ParsedXPathExpr,
        final_bound_variable: BoundVariable,
        first_var: BoundVariable,
    ) -> Tuple[BoundVariable, List[BindExpression]]:
        partial_mexpr_trees = self.expand_mexpr_trees(first_var.n_type, xpath_expr[0])
        if not partial_mexpr_trees:
            raise RuntimeError(
                "Could not convert XPath expressions to match expressions. "
                + "Please check the XPath expressions in your formula, including for conflicts."
            )

        if len(xpath_expr) == 1:
            bound_var = final_bound_variable
        else:
            bound_var_type = xpath_expr[0][-1][0]
            assert is_nonterminal(bound_var_type)
            bound_var = fresh_bound_variable(
                self.used_variables,
                BoundVariable(bound_var_type[1:-1], bound_var_type),
                add=False,
            )
            self.used_variables.add(bound_var.name)

        match_expressions = []
        for (
            expanded_match_expression,
            paths_to_bound_vars,
        ) in partial_mexpr_trees.items():
            assert len(paths_to_bound_vars) == 1
            paths_to_bound_vars_map = dict(zip(paths_to_bound_vars, [bound_var]))
            mexpr_elems = []
            for path, leaf in expanded_match_expression.leaves():
                if path in paths_to_bound_vars_map:
                    mexpr_elems.append(paths_to_bound_vars_map[path])
                else:
                    mexpr_elems.append(leaf.value)

            match_expressions.append(BindExpression(*mexpr_elems))

        return bound_var, match_expressions

    def expand_mexpr_trees(
        self, start_nonterminal: str, xpath_segment: ImmutableList[Tuple[str, int]]
    ):
        result: Dict[DerivationTree, List[Path]] = {
            DerivationTree(start_nonterminal): [()]
        }

        for nonterminal, position in xpath_segment[1:]:
            old_partial_mexpr_trees = dict(result)
            result: Dict[DerivationTree, List[Path]] = {}

            for partial_tree, paths in old_partial_mexpr_trees.items():
                path_to_expand = paths[-1]
                subtree = partial_tree.get_subtree(path_to_expand)

                assert subtree.children is None

                # Find expansions of including more than `position` occurrences of `nonterminal`.
                expansions = [
                    expansion
                    for expansion in self.canonical_grammar[subtree.value]
                    if sum([1 if elem == nonterminal else 0 for elem in expansion])
                    > position
                ]

                # Replace the indicated position in each `partial_mexpr_trees` list
                # with the new expansion; the new position points to the `nonterminal` element
                # that should be expanded next.
                for expansion in expansions:
                    result[
                        partial_tree.replace_path(
                            path_to_expand,
                            DerivationTree(
                                partial_tree.get_subtree(path_to_expand).value,
                                [
                                    DerivationTree(elem)
                                    if is_nonterminal(elem)
                                    else DerivationTree(elem, [])
                                    for elem in expansion
                                ],
                            ),
                        )
                    ] = paths[:-1] + [
                        path_to_expand + (nth_occ(expansion, nonterminal, position),)
                    ]

                assert all(
                    tree.get_subtree(paths[-1]).value == nonterminal
                    for tree, paths in result.items()
                )

        return result

    def enterStart(self, ctx: IslaLanguageParser.StartContext):
        self.used_variables = used_variables_in_concrete_syntax(ctx)

    def exitStart(self, ctx: IslaLanguageParser.StartContext):
        try:
            formula: Formula = self.mgr.create(self.formulas[ctx.formula()])
            formula = ensure_unique_bound_variables(formula)
            self.used_variables.update(
                {var.name for var in VariablesCollector.collect(formula)}
            )
            self.result = ensure_unique_bound_variables(
                self.close_over_xpath_expressions(
                    self.close_over_free_nonterminals(formula)
                )
            )

            free_variables = [
                var
                for var in self.result.free_variables()
                if not isinstance(var, Constant)
            ]
            if free_variables:
                raise SyntaxError(
                    "Unbound variables: "
                    + ", ".join(map(str, free_variables))
                    + f" in formula\n{unparse_isla(formula)}"
                )
        except RuntimeError as exc:
            raise SyntaxError(str(exc))

    def get_var(
        self, var_name: str, var_type: Optional[str] = None
    ) -> BoundVariable | Constant:
        if var_name == self.constant.name:
            return self.constant

        return self.mgr.bv(var_name, var_type)

    def known_var_names(self) -> Set[str]:
        return self.mgr.all_var_names() | {self.constant.name}

    def exitConstDecl(self, ctx: IslaLanguageParser.ConstDeclContext):
        self.constant = Constant(
            parse_tree_text(ctx.ID()), parse_tree_text(ctx.varType())
        )

    def enterQfdFormula(
        self, ctx: IslaLanguageParser.ForallContext | IslaLanguageParser.ExistsContext
    ):
        if not ctx.varId:
            var_type = parse_tree_text(ctx.boundVarType)
            self.register_var_for_free_nonterminal(var_type)

    def enterForall(self, ctx: IslaLanguageParser.ForallContext):
        self.enterQfdFormula(ctx)

    def enterExists(self, ctx: IslaLanguageParser.ExistsContext):
        self.enterQfdFormula(ctx)

    def exitQfdFormula(
        self,
        ctx: IslaLanguageParser.ForallContext
        | IslaLanguageParser.ExistsContext
        | IslaLanguageParser.ForallMexprContext
        | IslaLanguageParser.ExistsMexprContext,
        mexpr=False,
    ):
        is_forall = str(ctx.children[0]) == "forall"

        if mexpr:
            mexpr = self.parse_mexpr(
                antlr_get_text_with_whitespace(ctx.STRING())[1:-1], self.mgr
            )
        else:
            mexpr = None

        var_type = parse_tree_text(ctx.boundVarType)

        if ctx.varId:
            var_id = parse_tree_text(ctx.varId)

            # if self.mgr.var_declared(var_id):
            #     raise SyntaxError(
            #         f"Variable {var_id} already declared "
            #         f"(line {ctx.varId.line}, column {ctx.varId.column})"
            #     )
        else:
            var = self.register_var_for_free_nonterminal(var_type)
            # This "free" nonterminal is bound now; remove it from
            # the free nonterminals map.
            del self.vars_for_free_nonterminals[var_type]
            # ... and the XPath expressions map.
            for segments, final_var in list(self.vars_for_xpath_expressions.items()):
                if segments[0][0][0] == var_type:
                    del self.vars_for_xpath_expressions[segments]
                    new_segments = list_set(
                        segments, 0, list_set(segments[0], 0, (var.name, 0))
                    )
                    self.vars_for_xpath_expressions[new_segments] = final_var
            var_id = var.name

        if ctx.inId:
            in_var = self.get_var(parse_tree_text(ctx.inId))
        elif ctx.inVarType and parse_tree_text(ctx.inVarType) != "<start>":
            in_var = self.register_var_for_free_nonterminal(
                parse_tree_text(ctx.inVarType)
            )
        else:
            in_var = start_constant()

        self.formulas[ctx] = self.mgr.create(
            (ForallFormula if is_forall else ExistsFormula)(
                self.get_var(var_id, var_type),
                in_var,
                self.formulas[ctx.formula()],
                bind_expression=mexpr,
            ),
            safe=False,
        )

    def exitForall(self, ctx: IslaLanguageParser.ForallContext):
        self.exitQfdFormula(ctx)

    def exitExists(self, ctx: IslaLanguageParser.ExistsContext):
        self.exitQfdFormula(ctx)

    def exitForallMexpr(self, ctx: IslaLanguageParser.ForallMexprContext):
        self.exitQfdFormula(ctx, mexpr=True)

    def exitExistsMexpr(self, ctx: IslaLanguageParser.ExistsMexprContext):
        self.exitQfdFormula(ctx, mexpr=True)

    def exitNegation(self, ctx: IslaLanguageParser.NegationContext):
        self.formulas[ctx] = -self.formulas[ctx.formula()]

    def exitConjunction(self, ctx: IslaLanguageParser.ConjunctionContext):
        self.formulas[ctx] = (
            self.formulas[ctx.formula(0)] & self.formulas[ctx.formula(1)]
        )

    def exitDisjunction(self, ctx: IslaLanguageParser.DisjunctionContext):
        self.formulas[ctx] = (
            self.formulas[ctx.formula(0)] | self.formulas[ctx.formula(1)]
        )

    def exitImplication(self, ctx: IslaLanguageParser.ImplicationContext):
        left = self.formulas[ctx.formula(0)]
        right = self.formulas[ctx.formula(1)]
        self.formulas[ctx] = -left | right

    def exitEquivalence(self, ctx: IslaLanguageParser.EquivalenceContext):
        left = self.formulas[ctx.formula(0)]
        right = self.formulas[ctx.formula(1)]
        self.formulas[ctx] = (-left & -right) | (left & right)

    def exitExclusiveOr(self, ctx: IslaLanguageParser.ExclusiveOrContext):
        left = self.formulas[ctx.formula(0)]
        right = self.formulas[ctx.formula(1)]
        self.formulas[ctx] = (left & -right) | (-left & right)

    def exitPredicateAtom(self, ctx: IslaLanguageParser.PredicateAtomContext):
        predicate_name = parse_tree_text(ctx.ID())
        if (
            predicate_name not in self.structural_predicates_map
            and predicate_name not in self.semantic_predicates_map
        ):
            raise SyntaxError(
                f"Unknown predicate {predicate_name} in {parse_tree_text(ctx)}"
            )

        args = [self.predicate_args[arg] for arg in ctx.predicateArg()]

        is_structural = predicate_name in self.structural_predicates_map

        predicate = (
            self.structural_predicates_map[predicate_name]
            if is_structural
            else self.semantic_predicates_map[predicate_name]
        )

        if len(args) != predicate.arity:
            raise SyntaxError(
                f"Unexpected number {len(args)} for predicate {predicate_name} "
                f"({predicate.arity} expected) in {parse_tree_text(ctx)} "
                f"(line {ctx.ID().symbol.line}, column {ctx.ID().symbol.column}"
            )

        if is_structural:
            self.formulas[ctx] = StructuralPredicateFormula(predicate, *args)
        else:
            self.formulas[ctx] = SemanticPredicateFormula(predicate, *args)

    def exitPredicateArg(self, ctx: IslaLanguageParser.PredicateArgContext):
        if ctx.ID():
            self.predicate_args[ctx] = self.get_var(parse_tree_text(ctx.ID()))
        elif ctx.INT():
            self.predicate_args[ctx] = int(parse_tree_text(ctx))
        elif ctx.STRING():
            self.predicate_args[ctx] = parse_tree_text(ctx)[1:-1]
        elif ctx.VAR_TYPE():
            variable = self.register_var_for_free_nonterminal(
                parse_tree_text(ctx.VAR_TYPE())
            )
            self.predicate_args[ctx] = variable
        elif ctx.XPATHEXPR():
            variable = self.register_var_for_xpath_expression(parse_tree_text(ctx))
            self.predicate_args[ctx] = variable
        else:
            assert False, f"Unexpected predicate argument: {parse_tree_text(ctx)}"

    def exitSMTFormula(self, ctx: IslaLanguageParser.SMTFormulaContext):
        formula_text = self.smt_expressions[ctx.sexpr()]
        formula_text = formula_text.replace(r"\"", '""')

        # We have to replace XPath expressions in the formula, since they can break
        # the parsing (e.g., with `<a>[2]` indexed expressions).
        # for xpath_expr in self.vars_for_xpath_expressions:
        #     formula_text = formula_text.replace(xpath_expr, f'var_{abs(hash(xpath_expr))}')

        try:
            z3_constr = z3.parse_smt2_string(
                f"(assert {formula_text})",
                decls=(
                    {var: z3.String(var) for var in self.known_var_names()}
                    | {
                        var.name: z3.String(var.name)
                        for var in (
                            set(self.vars_for_free_nonterminals.values())
                            | set(self.vars_for_xpath_expressions.values())
                        )
                    }
                ),
            )[0]
        except z3.Z3Exception as exp:
            raise SyntaxError(
                f"Error parsing SMT formula '{formula_text}', {exp.value.decode().strip()}"
            )

        free_vars = [self.get_var(str(s)) for s in get_symbols(z3_constr)]
        self.formulas[ctx] = SMTFormula(z3_constr, *free_vars)

    def exitSexprTrue(self, ctx: IslaLanguageParser.SexprTrueContext):
        self.smt_expressions[ctx] = antlr_get_text_with_whitespace(ctx)

    def exitSexprFalse(self, ctx: IslaLanguageParser.SexprFalseContext):
        self.smt_expressions[ctx] = antlr_get_text_with_whitespace(ctx)

    def exitSexprNum(self, ctx: IslaLanguageParser.SexprNumContext):
        self.smt_expressions[ctx] = antlr_get_text_with_whitespace(ctx)

    def exitSexprId(self, ctx: IslaLanguageParser.SexprIdContext):
        id_text = parse_tree_text(ctx.ID())
        self.smt_expressions[ctx] = id_text

        if not ISLaEmitter.is_protected_smtlib_keyword(id_text):
            self.get_var(id_text)  # Simply register variable

    def exitSexprXPathExpr(self, ctx: IslaLanguageParser.SexprXPathExprContext):
        new_var = self.register_var_for_xpath_expression(parse_tree_text(ctx))
        self.smt_expressions[ctx] = new_var.name

    def exitSexprFreeId(self, ctx: IslaLanguageParser.SexprFreeIdContext):
        nonterminal = parse_tree_text(ctx.VAR_TYPE())
        var = self.register_var_for_free_nonterminal(nonterminal)
        self.smt_expressions[ctx] = var.name

    def exitSexprStr(self, ctx: IslaLanguageParser.SexprStrContext):
        self.smt_expressions[ctx] = antlr_get_text_with_whitespace(ctx)

    def exitSexprOp(self, ctx: IslaLanguageParser.SexprOpContext):
        self.smt_expressions[ctx] = parse_tree_text(ctx)

    def exitSexprPrefix(self, ctx: IslaLanguageParser.SexprPrefixContext):
        if not ctx.sexpr():
            self.smt_expressions[ctx] = parse_tree_text(ctx.op)
        else:
            self.smt_expressions[
                ctx
            ] = f'({parse_tree_text(ctx.op)} {" ".join([self.smt_expressions[child] for child in ctx.sexpr()])})'

    def exitSexprInfixReStr(self, ctx: IslaLanguageParser.SexprInfixReStrContext):
        self.smt_expressions[
            ctx
        ] = f"({parse_tree_text(ctx.op)} {self.smt_expressions[ctx.sexpr(0)]} {self.smt_expressions[ctx.sexpr(1)]})"

    def exitSexprInfixPlusMinus(
        self, ctx: IslaLanguageParser.SexprInfixPlusMinusContext
    ):
        self.smt_expressions[
            ctx
        ] = f"({parse_tree_text(ctx.op)} {self.smt_expressions[ctx.sexpr(0)]} {self.smt_expressions[ctx.sexpr(1)]})"

    def exitSexprInfixMulDiv(self, ctx: IslaLanguageParser.SexprInfixMulDivContext):
        self.smt_expressions[
            ctx
        ] = f"({parse_tree_text(ctx.op)} {self.smt_expressions[ctx.sexpr(0)]} {self.smt_expressions[ctx.sexpr(1)]})"

    def exitSexprInfixEq(self, ctx: IslaLanguageParser.SexprInfixEqContext):
        self.smt_expressions[
            ctx
        ] = f"({parse_tree_text(ctx.op)} {self.smt_expressions[ctx.sexpr(0)]} {self.smt_expressions[ctx.sexpr(1)]})"

    # def exitSepxrParen(self, ctx: IslaLanguageParser.SepxrParenContext):
    #     self.smt_expressions[ctx] = self.smt_expressions[ctx.sexpr()]

    def exitSepxrApp(self, ctx: IslaLanguageParser.SepxrAppContext):
        if not ctx.sexpr():
            self.smt_expressions[ctx] = parse_tree_text(ctx.op)
        else:
            self.smt_expressions[ctx] = (
                "("
                + " ".join([self.smt_expressions[child] for child in ctx.sexpr()])
                + ")"
            )

    def exitExistsInt(self, ctx: IslaLanguageParser.ExistsIntContext):
        var_id = parse_tree_text(ctx.ID())

        if self.mgr.var_declared(var_id):
            raise SyntaxError(
                f"Variable {var_id} already declared "
                f"(line {ctx.varId.symbol.line}, column {ctx.varId.symbol.column})"
            )

        self.formulas[ctx] = ExistsIntFormula(
            self.get_var(var_id, Variable.NUMERIC_NTYPE), self.formulas[ctx.formula()]
        )

    def exitForallInt(self, ctx: IslaLanguageParser.ForallIntContext):
        var_id = parse_tree_text(ctx.ID())

        if self.mgr.var_declared(var_id):
            raise SyntaxError(
                f"Variable {var_id} already declared "
                f"(line {ctx.varId.symbol.line}, column {ctx.varId.symbol.column})"
            )

        self.formulas[ctx] = ForallIntFormula(
            self.get_var(var_id, Variable.NUMERIC_NTYPE), self.formulas[ctx.formula()]
        )

    def exitParFormula(self, ctx: IslaLanguageParser.ParFormulaContext):
        self.formulas[ctx] = self.formulas[ctx.formula()]

    @staticmethod
    def is_protected_smtlib_keyword(symbol: str) -> bool:
        if symbol in {"let", "forall", "exists", "match", "!", "ite"}:
            return True

        try:
            z3.parse_smt2_string(f"(assert ({symbol} 1))")
            return True
        except Z3Exception as exc:
            return "unknown constant" not in str(exc)


def parse_isla(
    inp: str,
    grammar: Optional[Grammar] = None,
    structural_predicates: Optional[Set[StructuralPredicate]] = None,
    semantic_predicates: Optional[Set[SemanticPredicate]] = None,
) -> Formula:
    lexer = IslaLanguageLexer(InputStream(inp))
    parser = IslaLanguageParser(antlr4.CommonTokenStream(lexer))
    parser._errHandler = BailPrintErrorStrategy()
    isla_emitter = ISLaEmitter(grammar, structural_predicates, semantic_predicates)
    antlr4.ParseTreeWalker().walk(isla_emitter, parser.start())
    return isla_emitter.result


class BnfEmitter(bnfListener.bnfListener):
    def __init__(self):
        self.result: Optional[Grammar] = None
        self.partial_results = {}

    def exitBnf_grammar(self, ctx: bnfParser.Bnf_grammarContext):
        self.result = {}
        for derivation_rule_ctx in ctx.derivation_rule():
            derivation_rule = self.partial_results[derivation_rule_ctx]
            assert isinstance(derivation_rule[0], str)
            assert isinstance(derivation_rule[1], list)
            assert all(
                isinstance(alternative, str) for alternative in derivation_rule[1]
            )
            self.result[derivation_rule[0]] = derivation_rule[1]

    def exitDerivation_rule(self, ctx: bnfParser.Derivation_ruleContext):
        self.partial_results[ctx] = (
            parse_tree_text(ctx.NONTERMINAL()),
            [self.partial_results[alternative] for alternative in ctx.alternative()],
        )

    def exitAlternative(self, ctx: bnfParser.AlternativeContext):
        elems = []
        for child in ctx.children:
            child_text = parse_tree_text(child)
            if child_text and child_text[0] == '"':
                assert child_text[-1] == '"'
                child_text = child_text[1:-1]

            elems.append(instantiate_escaped_symbols(child_text))
        self.partial_results[ctx] = "".join(elems)


def parse_bnf(inp: str) -> Grammar:
    lexer = bnfLexer(InputStream(inp))
    parser = bnfParser(antlr4.CommonTokenStream(lexer))
    parser._errHandler = BailPrintErrorStrategy()
    bnf_emitter = BnfEmitter()
    antlr4.ParseTreeWalker().walk(bnf_emitter, parser.bnf_grammar())
    return bnf_emitter.result


class ISLaUnparser:
    def __init__(self, formula: Formula, indent="  "):
        assert isinstance(formula, Formula)
        self.formula = formula
        self.indent = indent

    def unparse(self) -> str:
        result: str = ""

        try:
            constant = next(
                (
                    c
                    for c in VariablesCollector.collect(self.formula)
                    if isinstance(c, Constant) and not c.is_numeric()
                )
            )

            if constant != Constant("start", "<start>"):
                result += f"const {constant.name}: {constant.n_type};\n\n"
        except StopIteration:
            pass

        result += "\n".join(self._unparse_constraint(self.formula))

        return result

    def _unparse_constraint(self, formula: Formula) -> List[str]:
        if isinstance(formula, QuantifiedFormula):
            return self._unparse_quantified_formula(formula)
        elif isinstance(formula, ExistsIntFormula):
            return self._unparse_exists_int_formula(formula)
        elif isinstance(formula, ForallIntFormula):
            return self._unparse_forall_int_formula(formula)
        elif isinstance(formula, ConjunctiveFormula) or isinstance(
            formula, DisjunctiveFormula
        ):
            return self._unparse_propositional_combination(formula)
        elif isinstance(formula, NegatedFormula):
            return self._unparse_negated_formula(formula)
        elif isinstance(formula, StructuralPredicateFormula) or isinstance(
            formula, SemanticPredicateFormula
        ):
            return self._unparse_predicate_formula(formula)
        elif isinstance(formula, SMTFormula):
            return self._unparse_smt_formula(formula)
        else:
            raise NotImplementedError(
                f"Unparsing of formulas of type {type(formula).__name__} not implemented."
            )

    def _unparse_match_expr(self, match_expr: BindExpression | None) -> str:
        return "" if match_expr is None else f'="{match_expr}"'

    def _unparse_quantified_formula(self, formula: QuantifiedFormula) -> List[str]:
        qfr = "forall" if isinstance(formula, ForallFormula) else "exists"
        result = [
            f"{qfr} {formula.bound_variable.n_type} {formula.bound_variable.name}"
            f"{self._unparse_match_expr(formula.bind_expression)} in {formula.in_variable}:"
        ]
        child_result = self._unparse_constraint(formula.inner_formula)
        result += [self.indent + line for line in child_result]

        return result

    def _unparse_propositional_combination(
        self, formula: ConjunctiveFormula | DisjunctiveFormula
    ):
        combinator = "and" if isinstance(formula, ConjunctiveFormula) else "or"
        child_results = [self._unparse_constraint(child) for child in formula.args]

        for idx, child_result in enumerate(child_results[:-1]):
            child_results[idx][-1] = child_results[idx][-1] + f" {combinator}"

        for idx, child_result in enumerate(child_results[1:]):
            child_results[idx] = [" " + line for line in child_results[idx]]

        child_results[0][0] = "(" + child_results[0][0][1:]
        child_results[-1][-1] += ")"

        return [line for child_result in child_results for line in child_result]

    def _unparse_predicate_formula(
        self, formula: StructuralPredicateFormula | SemanticPredicateFormula
    ):
        return [str(formula)]

    def _unparse_smt_formula(self, formula):
        return [smt_expr_to_str(formula.formula)]

        # result = formula.formula.sexpr()
        # # str.to_int is str.to.int in Z3; use this to preserve idempotency of parsing/unparsing
        # result = result.replace("str.to_int", "str.to.int")
        # return [result]

    def _unparse_negated_formula(self, formula):
        child_results = [self._unparse_constraint(child) for child in formula.args]
        result = [line for child_result in child_results for line in child_result]
        result[0] = "not(" + result[0]
        result[-1] += ")"
        return result

    def _unparse_forall_int_formula(self, formula):
        result = [f"forall int {formula.bound_variable.name}:"]
        child_result = self._unparse_constraint(formula.inner_formula)
        result += [self.indent + line for line in child_result]
        return result

    def _unparse_exists_int_formula(self, formula):
        result = [f"exists int {formula.bound_variable.name}:"]
        child_result = self._unparse_constraint(formula.inner_formula)
        result += [self.indent + line for line in child_result]
        return result


def unparse_isla(formula: Formula) -> str:
    return ISLaUnparser(formula).unparse()


def unparse_grammar(grammar: Grammar) -> str:
    def escape(elem: str) -> str:
        return (
            elem.replace("\\", r"\\")
            .replace('"', r"\"")
            .replace("\n", r"\n")
            .replace("\r", r"\r")
            .replace("\t", r"\t")
        )

    return "\n".join(
        f"{symbol} ::= "
        + " | ".join(
            '""'
            if not expansion
            else " ".join(
                (elem if is_nonterminal(elem) else f'"{escape(elem)}"')
                for elem in expansion
            )
            for expansion in expansions
        )
        for symbol, expansions in canonical(grammar).items()
    )


def get_conjuncts(formula: Formula) -> List[Formula]:
    return [
        conjunct
        for disjunct in split_disjunction(formula)
        for conjunct in split_conjunction(disjunct)
    ]


T = TypeVar("T")


def fresh_variable(
    used: MutableSet[Variable | str],
    base_name: str,
    n_type: str,
    constructor: Callable[[str, str], T],
    add: bool = True,
) -> T:
    name = base_name
    idx = 0
    while any(
        (used_var.name if isinstance(used_var, Variable) else used_var) == name
        for used_var in used
    ):
        name = f"{base_name}_{idx}"
        idx += 1

    result = constructor(name, n_type)
    if add:
        used.add(result)

    return result


def fresh_constant(
    used: MutableSet[Variable | str], proposal: Constant, add: bool = True
) -> Constant:
    return fresh_variable(used, proposal.name, proposal.n_type, Constant, add)


def fresh_bound_variable(
    used: MutableSet[Variable | str], proposal: BoundVariable, add: bool = True
) -> BoundVariable:
    return fresh_variable(used, proposal.name, proposal.n_type, BoundVariable, add)


def instantiate_top_constant(formula: Formula, tree: DerivationTree) -> Formula:
    top_constant: Constant = next(
        c
        for c in VariablesCollector.collect(formula)
        if isinstance(c, Constant) and not c.is_numeric()
    )
    return formula.substitute_expressions({top_constant: tree})


@lru_cache(maxsize=None)
def flatten_bound_elements(
    orig_bound_elements: Tuple[Union[BoundVariable, Tuple[BoundVariable, ...]], ...],
    grammar: ImmutableGrammar,
    in_nonterminal: Optional[str] = None,
) -> Tuple[Tuple[BoundVariable, ...], ...]:
    """Returns all possible bound elements lists where each contained optional either has
    been chosen or removed. If this BindExpression has no optionals, the returned list is
    a singleton."""
    bound_elements_combinations: Tuple[Tuple[BoundVariable, ...], ...] = ()

    # Consider all possible on/off combinations for optional elements
    optionals = [elem for elem in orig_bound_elements if isinstance(elem, tuple)]

    if not optionals:
        return (orig_bound_elements,)

    for combination in powerset(optionals):
        # Inline all chosen, remove all not chosen optionals
        raw_bound_elements: List[BoundVariable, ...] = []
        for bound_element in orig_bound_elements:
            if not isinstance(bound_element, tuple):
                raw_bound_elements.append(bound_element)
                continue

            if bound_element in combination:
                raw_bound_elements.extend(bound_element)

        bound_elements: List[BoundVariable] = []
        for bound_element in raw_bound_elements:
            # We have to merge consecutive dummy variables representing terminal symbols
            # ...and to split result elements containing two variables representing nonterminal symbols
            if (
                isinstance(bound_element, DummyVariable)
                and not is_nonterminal(bound_element.n_type)
                and bound_elements
                and isinstance(bound_elements[-1], DummyVariable)
                and not is_nonterminal(bound_elements[-1].n_type)
            ):
                bound_elements[-1] = DummyVariable(
                    bound_elements[-1].n_type + bound_element.n_type
                )
                continue

            bound_elements.append(bound_element)

        if is_valid_combination(tuple(bound_elements), grammar, in_nonterminal):
            bound_elements_combinations += (tuple(bound_elements),)

    return bound_elements_combinations


@lru_cache(maxsize=None)
def is_valid_combination(
    combination: Sequence[BoundVariable],
    immutable_grammar: ImmutableGrammar,
    in_nonterminal: Optional[str],
) -> bool:
    grammar = grammar_to_mutable(immutable_grammar)
    fuzzer = GrammarCoverageFuzzer(grammar, min_nonterminals=1, max_nonterminals=6)
    in_nonterminals = [in_nonterminal] if in_nonterminal else grammar.keys()

    for nonterminal in in_nonterminals:
        if nonterminal == "<start>":
            specialized_grammar = grammar
        else:
            specialized_grammar = copy.deepcopy(grammar)
            specialized_grammar["<start>"] = [nonterminal]
            delete_unreachable(specialized_grammar)

        parser = EarleyParser(specialized_grammar)

        for _ in range(3):
            inp = "".join(
                [
                    str(fuzzer.expand_tree(DerivationTree(v.n_type)))
                    if is_nonterminal(v.n_type)
                    else v.n_type
                    for v in combination
                ]
            )
            try:
                next(iter(parser.parse(inp)))
            except SyntaxError:
                break
        else:
            return True

    return False


def set_smt_auto_eval(formula: Formula, auto_eval: bool = False):
    class AutoEvalVisitor(FormulaVisitor):
        def visit_smt_formula(self, formula: SMTFormula):
            formula.auto_eval = auto_eval

    formula.accept(AutoEvalVisitor())


def set_smt_auto_subst(formula: Formula, auto_subst: bool = False):
    class AutoSubstVisitor(FormulaVisitor):
        def visit_smt_formula(self, formula: SMTFormula):
            formula.auto_subst = auto_subst

    formula.accept(AutoSubstVisitor())


def match(
    t: DerivationTree,
    mexpr_tree: DerivationTree,
    mexpr_var_paths: Dict[BoundVariable, Path],
    path_in_t: Path = (),
) -> Optional[Dict[BoundVariable, Tuple[Path, DerivationTree]]]:
    """
    This function is described in the
    [ISLa language specification](https://rindphi.github.io/isla/islaspec/).
    It takes a derivation tree corresponding to a match expression and a mapping from
    bound variables to their paths inside those trees. The result is a mapping from
    variables to their positions in the given tree `t`, or None if there is no match.

    :param t: The derivation tree to match.
    :param mexpr_tree: One derivation tree resulting from parsing the match expression.
    :param mexpr_var_paths: A mapping from variables bound in the match expression to
    their paths in `mexpr_tree`.
    :param path_in_t: The path in the original tree t (at the beginning of recursion).
    :return: `None` if there is no match, or a mapping of variables in the match
    expression to their matching subtrees in `t`.
    """

    def is_complete_match(
        t: DerivationTree, match_paths: Dict[BoundVariable, Tuple[Path, DerivationTree]]
    ) -> bool:
        nonlocal path_in_t
        return all(
            any(
                (
                    sub_path := match_path[len(path_in_t) :],
                    len(sub_path) <= len(leaf_path)
                    and leaf_path[: len(sub_path)] == sub_path,
                )[-1]
                for match_path, _ in match_paths.values()
            )
            for leaf_path, _ in t.leaves()
        )

    if (
        t.value != mexpr_tree.value
        or Exceptional.of(lambda: len(mexpr_tree.children) == 0 and t.children is None)
        .recover(lambda _: False)
        .get()
    ):
        return None

    # If the match expression tree is "open," we have a match!
    if (
        mexpr_tree.children is None
        or Exceptional.of(
            lambda: len(mexpr_tree.children) == 0 and len(t.children) == 0
        )
        .recover(lambda _: False)
        .get()
    ):
        assert not mexpr_var_paths or all(not path for path in mexpr_var_paths.values())

        if not is_nonterminal(t.value):
            # We matched a terminal symbol.
            # In that case, the concatenation of all dummy variables remaining in the
            # mexpr_var_paths should equal the current tree symbol. The join is due to
            # the split of dummies we perform in tree prefix creation; this is needed
            # for certain grammars where nonterminals sequences are not "bundled," but
            # occur in different subtrees.
            assert all(isinstance(var, DummyVariable) for var in mexpr_var_paths)
            assert (
                not mexpr_var_paths
                or "".join(map(lambda var: var.n_type, mexpr_var_paths.keys()))
                == t.value
            )

            if len(mexpr_var_paths) == 1:
                return {
                    bv: (path_in_t, t)
                    for bv in mexpr_var_paths
                    if not mexpr_var_paths[bv]
                }
            else:
                new_dummy = DummyVariable(
                    "".join(map(lambda var: var.n_type, mexpr_var_paths))
                )
                return {
                    new_dummy: (path_in_t, t)
                    for bv in mexpr_var_paths
                    if not mexpr_var_paths[bv]
                }

        assert 0 <= len(mexpr_var_paths) <= 1

        # `mexpr_var_paths` will have the form `{bv: ()}` iff this position is
        # associated to a bound variable; associate the current tree `t` to `bv` then.
        # Otherwise, we return an empty mapping (which signals success, just not
        # binding!).
        return {bv: (path_in_t, t) for bv in mexpr_var_paths if not mexpr_var_paths[bv]}

    assert not mexpr_var_paths or all(
        mexpr_var_paths[var] is not None for var in mexpr_var_paths
    )

    # On the other hand, if the numbers of children differ (and `mexpr_tree` *does* have
    # children), this cannot possibly be a match.
    if len(t.children or []) != len(mexpr_tree.children or []):
        return None

    assert t.children and mexpr_tree.children

    # Otherwise, proceed by matching the children.
    result = {}
    for idx in range(len(t.children)):
        maybe_match = match(
            t.children[idx],
            mexpr_tree.children[idx],
            {bv: path[1:] for bv, path in mexpr_var_paths.items() if path[0] == idx},
            path_in_t + (idx,),
        )
        if maybe_match is None:
            return None

        result |= maybe_match

    assert is_complete_match(t, result)
    return result


def parse_peg(
    inp: str, in_nonterminal: str, immutable_grammar: ImmutableGrammar
) -> Maybe[DerivationTree]:
    peg_parser = PEGParser(
        grammar_to_match_expr_grammar(in_nonterminal, immutable_grammar)
    )
    try:
        result = DerivationTree.from_parse_tree(peg_parser.parse(inp)[0])
        return Maybe(result if in_nonterminal == "<start>" else result.children[0])
    except Exception:
        return Maybe.nothing()


def parse_earley(
    inp: str, in_nonterminal: str, immutable_grammar: ImmutableGrammar
) -> Maybe[DerivationTree]:
    # Should we address ambiguities and return multiple parse trees?
    earley_parser = EarleyParser(
        grammar_to_match_expr_grammar(in_nonterminal, immutable_grammar)
    )

    try:
        result = DerivationTree.from_parse_tree(next(earley_parser.parse(inp)))
        return Maybe(result if in_nonterminal == "<start>" else result.children[0])
    except SyntaxError:
        return Maybe.nothing()


def parse(
    inp: str, in_nonterminal: str, immutable_grammar: ImmutableGrammar
) -> Maybe[DerivationTree]:
    monad = parse_peg(inp, in_nonterminal, immutable_grammar)

    if not monad.is_present():
        language_core_logger.debug(
            "Parsing match expression %s with EarleyParser",
            inp,
        )

    monad += (
        lambda _inp: parse_earley(inp, in_nonterminal, immutable_grammar),
        inp,
    )

    return monad
