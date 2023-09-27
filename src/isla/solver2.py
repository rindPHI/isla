import logging
import random
import sys
from abc import ABC, abstractmethod
from dataclasses import dataclass
from enum import Enum
from functools import reduce, lru_cache, partial
from typing import (
    Tuple,
    List,
    Set,
    Dict,
    Iterable,
    Callable,
    cast,
    AbstractSet,
    Sequence,
)

import z3
from frozendict import frozendict
from grammar_to_regex.cfg2regex import RegexConverter
from grammar_to_regex.regex import regex_to_z3
from neo_grammar_graph import NeoGrammarGraph
from orderedset import FrozenOrderedSet
from returns.functions import tap
from returns.maybe import Maybe, Nothing, Some
from returns.pipeline import flow
from returns.pointfree import lash, map_
from returns.result import Result, safe, Failure, Success

from isla.derivation_tree import DerivationTree
from isla.helpers import (
    is_nonterminal,
    deep_str,
    lazyjoin,
    merge_dict_of_sets,
    split_str_with_nonterminals,
    assertions_activated,
    delete_unreachable,
    compute_nullable_nonterminals,
    get_expansions,
    frozen_canonical,
    get_elem_by_equivalence,
    star,
    cluster_by_common_elements,
)
from isla.language import (
    ConjunctiveFormula,
    DisjunctiveFormula,
    Variable,
    SMTFormula,
    BoundVariable,
    fresh_constant,
    Constant,
    true,
    false,
)
from isla.language import Formula
from isla.parser import EarleyParser, PEGParser
from isla.type_defs import (
    FrozenCanonicalGrammar,
    Path,
    ImmutableList,
    Grammar,
    FrozenGrammar,
)
from isla.z3_helpers import (
    z3_subst,
    parent_relationships_in_z3_expr,
    smt_string_val_to_string,
    z3_eq,
    visit_z3_expr,
    numeric_intervals_from_regex,
    z3_or,
    z3_and,
    z3_solve,
)

LOGGER = logging.getLogger(__name__)


# BASIC DATA STRUCTURES
# =====================


class FormulaSet(FrozenOrderedSet[Formula]):
    """
    This class implements a frozen ordered set with specialized compression for
    formulas. An empty FormulaSet represents truth; adding "true" to a formula set
    does not change the formula set; adding "false" to a formula set results in
    a set consisting only of "false."

    Examples
    --------

    >>> var = Variable("var", "<var>")
    >>> constraint = SMTFormula('(= var "x")', var)

    >>> deep_str(FormulaSet([constraint, true(), constraint]))
    '{var == "x"}'

    >>> deep_str(FormulaSet([true(), constraint, constraint]))
    '{var == "x"}'

    >>> deep_str(FormulaSet([true()]))
    '{}'

    >>> deep_str(FormulaSet())
    '{}'

    >>> deep_str(FormulaSet([false(), constraint]))
    '{False}'

    >>> deep_str(FormulaSet([constraint, false()]))
    '{False}'

    >>> deep_str(FormulaSet([false()]) | FormulaSet([constraint]))
    '{False}'

    # >>> deep_str(FormulaSet([constraint]) | FormulaSet([false()]))
    # '{False}'
    """

    def __init__(self, base: Dict[Formula, None] | Iterable[Formula] = frozendict({})):
        super().__init__(base)
        self.the_dict = frozendict.fromkeys(
            reduce(
                lambda formulas, formula: (
                    formulas
                    if formula == true() or formulas == [false()]
                    else ([formula] if formula == false() else formulas + [formula])
                ),
                self,
                [],
            )
        )

    def __call__(self, *args, **kwargs):
        return FormulaSet(*args, **kwargs)


@dataclass(frozen=True)
class CDT:
    """
    A Conditioned Derivation Tree (CDT) is a derivation tree that is subject to
    constraints. Semantically, a CDT represents a set of derivation trees. This
    set is empty if the constraint set is unsatisfiable, and represents all
    concrete trees that can be derived from the (possibly open) derivation tree
    satisfying the constraints.
    """

    constraints: FormulaSet
    tree: DerivationTree

    def __str__(self):
        return f"({self.constraints} ▸ {self.tree})"


class Action(ABC):
    """
    An action comprises the information needed to make the application of a solver
    rule to an input CDT deterministic. The type of the action defines which rule
    is applied.
    """

    pass


@dataclass(frozen=True)
class StateTree:
    """
    A state tree keeps track of CDTs and their successors after rule applications
    in a solver run. It maintains a pointer to its parent. For each child, the
    action resulting in that child is stored with the child itself in the list of
    children.
    """

    node: CDT
    path: Path = ()
    children: Tuple[Tuple[Action, "StateTree"], ...] = ()

    def replace(self, path: Path, new_node: "StateTree") -> "StateTree":
        """
        Replaces the node at :code:`path` in this state tree with :code:`new_node`.
        The caller is responsible to maintain the correct paths in :code:`new_node`
        relative to the inserted position.

        Example
        -------

        We create a tree of the following structure::

            <root>
            ├─ <tree_0>
            │  ├─ <tree_2>
            │  └─ <tree_3>
            └─ <tree_1>

        >>> from isla.language import true

        >>> dummy_action = ExpandRuleAction((), 0)
        >>> tree_2 = StateTree(
        ...     CDT(FormulaSet(), DerivationTree("<tree_2>")), (0, 0)
        ... )
        >>> tree_3 = StateTree(
        ...     CDT(FormulaSet(), DerivationTree("<tree_3>")), (0, 1)
        ... )
        >>> tree_0 = StateTree(
        ...     CDT(FormulaSet(), DerivationTree("<tree_0>")),
        ...     (0,),
        ...     ((dummy_action, tree_2), (dummy_action, tree_3),),
        ... )
        >>> tree_1 = StateTree(CDT(FormulaSet(), DerivationTree("<tree_1>")), (1,))
        >>> stree = StateTree(
        ...     CDT(FormulaSet(), DerivationTree("<root>")),
        ...     (),
        ...     ((dummy_action, tree_0), (dummy_action, tree_1)),
        ... )

        Our goal is to change the tree to the following one:

            <root>
            ├─ <tree_0>
            │  ├─ <tree_2>
            │  └─ <X>
            └─ <tree_1>

        >>> tree_X = StateTree(
        ...     CDT(FormulaSet(), DerivationTree("<X>")), (0, 1)
        ... )
        >>> print(stree.replace((0, 1), tree_X))
        StateTree(({} ▸ <root>), [(Expand((), 0), StateTree(({} ▸ <tree_0>), [(Expand((), 0), StateTree(({} ▸ <tree_2>))), (Expand((), 0), StateTree(({} ▸ <X>)))])), (Expand((), 0), StateTree(({} ▸ <tree_1>)))])

        :param path: The path to replace.
        :param new_node: The new node to insert at the specified path.
        :return: An updated state tree.
        """  # noqa: E501

        if not path:
            return new_node

        return StateTree(
            self.node,
            self.path,
            self.children[: path[0]]
            + (
                (
                    self.children[path[0]][0],
                    self.children[path[0]][1].replace(path[1:], new_node),
                ),
            )
            + self.children[path[0] + 1 :],
        )

    def add_child(self, action: Action, node: CDT, path: Path = ()) -> "StateTree":
        """
        Adds a child to this state tree. The other children are preserved; the path of
        the added tree relative to this tree is automatically set. The added tree has
        no children.

        Example:
        --------

        We create a tree of the following structure::

            <root>
            └─ <tree_0>
               └─ <tree_2>

        The goal is to insert a :code:`tree_1` such that we obtain the following tree::

            <root>
            ├─ <tree_0>
            │  └─ <tree_2>
            └─ <tree_1>

        >>> from isla.language import true

        >>> dummy_action = ExpandRuleAction((), 0)
        >>> tree_2 = StateTree(
        ...     CDT(FormulaSet(), DerivationTree("<tree_2>")), (0, 0)
        ... )
        >>> tree_0 = StateTree(
        ...     CDT(FormulaSet(), DerivationTree("<tree_0>")),
        ...     (0,),
        ...     ((dummy_action, tree_2),),
        ... )
        >>> stree = StateTree(
        ...     CDT(FormulaSet(), DerivationTree("<root>")),
        ...     (),
        ...     ((dummy_action, tree_0),),
        ... )

        This is the original tree:

        >>> print(stree)
        StateTree(({} ▸ <root>), [(Expand((), 0), StateTree(({} ▸ <tree_0>), [(Expand((), 0), StateTree(({} ▸ <tree_2>)))]))])

        And here is the updated one:

        >>> new_cdt = CDT(FormulaSet(), DerivationTree("<tree_1>"))
        >>> print(stree.add_child(dummy_action, new_cdt))
        StateTree(({} ▸ <root>), [(Expand((), 0), StateTree(({} ▸ <tree_0>), [(Expand((), 0), StateTree(({} ▸ <tree_2>)))])), (Expand((), 0), StateTree(({} ▸ <tree_1>)))])

        Now, we add tree 1 to the inner node tree 0, resulting in::

            <root>
            └─ <tree_0>
               ├─ <tree_2>
               └─ <tree_1>

        >>> print(stree.add_child(dummy_action, new_cdt, (0,)))
        StateTree(({} ▸ <root>), [(Expand((), 0), StateTree(({} ▸ <tree_0>), [(Expand((), 0), StateTree(({} ▸ <tree_2>))), (Expand((), 0), StateTree(({} ▸ <tree_1>)))]))])

        :param action: The action leading to the new child.
        :param node: The CDT to add.
        :param path: The path to the parent of the new child
            (defaults to the root path, i.e., this state tree object).
        :return: An updated state tree.
        """  # noqa: E501

        child_at_path = self.get_subtree(path)

        return self.replace(
            path,
            StateTree(
                child_at_path.node,
                child_at_path.path,
                child_at_path.children
                + (
                    (
                        action,
                        StateTree(
                            node,
                            child_at_path.path + (len(child_at_path.children),),
                            (),
                        ),
                    ),
                ),
            ),
        )

    def get_subtree(self, path: Path) -> "StateTree":
        """
        Returns the subtree of this tree at the specified path.

        Example:
        --------

        We create a tree of the following structure::

            <root>
            ├─ <tree_0>
            │  └─ <tree_2>
            └─ <tree_1>

        >>> from isla.language import true

        >>> dummy_action = ExpandRuleAction((), 0)
        >>> tree_2 = StateTree(
        ...     CDT(FormulaSet(), DerivationTree("<tree_2>")), (0, 0)
        ... )
        >>> tree_0 = StateTree(
        ...     CDT(FormulaSet(), DerivationTree("<tree_0>")),
        ...     (0,),
        ...     ((dummy_action, tree_2),),
        ... )
        >>> tree_1 = StateTree(
        ...     CDT(FormulaSet(), DerivationTree("<tree_1>")), (1,))
        >>> stree = StateTree(
        ...     CDT(FormulaSet(), DerivationTree("<root>")),
        ...     (),
        ...     ((dummy_action, tree_0), (dummy_action, tree_1)),
        ... )

        At the empty path, there is the tree (the root) itself:

        >>> stree.get_subtree(()) == stree
        True

        The first child is tree 0:

        >>> print(stree.get_subtree((0,)))
        StateTree(({} ▸ <tree_0>), [(Expand((), 0), StateTree(({} ▸ <tree_2>)))])

        The first child of tree 0 is tree 2:

        >>> print(stree.get_subtree((0, 0)))
        StateTree(({} ▸ <tree_2>))

        :param path: The path of the tree node to return.
        :return: The tree node at the specified path.
        """

        curr_node = self
        while path:
            if not curr_node.children:
                raise RuntimeError(f"Cannot access path {path} in a leaf node")

            curr_node = curr_node.children[path[0]][1]
            path = path[1:]

        return curr_node

    def parent(self, root: "StateTree") -> "StateTree":
        """
        This method returns the parent of the this state tree relative to a specified
        root tree. It raises a :class:`RuntimeError` if no parent exists.

        Example:
        --------

        We create a tree of the following structure::

            <root>
            ├─ <tree_0>
            │  └─ <tree_2>
            └─ <tree_1>

        >>> from isla.language import true

        >>> dummy_action = ExpandRuleAction((), 0)
        >>> tree_2 = StateTree(
        ...     CDT(FormulaSet(), DerivationTree("<tree_2>")), (0, 0)
        ... )
        >>> tree_0 = StateTree(
        ...     CDT(FormulaSet(), DerivationTree("<tree_0>")),
        ...     (0,),
        ...     ((dummy_action, tree_2),),
        ... )
        >>> tree_1 = StateTree(CDT(FormulaSet(), DerivationTree("<tree_1>")), (1,))
        >>> stree = StateTree(
        ...     CDT(FormulaSet(), DerivationTree("<root>")),
        ...     (),
        ...     ((dummy_action, tree_0), (dummy_action, tree_1)),
        ... )

        The :code:`tree_2` is a leaf:

        >>> print(tree_2)
        StateTree(({} ▸ <tree_2>))

        Its parent is :code:`tree_0`:

        >>> print(tree_2.parent(stree))
        StateTree(({} ▸ <tree_0>), [(Expand((), 0), StateTree(({} ▸ <tree_2>)))])

        The parent of :code:`tree_0`, in turn, is :code:`root`:

        >>> print(tree_2.parent(stree).parent(stree))
        StateTree(({} ▸ <root>), [(Expand((), 0), StateTree(({} ▸ <tree_0>), [(Expand((), 0), StateTree(({} ▸ <tree_2>)))])), (Expand((), 0), StateTree(({} ▸ <tree_1>)))])

        It is the root node of our tree.

        >>> tree_2.parent(stree).parent(stree) == stree
        True

        We cannot ask the root for its parent:

        >>> stree.parent(stree)
        Traceback (most recent call last):
        ...
        RuntimeError: The root of a state tree has no parent

        :param root: The root node of the tree relative to which we look for the parent
            of this tree.
        :return: The parent of this tree relative to the specified root node.
        """  # noqa: E501

        if not self.path:
            assert self == root
            raise RuntimeError("The root of a state tree has no parent")

        return root.get_subtree(self.path[:-1])

    def __str__(self):
        return (
            f"StateTree({self.node}"
            + ((", " + deep_str(list(self.children))) if self.children else "")
            + ")"
        )


class Rule(ABC):
    """
    A rule computes successor states for a given state tree node if it is applicable.
    """

    @abstractmethod
    def action(self, state_tree: StateTree) -> Maybe[Action]:
        """
        This method checks whether this rule is applicable to the given state tree.
        It returns an action to be used with :meth:`~isla.solver2.Rule.apply` for
        generating a successor tree node.

        :param state_tree: The input tree node.
        :return: An action or nothing.
        """

        raise NotImplementedError

    @abstractmethod
    def apply(self, state_tree: StateTree, action: Action) -> StateTree:
        """
        Given an action of suitable type, this method computes the successor tree node
        for the given input node. The action can be computed using
        :meth:`isla.solver2.Rule.action`.

        :param state_tree: The input state tree node.
        :param action: The action with the necessary information for applying this Rule.
        :return: A successor state tree node.
        """

        raise NotImplementedError


# CONCRETE ACTIONS AND RULES
# ==========================


@dataclass(frozen=True)
class ExpandRuleAction(Action):
    path: Path
    alternative: int

    def __str__(self):
        return f"Expand({self.path}, {self.alternative})"


@dataclass(frozen=True)
class ExpandRule(Rule):
    grammar: FrozenGrammar
    __canonical_grammar: Maybe[FrozenCanonicalGrammar] = Nothing

    def __post_init__(self):
        object.__setattr__(
            self, "_ExpandRule__canonical_grammar", frozen_canonical(self.grammar)
        )

    def action(self, state_tree: StateTree) -> Maybe[ExpandRuleAction]:
        """
        This method computes an expansion action if it is applicable. It avoids
        previously taken actions from :code:`state_tree` and takes coverage into
        account. TODO: Implement this (see inline code comments).

        Consider the following grammar for our assignment language:

        >>> from frozendict import frozendict
        >>> import string
        >>> from isla.language import true

        >>> grammar: FrozenGrammar = frozendict({
        ...     "<start>":
        ...         ("<stmt>",),
        ...     "<stmt>":
        ...         ("<assgn> ; <stmt>", "<assgn>"),
        ...     "<assgn>":
        ...         ("<var> := <rhs>",),
        ...     "<rhs>":
        ...         ("<var>", "<digit>"),
        ...     "<var>": tuple(string.ascii_lowercase),
        ...     "<digit>": tuple(string.digits),
        ... })

        We create a derivation tree that permits exactly two expansions and a trivial
        state tree.

        >>> dtree = DerivationTree("<start>", (DerivationTree("<stmt>"),))
        >>> stree = StateTree(CDT(FormulaSet(), dtree))
        >>> rule = ExpandRule(grammar)
        >>> action = rule.action(stree)

        An action is returned for the open leaf, choosing either the first or the
        second expansion alternative for "<stmt>".

        >>> action.map(lambda a: a.path)
        <Some: (0,)>
        >>> action.map(lambda a: a.alternative).map(lambda alt: alt in {0, 1})
        <Some: True>

        :param state_tree: The input state tree.
        :return: An expansion action or nothing.
        """

        # Check if there are any open leaves
        open_leaves = tuple(state_tree.node.tree.open_leaves())
        if not open_leaves:
            return Maybe.nothing()

        # If there are open leaves, we choose a random one and apply a random expansion.
        # TODO 1: If there are siblings to state_tree, choose a *different* action.
        # TODO 2: We eventually must take syntactic and semantic coverage into account.
        #         For example, we might want to expand a leaf in a way leading to the
        #         possible instantiation of a quantifier, or covering a grammar k-path.
        #         This also means that we need more information about the context, such
        #         as covered k-paths or quantifiers.

        path, leaf = random.choice(open_leaves)
        alternative_id, alternative = random.choice(
            cast(
                Tuple[int, ImmutableList[ImmutableList[str]]],
                tuple(enumerate(self.__canonical_grammar[leaf.value])),
            )
        )

        return Some(ExpandRuleAction(path, alternative_id))

    def apply(self, state_tree: StateTree, action: ExpandRuleAction) -> StateTree:
        """
        This method applies a previously chosen :class:`~isla.solver2.ExpandRuleAction`
        to the given state tree.

        Example
        -------

        Consider the assignment language grammar:

        >>> from frozendict import frozendict
        >>> import string
        >>> from isla.language import true

        >>> grammar: FrozenGrammar = frozendict({
        ...     "<start>":
        ...         ("<stmt>",),
        ...     "<stmt>":
        ...         ("<assgn> ; <stmt>", "<assgn>"),
        ...     "<assgn>":
        ...         ("<var> := <rhs>",),
        ...     "<rhs>":
        ...         ("<var>", "<digit>"),
        ...     "<var>": tuple(string.ascii_lowercase),
        ...     "<digit>": tuple(string.digits),
        ... })
        >>> dtree = DerivationTree("<start>", (DerivationTree("<stmt>"),))
        >>> stree = StateTree(CDT(FormulaSet(), dtree))

        We expand the open leaf first with the first expansion rule:

        >>> rule = ExpandRule(grammar)

        >>> action = ExpandRuleAction((0,), 0)
        >>> print(rule.apply(stree, action))
        StateTree(({} ▸ <stmt>), [(Expand((0,), 0), StateTree(({} ▸ <assgn> ; <stmt>)))])

        Now, we choose the second expansion rule:

        >>> action = ExpandRuleAction((0,), 1)
        >>> print(rule.apply(stree, action))
        StateTree(({} ▸ <stmt>), [(Expand((0,), 1), StateTree(({} ▸ <assgn>)))])

        :param state_tree: The state tree whose derivation tree we should expand
            according to the specified action.
        :param action: The action comprising the information for the expansion.
        :return: The expanded state.
        """

        node = state_tree.node
        new_children = tuple(
            [
                DerivationTree(symbol)
                if is_nonterminal(symbol)
                else DerivationTree(symbol, ())
                for symbol in self.__canonical_grammar[
                    node.tree.get_subtree(action.path).value
                ][action.alternative]
            ]
        )
        new_tree = DerivationTree(node.tree.value, new_children)

        return state_tree.add_child(
            action, CDT(node.constraints, node.tree.replace_path(action.path, new_tree))
        )


@dataclass(frozen=True)
class SplitAndAction(Action):
    conjunction: ConjunctiveFormula

    def __str__(self):
        return f"SplitAnd({self.conjunction})"


@dataclass(frozen=True)
class SplitAndRule(Rule):
    def action(self, state_tree: StateTree) -> Maybe[SplitAndAction]:
        """
        This method returns an action if the constraint set in the provided state tree
        contains a conjunctive formula.

        Example
        -------

        >>> from isla.language import Constant, SMTFormula

        >>> conjunction = (
        ...     SMTFormula("(> (str.to_int x) 0)", Constant("x", "<X>"))
        ...     & SMTFormula("(< (str.to_int x) 9)", Constant("x", "<X>"))
        ... )
        >>> stree = StateTree(
        ...     CDT(FormulaSet([conjunction]), DerivationTree("<start>"))
        ... )
        >>> print(SplitAndRule().action(stree))
        <Some: SplitAnd((StrToInt(x) > 0 ∧ StrToInt(x) < 9))>

        :param state_tree: The input state tree.
        :return: An action if a conjunction is contained in the state tree or nothing.
        """

        constraints = state_tree.node.constraints

        return (
            safe(
                lambda: next(
                    c for c in constraints if isinstance(c, ConjunctiveFormula)
                )
            )()
            .bind(lambda c: Some(SplitAndAction(c)))
            .lash(lambda _: Nothing)
        )

    def apply(self, state_tree: StateTree, action: SplitAndAction) -> StateTree:
        """
        This method applies a :class:`~isla.solver2.SplitAndAction`.

        Example
        -------

        >>> from isla.language import Constant, SMTFormula

        >>> conjunction = (
        ...     SMTFormula("(> (str.to_int x) 0)", Constant("x", "<X>"))
        ...     & SMTFormula("(< (str.to_int x) 9)", Constant("x", "<X>"))
        ... )
        >>> stree = StateTree(
        ...     CDT(FormulaSet([conjunction]), DerivationTree("<start>"))
        ... )
        >>> action = SplitAndAction(conjunction)
        >>> print(SplitAndRule().apply(stree, action))
        StateTree(({(StrToInt(x) > 0 ∧ StrToInt(x) < 9)} ▸ <start>), [(SplitAnd((StrToInt(x) > 0 ∧ StrToInt(x) < 9)), StateTree(({StrToInt(x) > 0, StrToInt(x) < 9} ▸ <start>)))])


        :param state_tree: The input state tree.
        :param action: The action comprising the information about which formula to
            split.
        :return: The input state tree augmented with a new child resulting from
            splitting the conjunction.
        """  # noqa: E501

        node = state_tree.node
        return state_tree.add_child(
            action,
            CDT(
                node.constraints.difference({action.conjunction}).union(
                    set(action.conjunction.args)
                ),
                node.tree,
            ),
        )


@dataclass(frozen=True)
class ChooseOrAction(Action):
    disjunction: DisjunctiveFormula
    pos: int

    def __str__(self):
        return f"ChooseOr({self.disjunction}, {self.pos})"


@dataclass(frozen=True)
class ChooseOrRule(Rule):
    def action(self, state_tree: StateTree) -> Maybe[ChooseOrAction]:
        """
        This method returns an action if the constraint set in the provided state tree
        contains a disjunctive formula.

        Example
        -------

        >>> from isla.language import Constant, SMTFormula

        >>> disjunction = (
        ...     SMTFormula("(> (str.to_int x) 0)", Constant("x", "<X>"))
        ...     | SMTFormula("(< (str.to_int x) 9)", Constant("x", "<X>"))
        ... )
        >>> stree = StateTree(
        ...     CDT(FormulaSet([disjunction]), DerivationTree("<start>"))
        ... )
        >>> str(ChooseOrRule().action(stree)) in [
        ...     '<Some: ChooseOr((StrToInt(x) > 0 ∨ StrToInt(x) < 9), 0)>',
        ...     '<Some: ChooseOr((StrToInt(x) > 0 ∨ StrToInt(x) < 9), 1)>'
        ... ]
        True

        >>> ChooseOrRule().action(
        ...     StateTree(CDT(FormulaSet({}), DerivationTree("<start>"))))
        <Nothing>

        :param state_tree: The input state tree.
        :return: An action if a disjunction is contained in the state tree or nothing.
        """

        # TODO 1: If there is a sibling present, we should choose a different disjunct.
        # TODO 2: We will have to consider semantic coverage information (choose the
        #         disjunct whose origin formula has not been chosen for evaluation
        #         so far).

        constraints = state_tree.node.constraints
        return (
            safe(
                lambda: next(
                    c for c in constraints if isinstance(c, DisjunctiveFormula)
                )
            )()
            .bind(lambda c: Maybe.from_value(ChooseOrAction(c, random.choice([0, 1]))))
            .lash(lambda _: Nothing)
        )

    def apply(self, state_tree: StateTree, action: ChooseOrAction) -> StateTree:
        """
        This method applies a :class:`~isla.solver2.ChooseOrAction`.
        Other than :class:`~isla.solver2.SplitAnd`, only (a random) one disjunct is
        retained in the result.

        Example
        -------

        >>> from isla.language import Constant, SMTFormula

        >>> disjunction = (
        ...     SMTFormula("(> (str.to_int x) 0)", Constant("x", "<X>"))
        ...     | SMTFormula("(< (str.to_int x) 9)", Constant("x", "<X>"))
        ... )
        >>> stree = StateTree(
        ...     CDT(FormulaSet([disjunction]), DerivationTree("<start>"))
        ... )

        >>> action = ChooseOrAction(disjunction, 0)
        >>> print(ChooseOrRule().apply(stree, action))
        StateTree(({(StrToInt(x) > 0 ∨ StrToInt(x) < 9)} ▸ <start>), [(ChooseOr((StrToInt(x) > 0 ∨ StrToInt(x) < 9), 0), StateTree(({StrToInt(x) > 0} ▸ <start>)))])

        >>> action = ChooseOrAction(disjunction, 1)
        >>> print(ChooseOrRule().apply(stree, action))
        StateTree(({(StrToInt(x) > 0 ∨ StrToInt(x) < 9)} ▸ <start>), [(ChooseOr((StrToInt(x) > 0 ∨ StrToInt(x) < 9), 1), StateTree(({StrToInt(x) < 9} ▸ <start>)))])


        :param state_tree: The input state tree.
        :param action: The action comprising the information about which formula to
            split.
        :return: The input state tree augmented with a new child resulting from
            splitting the conjunction.
        """  # noqa: E501

        node = state_tree.node
        return state_tree.add_child(
            action,
            CDT(
                node.constraints.difference({action.disjunction}).union(
                    {action.disjunction.args[action.pos]}
                ),
                node.tree,
            ),
        )


@dataclass(frozen=True)
class SolveSMTAction(Action):
    cluster: FormulaSet
    result: bool | frozendict[Variable | DerivationTree, DerivationTree]

    def __str__(self):
        return f"SolveSMT({deep_str(self.cluster)} --> {deep_str(self.result)})"


@dataclass(frozen=True)
class SolveSMTRule(Rule):
    graph: NeoGrammarGraph

    # TODO: Refine action signature in Rule superclass/sibling classes
    def action(
        self, state_tree: StateTree
    ) -> Maybe[Result[SolveSMTAction, SyntaxError | StopIteration]]:
        """
        This function returns a :class:`~isla.solver2.SolveSMTAction` if there exit
        SMT formulas in the given state tree and a solution could be computed. The
        solution is either an assignment of derivation trees to variables or other
        derivation trees, True for valid formulas, or False for invalid formulas.
        Only the first *cluster* of constraints depending on the same variables is
        considered in solving. In case of an error during the solving process, some
        failure (SyntaxError or StopIteration) is returned. A SyntaxError signals that
        a solver solution does not conform to the grammar. A StopIteration signals
        that we could not generate another, different solution; this applies to the
        case that :code:`state_tree` already has children and we look for different
        ones.

        Example
        -------

        Consider our running assignment language example:

        >>> import string
        >>> grammar: Grammar = {
        ...     "<start>":
        ...         ["<stmt>"],
        ...     "<stmt>":
        ...         ["<assgn> ; <stmt>", "<assgn>"],
        ...     "<assgn>":
        ...         ["<var> := <rhs>"],
        ...     "<rhs>":
        ...         ["<var>", "<digit>"],
        ...     "<var>": list(string.ascii_lowercase),
        ...     "<digit>": list(string.digits)
        ... }
        >>> graph = NeoGrammarGraph(grammar)

        Assume we are in a state with two simple constraints: A :code:`<var>` variable
        should equal "x," and a :code:`<digit>` variable should attain a value
        greater 3.

        >>> var = Variable("var", "<var>")
        >>> var_tree = DerivationTree("<var>", id=0)
        >>> digit = Variable("digit", "<digit>")
        >>> digit_tree = DerivationTree("<digit>", id=1)

        >>> var_eq_x_constraint = SMTFormula(
        ...     '(= var "x")',
        ...     instantiated_variables=FrozenOrderedSet([var]),
        ...     substitutions={var: var_tree},
        ... )

        >>> digit_greater_3_constraint = SMTFormula(
        ...     '(> (str.to.int digit) 3)',
        ...     instantiated_variables=FrozenOrderedSet([digit]),
        ...     substitutions={digit: digit_tree},
        ... )

        This is the original derivation tree in our state.

        >>> orig_dtree = DerivationTree(
        ...     "<start>",
        ...     (
        ...         DerivationTree(
        ...             "<stmt>",
        ...             (
        ...                 DerivationTree(
        ...                     "<assgn>",
        ...                     (var_tree, DerivationTree(" := ", ()), digit_tree)
        ...                 ),
        ...             ),
        ...         ),
        ...     ),
        ... )

        We compute a SolveSMTAction in this situation.

        >>> constraints = FormulaSet([var_eq_x_constraint, digit_greater_3_constraint])
        >>> rule = SolveSMTRule(graph)
        >>> rule.action(StateTree(CDT(constraints, orig_dtree)))
        <Some: <Success: SolveSMT({(<var>_0 == "x", {'<var>_0': '<var>'})} --> {<var>: x})>>

        Note that we obtain a solution for the first cluster, the constraint on the
        variable "var."

        If there are no SMT formulas, we obtain Nothing:

        >>> rule.action(StateTree(CDT(FormulaSet(), orig_dtree)))
        <Nothing>

        For "wrong" constraints, e.g., comprising a string-to-int conversion on a
        :code:`<var>` variable, some SytaxError failure is returned:

        >>> deep_str(
        ...     rule.action(
        ...         StateTree(
        ...             CDT(
        ...                 FormulaSet([SMTFormula("(= (str.to.int var) 8)", var)]),
        ...                 orig_dtree,
        ...             )
        ...         )
        ...     )
        ... )[:51] + "...>>"
        '<Some: <Failure: Could not parse a numeric solution...>>'

        :param state_tree: The state tree node starting from which we try to find a
            solution to contained SMT formulas.
        :return: Nothing if there are not SMT formulas in the state tree; otherwise,
            some solution or some failure.
        """  # noqa: E501

        smt_formulas = [
            conjunct
            for conjunct in state_tree.node.constraints
            if isinstance(conjunct, SMTFormula)
        ]

        if not smt_formulas:
            return Nothing

        LOGGER.debug(
            "Eliminating first cluster of semantic formulas {%s}",
            lazyjoin(", ", smt_formulas),
        )

        return Some(
            unify_smt_formulas_and_solve_first_cluster(
                self.graph, smt_formulas, Some(state_tree)
            ).map(
                lambda cluster_and_result: SolveSMTAction(
                    cluster_and_result[0], cluster_and_result[1]
                )
            )
        )

    def apply(self, state_tree: StateTree, action: SolveSMTAction) -> StateTree:
        """
        TODO

        Example
        -------

        Consider our running assignment language example:

        >>> import string
        >>> grammar: Grammar = {
        ...     "<start>":
        ...         ["<stmt>"],
        ...     "<stmt>":
        ...         ["<assgn> ; <stmt>", "<assgn>"],
        ...     "<assgn>":
        ...         ["<var> := <rhs>"],
        ...     "<rhs>":
        ...         ["<var>", "<digit>"],
        ...     "<var>": list(string.ascii_lowercase),
        ...     "<digit>": list(string.digits)
        ... }
        >>> graph = NeoGrammarGraph(grammar)

        Assume we are in a state with two simple constraints: A :code:`<var>` variable
        should equal "x," and a :code:`<digit>` variable should attain a value
        greater 3.

        >>> var = Variable("var", "<var>")
        >>> var_tree = DerivationTree("<var>", id=0)
        >>> digit = Variable("digit", "<digit>")
        >>> digit_tree = DerivationTree("<digit>", id=1)

        >>> var_eq_x_constraint = SMTFormula(
        ...     '(= var "x")',
        ...     instantiated_variables=FrozenOrderedSet([var]),
        ...     substitutions={var: var_tree},
        ... )

        >>> digit_greater_3_constraint = SMTFormula(
        ...     '(> (str.to.int digit) 3)',
        ...     instantiated_variables=FrozenOrderedSet([digit]),
        ...     substitutions={digit: digit_tree},
        ... )

        This is the original derivation tree in our state.

        >>> orig_dtree = DerivationTree(
        ...     "<start>",
        ...     (
        ...         DerivationTree(
        ...             "<stmt>",
        ...             (
        ...                 DerivationTree(
        ...                     "<assgn>",
        ...                     (var_tree, DerivationTree(" := ", ()), digit_tree)
        ...                 ),
        ...             ),
        ...         ),
        ...     ),
        ... )

        We compute a SolveSMTAction in this situation.

        >>> constraints = FormulaSet([var_eq_x_constraint, digit_greater_3_constraint])
        >>> rule = SolveSMTRule(graph)
        >>> state_tree = StateTree(CDT(constraints, orig_dtree))
        >>> action = rule.action(state_tree).unwrap().unwrap()
        >>> print(deep_str(action))
        SolveSMT({(<var>_0 == "x", {'<var>_0': '<var>'})} --> {<var>: x})

        Next, we apply this action.

        >>> print(deep_str(rule.apply(state_tree, action).children[0]))
        (SolveSMT({(<var>_0 == "x", {'<var>_0': '<var>'})} --> {<var>: x}), StateTree(({(StrToInt(digit) > 3, {'digit': '<digit>'})} ▸ x := <digit>)))

        :param state_tree: TODO
        :param action: TODO
        :return:
        """  # noqa: E501

        new_constraints = state_tree.node.constraints.difference(action.cluster)
        new_tree = state_tree.node.tree
        if action.result is False:
            new_constraints = FormulaSet([false()])
        elif action.result is True:
            pass
        else:
            assert isinstance(action.result, dict)

            new_constraints = FormulaSet(
                map(
                    lambda constraint: constraint.substitute_expressions(action.result),
                    new_constraints,
                )
            )

            new_tree = new_tree.substitute(action.result)

        return state_tree.add_child(action, CDT(new_constraints, new_tree))


def unify_smt_formulas_and_solve_first_cluster(
    graph: NeoGrammarGraph,
    smt_formulas: Sequence[SMTFormula],
    maybe_state_tree: Maybe[StateTree] = Nothing,
) -> Result[
    Tuple[FormulaSet, bool | Dict[Variable | DerivationTree, DerivationTree]],
    SyntaxError | StopIteration,
]:
    """
    This function clusters the given SMT formulas and calls
    :func:`~isla.solver2.solve_smt_formulas` to solve the *first* cluster.
    For details of the solving process, see :func:`~isla.solver2.solve_smt_formulas`.
    Below, we demonstrate how the clustering works.

    Example
    -------

    Consider our running assignment language example:

    >>> import string
    >>> grammar: Grammar = {
    ...     "<start>":
    ...         ["<stmt>"],
    ...     "<stmt>":
    ...         ["<assgn> ; <stmt>", "<assgn>"],
    ...     "<assgn>":
    ...         ["<var> := <rhs>"],
    ...     "<rhs>":
    ...         ["<var>", "<digit>"],
    ...     "<var>": list(string.ascii_lowercase),
    ...     "<digit>": list(string.digits)
    ... }
    >>> graph = NeoGrammarGraph(grammar)

    We have a list of three simple constraints: A :code:`<var>` variable should equal
    "x," and a :code:`<digit>` variable should attain a value greater 3, but smaller
    than 8.

    >>> var = Variable("var", "<var>")
    >>> digit = Variable("digit", "<digit>")

    >>> var_eq_x_constraint = SMTFormula('(= var "x")', var)
    >>> digit_greater_3_constraint = SMTFormula('(> (str.to.int digit) 3)', digit)
    >>> digit_smaller_8_constraint = SMTFormula('(< (str.to.int digit) 8)', digit)

    Those constraints form two clusters. The constraint on the digit variable must be
    solved simultaneously since their solutions are not independent; the constraint
    on the var variable belongs to its own cluster.

    >>> constraints = (
    ...     var_eq_x_constraint,
    ...     digit_greater_3_constraint,
    ...     digit_smaller_8_constraint,
    ... )
    >>> deep_str(unify_smt_formulas_and_solve_first_cluster(graph, constraints))
    '<Success: ({var == "x"}, {var: x})>'

    The call resulted in a solution to "var" only, since the corresponding constraint
    formed the first cluster. If we reorder the constraints, we obtain a different
    result:

    >>> constraints = (
    ...     digit_greater_3_constraint,
    ...     digit_smaller_8_constraint,
    ...     var_eq_x_constraint)
    >>> deep_str(unify_smt_formulas_and_solve_first_cluster(graph, constraints))
    '<Success: ({StrToInt(digit) > 3, StrToInt(digit) < 8}, {digit: 4})>'

    The order of the "digit" constraints is irrelevant.

    >>> constraints = (
    ...     digit_greater_3_constraint,
    ...     digit_smaller_8_constraint,
    ... )
    >>> deep_str(unify_smt_formulas_and_solve_first_cluster(graph, constraints))
    '<Success: ({StrToInt(digit) > 3, StrToInt(digit) < 8}, {digit: 4})>'

    >>> constraints = (
    ...     digit_smaller_8_constraint,
    ...     digit_greater_3_constraint,
    ... )
    >>> deep_str(unify_smt_formulas_and_solve_first_cluster(graph, constraints))
    '<Success: ({StrToInt(digit) < 8, StrToInt(digit) > 3}, {digit: 4})>'

    In this case, the clustering works by variable names only. However, we also
    consider the *substitutions* in SMT formulas when clustering, since two variables
    with the same name may reference different trees; similarly, two variables with
    different names may reference the same tree.

    >>> digit_dtree_1 = DerivationTree("<digit>", id=2)
    >>> digit_dtree_2 = DerivationTree("<digit>", id=3)

    >>> digit_greater_3_constraint = SMTFormula(
    ...     "(> (str.to.int digit) 3)",
    ...     instantiated_variables=FormulaSet([digit]),
    ...     substitutions={digit: digit_dtree_1},
    ... )
    >>> digit_smaller_8_constraint = SMTFormula(
    ...     "(< (str.to.int digit) 8)",
    ...     instantiated_variables=FormulaSet([digit]),
    ...     substitutions={digit: digit_dtree_2},
    ... )

    >>> constraints = (
    ...     digit_greater_3_constraint,
    ...     digit_smaller_8_constraint,
    ... )
    >>> solution = unify_smt_formulas_and_solve_first_cluster(graph, constraints)
    >>> deep_str(solution)
    "<Success: ({(StrToInt(<digit>_2) > 3, {'<digit>_2': '<digit>'})}, {<digit>: 4})>"

    Changing the order of the constraints changes the result.

    >>> constraints = (
    ...     digit_smaller_8_constraint,
    ...     digit_greater_3_constraint,
    ... )
    >>> solution = unify_smt_formulas_and_solve_first_cluster(graph, constraints)
    >>> deep_str(solution)
    "<Success: ({(StrToInt(<digit>_3) < 8, {'<digit>_3': '<digit>'})}, {<digit>: 0})>"

    Now, we create a different "digit" variable, but let it refer to the same
    derivation tree.

    >>> digit_2 = Variable("digit_2", "<digit>")

    >>> digit_greater_3_constraint = SMTFormula(
    ...     "(> (str.to.int digit) 3)",
    ...     instantiated_variables=FormulaSet([digit]),
    ...     substitutions={digit: digit_dtree_1},
    ... )
    >>> digit_2_smaller_8_constraint = SMTFormula(
    ...     "(< (str.to.int digit_2) 8)",
    ...     instantiated_variables=FormulaSet([digit_2]),
    ...     substitutions={digit_2: digit_dtree_1},
    ... )

    >>> constraints = (
    ...     digit_greater_3_constraint,
    ...     digit_2_smaller_8_constraint,
    ... )
    >>> solution = unify_smt_formulas_and_solve_first_cluster(graph, constraints)
    >>> deep_str(solution)
    "<Success: ({(StrToInt(<digit>_2) > 3, {'<digit>_2': '<digit>'}), (StrToInt(<digit>_2) < 8, {'<digit>_2': '<digit>'})}, {<digit>: 4})>"

    >>> list(solution.unwrap()[1].keys()) == [digit_dtree_1]
    True

    Now, there is only one cluster: The order of the constraints does not matter.

    >>> constraints = (
    ...     digit_2_smaller_8_constraint,
    ...     digit_greater_3_constraint,
    ... )
    >>> solution = unify_smt_formulas_and_solve_first_cluster(graph, constraints)
    >>> deep_str(solution)
    "<Success: ({(StrToInt(<digit>_2) < 8, {'<digit>_2': '<digit>'}), (StrToInt(<digit>_2) > 3, {'<digit>_2': '<digit>'})}, {<digit>: 4})>"

    >>> list(solution.unwrap()[1].keys()) == [digit_dtree_1]
    True

    :param graph: The grammar graph representing the reference grammar.
    :param smt_formulas: The SMT-LIB formulas to solve.
    :param maybe_state_tree: The node in the state tree an SMT solving action should
        be applied on. This is used to obtain previous solutions and compute a new/
        different solution. If nothing is passed for this argument, we compute a
        solution without any exclusion constraints.
    :return: (1) The formulas in the cluster for which a solution was computed, and (2)
        a (possibly empty) list of solutions or a Boolean value (True if the
        formulas are universally valid or False for unsatisfiable/timeout) in the
        case of success. If a computed solution is no valid word in the respected
        sub grammar, a SyntaxError failure is returned. If another solution for the
        same state tree node resulted in a Boolean result, a failure with a
        StopIteration is returned.
    """

    # We cluster SMT formulas by tree substitutions. If there are two formulas with a
    # variable $var which is instantiated to different trees, we # need two separate
    # solutions. If, however, $var is instantiated with the *same* tree, we need one
    # solution to both formulas together.
    smt_formulas = rename_instantiated_variables_in_smt_formulas(smt_formulas)

    # We also cluster formulas by common variables (and instantiated subtrees:
    # One formula might yield an instantiation of a subtree of the instantiation of
    # another formula. They need to appear in the same cluster). The solver can
    # better handle smaller constraints, and those which do not have variables in
    # common can be handled independently.

    def cluster_keys(smt_formula: SMTFormula) -> FrozenOrderedSet[Variable]:
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

    formula_clusters: List[List[SMTFormula]] = cluster_by_common_elements(
        smt_formulas, cluster_keys
    )

    assert all(
        not cluster_keys(smt_formula)
        or any(smt_formula in cluster for cluster in formula_clusters)
        for smt_formula in smt_formulas
    ), "An SMT formula was not assigned to any cluster."

    formula_cluster = next(
        filter(
            None,
            formula_clusters
            + [
                [
                    smt_formula
                    for smt_formula in smt_formulas
                    if not cluster_keys(smt_formula)
                ]
            ],
        )
    )

    return solve_smt_formulas(graph, formula_cluster, maybe_state_tree).map(
        lambda result: (FormulaSet(formula_cluster), result)
    )


def solve_smt_formulas(
    graph: NeoGrammarGraph,
    smt_formulas: Iterable[SMTFormula],
    maybe_state_tree: Maybe[StateTree] = Nothing,
) -> Result[
    bool | Dict[Variable | DerivationTree, DerivationTree], SyntaxError | StopIteration
]:
    """
    Attempts to solve the given SMT-LIB formulas by calling Z3.

    This function does not unify variables pointing to the same derivation
    trees. E.g., a solution may be returned for the formula `var_1 = "a" and
    var_2 = "b"`, though `var_1` and `var_2` point to the same `<var>` tree as
    defined by their substitutions maps. Unification is performed in
    :func:`~isla.solver2.unify_smt_formulas_and_solve_first_cluster`.

    Example
    -------

    Consider our running assignment language example:

    >>> import string
    >>> grammar: Grammar = {
    ...     "<start>":
    ...         ["<stmt>"],
    ...     "<stmt>":
    ...         ["<assgn> ; <stmt>", "<assgn>"],
    ...     "<assgn>":
    ...         ["<var> := <rhs>"],
    ...     "<rhs>":
    ...         ["<var>", "<digit>"],
    ...     "<var>": list(string.ascii_lowercase),
    ...     "<digit>": list(string.digits)
    ... }
    >>> graph = NeoGrammarGraph(grammar)

    We simultaneously compute solutions for two simple constraints: A :code:`<var>`
    variable should equal "x," and a :code:`<digit>` variable should attain a value
    greater 3.

    >>> var = Variable("var", "<var>")
    >>> var_tree = DerivationTree("<var>")
    >>> digit = Variable("digit", "<digit>")
    >>> digit_tree = DerivationTree("<digit>")

    >>> var_eq_x_constraint = SMTFormula(
    ...     '(= var "x")',
    ...     instantiated_variables=FrozenOrderedSet([var]),
    ...     substitutions={var: var_tree},
    ... )

    >>> digit_greater_3_constraint = SMTFormula(
    ...     '(> (str.to.int digit) 3)',
    ...     instantiated_variables=FrozenOrderedSet([digit]),
    ...     substitutions={digit: digit_tree},
    ... )

    >>> solution = solve_smt_formulas(
    ...     graph, (var_eq_x_constraint, digit_greater_3_constraint)
    ... )
    >>> deep_str(solution)
    '<Success: {<var>: x, <digit>: 4}>'

    Let's assume we computed that solution before. It is not part of the state tree,
    and we want to compute another one. We construct the state tree, starting with
    the involved derivation trees:

    >>> parent_dtree = DerivationTree(
    ...     "<start>",
    ...     (
    ...         DerivationTree(
    ...             "<stmt>",
    ...             (
    ...                 DerivationTree(
    ...                     "<assgn>",
    ...                     (var_tree, DerivationTree(" := ", ()), digit_tree)
    ...                 ),
    ...             ),
    ...         ),
    ...     ),
    ... )

    >>> new_var_tree = DerivationTree(
    ...     "<var>", (solution.unwrap()[var_tree],), var_tree.id
    ... )
    >>> new_digit_tree = DerivationTree(
    ...     "<digit>", (solution.unwrap()[digit_tree],), digit_tree.id
    ... )

    >>> child_dtree = DerivationTree(
    ...     "<start>",
    ...     (
    ...         DerivationTree(
    ...             "<stmt>",
    ...             (
    ...                 DerivationTree(
    ...                     "<assgn>",
    ...                     (new_var_tree, DerivationTree(" := ", ()), new_digit_tree)
    ...                 ),
    ...             ),
    ...         ),
    ...     ),
    ... )

    >>> constraints = FormulaSet([var_eq_x_constraint, digit_greater_3_constraint])
    >>> tree = StateTree(CDT(constraints, parent_dtree)).add_child(
    ...     SolveSMTAction(constraints, solution.unwrap()),
    ...     CDT(FormulaSet([]), child_dtree)
    ... )

    >>> new_solution = solve_smt_formulas(
    ...     graph, (var_eq_x_constraint, digit_greater_3_constraint), Some(tree)
    ... )
    >>> deep_str(new_solution)
    '<Success: {<var>: x, <digit>: 5}>'

    We obtain a Boolean value for valid or unsatisfiable formulas or in the case of
    a timeout.

    >>> deep_str(solve_smt_formulas(
    ...     graph, (SMTFormula(z3_eq(digit.to_smt(), var.to_smt()), digit, var),)
    ... ))
    '<Success: False>'

    >>> deep_str(solve_smt_formulas(
    ...     graph, (SMTFormula(z3_eq(digit.to_smt(), digit.to_smt()), digit),)
    ... ))
    '<Success: True>'

    Once a "True" or "False" solution is contained in the state tree, no more solutions
    are produced. Instead, we return a Failure object with a StopIteration exception.

    >>> constraints = FormulaSet([
    ...     SMTFormula(z3_eq(digit.to_smt(), digit.to_smt()), digit)
    ... ])
    >>> tree = StateTree(CDT(constraints, parent_dtree)).add_child(
    ...     SolveSMTAction(constraints, True), CDT(FormulaSet([]), parent_dtree)
    ... )

    >>> deep_str(solve_smt_formulas(
    ...     graph,
    ...     (SMTFormula(z3_eq(digit.to_smt(), digit.to_smt()), digit),),
    ...     Some(tree)
    ... ))
    '<Failure: StopIteration()>'

    Finally, if a constraint is used in a wrong way, we obtain a SyntaxError failure.
    This happens, for example, if we ask for the integer representation of a
    :code:`<var>`:

    >>> (
    ...     deep_str(
    ...         solve_smt_formulas(
    ...             graph, (SMTFormula("(= (str.to.int var) 3)", var),)
    ...         )
    ...     )[:44]
    ...     + "...>"
    ... )
    '<Failure: Could not parse a numeric solution...>'

    :param graph: The grammar graph representing the reference grammar.
    :param smt_formulas: The SMT-LIB formulas to solve.
    :param maybe_state_tree: The node in the state tree an SMT solving action should
        be applied on. This is used to obtain previous solutions and compute a new/
        different solution. If nothing is passed for this argument, we compute a
        solution without any exclusion constraints.
    :return: A (possibly empty) list of solutions or a Boolean value (True if the
        formulas are universally valid or False for unsatisfiable/timeout) in the
        case of success. If a computed solution is no valid word in the respected
        sub grammar, a SyntaxError failure is returned. If another solution for the
        same state tree node resulted in a Boolean result, a failure with a
        StopIteration is returned.
    """

    # We first collect previous solutions. If any solution is a bool value, we
    # return a Failure. This function should not be called in those cases.
    def find_variable(dtree: DerivationTree) -> Variable:
        for formula in smt_formulas:
            for variable, other_dtree in formula.substitutions.items():
                if dtree.id == other_dtree.id:
                    return variable

        raise RuntimeError(
            "Could not to find a variable corresponding to a derivation tree that was "
            + "substituted in a previous SMT solution. This is probably a programming "
            + "error."
        )

    previous_solutions: ImmutableList[
        bool | Dict[Variable, z3.SeqRef]
    ] = maybe_state_tree.map(
        lambda state_tree: tuple(
            [
                action.result
                if isinstance(action.result, bool)
                else {
                    (
                        var_or_tree
                        if isinstance(var_or_tree, Variable)
                        else find_variable(var_or_tree)
                    ): z3.StringVal(str(val))
                    for var_or_tree, val in action.result.items()
                }
                for action, _ in state_tree.children
                if isinstance(action, SolveSMTAction)
            ]
        )
    ).value_or(
        ()
    )

    if any(isinstance(elem, bool) for elem in previous_solutions):
        # There is no further solution if any previous SMT solving rule application
        # returned True (universally valid) or False (unsatisfiable/timeout).
        return Failure(StopIteration())

    assert all(
        isinstance(previous_solution, dict) for previous_solution in previous_solutions
    )
    assert all(
        isinstance(var, Variable)
        for previous_solution in previous_solutions
        for var in previous_solution
    )
    assert all(
        isinstance(val, z3.SeqRef)
        for previous_solution in previous_solutions
        for val in previous_solution.values()
    )

    # If any SMT formula refers to *sub*trees in the instantiations of other SMT
    # formulas, we have to instantiate those first.
    priority_formulas = smt_formulas_referring_to_subtrees(smt_formulas)

    if priority_formulas:
        smt_formulas = priority_formulas
        assert not smt_formulas_referring_to_subtrees(smt_formulas)

    tree_substitutions = reduce(
        lambda d1, d2: d1 | d2,
        [smt_formula.substitutions for smt_formula in smt_formulas],
        {},
    )

    variables = reduce(
        lambda d1, d2: d1 | d2,
        [
            smt_formula.free_variables() | smt_formula.instantiated_variables
            for smt_formula in smt_formulas
        ],
        set(),
    )

    def process_solution(
        solver_result: SolverResult,
        maybe_model: Dict[Variable, DerivationTree],
    ) -> bool | Dict[Variable, DerivationTree]:
        if solver_result in (SolverResult.INVALID, SolverResult.UNKNOWN):
            return False

        if solver_result == SolverResult.VALID:
            return True

        assert variables, (
            "A satisfiable formula without variables must be logically valid; however, "
            + "a 'SolverResult.SATISFIABLE' result was returned."
        )
        assert maybe_model is not None

        return {
            tree_substitutions.get(variable, variable): maybe_model[variable]
            for variable in variables
        }

    return flow(
        solve_smt_formulas_with_language_constraints(
            graph,
            [smt_formula.formula for smt_formula in smt_formulas],
            variables,
            Some(tree_substitutions),
            Some(previous_solutions),
        ),
        map_(star(process_solution)),
    )


def smt_formulas_referring_to_subtrees(
    smt_formulas: Iterable[SMTFormula],
) -> List[SMTFormula]:
    """
    Returns a list of SMT formulas whose solutions address subtrees of other SMT
    formulas, but whose own substitution subtrees are in turn *not* referred by
    top-level substitution trees of other formulas. Those must be solved first to avoid
    inconsistencies.

    Example
    -------

    Consider our running assignment language example:

    >>> import string
    >>> grammar: Grammar = {
    ...     "<start>":
    ...         ["<stmt>"],
    ...     "<stmt>":
    ...         ["<assgn> ; <stmt>", "<assgn>"],
    ...     "<assgn>":
    ...         ["<var> := <rhs>"],
    ...     "<rhs>":
    ...         ["<var>", "<digit>"],
    ...     "<var>": list(string.ascii_lowercase),
    ...     "<digit>": list(string.digits)
    ... }

    Assume that we want to solve the following two constraints over that grammar:

    1. All digits should be greater or equal than 4.
    2. The first character in all assignments should be an "x".

    Those constraints cannot be solved simultaneously on the SMT level since SMT solvers
    are unaware of the inclusion of digits in assignments. We *first* must obtain a
    solution to constraint (1) and *then* a solution to constraint (2) incorporating
    the solution to (1).

    More precisely, we have two variables for a digit and an assignment:

    >>> digit = Variable("digit", "<digit>")
    >>> assgn = Variable("assgn", "<assgn>")

    The ISLa solver routines for grammar expansion and quantifier instantiation already
    constructed partial solutions (derivation trees) for these variables. Observe how
    the solution for the assignment references the solution for the digit.

    >>> digit_tree = DerivationTree("<digit>")
    >>> assgn_tree = DerivationTree(
    ...     "<assgn>",
    ...     (
    ...         DerivationTree("<var>"),
    ...         DerivationTree(" := ", ()),
    ...         DerivationTree("<rhs>", (digit_tree,)),
    ...     ),
    ... )

    Now, we specify the constraints:

    1. :code:`(>= (str.to.int digit) 4)`, and
    2. :code:`(= (str.at assgn 0) "x")`.

    >>> from orderedset import OrderedSet
    >>> digit_constraint = SMTFormula(
    ...     "(>= (str.to.int digit) 4)",
    ...     instantiated_variables=OrderedSet({digit}),
    ...     substitutions={digit: digit_tree},
    ... )
    >>> assgn_constraint = SMTFormula(
    ...     '(= (str.at assgn 0) "x")',
    ...     instantiated_variables=OrderedSet({assgn}),
    ...     substitutions={assgn: assgn_tree}
    ... )

    The function :func:`~isla.solver2.smt_formulas_referring_to_subtrees` detects that
    the digit constraint must be prioritized over the assignment constraint:

    >>> deep_str(
    ...     smt_formulas_referring_to_subtrees([digit_constraint, assgn_constraint])
    ... )
    "[(StrToInt(digit) >= 4, {'digit': '<digit>'})]"

    :param smt_formulas: The formulas to search for references to subtrees.
    :return: The list of conflicting formulas that must be solved first.
    """

    def subtree_ids(formula: SMTFormula) -> Set[int]:
        return {
            subtree.id
            for tree in formula.substitutions.values()
            for _, subtree in tree.paths()
            if subtree.id != tree.id
        }

    def tree_ids(formula: SMTFormula) -> Set[int]:
        return {tree.id for tree in formula.substitutions.values()}

    subtree_ids_for_formula: Dict[SMTFormula, Set[int]] = {
        formula: subtree_ids(formula) for formula in smt_formulas
    }

    tree_ids_for_formula: Dict[SMTFormula, Set[int]] = {
        formula: tree_ids(formula) for formula in smt_formulas
    }

    def independent_from_solutions_of_other_formula(
        idx: int, formula: SMTFormula
    ) -> bool:
        return all(
            not tree_ids_for_formula[other_formula].intersection(
                subtree_ids_for_formula[formula]
            )
            for other_idx, other_formula in enumerate(smt_formulas)
            if other_idx != idx
        )

    def refers_to_subtree_of_other_formula(idx: int, formula: SMTFormula) -> bool:
        return any(
            tree_ids_for_formula[formula].intersection(
                subtree_ids_for_formula[other_formula]
            )
            for other_idx, other_formula in enumerate(smt_formulas)
            if other_idx != idx
        )

    return [
        formula
        for idx, formula in enumerate(smt_formulas)
        if refers_to_subtree_of_other_formula(idx, formula)
        and independent_from_solutions_of_other_formula(idx, formula)
    ]


class SolverResult(Enum):
    VALID = 0
    INVALID = 1
    SATISFIABLE = 2
    UNKNOWN = 3

    @staticmethod
    def from_z3_result(z3_result) -> "SolverResult":
        """
        Transforms a Z3 result into a :class:`isla.solver2.SolverResult`. This function
        will not return a "VALID" since this is not communicated by Z3.

        :param z3_result: The Z3 result.
        :return: The :class:`isla.solver2.SolverResult`.
        """
        match z3_result:
            case z3.unsat:
                return SolverResult.INVALID
            case z3.unknown:
                return SolverResult.UNKNOWN
            case z3.sat:
                return SolverResult.SATISFIABLE


def solve_smt_formulas_with_language_constraints(
    graph: NeoGrammarGraph,
    smt_formulas: Iterable[z3.BoolRef],
    variables: AbstractSet[Variable],
    tree_substitutions: Maybe[Dict[Variable, DerivationTree]] = Maybe.empty,
    solutions_to_exclude: Maybe[List[Dict[Variable, z3.StringVal]]] = Maybe.empty,
    enable_optimized_z3_queries: bool = True,
) -> Result[
    Tuple[SolverResult, Dict[Variable | DerivationTree, DerivationTree]],
    SyntaxError,
]:
    """
    Computes a solution for the given SMT formulas. All values from the solution
    assignment satisfy the grammatical types of the variables they are assigned to
    (the "language constraints").

    Example
    -------

    Consider our running assignment language example:

    >>> import string
    >>> grammar: Grammar = {
    ...     "<start>":
    ...         ["<stmt>"],
    ...     "<stmt>":
    ...         ["<assgn> ; <stmt>", "<assgn>"],
    ...     "<assgn>":
    ...         ["<var> := <rhs>"],
    ...     "<rhs>":
    ...         ["<var>", "<digit>"],
    ...     "<var>": list(string.ascii_lowercase),
    ...     "<digit>": list(string.digits)
    ... }
    >>> graph = NeoGrammarGraph(grammar)

    We ask for the solution of :code:`str.to.int(n) != 0`, where "n" is of type
    :code:`<digit>`. Any solution returned will be such that "n" can be parsed as
    a :code:`<digit>` in the grammar. Since :code:`enable_optimized_z3_queries` is
    True by default, the variable is (internally) presented to the SMT solver as an
    integer.

    >>> n = Variable("n", "<digit>")
    >>> sat_res, solution = solve_smt_formulas_with_language_constraints(
    ...     graph,
    ...     smt_formulas=[z3.Not(z3_eq(z3.StrToInt(n.to_smt()), z3.IntVal(0)))],
    ...     variables={n}).unwrap()

    >>> print(sat_res)
    SolverResult.SATISFIABLE

    >>> 0 < int(str(solution[n])) <= 9
    True

    We can pass an already fixed assignment ofvariables to derivation trees that is
    considered in constraint solving.

    >>> x, y, z = (
    ...     Variable("x", "<assgn>"),
    ...     Variable("y", "<assgn>"),
    ...     Variable("y", "<assgn>"),
    ... )
    >>> constraints = (z3_eq(x.to_smt(), y.to_smt()), z3_eq(y.to_smt(), z.to_smt()))
    >>> tree_substitutions = {z: parse("a := 7", grammar).unwrap()}

    >>> deep_str(solve_smt_formulas_with_language_constraints(
    ...     graph, constraints, FormulaSet([x, y, z]), Some(tree_substitutions)))
    '<Success: (SolverResult.SATISFIABLE, {x: a := 7, y: a := 7})>'

    If a solution returned by the SMT solver does not fit to the grammar, a
    :class:`~returns.result.Failure` object is returned. If we ask for the integer
    representation of an :code:`<assgn>` variable to equal 3, for example, the solver
    returns "3" as requested; however, this cannot be parsed into an :code:`<assgn>`:

    >>> solve_smt_formulas_with_language_constraints(
    ...     graph,
    ...     smt_formulas=[
    ...         z3_eq(z3.StrToInt(x.to_smt()), z3.IntVal(3)),  # not "OK"
    ...         z3_eq(z.to_smt(), z3.StringVal("a := b"))  # "OK," but doesn't matter
    ...     ],
    ...     variables={x})
    <Failure: Could not parse a numeric solution (3) for variable x of type '<assgn>'; try running the solver without optimized Z3 queries or make sure that ranges are restricted to syntactically valid ones (according to the grammar).>

    :param graph: The grammar graph representing the grammar from which we obtain the
        language constraints.
    :param smt_formulas: The SMT formulas to solve.
    :param variables: The free variables in all SMT formulas.
    :param tree_substitutions: Already fixed substitutions of variables to derivation
        trees. Those variables are effectively not free; we expect these substitutions
        separately since SMT solvers don't know derivation trees.
    :param solutions_to_exclude: We exclude the exact combination of assignments in
        these solutions from the search space by adding
        :code:`not(x = s1[x] & y = s1[y] & ...) & not(...) & ...` to the SMT query.
    :param enable_optimized_z3_queries: If this parameter is True, "int" and "length"
        variables are specially handled. For example, all variables occurring
        exclusively in :code:`str.to.int(...)` contexts are fed to the SMT solver as
        integer variables and only later converted to strings/derivation trees. If this
        parameter is False, all variables are treated equally; their (string) structure
        if obtained from the grammar.
    :return: A :class:`~returns.result.Success` containing a tuple indicating the
        validity status resulting from the SMT call and a (possibly empty) map of
        solution assignments. If the solution returned by the solver is not part of the
        grammar (this mainly happens if :code:`enable_optimized_z3_queries` is True), a
        :class:`~returns.result.Failure` with a :class:`SyntaxError` is returned.
    """  # noqa: E501

    # We first check if the given formulas are valid or unsatisfiable without
    # additional language constraints.
    sat_result, _ = z3_solve(smt_formulas)
    if sat_result == z3.unsat:
        return Success((SolverResult.INVALID, {}))

    sat_result, _ = z3_solve((z3.Not(z3_and(tuple(smt_formulas))),))
    if sat_result == z3.unsat:
        return Success((SolverResult.VALID, {}))

    # We disable optimized Z3 queries if the SMT formulas contain "too concrete"
    # substitutions, that is, substitutions with a tree that is not merely an
    # open leaf. Example: we have a constrained `str.len(<chars>) < 10` and a
    # tree `<char><char>`; only the concrete length "10" is possible then. In fact,
    # we could simply finish of the tree and check the constraint, or restrict the
    # custom tree generation to admissible lengths, but we stay general here. The
    # SMT solution is more robust.

    if enable_optimized_z3_queries and not any(
        substitution.children
        for substitution in tree_substitutions.value_or({}).values()
    ):
        vars_in_context = infer_variable_contexts(variables, smt_formulas)
        length_vars = vars_in_context.length_vars
        int_vars = vars_in_context.int_vars
        flexible_vars = vars_in_context.flex_vars
    else:
        length_vars = frozenset()
        int_vars = frozenset()
        flexible_vars = frozenset(variables)

    # Add language constraints for "flexible" variables
    formulas: List[z3.BoolRef] = generate_language_constraints(
        graph, flexible_vars, tree_substitutions.value_or({})
    )

    # Create fresh variables for `str.len` and `str.to.int` variables.
    all_variables = set(variables)
    fresh_var_map: Dict[Variable, z3.ExprRef] = {}
    for var in length_vars | int_vars:
        fresh = fresh_constant(
            all_variables,
            Constant(var.name, "NOT-NEEDED"),
        )
        fresh_var_map[var] = z3.Int(fresh.name)

    # In `smt_formulas`, we replace all `length(...)` terms for "length variables"
    # with the corresponding fresh variable.
    replacement_map: Dict[z3.ExprRef, z3.ExprRef] = {
        expr: fresh_var_map[
            get_elem_by_equivalence(
                expr.children()[0],
                length_vars | int_vars,
                lambda e1, e2: e1 == e2.to_smt(),
            )
        ]
        for formula in smt_formulas
        for expr in visit_z3_expr(formula)
        if expr.decl().kind() in {z3.Z3_OP_SEQ_LENGTH, z3.Z3_OP_STR_TO_INT}
        and expr.children()[0] in {var.to_smt() for var in length_vars | int_vars}
    }

    # Perform substitution, add formulas
    formulas.extend(
        [
            cast(z3.BoolRef, z3_subst(formula, replacement_map))
            for formula in smt_formulas
        ]
    )

    # Lengths must be positive
    formulas.extend(
        [
            cast(
                z3.BoolRef,
                replacement_map[z3.Length(length_var.to_smt())] >= z3.IntVal(0),
            )
            for length_var in length_vars
        ]
    )

    # Add custom intervals for int variables
    def intervals_to_formula(
        repl_var: z3.ExprRef, intervals: List[Tuple[int, int]]
    ) -> List[z3.BoolRef]:
        """
        This function turns a list of intervals :code:`[(x1, y1), ..., (xn, yn)]`
        into a disjunction :code:`v >= x1 & v <= y1 | ... | v >= xn & v <= yn`.
        If :code:`xi` is :code:`-sys.maxsize`, then :code:`v >= xi` is omitted.
        Similarly, :code:`v <= yi` is omitted if :code:`yi` is :code:`sys.maxsize`.

        :param repl_var: The variable :code:`v` encoding the ranges of the intervals.
        :param intervals: The intervals to express as a formula.
        :return: A formula that is satisfiable for variables whose value resides in any
            of the given intervals.
        """
        return [
            z3_or(
                [
                    z3.And(
                        repl_var >= z3.IntVal(interval[0])
                        if interval[0] > -sys.maxsize
                        else z3.BoolVal(True),
                        repl_var <= z3.IntVal(interval[1])
                        if interval[1] < sys.maxsize
                        else z3.BoolVal(True),
                    )
                    for interval in intervals
                ]
            )
        ]

    for int_var in int_vars:
        if int_var.n_type == Variable.NUMERIC_NTYPE:
            # "NUM" variables range over the full int domain
            continue

        regex = extract_regular_expression(graph, int_var.n_type)
        maybe_intervals = numeric_intervals_from_regex(regex)
        repl_var = replacement_map[z3.StrToInt(int_var.to_smt())]
        formulas.extend(
            maybe_intervals.map(partial(intervals_to_formula, repl_var)).value_or([])
        )

    for prev_solution in solutions_to_exclude.value_or([]):
        prev_solution_formula = z3_and(
            [
                previous_solution_formula(
                    var, string_val, fresh_var_map, length_vars, int_vars
                )
                for var, string_val in prev_solution.items()
            ]
        )

        formulas.append(z3.Not(prev_solution_formula))

    sat_result, maybe_model = z3_solve(formulas)

    if sat_result != z3.sat:
        return Success((SolverResult.from_z3_result(sat_result), {}))

    assert maybe_model is not None
    assert SolverResult.from_z3_result(sat_result) == SolverResult.SATISFIABLE

    return reduce(
        lambda prev_success_or_failure, variable: prev_success_or_failure.bind(
            lambda res_and_map: (
                extract_model_value(
                    graph, variable, maybe_model, fresh_var_map, length_vars, int_vars
                ).map(
                    lambda model_value: (
                        res_and_map[0],
                        res_and_map[1] | {variable: model_value},
                    )
                )
            )
        ),
        variables,
        Success((SolverResult.SATISFIABLE, {})),
    )


def rename_instantiated_variables_in_smt_formulas(
    smt_formulas: Iterable[SMTFormula],
) -> ImmutableList[SMTFormula]:
    """
    This function renames the already instantiated (substituted) variables in an SMT
    formula. For any variable v associated to a tree t, the original, logical nam
    of v is replaced by :code:`"{t.value}_{t.id}"`. Thus, variables instantiated with
    the same trees will look the same, and variables with the same name, but
    instantiated with a different tree will look differently.

    Example
    -------

    In the following example, we twice consider the logical formula :code:`x = y`.
    However, in the first case, the variables are substituted with identical trees;
    thus, the formula becomes a tautology. In the second case, they are substituted
    by different trees, and the variables obtain different names.

    >>> x_1 = BoundVariable("x", "<A>")
    >>> x_1_t = DerivationTree("<A>", id=0)
    >>> y = BoundVariable("y", "<A>")
    >>> y_t = DerivationTree("<A>", id=0)
    >>> x_2 = BoundVariable("x", "<A>")
    >>> x_2_t = DerivationTree("<A>", id=1)
    >>> formulas = [
    ...     SMTFormula("(= x y)", x_1, y).substitute_expressions({x_1: x_1_t, y: y_t}),
    ...     SMTFormula("(= x y)", x_2, y).substitute_expressions({x_2: x_2_t, y: y_t}),
    ... ]
    >>> print(deep_str(rename_instantiated_variables_in_smt_formulas(formulas)))
    ((<A>_0 == <A>_0, {'<A>_0': '<A>'}), (<A>_1 == <A>_0, {'<A>_1': '<A>', '<A>_0': '<A>'}))

    :param smt_formulas: The SMT formulas to rename.
    :return: The renamed formulas.
    """  # noqa: E501

    result = []
    for sub_formula in smt_formulas:
        new_smt_formula = sub_formula.formula
        new_substitutions = sub_formula.substitutions
        new_instantiated_variables = sub_formula.instantiated_variables

        for subst_var, subst_tree in sub_formula.substitutions.items():
            new_name = f"{subst_tree.value}_{subst_tree.id}"
            new_var = BoundVariable(new_name, subst_var.n_type)

            new_smt_formula = z3_subst(
                new_smt_formula, {subst_var.to_smt(): new_var.to_smt()}
            )
            new_substitutions = {
                new_var if k == subst_var else k: v
                for k, v in new_substitutions.items()
            }
            new_instantiated_variables = {
                new_var if v == subst_var else v for v in new_instantiated_variables
            }

        result.append(
            SMTFormula(
                new_smt_formula,
                *sub_formula.free_variables_,
                instantiated_variables=new_instantiated_variables,
                substitutions=new_substitutions,
            )
        )

    return tuple(result)


@dataclass(frozen=True)
class VariableContexts:
    """
    A result object type for :func:`~isla.solver2.infer_variable_contexts` encapsulating
    variables appearing in different contexts: Length contexts, numeric contexts,
    and arbitrary ones.
    """

    length_vars: frozenset[Variable]
    int_vars: frozenset[Variable]
    flex_vars: frozenset[Variable]

    def __str__(self):
        return (
            f"{{LENGTH: {deep_str(self.length_vars)}, "
            + f"INT: {deep_str(self.int_vars)}, "
            + f"FLEX: {deep_str(self.flex_vars)}}}"
        )


def infer_variable_contexts(
    variables: AbstractSet[Variable], smt_formulas: Iterable[z3.BoolRef]
) -> VariableContexts:
    """
    Divides the given variables into

    1. those that occur only in :code:`length(...)` contexts,
    2. those that occur only in :code:`str.to.int(...)` contexts, and
    3. "flexible" constants occurring in other/various contexts.

    >>> x = Variable("x", "<X>")
    >>> y = Variable("y", "<Y>")

    Two variables in an arbitrary context.

    >>> from isla.z3_helpers import z3_eq
    >>> f = z3_eq(x.to_smt(), y.to_smt())
    >>> var_contexts = infer_variable_contexts({x, y}, (f,))
    >>> var_contexts.length_vars
    frozenset()
    >>> var_contexts.int_vars
    frozenset()
    >>> var_contexts.flex_vars == frozenset({
    ...     Variable("x", "<X>"), Variable("y", "<Y>")})
    True

    Variable x occurs in a length context, variable y in an arbitrary one.

    >>> f = z3.And(
    ...     z3.Length(x.to_smt()) > z3.IntVal(10),
    ...     z3_eq(y.to_smt(), z3.StringVal("y")))
    >>> deep_str(infer_variable_contexts({x, y}, (f,)))
    '{LENGTH: {x}, INT: {}, FLEX: {y}}'

    Variable x occurs in a length context, y does not occur.

    >>> f: z3.BoolRef = z3.Length(x.to_smt()) > z3.IntVal(10)
    >>> deep_str(infer_variable_contexts({x, y}, (f,)))
    '{LENGTH: {x}, INT: {}, FLEX: {y}}'

    Variables x and y both occur in a length context.

    >>> f: z3.BoolRef = z3.Length(x.to_smt()) > z3.Length(y.to_smt())
    >>> var_contexts = infer_variable_contexts({x, y}, (f,))
    >>> var_contexts.length_vars == frozenset({
    ...     Variable("x", "<X>"), Variable("y", "<Y>")})
    True
    >>> var_contexts.int_vars
    frozenset()
    >>> var_contexts.flex_vars
    frozenset()

    Variable x occurs in a :code:`str.to.int` context.

    >>> f = z3.StrToInt(x.to_smt()) > z3.IntVal(17)
    >>> deep_str(infer_variable_contexts({x}, (f,)))
    '{LENGTH: {}, INT: {x}, FLEX: {}}'

    Now, x also occurs in a different context; it's "flexible" now.

    >>> f = z3.And(
    ...     z3.StrToInt(x.to_smt()) > z3.IntVal(17),
    ...     z3_eq(x.to_smt(), z3.StringVal("17")))
    >>> deep_str(infer_variable_contexts({x}, (f,)))
    '{LENGTH: {}, INT: {}, FLEX: {x}}'

    :param variables: The constants to divide/filter from.
    :param smt_formulas: The SMT formulas to consider in the filtering.
    :return: A pair of constants occurring in `str.len` contexts, and the
    remaining ones. The union of both sets equals `variables`, and both sets
    are disjoint.
    """

    parent_relationships = reduce(
        merge_dict_of_sets,
        [parent_relationships_in_z3_expr(formula) for formula in smt_formulas],
        {},
    )

    contexts: Dict[Variable, Set[int]] = {
        var: {
            expr.decl().kind() for expr in parent_relationships.get(var.to_smt(), set())
        }
        or {-1}
        for var in variables
    }

    # The set `length_vars` consists of all variables that only occur in
    # `str.len(...)` context.
    length_vars: Set[Variable] = {
        var
        for var in variables
        if all(context == z3.Z3_OP_SEQ_LENGTH for context in contexts[var])
    }

    # The set `int_vars` consists of all variables that only occur in
    # `str.to.int(...)` context.
    int_vars: Set[Variable] = {
        var
        for var in variables
        if all(context == z3.Z3_OP_STR_TO_INT for context in contexts[var])
    }

    # "Flexible" variables are the remaining ones.
    flexible_vars = variables.difference(length_vars).difference(int_vars)

    return VariableContexts(
        length_vars=frozenset(length_vars),
        int_vars=frozenset(int_vars),
        flex_vars=frozenset(flexible_vars),
    )


@lru_cache
def extract_regular_expression(
    graph: NeoGrammarGraph, nonterminal: str, grammar_unwinding_threshold: int = 4
) -> z3.ReRef:
    """
    This function computes an approximate regular expression for the language of the
    given nonterminal in the grammar represented by the given graph. The returned
    regular expression is precise if the language in question is regular. If this is
    not the case, we unwind the non-regular expansions
    :code:`grammar_unwinding_threshold` times and return the regular expression for
    this approximate grammar.

    Example
    -------

    We extract a (precise) regular expression for the :code:`<stmt>` sub language of
    the assignment language:

    >>> import string
    >>> grammar: Grammar = {
    ...     "<start>":
    ...         ["<stmt>"],
    ...     "<stmt>":
    ...         ["<assgn> ; <stmt>", "<assgn>"],
    ...     "<assgn>":
    ...         ["<var> := <rhs>"],
    ...     "<rhs>":
    ...         ["<var>", "<digit>"],
    ...     "<var>": list(string.ascii_lowercase),
    ...     "<digit>": list(string.digits)
    ... }
    >>> graph = NeoGrammarGraph(grammar)

    >>> extract_regular_expression(graph, "<stmt>")
    re.++(re.++(re.++(Star(re.++(re.++(re.++(Range("a", "z"),
                                            Re(" := ")),
                                       Union(Range("0", "9"),
                                            Range("a", "z"))),
                                 Re(" ; "))),
                      Range("a", "z")),
                Re(" := ")),
          Union(Range("0", "9"), Range("a", "z")))

    :param graph: The grammar graph representing the grammar for which we should
        compute a regular expression.
    :param nonterminal: The start nonterminal for the sub language for which we should
        comptues a regular expression.
    :param grammar_unwinding_threshold: The number of times non-regular grammar
        expansions should be unwound if necessary for the computation of an
        approximate regular expression.
    :return: A (possibly approximate) Z3 regular expression for the given grammar
        sub-language.
    """

    # For definitions like `<a> ::= <b>`, we only compute the regular expression
    # for `<b>`. That way, we might save some calls if `<b>` is used multiple times
    # (e.g., as in `<byte>`).
    canonical_expansions = [
        split_str_with_nonterminals(expansion)
        for expansion in graph.grammar[nonterminal]
    ]

    if (
        len(canonical_expansions) == 1
        and len(canonical_expansions[0]) == 1
        and is_nonterminal(canonical_expansions[0][0])
    ):
        sub_nonterminal = canonical_expansions[0][0]
        assert (
            nonterminal != sub_nonterminal
        ), f"Expansion {nonterminal} => {sub_nonterminal}: Infinite recursion!"
        return extract_regular_expression(
            graph, sub_nonterminal, grammar_unwinding_threshold
        )

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
            and not graph.reachable(elem, nonterminal)
            for elem in canonical_expansions[0]
        )
    ):
        return z3.Concat(
            *[
                z3.Re(elem)
                if not is_nonterminal(elem)
                else extract_regular_expression(
                    graph, elem, grammar_unwinding_threshold
                )
                for elem in canonical_expansions[0]
            ]
        )

    regex_conv = RegexConverter(
        graph.grammar,
        compress_unions=True,
        max_num_expansions=grammar_unwinding_threshold,
    )

    regex = regex_conv.to_regex(nonterminal, convert_to_z3=False)
    LOGGER.debug(f"Computed regular expression for nonterminal {nonterminal}:\n{regex}")
    z3_regex = regex_to_z3(regex)

    if assertions_activated():
        # Check correctness of regular expression
        grammar = graph.subgraph(nonterminal).grammar

        # L(regex) \subseteq L(grammar)
        LOGGER.debug(
            "Checking L(regex) \\subseteq L(grammar) for "
            + "nonterminal '%s' and regex '%s'",
            nonterminal,
            regex,
        )
        assert_regex_lang_subset_grammar_lang(z3_regex, grammar)

    return z3_regex


def assert_regex_lang_subset_grammar_lang(z3_regex: z3.ReRef, grammar: Grammar) -> None:
    """
    Generates strings from the given regular expressions and asserts that they are in
    the language of the grammar by attempting to parse the generated strings. Has not
    side effects in the case of success; if a string represented by the regular
    expression is not in the grammar language, an AssertionError is raised.

    :param z3_regex: The regex of the regex-grammar-inclusion-check.
    :param grammar: The grammar of the regex-grammar-inclusion-check.
    :return: Nothing.
    """

    parser = EarleyParser(grammar)
    c = z3.String("c")

    prev: Set[str] = set()
    for _ in range(100):
        s = z3.Solver()
        s.add(z3.InRe(c, z3_regex))
        for inp in prev:
            s.add(z3.Not(c == z3.StringVal(inp)))
        if s.check() != z3.sat:
            LOGGER.debug(
                "Cannot find the %d-th solution for regex %s (timeout).\nThis is "
                + "*not* a problem if there not that many solutions (for regexes "
                + "with finite language), or if we are facing a meaningless "
                + "timeout of the solver.",
                len(prev) + 1,
                z3_regex,
            )
            break

        new_inp = smt_string_val_to_string(s.model()[c])
        try:
            next(parser.parse(new_inp))
        except SyntaxError:
            assert (
                False
            ), f"Input '{new_inp}' from regex language is not in grammar language."

        prev.add(new_inp)


def generate_language_constraints(
    graph: NeoGrammarGraph,
    variables: Iterable[Variable],
    tree_substitutions: Dict[Variable, DerivationTree],
) -> List[z3.BoolRef]:
    r"""
    This function generates Z3 constraints on the language of the given variables.
    We distinguish three cases:

    1. The variable is *numeric.* In this case, a regular expression describing the
       natural numbers (incl. 0) is returned. TODO: Numeric qfrs will be removed in 2.0.
    2. The variable is in :code:`tree_substitutions`. In this case, we concatenate
       the regular expressions for the tree leaves.
    3. Otherwise, we compute the regular expression directly from the grammar.

    Examples
    --------

    Consider our assignment language:

    >>> import string
    >>> grammar: Grammar = {
    ...     "<start>":
    ...         ["<stmt>"],
    ...     "<stmt>":
    ...         ["<assgn> ; <stmt>", "<assgn>"],
    ...     "<assgn>":
    ...         ["<var> := <rhs>"],
    ...     "<rhs>":
    ...         ["<var>", "<digit>"],
    ...     "<var>": list(string.ascii_lowercase),
    ...     "<digit>": list(string.digits)
    ... }
    >>> graph = NeoGrammarGraph(grammar)

    When asking for the constraint of an :code:`<assgn>` that is not contained in the
    substitutions, the full grammar-based regular expression is returned:

    >>> assgn_var = Variable("assngn", "<assgn>")
    >>> generate_language_constraints(graph, [assgn_var], {})
    [InRe(assngn,
         re.++(re.++(Range("a", "z"), Re(" := ")),
               Union(Range("0", "9"), Range("a", "z"))))]

    However, if :code:`assgn_var` is associated in the substitutions to a derivation
    tree assigning a :code:`<digit>` to the :code:`<var>`, a more restrictive constraint
    is returned:

    >>> tree = DerivationTree(
    ...     "<start>", [
    ...         DerivationTree(
    ...             "<stmt>", [
    ...                 DerivationTree(
    ...                     "<assgn>", [
    ...                         DerivationTree("<var>"),
    ...                         DerivationTree(" := ", ()),
    ...                         DerivationTree("<rhs>", (DerivationTree("<digit>"),)),
    ...                     ])])])

    >>> generate_language_constraints(graph, [assgn_var], {assgn_var: tree})
    [InRe(assngn,
         re.++(re.++(Range("a", "z"), Re(" := ")),
               Range("0", "9")))]

    :param graph: The graph representing the grammar of the variables.
    :param variables: The variables for which language constraints should be
        generated.
    :param tree_substitutions: Substitutions from variables to trees specializing
        the language represented by the variables.
    :return: A set of language constraints for the given variables.
    """

    formulas: List[z3.BoolRef] = []
    for constant in variables:
        if constant.is_numeric():
            # TODO: This case will be obsolete after the removal of numeric qfrs
            regex = z3.Union(
                z3.Re("0"),
                z3.Concat(z3.Range("1", "9"), z3.Star(z3.Range("0", "9"))),
            )
        elif constant in tree_substitutions:
            # We have a more concrete shape of the desired instantiation available
            regexes = [
                extract_regular_expression(graph, t) if is_nonterminal(t) else z3.Re(t)
                for t in split_str_with_nonterminals(str(tree_substitutions[constant]))
            ]
            assert regexes
            regex = z3.Concat(*regexes) if len(regexes) > 1 else regexes[0]
        else:
            regex = extract_regular_expression(graph, constant.n_type)

        formulas.append(z3.InRe(z3.String(constant.name), regex))

    return formulas


def previous_solution_formula(
    var: Variable,
    string_val: z3.StringVal,
    fresh_var_map: Dict[Variable, z3.ExprRef],
    length_vars: AbstractSet[Variable],
    int_vars: AbstractSet[Variable],
) -> z3.BoolRef:
    """
    Computes a formula describing the previously found solution
    :code:`var == string_val` for an :class:`~isla.language.SMTFormula`.
    Considers the special cases that :code:`var` is a "length" or "int"
    variable, i.e., occurred only in these contexts in the formula this
    solution is about.

    >>> x = Variable("x", "<X>")
    >>> previous_solution_formula(x, z3.StringVal("val"), {}, set(), set())
    x == "val"

    >>> previous_solution_formula(
    ...     x, z3.StringVal("val"), {x: z3.Int("x_0")}, {x}, set())
    x_0 == 3

    >>> previous_solution_formula(x, z3.StringVal("10"), {x: z3.Int("x_0")}, set(), {x})
    x_0 == 10

    >>> x = Variable("x", Variable.NUMERIC_NTYPE)
    >>> previous_solution_formula(x, z3.StringVal("10"), {x: z3.Int("x_0")}, set(), {x})
    x_0 == 10

    A "numeric" variable (of "NUM" type) is expected to always be an int variable,
    which also needs to be reflected in its inclusion in :code:`fresh_var_map`.

    >>> x = Variable("x", Variable.NUMERIC_NTYPE)
    >>> previous_solution_formula(x, z3.StringVal("10"), {}, set(), set())
    Traceback (most recent call last):
    ...
    AssertionError

    :param var: The variable the solution is for.
    :param string_val: The solution for :code:`var`.
    :param fresh_var_map: A map from variables to fresh variables for "length" or
                          "int" variables.
    :param length_vars: The "length" variables.
    :param int_vars: The "int" variables.
    :return: An equation describing the previous solution.
    """

    if var in int_vars:
        return z3_eq(
            fresh_var_map[var],
            z3.IntVal(int(smt_string_val_to_string(string_val))),
        )
    elif var in length_vars:
        return z3_eq(
            fresh_var_map[var],
            z3.IntVal(len(smt_string_val_to_string(string_val))),
        )
    else:
        assert not var.is_numeric()
        return z3_eq(var.to_smt(), string_val)


def extract_model_value(
    graph: NeoGrammarGraph,
    var: Variable,
    model: z3.ModelRef,
    fresh_var_map: Dict[Variable, z3.ExprRef],
    length_vars: AbstractSet[Variable],
    int_vars: AbstractSet[Variable],
) -> Result[DerivationTree, SyntaxError]:
    r"""
    Extracts a value for :code:`var` from :code:`model`. Considers the following
    special cases:

    Numeric Variables
        Returns a closed derivation tree of one node with a string representation
        of the numeric solution.

    "Length" Variables
        Returns a string of the length corresponding to the model and
        :code:`fresh_var_map`, see also
        :meth:`~isla.solver2.safe_create_fixed_length_tree()`.

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
    >>> graph = NeoGrammarGraph(grammar)

    **Numeric Variables:**

    >>> n = Variable("n", Variable.NUMERIC_NTYPE)
    >>> f = z3_eq(z3.StrToInt(n.to_smt()), z3.IntVal(15))
    >>> z3_solver = z3.Solver()
    >>> z3_solver.add(f)
    >>> z3_solver.check()
    sat
    >>> model = z3_solver.model()
    >>> DerivationTree.next_id = 1
    >>> extract_model_value(graph,n, model, {}, set(), set()).unwrap()
    DerivationTree('15', (), id=1)

    For a trivially true solution on numeric variables, we return a random number:

    >>> f = z3_eq(n.to_smt(), n.to_smt())
    >>> z3_solver = z3.Solver()
    >>> z3_solver.add(f)
    >>> z3_solver.check()
    sat

    >>> model = z3_solver.model()
    >>> DerivationTree.next_id = 1
    >>> random.seed(0)
    >>> extract_model_value(graph, n, model, {n: n.to_smt()}, set(), {n}).unwrap()
    DerivationTree('-2116850434379610162', (), id=1)

    **"Length" Variables:**

    >>> x = Variable("x", "<X>")
    >>> x_0 = z3.Int("x_0")
    >>> f = z3_eq(x_0, z3.IntVal(3))
    >>> z3_solver = z3.Solver()
    >>> z3_solver.add(f)
    >>> z3_solver.check()
    sat
    >>> model = z3_solver.model()
    >>> result = extract_model_value(graph, x, model, {x: x_0}, {x}, set())
    >>> result.unwrap().value
    '<X>'
    >>> str(result.unwrap())
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
    >>> extract_model_value(graph, y, model, {y: y_0}, set(), {y}).unwrap()
    DerivationTree('<Y>', (DerivationTree('<digit>', (DerivationTree('5', (), id=1),), id=2),), id=3)

    **"Flexible" Variables:**

    >>> f = z3_eq(x.to_smt(), z3.StringVal("xxxxx"))
    >>> z3_solver = z3.Solver()
    >>> z3_solver.add(f)
    >>> z3_solver.check()
    sat
    >>> model = z3_solver.model()
    >>> result = extract_model_value(graph, x, model, {}, set(), set())
    >>> result.unwrap().value
    '<X>'
    >>> str(result.unwrap())
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
    >>> graph = NeoGrammarGraph(grammar)

    >>> i = Variable("i", "<int>")
    >>> i_0 = z3.Int("i_0")
    >>> f = z3_eq(i_0, z3.IntVal(5))

    >>> z3_solver = z3.Solver()
    >>> z3_solver.add(f)
    >>> z3_solver.check()
    sat

    The following test works when run from the IDE, but unfortunately not when
    started from CI/the `test_doctests.py` script. Thus, we only show it as code
    block (we added a unit test as a replacement) (TODO Add new unit test)::

        model = z3_solver.model()
        print(solver.extract_model_value(graph, i, model, {i: i_0}, set(), {i}))
        # Prints: +005

    :param graph: The grammar graph representing the grammar for :code:`var`.
    :param var: The variable for which to extract a solution from the model.
    :param model: The model containing the solution.
    :param fresh_var_map: A map from variables to fresh symbols for "length" and
                          "int" variables.
    :param length_vars: The set of "length" variables.
    :param int_vars: The set of "int" variables.
    :return: A :class:`~isla.derivation_tree.DerivationTree` object corresponding
             to the solution in :code:`model`.
    """  # noqa: E501

    f_flex_vars = extract_model_value_flexible_var
    f_int_vars = partial(extract_model_value_int_var, f_flex_vars)
    f_length_vars = partial(extract_model_value_length_var, f_int_vars)
    f_num_vars = partial(extract_model_value_numeric_var, f_length_vars)

    return f_num_vars(graph, var, model, fresh_var_map, length_vars, int_vars)


ExtractModelValueFallbackType = Callable[
    [
        NeoGrammarGraph,
        Variable,
        z3.ModelRef,
        Dict[Variable, z3.ExprRef],
        Set[Variable],
        Set[Variable],
    ],
    Result[DerivationTree, SyntaxError],
]


def extract_model_value_numeric_var(
    fallback: ExtractModelValueFallbackType,
    graph: NeoGrammarGraph,
    var: Variable,
    model: z3.ModelRef,
    fresh_var_map: Dict[Variable, z3.ExprRef],
    length_vars: Set[Variable],
    int_vars: Set[Variable],
) -> Result[DerivationTree, SyntaxError]:
    """
    Addresses the case of numeric variables from
    :meth:`~isla.solver2.extract_model_value`.

    :param fallback: The function to call if this function is not responsible.
    :param graph: The grammar graph representing the grammar for :code:`var`.
    :param var: See :meth:`~isla.solver2.extract_model_value`.
    :param model: See :meth:`~isla.solver2.extract_model_value`.
    :param fresh_var_map: See :meth:`~isla.solver2.extract_model_value`.
    :param length_vars: See :meth:`~isla.solver2.extract_model_value`.
    :param int_vars: See :meth:`~isla.solver2.extract_model_value`.
    :return: See :meth:`~isla.solver2.extract_model_value`.
    """

    if not var.is_numeric():
        return fallback(graph, var, model, fresh_var_map, length_vars, int_vars)

    z3_var = z3.String(var.name)
    if z3_var.decl() in model.decls():
        model_value = model[z3_var]
    else:
        assert var in int_vars
        assert var in fresh_var_map

        model_value = model[fresh_var_map[var]]

        if model_value is None:
            # This can happen for universally true formulas, e.g., `x = x`.
            # In that case, we return a random integer.
            model_value = z3.IntVal(random.randint(-sys.maxsize, sys.maxsize))

    assert (
        model_value is not None
    ), f"No solution for variable {var} found in model {model}"

    string_value = smt_string_val_to_string(model_value)
    assert string_value
    assert (
        string_value.isnumeric()
        or string_value[0] == "-"
        and string_value[1:].isnumeric()
    )

    return Success(DerivationTree(string_value, ()))


def extract_model_value_length_var(
    fallback: ExtractModelValueFallbackType,
    graph: NeoGrammarGraph,
    var: Variable,
    model: z3.ModelRef,
    fresh_var_map: Dict[Variable, z3.ExprRef],
    length_vars: Set[Variable],
    int_vars: Set[Variable],
) -> Result[DerivationTree, SyntaxError]:
    """
    Addresses the case of length variables from
    :meth:`~isla.solver2.extract_model_value`.

    :param fallback: The function to call if this function is not responsible.
    :param graph: The grammar graph representing the grammar for :code:`var`.
    :param var: See :meth:`~isla.solver2.extract_model_value`.
    :param model: See :meth:`~isla.solver2.extract_model_value`.
    :param fresh_var_map: See :meth:`~isla.solver2.extract_model_value`.
    :param length_vars: See :meth:`~isla.solver2.extract_model_value`.
    :param int_vars: See :meth:`~isla.solver2.extract_model_value`.
    :return: See :meth:`~isla.solver2.extract_model_value`.
    """

    if var not in length_vars:
        return fallback(graph, var, model, fresh_var_map, length_vars, int_vars)

    assert var in fresh_var_map
    assert fresh_var_map[var].decl() in model.decls()

    fixed_length_tree = create_fixed_length_tree(
        start=var.n_type,
        canonical_grammar=frozen_canonical(graph.grammar),
        target_length=model[fresh_var_map[var]].as_long(),
    )

    match fixed_length_tree:
        case Some(tree):
            return Success(tree)
        case Maybe.empty:
            return Failure(
                SyntaxError(
                    f"Could not create a tree with the start symbol '{var.n_type}' "
                    + f"of length {model[fresh_var_map[var]].as_long()}; try "
                    + "running the solver without optimized Z3 queries or make "
                    + "sure that lengths are restricted to syntactically valid "
                    + "ones (according to the grammar).",
                )
            )


def extract_model_value_int_var(
    fallback: ExtractModelValueFallbackType,
    graph: NeoGrammarGraph,
    var: Variable,
    model: z3.ModelRef,
    fresh_var_map: Dict[Variable, z3.ExprRef],
    length_vars: Set[Variable],
    int_vars: Set[Variable],
) -> Result[DerivationTree, SyntaxError]:
    """
    Addresses the case of int variables from
    :meth:`~isla.solver2.extract_model_value`.

    :param fallback: The function to call if this function is not responsible.
    :param graph: The grammar graph representing the grammar for :code:`var`.
    :param var: See :meth:`~isla.solver2.extract_model_value`.
    :param model: See :meth:`~isla.solver2.extract_model_value`.
    :param fresh_var_map: See :meth:`~isla.solver2.extract_model_value`.
    :param length_vars: See :meth:`~isla.solver2.extract_model_value`.
    :param int_vars: See :meth:`~isla.solver2.extract_model_value`.
    :return: See :meth:`~isla.solver2.extract_model_value`.
    """
    if var not in int_vars:
        return fallback(graph, var, model, fresh_var_map, length_vars, int_vars)

    str_model_value = model[fresh_var_map[var]].as_string()

    try:
        int_model_value = int(str_model_value)
    except ValueError:
        raise RuntimeError(f"Value {str_model_value} for {var} is not a number")

    var_type = var.n_type

    def parse_with_extended_format() -> Result[DerivationTree, Exception]:
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
                extract_regular_expression(graph, var.n_type),
            )
        )

        if z3_solver.check() != z3.sat:
            return Failure(
                SyntaxError(
                    "Could not parse a numeric solution "
                    + f"({str_model_value}) for variable "
                    + f"{var} of type '{var.n_type}'; try "
                    + "running the solver without optimized Z3 queries or make "
                    + "sure that ranges are restricted to syntactically valid "
                    + "ones (according to the grammar).",
                )
            )

        return parse(
            (
                z3_solver.model()[maybe_plus_var].as_string()
                if int_model_value >= 0
                else "-"
            )
            + z3_solver.model()[zeroes_padding_var].as_string()
            + (str_model_value if int_model_value >= 0 else str(-int_model_value)),
            graph.grammar,
            var.n_type,
        )

    return parse(
        str(int_model_value),
        graph.grammar,
        start_nonterminal=var_type,
    ).lash(lambda _: parse_with_extended_format())


def extract_model_value_flexible_var(
    graph: NeoGrammarGraph,
    var: Variable,
    model: z3.ModelRef,
    fresh_var_map: Dict[Variable, z3.ExprRef],
    length_vars: Set[Variable],
    int_vars: Set[Variable],
) -> Result[DerivationTree, SyntaxError]:
    """
    Addresses the case of "flexible" variables from
    :meth:`~isla.solver2.extract_model_value`.

    :param graph: The grammar graph representing the grammar for :code:`var`.
    :param var: See :meth:`~isla.solver2.extract_model_value`.
    :param model: See :meth:`~isla.solver2.extract_model_value`.
    :param fresh_var_map: See :meth:`~isla.solver2.extract_model_value`.
    :param length_vars: See :meth:`~isla.solver2.extract_model_value`.
    :param int_vars: See :meth:`~isla.solver2.extract_model_value`.
    :return: See :meth:`~isla.solver2.extract_model_value`.
    """

    return parse(
        smt_string_val_to_string(model[z3.String(var.name)]),
        graph.grammar,
        start_nonterminal=var.n_type,
    )


@safe
def parse_peg(
    inp: str, grammar: Grammar, start_nonterminal: str = "<start>"
) -> Result[DerivationTree, SyntaxError | RecursionError]:
    """
    This function parses :code:`inp` in the given grammar with the specified start
    nonterminal using a PEG parser.

    See also :func:`~isla.language.parse_match_expression`.

    Example
    -------

    Consider the following grammar for the assignment language.

    >>> import string
    >>> grammar: Grammar = {
    ...     "<start>":
    ...         ["<stmt>"],
    ...     "<stmt>":
    ...         ["<assgn> ; <stmt>", "<assgn>"],
    ...     "<assgn>":
    ...         ["<var> := <rhs>"],
    ...     "<rhs>":
    ...         ["<var>", "<digit>"],
    ...     "<var>": list(string.ascii_lowercase),
    ...     "<digit>": list(string.digits)
    ... }

    We parse a statement with two assignments; the resulting tree starts with the
    specified nonterminal :code:`<start>`:

    >>> deep_str(parse_peg("x := 0 ; y := x", grammar).map(lambda t: (t, t.value)))
    '<Success: (x := 0 ; y := x, <start>)>'

    Now, we parse a single assignment with the :code:`<assgn>` start nonterminal:

    >>> deep_str(parse_peg("x := 0", grammar, "<assgn>").map(lambda t: (t, t.value)))
    '<Success: (x := 0, <assgn>)>'

    In case of an error, a Failure is returned:

    >>> print(deep_str(parse_peg("x := 0 FOO", grammar, "<assgn>").alt(
    ...     lambda e: f'"{type(e).__name__}: {e}"')))
    <Failure: "SyntaxError: at ' FOO'">

    The grammar above was a grammar that could be interpreted as a PEG grammar. Parsing
    a statement with the grammar below (changed order of the expansions for statements)
    can, in general, only be parsed with the EarleyParser:

    >>> grammar: Grammar = {
    ...     "<start>":
    ...         ["<stmt>"],
    ...     "<stmt>":
    ...         ["<assgn>", "<assgn> ; <stmt>"],
    ...     "<assgn>":
    ...         ["<var> := <rhs>"],
    ...     "<rhs>":
    ...         ["<var>", "<digit>"],
    ...     "<var>": list(string.ascii_lowercase),
    ...     "<digit>": list(string.digits)
    ... }

    We have seen this example before; this time, the PEG parser will not return a
    valid result:

    >>> parse_peg("x := 0 ; y := x", grammar).failure()
    SyntaxError("at ' ; y := x'")

    The PEG parser raises a :class:`RecursionError` in certain cases (the Earley
    parser would raise a :class:`SyntaxError` in this example):

    >>> grammar: Grammar = {
    ...     "<start>": ["<a>"],
    ...     "<a>": ["<a>"]
    ... }

    >>> type(parse_peg("a", grammar).failure()).__name__
    'RecursionError'

    :param inp: The input to parse.
    :param grammar: The grammar to parse the input in.
    :param start_nonterminal: The start nonterminal.
    :return: A derivation tree in the case of success or an Exception (most likely a
        SyntaxError) in the case of failure when parsing the given input with a PEG
        parser.
    """

    if start_nonterminal != "<start>":
        grammar = grammar | {"<start>": [start_nonterminal]}
        grammar = delete_unreachable(grammar)

    # Should we address ambiguities and return multiple parse trees?
    result = DerivationTree.from_parse_tree(PEGParser(grammar).parse(inp)[0])
    return result if start_nonterminal == "<start>" else result.children[0]


@safe
def parse_earley(
    inp: str,
    grammar: Grammar,
    start_nonterminal: str = "<start>",
) -> Result[DerivationTree, SyntaxError]:
    """
    This function parses :code:`inp` in the given grammar with the specified start
    nonterminal using an EarleyParser.

    *Attention:* If the Earley parser returns multiple parse trees, we select and return
    only the first one. Ambiguities are not considered!

    See also :func:`~isla.language.parse_match_expression`.

    Example
    -------

    Consider the following grammar for the assignment language.

    >>> import string
    >>> grammar: Grammar = {
    ...     "<start>":
    ...         ["<stmt>"],
    ...     "<stmt>":
    ...         ["<assgn> ; <stmt>", "<assgn>"],
    ...     "<assgn>":
    ...         ["<var> := <rhs>"],
    ...     "<rhs>":
    ...         ["<var>", "<digit>"],
    ...     "<var>": list(string.ascii_lowercase),
    ...     "<digit>": list(string.digits)
    ... }

    We parse a statement with two assignments; the resulting tree starts with the
    specified nonterminal :code:`<start>`:

    >>> deep_str(parse_earley("x := 0 ; y := x", grammar).map(lambda t: (t, t.value)))
    '<Success: (x := 0 ; y := x, <start>)>'

    >>> deep_str(parse_earley("x := 0 ; y := x", grammar).map(lambda t: (t, t.value)))
    '<Success: (x := 0 ; y := x, <start>)>'

    Now, we parse a single assignment with the :code:`<assgn>` start nonterminal:

    >>> deep_str(parse_earley("x := 0", grammar, "<assgn>").map(lambda t: (t, t.value)))
    '<Success: (x := 0, <assgn>)>'

    In case of an error, a Failure is returned:

    >>> print(deep_str(parse_earley("x := 0 FOO", grammar, "<assgn>").alt(
    ...     lambda e: f'"{type(e).__name__}: {e}"')))
    <Failure: "SyntaxError: at ' FOO'">

    The grammar above was a grammar that could be interpreted as a PEG grammar. Parsing
    a statement with the grammar below (changed order of the expansions for statements)
    can, in general, only be parsed with the EarleyParser:

    Unlike the PEG parser (:func:`~isla.solver2.parse_peg`), this function can deal
    with the modified grammar where the order of the alternatives for statements is
    changed:

    >>> grammar: Grammar = {
    ...     "<start>":
    ...         ["<stmt>"],
    ...     "<stmt>":
    ...         ["<assgn>", "<assgn> ; <stmt>"],
    ...     "<assgn>":
    ...         ["<var> := <rhs>"],
    ...     "<rhs>":
    ...         ["<var>", "<digit>"],
    ...     "<var>": list(string.ascii_lowercase),
    ...     "<digit>": list(string.digits)
    ... }

    We get a Success result:

    >>> deep_str(parse_earley("x := 0 ; y := x", grammar).map(lambda t: (t, t.value)))
    '<Success: (x := 0 ; y := x, <start>)>'

    :param inp: The input to parse.
    :param grammar: The grammar to parse the input in.
    :param start_nonterminal: The start nonterminal.
    :return: A derivation tree in the case of success or an Exception (most likely a
        SyntaxError) in the case of failure when parsing the given input with an Earley
        parser.
    """

    if start_nonterminal != "<start>":
        grammar = grammar | {"<start>": [start_nonterminal]}
        grammar = delete_unreachable(grammar)

    # Should we address ambiguities and return multiple parse trees?
    result = DerivationTree.from_parse_tree(next(EarleyParser(grammar).parse(inp)))
    return result if start_nonterminal == "<start>" else result.children[0]


def parse(
    inp: str,
    grammar: Grammar,
    start_nonterminal: str = "<start>",
) -> Result[DerivationTree, SyntaxError]:
    """
    This function parses :code:`inp` in the given grammar with the specified start
    nonterminal. It first tries whether the input can be parsed with a PEG parser;
    if this fails, it falls back to an Earley parser.

    *Attention:* If the Earley parser returns multiple parse trees, we select and return
    only the first one. Ambiguities are not considered!

    Example
    -------

    Consider the following grammar for the assignment language.

    >>> import string
    >>> grammar: Grammar = {
    ...     "<start>":
    ...         ["<stmt>"],
    ...     "<stmt>":
    ...         ["<assgn> ; <stmt>", "<assgn>"],
    ...     "<assgn>":
    ...         ["<var> := <rhs>"],
    ...     "<rhs>":
    ...         ["<var>", "<digit>"],
    ...     "<var>": list(string.ascii_lowercase),
    ...     "<digit>": list(string.digits)
    ... }

    We parse a statement with two assignments; the resulting tree starts with the
    specified nonterminal :code:`<start>`:

    >>> deep_str(parse("x := 0 ; y := x", grammar).map(lambda t: (t, t.value)))
    '<Success: (x := 0 ; y := x, <start>)>'

    Now, we parse a single assignment with the :code:`<assgn>` start nonterminal:

    >>> deep_str(parse("x := 0", grammar, "<assgn>").map(lambda t: (t, t.value)))
    '<Success: (x := 0, <assgn>)>'

    In case of an error, a Failure is returned:

    >>> print(deep_str(parse("x := 0 FOO", grammar, "<assgn>").alt(
    ...     lambda e: f'"{type(e).__name__}: {e}"')))
    <Failure: "SyntaxError: at ' FOO'">

    :param inp: The input to parse.
    :param start_nonterminal: The start nonterminmal.
    :param grammar: The grammar to parse the input in.
    :return: A parsed derivation tree or a Nothing nonterminal if parsing was
        unsuccessful.
    """

    return flow(
        parse_peg(inp, grammar, start_nonterminal),
        tap(
            lambda _: LOGGER.debug(
                "Parsing expression %s with EarleyParser",
                inp,
            )
        ),
        lash(lambda _: parse_earley(inp, grammar, start_nonterminal)),
    )


def create_fixed_length_tree(
    start: DerivationTree | str,
    canonical_grammar: FrozenCanonicalGrammar,
    target_length: int,
) -> Maybe[DerivationTree]:
    """
    This function attempts to create a derivation tree starting in the specified start
    nonterminal symbol or based on the specified initial derivation tree whose
    unparsed form (string representation) has the specifeid target length.

    Example
    -------

    Consider the assignment langugage grammar.

    >>> import string
    >>> grammar: FrozenCanonicalGrammar = frozendict({
    ...     "<start>":
    ...         (("<stmt>",),),
    ...     "<stmt>":
    ...         (("<assgn>", " ; ", "<stmt>"), ("<assgn>",)),
    ...     "<assgn>":
    ...         (("<var>", " := ", "<rhs>"),),
    ...     "<rhs>":
    ...         (("<var>",), ("<digit>",)),
    ...     "<var>": tuple([(c,) for c in string.ascii_lowercase]),
    ...     "<digit>": tuple([(c,) for c in string.digits]),
    ... })

    All assignment language expressions of length 15 consist of two assignments.

    >>> result = create_fixed_length_tree("<stmt>", grammar, 15)
    >>> result.map(lambda t: len(str(t)))
    <Some: 15>

    >>> result.map(lambda t: len(t.filter(lambda n: n.value == "<assgn>")))
    <Some: 2>

    There exists no assignment language expression of length 14.

    >>> create_fixed_length_tree("<stmt>", grammar, 14)
    <Nothing>

    :param start: The start nonterminal or initial tree for the expression that should
        be generated.
    :param canonical_grammar: The grammar for the expression that should be generated,
        in canonical form.
    :param target_length: The target length of the expression that should be generated.
    :return: An expression of the specified length or :code:`None` if no such expression
        could be found.
    """

    nullable = compute_nullable_nonterminals(canonical_grammar)
    start = DerivationTree(start) if isinstance(start, str) else start
    stack: List[
        Tuple[DerivationTree, int, ImmutableList[Tuple[Path, DerivationTree]]]
    ] = [
        (start, int(start.value not in nullable), (((), start),)),
    ]

    while stack:
        tree, curr_len, open_leaves = stack.pop()

        if not open_leaves:
            if curr_len == target_length:
                return Maybe.from_value(tree)
            else:
                continue

        if curr_len > target_length:
            continue

        idx: int
        leaf: DerivationTree
        for idx, (_, leaf) in reversed(list(enumerate(open_leaves))):
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

            stack.extend(
                [
                    expand_leaf(
                        tree,
                        curr_len,
                        open_leaves,
                        idx,
                        expansion,
                        nullable,
                    )
                    for expansion in reversed(expansions)
                ]
            )

    return Nothing


def expand_leaf(
    tree: DerivationTree,
    min_unparsed_tree_len: int,
    open_leaves: ImmutableList[Tuple[Path, DerivationTree]],
    leaf_idx: int,
    expansion: ImmutableList[str],
    nullable_nonterminals: Set[str],
) -> Tuple[DerivationTree, int, ImmutableList[Tuple[Path, DerivationTree]]]:
    """
    This function expands a leaf in :code:`tree` according to the grammar expansion
    in :code:`expansion` and returns (1) the expanded tree, (2) a lower bound on the
    length of the resulting unparsed tree, and (3) a list of open leaves in the
    resulting tree. The leaf to expand is specified by its index :code:`leaf_idx`
    in the list :code:`open_leaves` of open leaves in :code:`tree`.

    >>> tree = DerivationTree("<stmt>", (DerivationTree("<assgn>"),))
    >>> min_unparsed_tree_len = 1
    >>> open_leaves = (((0,), tree.get_subtree((0,))),)
    >>> leaf_idx = 0
    >>> expansion = ('<var>', ' := ', '<rhs>')
    >>> nullable_nonterminals = set()

    >>> print(
    ...     deep_str(
    ...         expand_leaf(
    ...             tree,
    ...             min_unparsed_tree_len,
    ...             open_leaves,
    ...             leaf_idx,
    ...             expansion,
    ...             nullable_nonterminals,
    ...         )
    ...     )
    ... )
    (<var> := <rhs>, 6, (((0, 0), <var>), ((0, 2), <rhs>)))

    :param tree: The derivation tree in which we should expand an open leaf.
    :param min_unparsed_tree_len: The minimal length of the unparsed input tree.
    :param open_leaves: The open leaves in the input tree.
    :param leaf_idx: The index of the leaf to expand in :code:`open_leaves`.
    :param expansion: The expansion alternative to apply.
    :param nullable_nonterminals: A set of nullable nonterminals in the reference
        grammar.
    :return: A triple of (1) the expanded tree, (2) a lower bound on the length of
        the unparsed tree, which will be precise for closed trees, and (3) the list
        of open leaves in the new tree.
    """

    leaf = open_leaves[leaf_idx][1]
    path_to_leaf = open_leaves[leaf_idx][0]

    new_children = tuple(
        [
            DerivationTree(elem, None if is_nonterminal(elem) else ())
            for elem in expansion
        ]
    )

    expanded_tree = tree.replace_path(
        path_to_leaf,
        DerivationTree(
            leaf.value,
            new_children,
        ),
    )

    next_candidate_len = (
        min_unparsed_tree_len
        + sum(
            [
                len(child.value)
                if child.children == ()
                else (1 if child.value not in nullable_nonterminals else 0)
                for child in new_children
            ]
        )
        - int(leaf.value not in nullable_nonterminals)
    )

    next_candidate_open_leaves = (
        open_leaves[:leaf_idx]
        + tuple(
            [
                (path_to_leaf + (child_idx,), new_child)
                for child_idx, new_child in enumerate(new_children)
                if is_nonterminal(new_child.value)
            ]
        )
        + open_leaves[leaf_idx + 1 :]
    )

    return (
        expanded_tree,
        next_candidate_len,
        next_candidate_open_leaves,
    )