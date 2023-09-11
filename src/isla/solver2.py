import logging
import random
import sys
from abc import ABC, abstractmethod
from dataclasses import dataclass
from functools import reduce, lru_cache, partial
from typing import Tuple, List, Set, Dict, Iterable, Callable, cast, AbstractSet

import z3
from frozendict import frozendict
from grammar_to_regex.cfg2regex import RegexConverter
from grammar_to_regex.regex import regex_to_z3
from neo_grammar_graph import NeoGrammarGraph
from orderedset import FrozenOrderedSet
from returns.functions import tap
from returns.maybe import Maybe, Nothing, Some
from returns.pipeline import flow
from returns.pointfree import lash
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
)
from isla.language import (
    ConjunctiveFormula,
    DisjunctiveFormula,
    Variable,
    SMTFormula,
    BoundVariable,
    fresh_constant,
    Constant,
)
from isla.language import Formula
from isla.parser import EarleyParser, PEGParser
from isla.type_defs import FrozenCanonicalGrammar, Path, ImmutableList, Grammar
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


@dataclass(frozen=True)
class CDT:
    """
    A Conditioned Derivation Tree (CDT) is a derivation tree that is subject to
    constraints. Semantically, a CDT represents a set of derivation trees. This
    set is empty if the constraint set is unsatisfiable, and represents all
    concrete trees that can be derived from the (possibly open) derivation tree
    satisfying the constraints.
    """

    constraints: FrozenOrderedSet[Formula]
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
        ...     CDT(FrozenOrderedSet([true()]), DerivationTree("<tree_2>")), (0, 0)
        ... )
        >>> tree_3 = StateTree(
        ...     CDT(FrozenOrderedSet([true()]), DerivationTree("<tree_3>")), (0, 1)
        ... )
        >>> tree_0 = StateTree(
        ...     CDT(FrozenOrderedSet([true()]), DerivationTree("<tree_0>")),
        ...     (0,),
        ...     ((dummy_action, tree_2), (dummy_action, tree_3),),
        ... )
        >>> tree_1 = StateTree(CDT(FrozenOrderedSet([true()]), DerivationTree("<tree_1>")), (1,))
        >>> stree = StateTree(
        ...     CDT(FrozenOrderedSet([true()]), DerivationTree("<root>")),
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
        ...     CDT(FrozenOrderedSet([true()]), DerivationTree("<X>")), (0, 1)
        ... )
        >>> print(stree.replace((0, 1), tree_X))
        StateTree(({True} ▸ <root>), [(Expand((), 0), StateTree(({True} ▸ <tree_0>), [(Expand((), 0), StateTree(({True} ▸ <tree_2>))), (Expand((), 0), StateTree(({True} ▸ <X>)))])), (Expand((), 0), StateTree(({True} ▸ <tree_1>)))])

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
        ...     CDT(FrozenOrderedSet([true()]), DerivationTree("<tree_2>")), (0, 0)
        ... )
        >>> tree_0 = StateTree(
        ...     CDT(FrozenOrderedSet([true()]), DerivationTree("<tree_0>")),
        ...     (0,),
        ...     ((dummy_action, tree_2),),
        ... )
        >>> stree = StateTree(
        ...     CDT(FrozenOrderedSet([true()]), DerivationTree("<root>")),
        ...     (),
        ...     ((dummy_action, tree_0),),
        ... )

        This is the original tree:

        >>> print(stree)
        StateTree(({True} ▸ <root>), [(Expand((), 0), StateTree(({True} ▸ <tree_0>), [(Expand((), 0), StateTree(({True} ▸ <tree_2>)))]))])

        And here is the updated one:

        >>> new_cdt = CDT(FrozenOrderedSet([true()]), DerivationTree("<tree_1>"))
        >>> print(stree.add_child(dummy_action, new_cdt))
        StateTree(({True} ▸ <root>), [(Expand((), 0), StateTree(({True} ▸ <tree_0>), [(Expand((), 0), StateTree(({True} ▸ <tree_2>)))])), (Expand((), 0), StateTree(({True} ▸ <tree_1>)))])

        Now, we add tree 1 to the inner node tree 0, resulting in::

            <root>
            └─ <tree_0>
               ├─ <tree_2>
               └─ <tree_1>

        >>> print(stree.add_child(dummy_action, new_cdt, (0,)))
        StateTree(({True} ▸ <root>), [(Expand((), 0), StateTree(({True} ▸ <tree_0>), [(Expand((), 0), StateTree(({True} ▸ <tree_2>))), (Expand((), 0), StateTree(({True} ▸ <tree_1>)))]))])

        :param action: The action leading to the new child.
        :param node: The CDT to add.
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
        ...     CDT(FrozenOrderedSet([true()]), DerivationTree("<tree_2>")), (0, 0)
        ... )
        >>> tree_0 = StateTree(
        ...     CDT(FrozenOrderedSet([true()]), DerivationTree("<tree_0>")),
        ...     (0,),
        ...     ((dummy_action, tree_2),),
        ... )
        >>> tree_1 = StateTree(
        ...     CDT(FrozenOrderedSet([true()]), DerivationTree("<tree_1>")), (1,))
        >>> stree = StateTree(
        ...     CDT(FrozenOrderedSet([true()]), DerivationTree("<root>")),
        ...     (),
        ...     ((dummy_action, tree_0), (dummy_action, tree_1)),
        ... )

        At the empty path, there is the tree (the root) itself:

        >>> stree.get_subtree(()) == stree
        True

        The first child is tree 0:

        >>> print(stree.get_subtree((0,)))
        StateTree(({True} ▸ <tree_0>), [(Expand((), 0), StateTree(({True} ▸ <tree_2>)))])

        The first child of tree 0 is tree 2:

        >>> print(stree.get_subtree((0, 0)))
        StateTree(({True} ▸ <tree_2>))

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
        ...     CDT(FrozenOrderedSet([true()]), DerivationTree("<tree_2>")), (0, 0)
        ... )
        >>> tree_0 = StateTree(
        ...     CDT(FrozenOrderedSet([true()]), DerivationTree("<tree_0>")),
        ...     (0,),
        ...     ((dummy_action, tree_2),),
        ... )
        >>> tree_1 = StateTree(CDT(FrozenOrderedSet([true()]), DerivationTree("<tree_1>")), (1,))
        >>> stree = StateTree(
        ...     CDT(FrozenOrderedSet([true()]), DerivationTree("<root>")),
        ...     (),
        ...     ((dummy_action, tree_0), (dummy_action, tree_1)),
        ... )

        The :code:`tree_2` is a leaf:

        >>> print(tree_2)
        StateTree(({True} ▸ <tree_2>))

        Its parent is :code:`tree_0`:

        >>> print(tree_2.parent(stree))
        StateTree(({True} ▸ <tree_0>), [(Expand((), 0), StateTree(({True} ▸ <tree_2>)))])

        The parent of :code:`tree_0`, in turn, is :code:`root`:

        >>> print(tree_2.parent(stree).parent(stree))
        StateTree(({True} ▸ <root>), [(Expand((), 0), StateTree(({True} ▸ <tree_0>), [(Expand((), 0), StateTree(({True} ▸ <tree_2>)))])), (Expand((), 0), StateTree(({True} ▸ <tree_1>)))])

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
    grammar: FrozenCanonicalGrammar

    def action(self, state_tree: StateTree) -> Maybe[ExpandRuleAction]:
        """
        This method computes an expansion action if it is applicable. It avoids
        previously taken actions from :code:`state_tree` and takes coverage into
        account. TODO: Implement this (see inline code comments).

        Consider the following grammar for our assignment language:

        >>> from frozendict import frozendict
        >>> import string
        >>> from isla.language import true

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

        We create a derivation tree that permits exactly two expansions and a trivial
        state tree.

        >>> dtree = DerivationTree("<start>", (DerivationTree("<stmt>"),))
        >>> stree = StateTree(CDT(FrozenOrderedSet([true()]), dtree))
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
                tuple(enumerate(self.grammar[leaf.value])),
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
        >>> dtree = DerivationTree("<start>", (DerivationTree("<stmt>"),))
        >>> stree = StateTree(CDT(FrozenOrderedSet([true()]), dtree))

        We expand the open leaf first with the first expansion rule:

        >>> rule = ExpandRule(grammar)

        >>> action = ExpandRuleAction((0,), 0)
        >>> print(rule.apply(stree, action))
        StateTree(({True} ▸ <stmt>), [(Expand((0,), 0), StateTree(({True} ▸ <assgn> ; <stmt>)))])

        Now, we choose the second expansion rule:

        >>> action = ExpandRuleAction((0,), 1)
        >>> print(rule.apply(stree, action))
        StateTree(({True} ▸ <stmt>), [(Expand((0,), 1), StateTree(({True} ▸ <assgn>)))])

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
                for symbol in self.grammar[node.tree.get_subtree(action.path).value][
                    action.alternative
                ]
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
        ...     CDT(FrozenOrderedSet([conjunction]), DerivationTree("<start>"))
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
        ...     CDT(FrozenOrderedSet([conjunction]), DerivationTree("<start>"))
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
        ...     CDT(FrozenOrderedSet([disjunction]), DerivationTree("<start>"))
        ... )
        >>> str(ChooseOrRule().action(stree)) in [
        ...     '<Some: ChooseOr((StrToInt(x) > 0 ∨ StrToInt(x) < 9), 0)>',
        ...     '<Some: ChooseOr((StrToInt(x) > 0 ∨ StrToInt(x) < 9), 1)>'
        ... ]
        True

        >>> ChooseOrRule().action(
        ...     StateTree(CDT(FrozenOrderedSet({}), DerivationTree("<start>"))))
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
        ...     CDT(FrozenOrderedSet([disjunction]), DerivationTree("<start>"))
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
    result: bool | frozendict[Variable | DerivationTree, DerivationTree]

    def __str__(self):
        return f"SolveSMT({deep_str(self.result)})"


@dataclass(frozen=True)
class SolveSMTRule(Rule):
    def action(self, state_tree: StateTree) -> Maybe[Action]:
        """
        TODO

        :param state_tree:
        :return:
        """

        semantic_formulas = [
            conjunct
            for conjunct in state_tree.node.constraints
            if isinstance(conjunct, SMTFormula)
        ]

        # other_formulas = [
        #     conjunct
        #     for conjunct in state_tree.node.constraints
        #     if not isinstance(conjunct, SMTFormula)
        # ]

        if not semantic_formulas:
            return Maybe.nothing()

        LOGGER.debug(
            "Eliminating semantic formulas [%s]", lazyjoin(", ", semantic_formulas)
        )

        raise NotImplementedError

    def apply(self, state_tree: StateTree, action: Action) -> StateTree:
        """
        TODO

        :param state_tree:
        :param action:
        :return:
        """

        raise NotImplementedError


def solve_smt_formulas_with_language_constraints(
    graph: NeoGrammarGraph,
    smt_formulas: Iterable[z3.BoolRef],
    variables: AbstractSet[Variable],
    tree_substitutions: Maybe[Dict[Variable, DerivationTree]] = Maybe.empty,
    solutions_to_exclude: Maybe[List[Dict[Variable, z3.StringVal]]] = Maybe.empty,
    enable_optimized_z3_queries: bool = True,
) -> Result[Tuple[z3.CheckSatResult, Dict[Variable, DerivationTree]], SyntaxError]:
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
    
    >>> sat_res
    sat
    
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
    ...     graph, constraints, FrozenOrderedSet([x, y, z]), Some(tree_substitutions)))
    <Success: (sat, {x: a := 7, y: a := 7})>

    If a solution returned by the SMT solver does not fit to the grammar, a
    :class:`~returns.result.Failure` object is returned. If we ask for the integer
    representation of an :code:`<assgn>` variable to equal 3, for example, the solver
    returns "3" as requested; however, this cannot be parsed into an :code:`<assgn>`:

    >>> solve_smt_formulas_with_language_constraints(
    ...     graph,
    ...     smt_formulas=[z3_eq(z3.StrToInt(x.to_smt()), z3.IntVal(3))],
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
    :return: A :class:`~returns.result.Success` containing a tuple indicating the status
        returned from the SMT solver and a (possibly empty) map of solution assignments.
        If the solution returned by the solver is not part of the grammar (this mainly
        happens if :code:`enable_optimized_z3_queries` is True), a
        :class:`~returns.result.Failure` with a :class:`SyntaxError` is returned.
    """  # noqa: E501

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
    for int_var in int_vars:
        if int_var.n_type == Variable.NUMERIC_NTYPE:
            # "NUM" variables range over the full int domain
            continue

        regex = extract_regular_expression(graph, int_var.n_type)
        maybe_intervals = numeric_intervals_from_regex(regex)
        repl_var = replacement_map[z3.StrToInt(int_var.to_smt())]
        formulas.extend(
            maybe_intervals.map(
                lambda intervals: [
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
            ).value_or([])
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
        return Success((sat_result, {}))

    assert maybe_model is not None

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
        Success((sat_result, {})),
    )


def rename_instantiated_variables_in_smt_formulas(
    smt_formulas: List[SMTFormula],
) -> List[SMTFormula]:
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
    [(<A>_0 == <A>_0, {'<A>_0': '<A>'}), (<A>_1 == <A>_0, {'<A>_1': '<A>', '<A>_0': '<A>'})]

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

    return result


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
    <Success: (x := 0 ; y := x, <start>)>

    >>> deep_str(parse_peg("x := 0 ; y := x", grammar).map(lambda t: (t, t.value)))
    <Success: (x := 0 ; y := x, <start>)>

    Now, we parse a single assignment with the :code:`<assgn>` start nonterminal:

    >>> deep_str(parse_peg("x := 0", grammar, "<assgn>").map(lambda t: (t, t.value)))
    <Success: (x := 0, <assgn>)>

    In case of an error, a Failure is returned:

    >>> deep_str(parse_peg("x := 0 FOO", grammar, "<assgn>").alt(
    ...     lambda e: f'"{type(e).__name__}: {e}"'))
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
    <Success: (x := 0 ; y := x, <start>)>

    >>> deep_str(parse_earley("x := 0 ; y := x", grammar).map(lambda t: (t, t.value)))
    <Success: (x := 0 ; y := x, <start>)>

    Now, we parse a single assignment with the :code:`<assgn>` start nonterminal:

    >>> deep_str(parse_earley("x := 0", grammar, "<assgn>").map(lambda t: (t, t.value)))
    <Success: (x := 0, <assgn>)>

    In case of an error, a Failure is returned:

    >>> deep_str(parse_earley("x := 0 FOO", grammar, "<assgn>").alt(
    ...     lambda e: f'"{type(e).__name__}: {e}"'))
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
    <Success: (x := 0 ; y := x, <start>)>

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
    <Success: (x := 0 ; y := x, <start>)>

    Now, we parse a single assignment with the :code:`<assgn>` start nonterminal:

    >>> deep_str(parse("x := 0", grammar, "<assgn>").map(lambda t: (t, t.value)))
    <Success: (x := 0, <assgn>)>

    In case of an error, a Failure is returned:

    >>> deep_str(parse("x := 0 FOO", grammar, "<assgn>").alt(
    ...     lambda e: f'"{type(e).__name__}: {e}"'))
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
