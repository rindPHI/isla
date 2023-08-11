import random
import string
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Tuple

from frozendict import frozendict
from orderedset import FrozenOrderedSet
from isla.language import true, ConjunctiveFormula, SMTFormula, Constant, \
    DisjunctiveFormula
from isla.derivation_tree import DerivationTree
from isla.helpers import Maybe, is_nonterminal, deep_str
from isla.language import Formula
from isla.type_defs import FrozenCanonicalGrammar, Path


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
        """

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
        """

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
        """

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

        >>> grammar: FrozenCanonicalGrammar = frozendict({
        ...     "<start>":
        ...         ("<stmt>",),
        ...     "<stmt>":
        ...         ("<assgn> ; <stmt>", "<assgn>"),
        ...     "<assgn>":
        ...         ("<var> := <rhs>",),
        ...     "<rhs>":
        ...         ("<var>", "<digit>",),
        ...     "<var>": tuple(string.ascii_lowercase),
        ...     "<digit>": tuple(string.digits)
        ... })

        We create a derivation tree that permits exactly two expansions and a trivial
        state tree.

        >>> dtree = DerivationTree("<start>", (DerivationTree("<stmt>"),))
        >>> stree = StateTree(CDT(FrozenOrderedSet([true()]), dtree))
        >>> rule = ExpandRule(grammar)
        >>> action = rule.action(stree)

        An action is returned for the open leaf, choosing either the first or the
        second expansion alternative for "<stmt>".

        >>> action.is_present()
        True
        >>> action.map(lambda a: a.path)
        Maybe(a=(0,))
        >>> action.map(lambda a: a.alternative).map(lambda alt: alt in {0, 1})
        Maybe(a=True)

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
            tuple(enumerate(self.grammar[leaf.value]))
        )

        return Maybe(ExpandRuleAction(path, alternative_id))

    def apply(self, state_tree: StateTree, action: ExpandRuleAction) -> StateTree:
        """
        This method applies a previously chosen :class:`~isla.solver2.ExpandRuleAction`
        to the given state tree.

        Example
        -------

        Consider the assignment language grammar:

        >>> grammar: FrozenCanonicalGrammar = frozendict({
        ...     "<start>":
        ...         ("<stmt>",),
        ...     "<stmt>":
        ...         ("<assgn> ; <stmt>", "<assgn>"),
        ...     "<assgn>":
        ...         ("<var> := <rhs>",),
        ...     "<rhs>":
        ...         ("<var>", "<digit>",),
        ...     "<var>": tuple(string.ascii_lowercase),
        ...     "<digit>": tuple(string.digits)
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

        >>> conjunction = (
        ...     SMTFormula("(> (str.to_int x) 0)", Constant("x", "<X>"))
        ...     & SMTFormula("(< (str.to_int x) 9)", Constant("x", "<X>"))
        ... )
        >>> stree = StateTree(
        ...     CDT(FrozenOrderedSet([conjunction]), DerivationTree("<start>"))
        ... )
        >>> print(SplitAndRule().action(stree))
        Maybe(SplitAnd((StrToInt(x) > 0 ∧ StrToInt(x) < 9)))

        :param state_tree: The input state tree.
        :return: An action if a conjunction is contained in the state tree or nothing.
        """

        constraints = state_tree.node.constraints
        return Maybe.from_iterator(
            (c for c in constraints if isinstance(c, ConjunctiveFormula))
        ).map(lambda c: SplitAndAction(c))

    def apply(self, state_tree: StateTree, action: SplitAndAction) -> StateTree:
        """
        This method applies a :class:`~isla.solver2.SplitAndAction`.

        Example
        -------

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
        """

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

        >>> disjunction = (
        ...     SMTFormula("(> (str.to_int x) 0)", Constant("x", "<X>"))
        ...     | SMTFormula("(< (str.to_int x) 9)", Constant("x", "<X>"))
        ... )
        >>> stree = StateTree(
        ...     CDT(FrozenOrderedSet([disjunction]), DerivationTree("<start>"))
        ... )
        >>> str(ChooseOrRule().action(stree)) in [
        ...     "Maybe(ChooseOr((StrToInt(x) > 0 ∨ StrToInt(x) < 9), 0))",
        ...     "Maybe(ChooseOr((StrToInt(x) > 0 ∨ StrToInt(x) < 9), 1))"
        ... ]
        True

        :param state_tree: The input state tree.
        :return: An action if a disjunction is contained in the state tree or nothing.
        """

        # TODO 1: If there is a sibling present, we should choose a different disjunct.
        # TODO 2: We will have to consider semantic coverage information (choose the
        #         disjunct whose origin formula has not been chosen for evaluation
        #         so far).

        constraints = state_tree.node.constraints
        return Maybe.from_iterator(
            (c for c in constraints if isinstance(c, DisjunctiveFormula))
        ).map(lambda c: ChooseOrAction(c, random.choice([0, 1])))

    def apply(self, state_tree: StateTree, action: ChooseOrAction) -> StateTree:
        """
        This method applies a :class:`~isla.solver2.ChooseOrAction`.
        Other than :class:`~isla.solver2.SplitAnd`, only (a random) one disjunct is
        retained in the result.

        Example
        -------

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
        """

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
