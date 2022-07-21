import html
from functools import lru_cache
from typing import Optional, Sequence, Dict, Set, Tuple, List, Callable, Union, Generator

import datrie
from grammar_graph import gg
from graphviz import Digraph

from isla.helpers import is_nonterminal, mk_subtree_trie, path_to_trie_key, traverse, TRAVERSE_POSTORDER
from isla.type_defs import Path, Grammar, ParseTree


class DerivationTree:
    """Derivation trees are immutable!"""
    next_id: int = 0

    TRAVERSE_PREORDER = 0
    TRAVERSE_POSTORDER = 1

    def __init__(self, value: str,
                 children: Optional[Sequence['DerivationTree']] = None,
                 id: Optional[int] = None,
                 k_paths: Optional[Dict[int, Set[Tuple[gg.Node, ...]]]] = None,
                 hash: Optional[int] = None,
                 structural_hash: Optional[int] = None,
                 is_open: Optional[bool] = None):
        self.__value = value
        self.__children = None if children is None else tuple(children)

        if id:
            self._id = id
        else:
            self._id = DerivationTree.next_id
            DerivationTree.next_id += 1

        self.__len = 1 if not children else None
        self.__hash = hash
        self.__structural_hash = structural_hash
        self.__k_paths: Dict[int, Set[Tuple[gg.Node, ...]]] = k_paths or {}

        self.__is_open = is_open
        if children is None:
            self.__is_open = True

    def __setstate__(self, state):
        # To ensure that when resuming from a checkpoint during debugging,
        # ID uniqueness constraints are maintained.
        self.__dict__.update(state)
        if self.id >= DerivationTree.next_id:
            DerivationTree.next_id = self.id + 1

    @property
    def children(self) -> Tuple['DerivationTree']:
        return self.__children

    @property
    def value(self) -> str:
        return self.__value

    @property
    def id(self) -> int:
        return self._id

    @id.setter
    def id(self, value: int):
        raise NotImplementedError()

    def has_unique_ids(self) -> bool:
        return all(
            not any(
                subt_1 is not subt_2 and subt_1.id == subt_2.id
                for _, subt_2 in self.paths())
            for _, subt_1 in self.paths())

    def k_coverage(self, graph: gg.GrammarGraph, k: int) -> float:
        return len(self.k_paths(graph, k)) / len(graph.k_paths(k))

    def k_paths(self, graph: gg.GrammarGraph, k: int) -> Set[Tuple[gg.Node, ...]]:
        if k not in self.__k_paths:
            self.recompute_k_paths(graph, k)
            assert k in self.__k_paths

        return self.__k_paths[k]

    def recompute_k_paths(self, graph: gg.GrammarGraph, k: int) -> Set[Tuple[gg.Node, ...]]:
        self.__k_paths[k] = set(iter(graph.k_paths_in_tree(self.to_parse_tree(), k)))
        return self.__k_paths[k]

    def root_nonterminal(self) -> str:
        assert is_nonterminal(self.value)
        return self.value

    def num_children(self) -> int:
        return 0 if self.children is None else len(self.children)

    def is_open(self):
        if self.__is_open is None:
            self.__is_open = self.__compute_is_open()

        return self.__is_open

    def __compute_is_open(self):
        if self.children is None:
            return True

        result = False

        def action(_, node: DerivationTree) -> bool:
            nonlocal result
            if node.children is None:
                result = True
                return True

            return False

        self.traverse(lambda p, n: None, action)

        return result

    def is_complete(self):
        return not self.is_open()

    @lru_cache(maxsize=20)
    def get_subtree(self, path: Path) -> 'DerivationTree':
        """Access a subtree based on `path` (a list of children numbers)"""
        curr_node = self
        while path:
            curr_node = curr_node.children[path[0]]
            path = path[1:]

        return curr_node

    def is_valid_path(self, path: Path) -> bool:
        curr_node = self
        while path:
            if not curr_node.children or len(curr_node.children) <= path[0]:
                return False

            curr_node = curr_node.children[path[0]]
            path = path[1:]

        return True

    @lru_cache
    def paths(self) -> List[Tuple[Path, 'DerivationTree']]:
        def action(path, node):
            result.append((path, node))

        result: List[Tuple[Path, 'DerivationTree']] = []
        self.traverse(action, kind=DerivationTree.TRAVERSE_PREORDER)
        return result

    @lru_cache
    def trie(self) -> datrie.Trie:
        """Mapping from Paths (encoded as unicode Strings) to pairs of a path
        and a corresponding subtree, in efficient Trie structure. The path
        in the value is the unencoded version of the path in the key; this
        saves some time for decoding the path. Use `helpers.path_to_trie_key`
        and `helpers.trie_key_to_path` for de/encoding paths for trie usage.
        Can be used like a dictionary. Keys (paths) are ordered according
        to a pre-order traversal."""
        trie = mk_subtree_trie()  # Works for up to 30 children of a node
        for path, subtree in self.paths():
            trie[path_to_trie_key(path)] = (path, subtree)
        return trie

    def filter(self, f: Callable[['DerivationTree'], bool],
               enforce_unique: bool = False) -> List[Tuple[Path, 'DerivationTree']]:
        result: List[Tuple[Path, 'DerivationTree']] = []

        for path, subtree in self.paths():
            if f(subtree):
                result.append((path, subtree))

                if enforce_unique and len(result) > 1:
                    raise RuntimeError(f"Found searched-for element more than once in {self}")

        return result

    def find_node(self, node_or_id: Union['DerivationTree', int]) -> Optional[Path]:
        """Finds a node by its (assumed unique) ID. Returns the path relative to this node."""
        if isinstance(node_or_id, DerivationTree):
            node_or_id = node_or_id.id

        try:
            return next(path for path, subtree in self.paths() if subtree.id == node_or_id)
        except StopIteration:
            return None

        stack: List[Tuple[Path, DerivationTree]] = [((), self)]
        while stack:
            path, tree = stack.pop()
            if tree.id == node_or_id:
                return path

            if tree.children:
                stack.extend([(path + (idx,), child) for idx, child in enumerate(tree.children)])

        return None

    def traverse(
            self,
            action: Callable[[Path, 'DerivationTree'], None],
            abort_condition: Callable[[Path, 'DerivationTree'], bool] = lambda p, n: False,
            kind: int = TRAVERSE_PREORDER,
            reverse: bool = False) -> None:
        stack_1: List[Tuple[Path, DerivationTree]] = [((), self)]
        stack_2: List[Tuple[Path, DerivationTree]] = []

        if kind == DerivationTree.TRAVERSE_PREORDER:
            reverse = not reverse

        while stack_1:
            path, node = stack_1.pop()

            if abort_condition(path, node):
                return

            if kind == DerivationTree.TRAVERSE_POSTORDER:
                stack_2.append((path, node))

            if kind == DerivationTree.TRAVERSE_PREORDER:
                action(path, node)

            if node.children:
                iterator = reversed(node.children) if reverse else iter(node.children)

                for idx, child in enumerate(iterator):
                    new_path = path + ((len(node.children) - idx - 1) if reverse else idx,)
                    stack_1.append((new_path, child))

        if kind == DerivationTree.TRAVERSE_POSTORDER:
            while stack_2:
                action(*stack_2.pop())

    def bfs(self,
            action: Callable[[Path, 'DerivationTree'], None],
            abort_condition: Callable[[Path, 'DerivationTree'], bool] = lambda p, n: False):
        queue: List[Tuple[Path, DerivationTree]] = [((), self)]  # FIFO queue
        explored: Set[Path] = {()}

        while queue:
            p, v = queue.pop(0)
            action(p, v)
            if abort_condition(p, v):
                return

            for child_idx, child in enumerate(v.children or []):
                child_path = p + (child_idx,)
                if child_path in explored:
                    continue

                explored.add(child_path)
                queue.append((child_path, child))

    def nonterminals(self) -> Set[str]:
        result: Set[str] = set()

        def add_if_nonterminal(_: Path, tree: DerivationTree):
            if is_nonterminal(tree.value):
                result.add(tree.value)

        self.traverse(action=add_if_nonterminal)

        return result

    def terminals(self) -> List[str]:
        result: List[str] = []

        def add_if_terminal(_: Path, tree: DerivationTree):
            if not is_nonterminal(tree.value):
                result.append(tree.value)

        self.traverse(action=add_if_terminal)

        return result

    def reachable_symbols(self, grammar: Grammar, is_reachable: Callable[[str, str], bool]) -> Set[str]:
        return self.nonterminals() | {
            nonterminal for nonterminal in grammar
            if any(is_reachable(leaf[1].value, nonterminal)
                   for leaf in self.leaves()
                   if is_nonterminal(leaf[1].value))
        }

    def next_path(self, path: Path, skip_children=False) -> Optional[Path]:
        """
        Returns the next path in the tree. Repeated calls result in an iterator over the paths in the tree.
        """

        def num_children(path: Path) -> int:
            _, children = self.get_subtree(path)
            if children is None:
                return 0
            return len(children)

        # Descent towards left-most child leaf
        if not skip_children and num_children(path) > 0:
            return path + (0,)

        # Find next sibling
        for i in range(1, len(path)):
            if path[-i] + 1 < num_children(path[:-i]):
                return path[:-i] + (path[-i] + 1,)

        # Proceed to next root child
        if path and path[0] + 1 < num_children(tuple()):
            return path[0] + 1,

        # path already is the last path.
        assert skip_children or list(self.paths())[-1][0] == path
        return None

    def replace_path(
            self,
            path: Path,
            replacement_tree: 'DerivationTree',
            retain_id=False) -> 'DerivationTree':
        """Returns tree where replacement_tree has been inserted at `path` instead of the original subtree"""
        stack: List[DerivationTree] = [self]
        for idx in path:
            stack.append(stack[-1].children[idx])

        if retain_id:
            replacement_tree = DerivationTree(
                replacement_tree.value,
                replacement_tree.children,
                id=stack[-1].id,
                is_open=replacement_tree.is_open(),
            )

        stack[-1] = replacement_tree

        for idx in reversed(path):
            assert len(stack) > 1
            replacement = stack.pop()
            parent = stack.pop()

            children = parent.children
            new_children = (
                    children[:idx] +
                    (replacement,) +
                    children[idx + 1:])

            if replacement.__is_open is True:
                is_open = True
            elif replacement.__is_open is False and parent.__is_open is False:
                is_open = False
            else:
                is_open = None

            stack.append(DerivationTree(
                parent.value,
                new_children,
                id=parent.id,
                is_open=is_open))

        assert len(stack) == 1
        return stack[0]

    def leaves(self) -> Generator[Tuple[Path, 'DerivationTree'], None, None]:
        return ((path, sub_tree)
                for path, sub_tree in self.paths()
                if not sub_tree.children)

    def open_leaves(self) -> Generator[Tuple[Path, 'DerivationTree'], None, None]:
        return ((path, sub_tree)
                for path, sub_tree in self.paths()
                if sub_tree.children is None)

    def depth(self) -> int:
        if not self.children:
            return 1
        return 1 + max(child.depth() for child in self.children)

    def new_ids(self) -> 'DerivationTree':
        return DerivationTree(
            self.value,
            None if self.children is None
            else [child.new_ids() for child in self.children])

    def __len__(self):
        if self.__len is None:
            self.__len = sum([len(child) for child in (self.children or [])]) + 1

        return self.__len

    def __lt__(self, other):
        return len(self) < len(other)

    def __le__(self, other):
        return len(self) <= len(other)

    def __gt__(self, other):
        return len(self) > len(other)

    def __ge__(self, other):
        return len(self) >= len(other)

    def substitute(self, subst_map: Dict['DerivationTree', 'DerivationTree']) -> 'DerivationTree':
        # We perform an iterative reverse post-order depth-first traversal and use a stack
        # to store intermediate results from lower levels.
        assert self.has_unique_ids()

        # Looking up IDs performs much better for big trees, since we do not necessarily
        # have to compute hashes for all nodes (made necessary by tar case study).
        # We remove "nested" replacements since removing elements in replacements is not intended.

        id_subst_map = {
            tree.id: repl for tree, repl in subst_map.items()
            if (isinstance(tree, DerivationTree) and
                all(repl.id == tree.id or repl.find_node(tree.id) is None
                    for otree, repl in subst_map.items()
                    if isinstance(otree, DerivationTree)))
        }

        result = self
        for tree_id in id_subst_map:
            path = result.find_node(tree_id)
            if path is not None:
                result = result.replace_path(path, id_subst_map[tree_id])

        return result

    def is_prefix(self, other: 'DerivationTree') -> bool:
        if len(self) > len(other):
            return False

        if self.value != other.value:
            return False

        if not self.children:
            return self.children is None or (not other.children and other.children is not None)

        if not other.children:
            return False

        assert self.children
        assert other.children

        if len(self.children) != len(other.children):
            return False

        return all(self.children[idx].is_prefix(other.children[idx])
                   for idx, _ in enumerate(self.children))

    def is_potential_prefix(self, other: 'DerivationTree') -> bool:
        """Returns `True` iff this the `other` tree can be extended such that this tree
        is a prefix of the `other` tree."""
        if self.value != other.value:
            return False

        if not self.children:
            return self.children is None or (not other.children and other.children is not None)

        if not other.children:
            return other.children is None

        assert self.children
        assert other.children

        if len(self.children) != len(other.children):
            return False

        return all(self.children[idx].is_potential_prefix(other.children[idx])
                   for idx, _ in enumerate(self.children))

    @staticmethod
    def from_parse_tree(tree: ParseTree):
        result_stack: List[DerivationTree] = []

        def action(_, tree: ParseTree) -> None:
            node, children = tree
            if not children:
                result_stack.append(DerivationTree(node, children))
                return

            children_results: List[DerivationTree] = []
            for _ in range(len(children)):
                children_results.append(result_stack.pop())

            result_stack.append(DerivationTree(node, children_results))

        traverse(tree, action, kind=TRAVERSE_POSTORDER, reverse=True)

        assert len(result_stack) == 1
        result = result_stack[0]

        return result

    def to_parse_tree(self) -> ParseTree:
        return self.value, None if self.children is None else [child.to_parse_tree() for child in self.children]

    def __iter__(self):
        # Allows tuple unpacking: node, children = tree
        yield self.value
        yield self.children

    def compute_hash_iteratively(self, structural=False):
        # We perform an iterative reverse post-order depth-first traversal and use a stack
        # to store intermediate results from lower levels.

        stack: List[int] = []

        def action(_, node: DerivationTree) -> None:
            if structural and node.__structural_hash is not None:
                for _ in range(len(node.children or [])):
                    stack.pop()
                stack.append(node.__structural_hash)
                return
            if not structural and node.__hash is not None:
                for _ in range(len(node.children or [])):
                    stack.pop()
                stack.append(node.__hash)
                return

            if node.children is None:
                node_hash = hash(node.value) if structural else hash((node.value, node.id))
            else:
                children_values = []
                for _ in range(len(node.children)):
                    children_values.append(stack.pop())
                node_hash = hash(((node.value,) if structural else (node.value, node.id)) + tuple(children_values))

            stack.append(node_hash)
            if structural:
                node.__structural_hash = node_hash
            else:
                node.__hash = node_hash

        self.traverse(action, kind=DerivationTree.TRAVERSE_POSTORDER, reverse=True)

        assert len(stack) == 1
        return stack.pop()

    def __hash__(self):
        # return self.id  # Should be unique!
        if self.__hash is not None:
            return self.__hash

        self.__hash = self.compute_hash_iteratively(structural=False)
        return self.__hash

    def structural_hash(self):
        if self.__structural_hash is not None:
            return self.__structural_hash

        self.__structural_hash = self.compute_hash_iteratively(structural=True)
        return self.__structural_hash

    def structurally_equal(self, other: 'DerivationTree'):
        if not isinstance(other, DerivationTree):
            return False

        if (self.value != other.value
                or (self.children is None and other.children is not None)
                or (other.children is None and self.children is not None)):
            return False

        if self.children is None:
            return True

        if len(self.children) != len(other.children):
            return False

        return all(self.children[idx].structurally_equal(other.children[idx])
                   for idx in range(len(self.children)))

    def __eq__(self, other):
        """
        Equality takes the randomly assigned ID into account!
        So trees with the same structure might not be equal.
        """
        stack: List[Tuple[DerivationTree, DerivationTree]] = [(self, other)]

        while stack:
            t1, t2 = stack.pop()
            if (not isinstance(t2, DerivationTree)
                    or t1.value != t2.value
                    or t1.id != t2.id
                    or (t1.children is None and t2.children is not None)
                    or (t2.children is None and t1.children is not None)
                    or len(t1.children or []) != len(t2.children or [])):
                return False

            if t1.children:
                assert t2.children
                stack.extend(list(zip(t1.children, t2.children)))

        return True

    def __repr__(self):
        return f"DerivationTree({repr(self.value)}, {repr(self.children)}, id={self.id})"

    @lru_cache(maxsize=100)
    def to_string(self, show_open_leaves: bool = False) -> str:
        result = []
        stack = [self]

        while stack:
            node = stack.pop(0)
            symbol = node.value
            children = node.children

            if not children:
                if children is not None:
                    result.append("" if is_nonterminal(symbol) else symbol)
                else:
                    result.append(symbol if show_open_leaves else "")

                continue

            stack = list(children) + stack

        return ''.join(result)

    def __str__(self) -> str:
        return self.to_string(show_open_leaves=True)

    def to_dot(self) -> str:
        dot = Digraph(comment="Derivation Tree")
        dot.attr('node', shape='plain')

        def action(_, t: DerivationTree):
            dot.node(repr(t.id), "<" + html.escape(t.value) + f' <FONT COLOR="gray">({t.id})</FONT>>')
            for child in t.children or []:
                dot.edge(repr(t.id), repr(child.id))

        self.traverse(action)

        return dot.source
