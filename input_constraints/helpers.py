import copy
import sys
from typing import Optional, Set, Callable, Generator, Tuple, List, Dict, Union

import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.GrammarFuzzer import GrammarFuzzer, all_terminals, tree_to_string
from fuzzingbook.Grammars import unreachable_nonterminals
from grammar_graph.gg import GrammarGraph

from input_constraints.type_defs import Path, ParseTree, Grammar, CanonicalGrammar, AbstractTree


def traverse_tree(tree: ParseTree, action: Callable[[Path, ParseTree], None]) -> None:
    for path, subtree in path_iterator(tree):
        action(path, subtree)


def path_iterator(tree: AbstractTree, path: Path = ()) -> Generator[Tuple[Path, AbstractTree], None, None]:
    yield path, tree
    if tree[1] is not None:
        for i, child in enumerate(tree[1]):
            yield from path_iterator(child, path + (i,))


def last_path(tree: AbstractTree) -> Path:
    result: List[int] = []
    curr_tree = tree
    while curr_tree[1]:
        last_idx = len(curr_tree[1]) - 1
        result.append(last_idx)
        curr_tree = curr_tree[1][last_idx]
    return tuple(result)


def find_subtree(tree: ParseTree, subtree: ParseTree, path: Path = tuple()) -> List[Path]:
    current_subtree = get_subtree(path, tree)
    if current_subtree == subtree:
        return [path]

    node, children = current_subtree
    if not children:
        return []

    result = []
    for idx in range(len(children)):
        child_result = find_subtree(tree, subtree, path + (idx,))
        if child_result is not None:
            result.extend(child_result)

    return result


def get_path_of_subtree(tree: ParseTree, subtree: ParseTree, path: Path = tuple()) -> Optional[Path]:
    current_subtree = get_subtree(path, tree)
    if current_subtree is subtree:
        return path

    node, children = current_subtree
    if not children:
        return None

    for idx in range(len(children)):
        child_result = get_path_of_subtree(tree, subtree, path + (idx,))
        if child_result is not None:
            return child_result

    return None


def delete_unreachable(grammar: Grammar) -> None:
    for unreachable in unreachable_nonterminals(grammar):
        del grammar[unreachable]


def replace_tree(in_tree: AbstractTree,
                 to_replace: AbstractTree,
                 with_tree: AbstractTree) -> AbstractTree:
    if in_tree == to_replace:
        return with_tree

    symbol, children = in_tree

    if not children:
        return symbol, children

    new_children = []
    for child in children:
        child_result = replace_tree(child, to_replace, with_tree)
        new_children.append(child_result)

    return symbol, new_children


def replace_tree_path(in_tree: AbstractTree, path: Path, replacement_tree: AbstractTree) -> AbstractTree:
    """Returns tree where replacement_tree has been inserted at `path` instead of the original subtree"""
    node, children = in_tree

    if not path:
        return replacement_tree

    head = path[0]
    new_children = (children[:head] +
                    [replace_tree_path(children[head], path[1:], replacement_tree)] +
                    children[head + 1:])

    return node, new_children


def id_prsrv_replace_tree_path(in_tree: AbstractTree, path: Path, replacement_tree: AbstractTree) -> AbstractTree:
    """In-place subtree replacement preserving identity of other subtrees."""
    if not path:
        return replacement_tree

    curr_parent = in_tree
    last_idx = path[0]
    curr_tree = curr_parent[1][last_idx]
    path = path[1:]

    while path:
        last_idx = path[0]
        path = path[1:]
        curr_parent = curr_tree
        curr_tree = curr_tree[1][last_idx]

    curr_parent[1][last_idx] = replacement_tree

    return in_tree


def is_after(path_1: Path, path_2: Path) -> bool:
    return not is_before(path_1, path_2) and \
           not is_prefix(path_1, path_2) and \
           not is_prefix(path_2, path_1)


def is_prefix(path_1: Path, path_2: Path) -> bool:
    if not path_1:
        return True

    if not path_2:
        return False

    car_1, *cdr_1 = path_1
    car_2, *cdr_2 = path_2

    if car_1 != car_2:
        return False
    else:
        return is_prefix(cdr_1, cdr_2)


def is_before(path_1: Path, path_2: Path) -> bool:
    if not path_1 or not path_2:
        # Note: (1,) is not before (1,0), since it's a prefix!
        # Also, (1,) cannot be before ().
        # But (1,0) would be before (1,1).
        return False

    car_1, *cdr_1 = path_1
    car_2, *cdr_2 = path_2

    if car_1 < car_2:
        return True
    elif car_2 < car_1:
        return False
    else:
        return is_before(tuple(cdr_1), tuple(cdr_2))


def get_subtree(path: Path, tree: ParseTree) -> ParseTree:
    """Access a subtree based on `path` (a list of children numbers)"""
    node, children = tree

    if not path:
        return tree

    return get_subtree(path[1:], children[path[0]])


def next_path(path: Path, tree: ParseTree) -> Optional[Path]:
    """Returns the next path in the tree; does not proceed towards leaves!

    TODO: Check whether next_path actually makes sense, or whether we should use next_path_complete..."""
    if not path:
        return None

    node, children = get_subtree(path[:-1], tree)
    if len(children) > path[-1] + 1:
        return path[:-1] + (path[-1] + 1,)
    else:
        return next_path(path[:-1], tree)


def next_path_complete(path: Path, tree: ParseTree) -> Optional[Path]:
    """
    Returns the next path in the tree. Repeated calls result in an iterator over
    the paths in the tree, unlike next_path.
    """

    def num_children(path: Path) -> int:
        _, children = get_subtree(path, tree)
        if children is None:
            return 0
        return len(children)

    # Descent towards left-most child leaf
    if num_children(path) > 0:
        return path + (0,)

    # Find next sibling
    for i in range(1, len(path)):
        if path[-i] + 1 < num_children(path[:-i]):
            return path[:-i] + (path[-i] + 1,)

    # Proceed to next root child
    if path[0] + 1 < num_children(tuple()):
        return path[0] + 1,

    # path already is the last path.
    assert list(path_iterator(tree))[-1][0] == path
    return None

    # last_child_idx = path[-1]
    # while path and path[-1] + 1 >= num_children(path):
    #     last_child_idx = path[-1]
    #     path = path[:-1]
    #
    # if last_child_idx + 1 < num_children(path):
    #     return path + (last_child_idx + 1,)
    # else:
    #     return None


def prev_path_complete(path: Path, tree: ParseTree) -> Optional[Path]:
    """
    Returns the previous path in the tree. Repeated calls result in an iterator over
    the paths in the tree (in reverse order), unlike next_path.
    """
    if not path:
        return None

    if path[-1] - 1 >= 0:
        new_path = path[:-1] + (path[-1] - 1,)
        # Proceed right-most leaf
        _, children = get_subtree(new_path, tree)
        while children:
            new_path = new_path + (len(children) - 1,)
            _, children = get_subtree(new_path, tree)

        return new_path
    else:
        return path[:-1]


def reverse_tree_iterator(start_path: Path, tree: ParseTree) -> Generator[Tuple[Path, ParseTree], None, None]:
    curr_path = prev_path_complete(start_path, tree)
    while curr_path is not None:
        yield curr_path, get_subtree(curr_path, tree)
        curr_path = prev_path_complete(curr_path, tree)


def get_symbols(formula: z3.BoolRef) -> Set[z3.Symbol]:
    result: Set[z3.Symbol] = set()

    def recurse(elem: z3.ExprRef):
        op = elem.decl()
        if z3.is_const(elem) and op.kind() == z3.Z3_OP_UNINTERPRETED:
            if op.range() != z3.StringSort():
                raise NotImplementedError(
                    f"This class was developed for String symbols only, found {op.range()}")

            result.add(op.name())

        for child in elem.children():
            recurse(child)

    recurse(formula)
    return result


def dfs(tree: AbstractTree, action: Callable[[AbstractTree], None] = print):
    node, children = tree
    action(tree)
    if children is not None:
        for child in children:
            dfs(child, action)


def geometric_sequence(length: int, base: float = 1.1) -> List[int]:
    return list(map(lambda x: 1.1 ** x, range(0, length)))


def is_canonical_grammar(grammar: Union[Grammar, CanonicalGrammar]) -> bool:
    return type(next(item[1] for item in grammar.items())[0]) is list


def tree_list_to_str(tree_list: List) -> str:
    head, tail = tree_list
    assert type(head) is str
    return f"[{head}, [{', '.join(map(tree_list_to_str, tail))}]]"


def visit_z3_expr(e: Union[z3.ExprRef, z3.QuantifierRef],
                  seen: Optional[Dict[Union[z3.ExprRef, z3.QuantifierRef], bool]] = None) -> \
        Generator[Union[z3.ExprRef, z3.QuantifierRef], None, None]:
    if seen is None:
        seen = {}
    elif e in seen:
        return

    seen[e] = True
    yield e

    if z3.is_app(e):
        for ch in e.children():
            for e in visit_z3_expr(ch, seen):
                yield e
        return

    if z3.is_quantifier(e):
        for e in visit_z3_expr(e.body(), seen):
            yield e
        return


def is_z3_var(expr: z3.ExprRef) -> bool:
    return z3.is_const(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED


def tree_depth(tree: ParseTree, depth: int = 1) -> int:
    _, children = tree
    if not children:
        return depth
    else:
        return max([tree_depth(child, depth + 1) for child in children])


class TreeExpander(GrammarFuzzer):
    def expand_tree_once(self, tree: ParseTree) -> List[ParseTree]:
        """Choose an unexpanded symbol in tree; expand it.  Can be overloaded in subclasses."""
        (symbol, children) = tree
        if children is None:
            # Expand this node
            return self.expand_node(tree)

        # Find all children with possible expansions
        expandable_children = [
            c for c in children if self.any_possible_expansions(c)]

        # `index_map` translates an index in `expandable_children`
        # back into the original index in `children`
        index_map = [i for (i, c) in enumerate(children)
                     if c in expandable_children]

        result = []

        for child_to_be_expanded in range(len(expandable_children)):
            for children_expansion in self.expand_tree_once(expandable_children[child_to_be_expanded]):
                children_ = copy.deepcopy(children)
                children_[index_map[child_to_be_expanded]] = children_expansion
                result.append((symbol, children_))

        return result

    def expand_node(self, node):
        (symbol, children) = node
        assert children is None

        if self.log:
            print("Expanding", all_terminals(node), "exhaustively")

        # Fetch the possible expansions from grammar...
        expansions = self.grammar[symbol]
        possible_children = [self.expansion_to_children(
            expansion) for expansion in expansions]

        # Return with new children
        return [(symbol, chosen_children) for chosen_children in possible_children]


def compute_numeric_nonterminals(grammar: Grammar) -> Dict[str, Tuple[int, int]]:
    # TODO: This could be a performance bottleneck. We should try to statically solve this!
    result = {}
    for nonterminal in grammar:
        new_grammar = copy.deepcopy(grammar)
        new_grammar["<start>"] = [nonterminal]
        delete_unreachable(new_grammar)
        fuzzer = GrammarCoverageFuzzer(new_grammar)

        lower_bound, upper_bound = sys.maxsize, -1
        for _ in range(100):
            inp = fuzzer.fuzz()
            if not (inp.isnumeric()):
                break
            int_repr = int(inp)
            if int_repr < lower_bound:
                lower_bound = int_repr
            elif int_repr > upper_bound:
                upper_bound = int_repr
        else:
            result[nonterminal] = (lower_bound, upper_bound)

    return result


def tree_to_tuples(tree: AbstractTree) -> Tuple[Union[str, 'isla.Variable'], Optional[Tuple]]:
    node, children = tree
    if children is None:
        return node, None
    else:
        return node, tuple([tree_to_tuples(child) for child in children])


def z3_subst_assgn(inp: z3.ExprRef, subst_map: Dict['isla.Variable', ParseTree]) -> z3.ExprRef:
    return z3_subst(inp, {v.to_smt(): z3.StringVal(tree_to_string(t))
                          for v, t in subst_map.items()})


def z3_subst(inp: z3.ExprRef, subst_map: Dict[z3.ExprRef, z3.ExprRef]) -> z3.ExprRef:
    return z3.substitute(inp, *tuple(subst_map.items()))


def get_leaves(tree: AbstractTree) -> Generator[Tuple[Path, AbstractTree], None, None]:
    return ((path, sub_tree)
            for path, sub_tree in path_iterator(tree)
            if not sub_tree[1])


def open_concrete_leaves(tree: AbstractTree) -> Generator[Tuple[Path, AbstractTree], None, None]:
    return ((path, sub_tree)
            for path, sub_tree in path_iterator(tree)
            if type(sub_tree[0]) is str and sub_tree[1] is None)


def all_open_leaves(tree: AbstractTree) -> Generator[Tuple[Path, AbstractTree], None, None]:
    return ((path, sub_tree)
            for path, sub_tree in path_iterator(tree)
            if sub_tree[1] is None)


def reachable(grammar: Grammar, nonterminal: str, to_nonterminal: str) -> bool:
    graph = GrammarGraph.from_grammar(grammar)
    return graph.get_node(nonterminal).reachable(graph.get_node(to_nonterminal))
