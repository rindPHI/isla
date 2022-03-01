import itertools
import math
import re
from typing import Set, Generator, Tuple, List, Dict, Union, TypeVar, Sequence, cast, Callable, Iterable

from fuzzingbook.Grammars import unreachable_nonterminals

from isla.type_defs import Path, Grammar, ParseTree, ImmutableGrammar

S = TypeVar('S')
T = TypeVar('T')


def pop(l: List[S], default: T = None, index=0) -> Union[S, T]:
    return default if not l else l.pop(index)


def replace_line_breaks(inp: str) -> str:
    return inp.replace("\n", "\\n")


def parent_reflexive(path_1: Path, path_2: Path) -> bool:
    return len(path_1) <= len(path_2) and path_1 == path_2[:len(path_1)]


def parent_or_child(path_1: Path, path_2: Path) -> bool:
    return path_1[:len(path_2)] == path_2 or path_2[:len(path_1)] == path_1


def path_iterator(tree: ParseTree, path: Path = ()) -> Generator[Tuple[Path, ParseTree], None, None]:
    yield path, tree
    if tree[1] is not None:
        for i, child in enumerate(tree[1]):
            yield from path_iterator(child, path + (i,))


def delete_unreachable(grammar: Grammar) -> None:
    for unreachable in unreachable_nonterminals(grammar):
        del grammar[unreachable]


def replace_tree_path(in_tree: ParseTree, path: Path, replacement_tree: ParseTree) -> ParseTree:
    """Returns tree where replacement_tree has been inserted at `path` instead of the original subtree"""
    node, children = in_tree

    if not path:
        return replacement_tree

    head = path[0]
    new_children = (children[:head] +
                    [replace_tree_path(children[head], path[1:], replacement_tree)] +
                    children[head + 1:])

    return node, new_children


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


TRAVERSE_PREORDER = 0
TRAVERSE_POSTORDER = 1


def traverse(
        tree: ParseTree,
        action: Callable[[Path, ParseTree], None],
        abort_condition: Callable[[Path, ParseTree], bool] = lambda p, n: False,
        kind: int = TRAVERSE_PREORDER,
        reverse: bool = False) -> None:
    stack_1: List[Tuple[Path, ParseTree]] = [((), tree)]
    stack_2: List[Tuple[Path, ParseTree]] = []

    if kind == TRAVERSE_PREORDER:
        reverse = not reverse

    while stack_1:
        path, node = stack_1.pop()
        symbol, children = node

        if abort_condition(path, node):
            return

        if kind == TRAVERSE_POSTORDER:
            stack_2.append((path, node))

        if kind == TRAVERSE_PREORDER:
            action(path, node)

        if children:
            iterator = reversed(children) if reverse else iter(children)

            for idx, child in enumerate(iterator):
                new_path = path + ((len(children) - idx - 1) if reverse else idx,)
                stack_1.append((new_path, child))

    if kind == TRAVERSE_POSTORDER:
        while stack_2:
            action(*stack_2.pop())


def tree_to_string(tree: ParseTree) -> str:
    result = []
    stack = [tree]

    while stack:
        symbol, children = stack.pop(0)

        if not children:
            result.append('' if is_nonterminal(symbol) else symbol)
            continue

        for child in reversed(children):
            stack.insert(0, child)

    return ''.join(result)


def tree_depth(tree: ParseTree) -> int:
    if not tree[1]:
        return 1

    return 1 + max(tree_depth(child) for child in tree[1])


def tree_size(tree: ParseTree) -> int:
    if not tree[1]:
        return 1

    return 1 + sum(tree_depth(child) for child in tree[1])


def dict_of_lists_to_list_of_dicts(dict_of_lists: Dict[S, Iterable[T]]) -> List[Dict[S, T]]:
    keys = list(dict_of_lists.keys())
    list_of_values = [dict_of_lists[key] for key in keys]
    product = list(itertools.product(*list_of_values))

    return [dict(zip(keys, product_elem)) for product_elem in product]


def roundup(x: int, to: int) -> int:
    return int(math.ceil(x / float(to))) * int(to)


def powerset(iterable):
    """powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"""
    s = list(iterable)
    return itertools.chain.from_iterable(
        itertools.combinations(s, r)
        for r in range(len(s) + 1))


def weighted_geometric_mean(seq: Sequence[float], weights: Sequence[float]) -> float:
    assert len(seq) == len(weights)
    assert all(w >= 0 for w in weights)

    return (math.prod([(n + 1) ** w for n, w in zip(seq, weights) if w > 0]) **
            (1 / sum([w for w in weights if w > 0]))) - 1


def grammar_to_immutable(grammar: Grammar) -> ImmutableGrammar:
    return cast(
        Tuple[Tuple[str, Tuple[str, ...]]],
        tuple({k: tuple(v) for k, v in grammar.items()}.items()))


def immutable_to_grammar(immutable: ImmutableGrammar) -> Grammar:
    return {k: list(v) for k, v in dict(immutable).items()}


def nested_list_to_tuple(l: List[Union[T, List[T]]]) -> Tuple[Union[T, Tuple[T, ...]], ...]:
    return tuple([tuple(elem) if isinstance(elem, list) else elem for elem in l])


def assertions_activated() -> bool:
    result = False

    def set_result_to_true() -> bool:
        nonlocal result
        result = True
        return True

    assert set_result_to_true()
    return result


def split_str_with_nonterminals(expression: str) -> List[str]:
    return [token for token in re.split(
        RE_NONTERMINAL, expression) if token]


def cluster_by_common_elements(l: Sequence[T], f: Callable[[T], Set[S]]) -> List[List[T]]:
    """
    Clusters elements of l by shared elements. Elements of interest are obtained using f.
    For instance, to cluster a list of lists based on common list elements:

    >>> cluster_by_common_elements([[1,2], [2,3], [3,4], [5,6]], lambda l: {e for e in l})

    Gives [[[2, 3], [3, 4], [1, 2]], [[5, 6]]].

    >>> cluster_by_common_elements([1,2,3,4,5,6,7], lambda e: {e, e+3})

    Outputs [[2, 5], [3, 6], [4, 7, 1]].

    :param l: The list to cluster.
    :param f: The function to determine commonality.
    :return: The clusters w.r.t. f.
    """
    clusters = [[e2 for e2 in l if not f(e1).isdisjoint(f(e2))] for e1 in l]

    result = []
    for c in clusters:
        # Merge clusters with common elements...
        clusters_with_common_elements = [c1 for c1 in result if any(not f(e).isdisjoint(f(e1)) for e in c for e1 in c1)]
        for c1 in clusters_with_common_elements:
            result.remove(c1)

        merged_cluster = c + [e for c1 in clusters_with_common_elements for e in c1]

        # ...and remove duplicate elements from the merged cluster.
        no_dupl_cluster = []
        for cluster in merged_cluster:
            if cluster in no_dupl_cluster:
                continue
            no_dupl_cluster.append(cluster)

        result.append(no_dupl_cluster)

    return result


RE_NONTERMINAL = re.compile(r'(<[^<> ]*>)')


def is_nonterminal(s):
    return RE_NONTERMINAL.match(s)


def nonterminals(expansion: str) -> List[str]:
    return RE_NONTERMINAL.findall(expansion)


def strip_ws(inp: str) -> str:
    inp = inp.strip()
    inp = inp.replace("\n", " ")
    while True:
        new_inp = inp.replace("  ", " ")
        if new_inp == inp:
            break
        inp = new_inp
    return inp
