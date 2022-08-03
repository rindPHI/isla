import copy
import itertools
import math
import re
import sys
from bisect import bisect_left
from dataclasses import dataclass
from functools import lru_cache
from typing import Set, Generator, Tuple, List, Dict, Union, TypeVar, Sequence, cast, Callable, Iterable, Any, Optional

import datrie

from isla.type_defs import Path, Grammar, ParseTree, ImmutableGrammar, CanonicalGrammar

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


def canonical(grammar: Grammar) -> CanonicalGrammar:
    # Slightly optimized w.r.t. Fuzzing Book version: Call to split on
    # compiled regex instead of fresh compilation every time.
    def split(expansion):
        if isinstance(expansion, tuple):
            expansion = expansion[0]

        return [
            token
            for token in RE_NONTERMINAL.split(expansion)
            if token]

    return {
        k: [split(expression) for expression in alternatives]
        for k, alternatives in grammar.items()
    }


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


def srange(characters: str) -> List[str]:
    """Construct a list with all characters in the string"""
    return [c for c in characters]


def crange(character_start: str, character_end: str) -> List[str]:
    return [chr(i) for i in range(ord(character_start), ord(character_end) + 1)]


RE_EXTENDED_NONTERMINAL = re.compile(r'(<[^<> ]*>[?+*])')


def extended_nonterminals(expansion: str) -> List[str]:
    # In later chapters, we allow expansions to be tuples,
    # with the expansion being the first element
    if isinstance(expansion, tuple):
        expansion = expansion[0]
    return RE_EXTENDED_NONTERMINAL.findall(expansion)


def extend_grammar(grammar: Grammar, extension: Optional[Grammar] = None) -> Grammar:
    if extension is None:
        extension = {}
    new_grammar = copy.deepcopy(grammar)
    new_grammar.update(extension)
    return new_grammar


def new_symbol(grammar: Grammar, symbol_name: str = "<symbol>") -> str:
    """Return a new symbol for `grammar` based on `symbol_name`"""
    if symbol_name not in grammar:
        return symbol_name

    count = 1
    while True:
        tentative_symbol_name = symbol_name[:-1] + "-" + repr(count) + ">"
        if tentative_symbol_name not in grammar:
            return tentative_symbol_name
        count += 1


def convert_ebnf_operators(ebnf_grammar: Grammar) -> Grammar:
    """Convert a grammar in extended BNF to BNF"""
    grammar = extend_grammar(ebnf_grammar)
    for nonterminal in ebnf_grammar:
        expansions = ebnf_grammar[nonterminal]

        for i in range(len(expansions)):
            expansion = expansions[i]
            extended_symbols = extended_nonterminals(expansion)

            for extended_symbol in extended_symbols:
                operator = extended_symbol[-1:]
                original_symbol = extended_symbol[:-1]
                assert original_symbol in ebnf_grammar, \
                    f"{original_symbol} is not defined in grammar"

                new_sym = new_symbol(grammar, original_symbol)

                exp = grammar[nonterminal][i]
                opts = None
                if isinstance(exp, tuple):
                    (exp, opts) = exp
                assert isinstance(exp, str)

                new_exp = exp.replace(extended_symbol, new_sym, 1)
                if opts:
                    grammar[nonterminal][i] = (new_exp, opts)
                else:
                    grammar[nonterminal][i] = new_exp

                if operator == '?':
                    grammar[new_sym] = ["", original_symbol]
                elif operator == '*':
                    grammar[new_sym] = ["", original_symbol + new_sym]
                elif operator == '+':
                    grammar[new_sym] = [
                        original_symbol, original_symbol + new_sym]

    return grammar


RE_PARENTHESIZED_EXPR = re.compile(r'\([^()]*\)[?+*]')


def parenthesized_expressions(expansion: str) -> List[str]:
    # In later chapters, we allow expansions to be tuples,
    # with the expansion being the first element
    if isinstance(expansion, tuple):
        expansion = expansion[0]

    return RE_PARENTHESIZED_EXPR.findall(expansion)


def convert_ebnf_parentheses(ebnf_grammar: Grammar) -> Grammar:
    """Convert a grammar in extended BNF to BNF"""
    grammar = extend_grammar(ebnf_grammar)
    for nonterminal in ebnf_grammar:
        expansions = ebnf_grammar[nonterminal]

        for i in range(len(expansions)):
            expansion = expansions[i]
            if not isinstance(expansion, str):
                expansion = expansion[0]

            while True:
                parenthesized_exprs = parenthesized_expressions(expansion)
                if len(parenthesized_exprs) == 0:
                    break

                for expr in parenthesized_exprs:
                    operator = expr[-1:]
                    contents = expr[1:-2]

                    new_sym = new_symbol(grammar)

                    exp = grammar[nonterminal][i]
                    opts = None
                    if isinstance(exp, tuple):
                        (exp, opts) = exp
                    assert isinstance(exp, str)

                    expansion = exp.replace(expr, new_sym + operator, 1)
                    if opts:
                        grammar[nonterminal][i] = (expansion, opts)
                    else:
                        grammar[nonterminal][i] = expansion

                    grammar[new_sym] = [contents]

    return grammar


def convert_ebnf_grammar(ebnf_grammar: Grammar) -> Grammar:
    return convert_ebnf_operators(convert_ebnf_parentheses(ebnf_grammar))


RE_NONTERMINAL = re.compile(r'(<[^<> ]*>)')


@lru_cache(maxsize=None)
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


def transitive_closure(relation: Iterable[Tuple[S, T]]) -> Set[Tuple[S, T]]:
    closure = set(relation)
    while True:
        new_relations: Set[Tuple[S, T]] = {
            (x, w)
            for x, y in closure
            for q, w in closure if q == y}

        closure_until_now = closure | new_relations

        if closure_until_now == closure:
            break

        closure = closure_until_now

    return closure


def remove_subtrees_for_prefix(
        subtrees: List[Tuple[Path, Any]],
        prefix: Path) -> List[Tuple[Path, Any]]:
    if not prefix or not subtrees:
        return []

    keyed_subtrees = KeyList(subtrees, key=lambda t: t[0])
    pos_start = bisect_left(keyed_subtrees, prefix)

    if subtrees[pos_start][0][:len(prefix)] != prefix:
        # Prefix does not exist in list! Thus, return the whole list
        result = subtrees
    else:
        pos_end = bisect_left(keyed_subtrees, prefix[:-1] + (prefix[-1] + 1,), lo=pos_start + 1)
        result = subtrees[:pos_start] + subtrees[pos_end:]

    # assert result == [(p, s) for p, s in subtrees if not p[:len(prefix)] == prefix]

    return result


class KeyList(Sequence):
    # bisect doesn't accept a key function, so we build the key into our sequence.
    def __init__(self, l, key):
        self.l = l
        self.key = key

    def __len__(self):
        return len(self.l)

    def __getitem__(self, index):
        return self.key(self.l[index])


def mk_subtree_trie() -> datrie.Trie:
    return datrie.Trie([chr(i) for i in range(30)])


def path_to_trie_key(path: Path) -> str:
    # 0-bytes are ignored by the trie ==> +1
    # To represent the empty part, reserve chr(1) ==> +2
    if not path:
        return chr(1)

    return chr(1) + "".join([chr(i + 2) for i in path])


def trie_key_to_path(key: str) -> Path:
    if not key or key[0] != chr(1):
        raise RuntimeError(f"Invalid trie key '{key}' ({[ord(c) for c in key]}), should start with 1")

    if key == chr(1):
        return ()

    return tuple([ord(c) - 2 for c in key if ord(c) != 1])


def get_subtrie(trie: datrie.Trie, new_root_path: Path | str) -> datrie.Trie:
    subtrees_trie = mk_subtree_trie()

    if isinstance(new_root_path, str):
        root_key = new_root_path
        root_path_len = len(root_key) - 1
    else:
        assert isinstance(new_root_path, tuple)
        root_key = path_to_trie_key(new_root_path)
        root_path_len = len(new_root_path)

    for suffix in trie.suffixes(root_key):
        path, tree = trie[root_key + suffix]
        subtrees_trie[chr(1) + suffix] = (path[root_path_len:], tree)

    return subtrees_trie


def copy_trie(trie: datrie.Trie) -> datrie.Trie:
    result = mk_subtree_trie()
    for key, value in trie.items():
        result[key] = value
    return result


def start_symbol():
    return '<start>'


def def_used_nonterminals(grammar: Grammar, _start_symbol: str = start_symbol()) -> \
        Tuple[Optional[Set[str]], Optional[Set[str]]]:
    """Return a pair (`defined_nonterminals`, `used_nonterminals`) in `grammar`.
    In case of error, return (`None`, `None`)."""

    defined_nonterminals = set()
    used_nonterminals = {_start_symbol}

    for defined_nonterminal in grammar:
        defined_nonterminals.add(defined_nonterminal)
        expansions = grammar[defined_nonterminal]
        if not isinstance(expansions, list):
            print(repr(defined_nonterminal) + ": expansion is not a list",
                  file=sys.stderr)
            return None, None

        if len(expansions) == 0:
            print(repr(defined_nonterminal) + ": expansion list empty",
                  file=sys.stderr)
            return None, None

        for expansion in expansions:
            if isinstance(expansion, tuple):
                expansion = expansion[0]
            if not isinstance(expansion, str):
                print(repr(defined_nonterminal) + ": "
                      + repr(expansion) + ": not a string",
                      file=sys.stderr)
                return None, None

            for used_nonterminal in nonterminals(expansion):
                used_nonterminals.add(used_nonterminal)

    return defined_nonterminals, used_nonterminals


def reachable_nonterminals(grammar: Grammar, _start_symbol: str = start_symbol()) -> Set[str]:
    reachable = set()

    def _find_reachable_nonterminals(grammar, symbol):
        nonlocal reachable
        reachable.add(symbol)
        for expansion in grammar.get(symbol, []):
            for nonterminal in nonterminals(expansion):
                if nonterminal not in reachable:
                    _find_reachable_nonterminals(grammar, nonterminal)

    _find_reachable_nonterminals(grammar, _start_symbol)
    return reachable


def unreachable_nonterminals(grammar: Grammar, _start_symbol=start_symbol()) -> Set[str]:
    return grammar.keys() - reachable_nonterminals(grammar, _start_symbol)


def is_valid_grammar(grammar: Grammar, _start_symbol: str = start_symbol(), ) -> bool:
    """Check if the given `grammar` is valid.
       `start_symbol`: optional start symbol (default: `<start>`)
       `supported_opts`: options supported (default: none)"""

    defined_nonterminals, used_nonterminals = \
        def_used_nonterminals(grammar, _start_symbol)
    if defined_nonterminals is None or used_nonterminals is None:
        return False

    # Do not complain about '<start>' being not used,
    # even if start_symbol is different
    if start_symbol() in grammar:
        used_nonterminals.add(start_symbol())

    for unused_nonterminal in defined_nonterminals - used_nonterminals:
        print(repr(unused_nonterminal) + ": defined, but not used",
              file=sys.stderr)
    for undefined_nonterminal in used_nonterminals - defined_nonterminals:
        print(repr(undefined_nonterminal) + ": used, but not defined",
              file=sys.stderr)

    # Symbols must be reachable either from <start> or given start symbol
    unreachable = unreachable_nonterminals(grammar, _start_symbol)
    msg_start_symbol = _start_symbol

    if start_symbol() in grammar:
        unreachable = unreachable - reachable_nonterminals(grammar, start_symbol())
        if start_symbol != start_symbol():
            msg_start_symbol += " or " + start_symbol()

    for unreachable_nonterminal in unreachable:
        print(repr(unreachable_nonterminal) + ": unreachable from " + msg_start_symbol,
              file=sys.stderr)

    return used_nonterminals == defined_nonterminals and len(unreachable) == 0


@dataclass(frozen=True)
class lazyjoin:
    s: str
    items: Iterable[Any]

    def __str__(self):
        return self.s.join(map(str, self.items))


@dataclass(frozen=True)
class lazystr:
    c: Callable[[], Any]

    def __str__(self):
        return str(self.c())


def replace_in_list(l: List[T], repl: S | List[S], idx: int) -> List[T | S]:
    assert -len(l) <= idx < len(l)
    if idx < 0:
        idx = len(l) + idx
    return l[0:idx] + (repl if isinstance(repl, list) else [repl]) + l[idx + 1:]


def nth_occ(haystack: Sequence[T], needle: T, n: int) -> Optional[int]:
    assert n >= 0
    num_occs = 0
    for idx, elem in enumerate(haystack):
        if elem == needle:
            if num_occs == n:
                return idx
            num_occs += 1

    return None
