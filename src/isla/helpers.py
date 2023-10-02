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
import importlib.resources
import itertools
import logging
import math
import operator
import random
import re
import sys
from dataclasses import dataclass
from functools import lru_cache, reduce
from typing import (
    Set,
    Generator,
    Tuple,
    List,
    Dict,
    Union,
    TypeVar,
    Sequence,
    cast,
    Callable,
    Iterable,
    Any,
    Optional,
    AbstractSet,
    Iterator,
)

import returns
from frozendict import frozendict
from orderedset import OrderedSet
from returns.maybe import Maybe, Some
from returns.result import safe, Success, Failure, Result

from isla.global_config import GLOBAL_CONFIG
from isla.type_defs import (
    Path,
    Grammar,
    ParseTree,
    ImmutableGrammar,
    CanonicalGrammar,
    ImmutableList,
    FrozenCanonicalGrammar,
    FrozenGrammar,
)

HELPERS_LOGGER = logging.getLogger(__name__)

R = TypeVar("R")
S = TypeVar("S")
T = TypeVar("T")


def singleton_iterator(elem: T) -> Iterator[T]:
    """
    Creates an iterator from a single element.

    >>> it = singleton_iterator(1)
    >>> next(it)
    1

    >>> deep_str(safe(lambda: next(it))())
    '<Failure: StopIteration()>'

    :param elem: The element to create an iterator from.
    :return: The resulting iterator of one element.
    """

    return (x for x in [elem])


def star(f: Callable[[[Any, ...]], T]) -> Callable[[Sequence[Any]], T]:
    return lambda x: f(*x)


def is_path(maybe_path: Any) -> bool:
    """
    >>> is_path("str")
    False

    >>> is_path((1, (), 0))
    False

    >>> is_path((1, 2, 0))
    True

    :param maybe_path: Element to check for being a `Path`.
    :return: Returns `True` if `maybe_path` is a `Path`.
    """
    return isinstance(maybe_path, tuple) and all(
        isinstance(elem, int) for elem in maybe_path
    )


def pop(a_list: List[S], default: T = None, index=0) -> Union[S, T]:
    return default if not a_list else a_list.pop(index)


def replace_line_breaks(inp: str) -> str:
    return inp.replace("\n", "\\n")


def parent_reflexive(path_1: Path, path_2: Path) -> bool:
    return len(path_1) <= len(path_2) and path_1 == path_2[: len(path_1)]


def parent_or_child(path_1: Path, path_2: Path) -> bool:
    return path_1[: len(path_2)] == path_2 or path_2[: len(path_1)] == path_1


def path_iterator(
    tree: ParseTree, path: Path = ()
) -> Generator[Tuple[Path, ParseTree], None, None]:
    yield path, tree
    if tree[1] is not None:
        for i, child in enumerate(tree[1]):
            yield from path_iterator(child, path + (i,))


def delete_unreachable(grammar: Grammar) -> Grammar:
    return {
        nonterminal: expansions
        for nonterminal, expansions in grammar.items()
        if nonterminal not in unreachable_nonterminals(grammar)
    }


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
    reverse: bool = False,
) -> None:
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
            result.append("" if is_nonterminal(symbol) else symbol)
            continue

        for child in reversed(children):
            stack.insert(0, child)

    return "".join(result)


def split_expansion(expansion: str) -> List[str]:
    """
    Splits the given expansion alternative into tokens.

    >>> str(split_expansion("a<b><b>c<d>e"))
    "['a', '<b>', '<b>', 'c', '<d>', 'e']"

    :param expansion: The expansion alternative to split at nonterminal boundaries.
    :return: The separated terminal and nonterminal symbols in the expansion, in the
        original order.
    """

    return [token for token in RE_NONTERMINAL.split(expansion) if token]


def canonical(grammar: Grammar) -> CanonicalGrammar:
    """
    This function converts a grammar to a "canonical" form in which terminals and
    nonterminals in expansion alternatives are split.

    Example
    -------

    >>> import string
    >>> grammar = {
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

    Before conversion, there are two entries for :code:`<stmt>` including sequences
    of (non-)terminals:

    >>> print(grammar["<stmt>"])
    ['<assgn> ; <stmt>', '<assgn>']

    After conversion, the entries are lists of individual (non)-terminals:

    >>> print(canonical(grammar)["<stmt>"])
    [['<assgn>', ' ; ', '<stmt>'], ['<assgn>']]

    :param grammar: The grammar to convert.
    :return: The converted canonical grammar.
    """
    return {
        k: [split_expansion(expression) for expression in alternatives]
        for k, alternatives in grammar.items()
    }


def frozen_canonical(grammar: Grammar | FrozenGrammar) -> FrozenCanonicalGrammar:
    """
    A "frozen" version of :func:`isla.helpers.canonical`.

    Example
    -------

    >>> grammar = {
    ...     "<start>": ["<int>"],
    ...     "<int>": ["<sign>00<leaddigit><digits>"],
    ...     "<sign>": ["-", "+"],
    ...     "<digits>": ["", "<digit><digits>"],
    ...     "<digit>": list("0123456789"),
    ...     "<leaddigit>": list("123456789"),
    ... }

    >>> result = frozen_canonical(grammar)

    >>> type(result).__name__
    'frozendict'
    >>> result["<digits>"]
    ((), ('<digit>', '<digits>'))

    :param grammar: The grammar to convert to frozen canonical form.
    :return: The frozen canonical grammar.
    """

    def split(expansion):
        if isinstance(expansion, tuple):
            expansion = expansion[0]

        return tuple([token for token in RE_NONTERMINAL.split(expansion) if token])

    return frozendict(
        {
            k: tuple([split(expression) for expression in alternatives])
            for k, alternatives in grammar.items()
        }
    )


def dict_of_lists_to_list_of_dicts(
    dict_of_lists: Dict[S, Iterable[T]]
) -> List[Dict[S, T]]:
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
        itertools.combinations(s, r) for r in range(len(s) + 1)
    )


def weighted_geometric_mean(seq: Sequence[float], weights: Sequence[float]) -> float:
    assert len(seq) == len(weights)
    assert all(w >= 0 for w in weights)

    return (
        math.prod([(n + 1) ** w for n, w in zip(seq, weights) if w > 0])
        ** (1 / sum([w for w in weights if w > 0]))
    ) - 1


def grammar_to_immutable(grammar: Grammar) -> ImmutableGrammar:
    return cast(
        ImmutableGrammar, tuple({k: tuple(v) for k, v in grammar.items()}.items())
    )


def grammar_to_mutable(grammar: ImmutableGrammar) -> Grammar:
    return {nonterminal: list(expansion) for nonterminal, expansion in grammar}


def nested_list_to_tuple(
    a_list: List[Union[T, List[T]]]
) -> Tuple[Union[T, Tuple[T, ...]], ...]:
    return tuple([tuple(elem) if isinstance(elem, list) else elem for elem in a_list])


def assertions_activated() -> bool:
    """
    Checks if assertions are activated. Returns False if the
    :code:`ASSERTIONS_ACTIVATED` variable in :module:`isla.global_config` is False.
    Otherwise, returns True if, and only if, assertions are globally active, i.e.,
    an :code:`assert False` would raise an exception.

    :return: True iff assertions are active.
    """
    if not GLOBAL_CONFIG.assertions_activated:
        return False

    result = False

    def set_result_to_true() -> bool:
        nonlocal result
        result = True
        return True

    assert set_result_to_true()
    return result


def split_str_with_nonterminals(expression: str) -> List[str]:
    return [token for token in re.split(RE_NONTERMINAL, expression) if token]


def cluster_by_common_elements(
    a_list: Sequence[T], f: Callable[[T], AbstractSet[S]]
) -> List[List[T]]:
    """
    Clusters elements of l by shared elements. Elements of interest are obtained using f.
    For instance, to cluster a list of lists based on common list elements:

    >>> cluster_by_common_elements([[1,2], [2,3], [3,4], [5,6]], lambda l: {e for e in l})
    [[[2, 3], [3, 4], [1, 2]], [[5, 6]]]

    >>> cluster_by_common_elements([1,2,3,4,5,6,7], lambda e: {e, e+3})
    [[2, 5], [3, 6], [4, 7, 1]]

    :param a_list: The list to cluster.
    :param f: The function to determine commonality.
    :return: The clusters w.r.t. f.
    """
    clusters = [[e2 for e2 in a_list if not f(e1).isdisjoint(f(e2))] for e1 in a_list]

    result = []
    for c in clusters:
        # Merge clusters with common elements...
        clusters_with_common_elements = [
            c1
            for c1 in result
            if any(not f(e).isdisjoint(f(e1)) for e in c for e1 in c1)
        ]
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


RE_EXTENDED_NONTERMINAL = re.compile(r"(<[^<> ]*>[?+*])")


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
                assert (
                    original_symbol in ebnf_grammar
                ), f"{original_symbol} is not defined in grammar"

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

                if operator == "?":
                    grammar[new_sym] = ["", original_symbol]
                elif operator == "*":
                    grammar[new_sym] = ["", original_symbol + new_sym]
                elif operator == "+":
                    grammar[new_sym] = [original_symbol, original_symbol + new_sym]

    return grammar


RE_PARENTHESIZED_EXPR = re.compile(r"\([^()]*\)[?+*]")


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


RE_NONTERMINAL = re.compile(r"(<[^<> ]*>)")


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


def start_symbol():
    return "<start>"


def def_used_nonterminals(
    grammar: Grammar, _start_symbol: str = start_symbol()
) -> Tuple[Optional[Set[str]], Optional[Set[str]]]:
    """Return a pair (`defined_nonterminals`, `used_nonterminals`) in `grammar`.
    In case of error, return (`None`, `None`)."""

    defined_nonterminals = set()
    used_nonterminals = {_start_symbol}

    for defined_nonterminal in grammar:
        defined_nonterminals.add(defined_nonterminal)
        expansions = grammar[defined_nonterminal]
        if not isinstance(expansions, list) and not isinstance(expansions, tuple):
            print(
                repr(defined_nonterminal) + ": expansion is not a list", file=sys.stderr
            )
            return None, None

        if len(expansions) == 0:
            print(repr(defined_nonterminal) + ": expansion list empty", file=sys.stderr)
            return None, None

        for expansion in expansions:
            # if isinstance(expansion, tuple):
            #     expansion = expansion[0]
            if not isinstance(expansion, str):
                print(
                    repr(defined_nonterminal)
                    + ": "
                    + repr(expansion)
                    + ": not a string",
                    file=sys.stderr,
                )
                return None, None

            for used_nonterminal in nonterminals(expansion):
                used_nonterminals.add(used_nonterminal)

    return defined_nonterminals, used_nonterminals


def reachable_nonterminals(
    grammar: Grammar, _start_symbol: str = start_symbol()
) -> Set[str]:
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


def unreachable_nonterminals(
    grammar: Grammar, _start_symbol=start_symbol()
) -> Set[str]:
    return grammar.keys() - reachable_nonterminals(grammar, _start_symbol)


def is_valid_grammar(
    grammar: Grammar,
    _start_symbol: str = start_symbol(),
) -> bool:
    """Check if the given `grammar` is valid.
    `start_symbol`: optional start symbol (default: `<start>`)
    `supported_opts`: options supported (default: none)"""

    defined_nonterminals, used_nonterminals = def_used_nonterminals(
        grammar, _start_symbol
    )
    if defined_nonterminals is None or used_nonterminals is None:
        return False

    # Do not complain about '<start>' being not used,
    # even if start_symbol is different
    if start_symbol() in grammar:
        used_nonterminals.add(start_symbol())

    for unused_nonterminal in defined_nonterminals - used_nonterminals:
        print(repr(unused_nonterminal) + ": defined, but not used", file=sys.stderr)
    for undefined_nonterminal in used_nonterminals - defined_nonterminals:
        print(repr(undefined_nonterminal) + ": used, but not defined", file=sys.stderr)

    # Symbols must be reachable either from <start> or given start symbol
    unreachable = unreachable_nonterminals(grammar, _start_symbol)
    msg_start_symbol = _start_symbol

    if start_symbol() in grammar:
        unreachable = unreachable - reachable_nonterminals(grammar, start_symbol())
        if start_symbol != start_symbol():
            msg_start_symbol += " or " + start_symbol()

    for unreachable_nonterminal in unreachable:
        print(
            repr(unreachable_nonterminal) + ": unreachable from " + msg_start_symbol,
            file=sys.stderr,
        )

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


def nth_occ(haystack: Sequence[T], needle: T, n: int) -> Optional[int]:
    assert n >= 0
    num_occs = 0
    for idx, elem in enumerate(haystack):
        if elem == needle:
            if num_occs == n:
                return idx
            num_occs += 1

    return None


def list_set(ilist: ImmutableList[T], repl_idx: int, new_elem: T) -> ImmutableList[T]:
    return ilist[:repl_idx] + (new_elem,) + ilist[repl_idx + 1 :]


def list_del(ilist: Sequence[T], del_idx: int) -> Sequence[T]:
    return ilist[:del_idx] + ilist[del_idx + 1 :]


def is_float(num: Any) -> bool:
    try:
        float(num)
        return True
    except ValueError:
        return False


def get_isla_resource_file_content(path_to_file: str) -> str:
    traversable = importlib.resources.files("isla").joinpath(path_to_file)
    with importlib.resources.as_file(traversable) as path:
        with open(path, "r") as file:
            return file.read()


def eassert(
    expr: T,
    condition: bool | Callable[[T], bool],
    msg: str | Callable[[], str] = "",
) -> T:
    cond = condition if isinstance(condition, bool) else condition(expr)
    assert cond, msg if isinstance(msg, str) else msg()
    return expr


def shuffle(a_list: List[T]) -> List[T]:
    result: List[T] = list(a_list)
    random.shuffle(result)
    return result


Seq = TypeVar("Seq", bound=Sequence)


def eliminate_suffixes(a_list: Sequence[Seq]) -> List[Seq]:
    return [
        seq
        for idx_1, seq in enumerate(a_list)
        if not any(
            idx_1 != idx_2 and len(pref) < len(seq) and pref == seq[: len(pref)]
            for idx_2, pref in enumerate(a_list)
        )
    ]


def to_id(f: Callable[[T], Any]) -> Callable[[T], T]:
    def result(inp: T) -> T:
        f(inp)
        return inp

    return result


def instantiate_escaped_symbols(text: str) -> str:
    backslash_escape_placeholder = "$$BESC$$"
    assert backslash_escape_placeholder not in text

    repl_map = {
        r"\b": "\b",
        r"\t": "\t",
        r"\n": "\n",
        r"\r": "\r",
        r"\"": '"',
        r"\x0b": "\x0b",
        r"\x0c": "\x0c",
    } | {r"\x" + hex(i)[2:].rjust(2, "0"): chr(i) for i in range(0, 256)}

    text = text.replace("\\\\", backslash_escape_placeholder)
    for escaped_char in repl_map:
        text = text.replace(escaped_char, repl_map[escaped_char])

    return text.replace(backslash_escape_placeholder, "\\")


def get_elem_by_equivalence(
    elem: T, elems: Iterable[S], equiv: Callable[[T, S], bool] = operator.eq
) -> S:
    """
    Returns the first element in `elems` that is equivalent to `elem` according
    to the relation `equiv`. Raises an AssertionError if no such element exists.

    :param elem: The element for which an equivalent one should be found.
    :param elems: The container to search.
    :param equiv: An equivalence relation. Default is standard equivalence `==`.
    :return: An equivalent element from `elems`.
    """

    match safe(
        lambda: next(other_elem for other_elem in elems if equiv(elem, other_elem))
    )():
        case Success(elem):
            return elem
        case Failure(_):
            raise RuntimeError(
                f"Could not find element equivalent to {elem} in container {elems}"
            )


def get_expansions(leaf_value: str, grammar: CanonicalGrammar | FrozenCanonicalGrammar):
    all_expansions = grammar[leaf_value]

    terminal_expansions = [
        expansion
        for expansion in all_expansions
        if len(expansion) == 1 and not is_nonterminal(expansion[0])
    ]

    expansions = [
        expansion
        for expansion in all_expansions
        if expansion not in terminal_expansions
    ]

    return terminal_expansions, expansions


def compute_nullable_nonterminals(
    canonical_grammar: CanonicalGrammar | FrozenCanonicalGrammar,
) -> Set[str]:
    result = {
        nonterminal
        for nonterminal in canonical_grammar
        if any(not expansion for expansion in canonical_grammar[nonterminal])
    }

    changed = True
    while changed:
        changed = False

        for nonterminal in set(canonical_grammar).difference(result):
            if any(
                all(elem in result for elem in expansion)
                for expansion in canonical_grammar[nonterminal]
            ):
                changed = True
                result.add(nonterminal)

    return result


def merge_dict_of_sets(
    dict_1: Dict[T, Set[S]], dict_2: Dict[T, Set[S]]
) -> Dict[T, Set[S]]:
    """
    Merges the given dictionaries.

    >>> dict_1 = {1: {2}, 2: {3}, 3: set()}
    >>> dict_2 = {1: {42}, 3: {17}, 4: {5, 6}}
    >>> merge_dict_of_sets(dict_1, dict_2)
    {1: {2, 42}, 2: {3}, 3: {17}, 4: {5, 6}}

    :param dict_1: First dict to merge.
    :param dict_2: Second dict to merge.
    :return: The merged dictionary.
    """
    result = {**dict_1, **dict_2}
    for key in result:
        if key in dict_1 and key in dict_2:
            result[key] = dict_1[key] | dict_2[key]
    return result


def merge_intervals(
    *list_of_maybe_intervals: Maybe[List[Tuple[int, int]]]
) -> Maybe[List[Tuple[int, int]]]:
    """
    Merges a sequence of potential lists of intervals. Intervals are sorted, directly
    neighboring and overlapping ones are merged. If any list is not present, a
    :code:`Nothing` is returned.

    >>> merge_intervals(*[Some([(1, 2)]), Some([(3, 4), (0, 1)])])
    <Some: [(0, 4)]>

    >>> merge_intervals(*[Some([(1, 2)]), Some([(4, 5), (0, 1)])])
    <Some: [(0, 2), (4, 5)]>

    >>> from returns.maybe import Nothing
    >>> merge_intervals(*[Some([(1, 2)]), Nothing, Some([(3, 4), (0, 1)])])
    <Nothing>

    :param list_of_maybe_intervals: The sequence of potential lists of intervals.
    :return: A potential list of intervals.
    """

    maybe_list_of_intervals: Maybe[List[Tuple[int, int]]] = reduce(
        lambda acc, maybe_intervals: acc.bind(
            lambda list_of_intervals: maybe_intervals.bind(
                lambda other_list_of_intervals: Some(
                    list_of_intervals + other_list_of_intervals
                )
            )
        ),
        list_of_maybe_intervals,
    )

    def merge_two_intervals(
        i1: Tuple[int, int], i2: Tuple[int, int]
    ) -> List[Tuple[int, int]]:
        assert i1[0] <= i2[0], "Assumed sorted intervals"

        if i1[1] + 1 < i2[0]:
            # Separated intervals
            return [i1, i2]

        # Overlapping intervals:
        # (1, 4), (5, 7) -> (1, 7)
        # (1, 4), (2, 5) -> (1, 5)
        # (1, 4), (2, 3) -> (1, 4)
        return [(i1[0], max(i1[1], i2[1]))]

    return maybe_list_of_intervals.map(
        lambda list_of_intervals: reduce(
            lambda acc, interval: (
                [interval]
                if not acc
                else (acc[:-1] + merge_two_intervals(acc[-1], interval))
            ),
            sorted(list_of_intervals, key=lambda interval: interval[0]),
            [],
        )
    )


def deep_str(obj: Any) -> str:
    """
    This function computes a "deep" string representation of :code:`obj`. This means
    that it also (recursively) invokes :code:`__str__` on all the elements of a list,
    tuple, set, OrderedSet, dict, or Success/Failure container (from the returns
    library).

    Example:
    --------

    We constuct a simple class with different :code:`__str__` and :code:`__repr__`
    implementations:

    >>> class X:
    ...     def __str__(self):
    ...         return "'An X'"
    ...     def __repr__(self):
    ...         return "X()"

    Invoking :code:`str` returns a "shallow" string representation:

    >>> str((X(), X()))
    '(X(), X())'

    Invoking :code:`deep_str` also converts the elements of the tuple to a string:

    >>> deep_str((X(), X()))
    "('An X', 'An X')"

    This also works for nested collections, such as a tuple in a list:

    >>> deep_str([(X(),)])
    "[('An X',)]"

    It also works for dictionaries...

    >>> deep_str({X(): [X()]})
    "{'An X': ['An X']}"

    ...frozen dictionaries...

    >>> deep_str(frozendict({X(): [X()]}))
    "{'An X': ['An X']}"

    ...sets...

    >>> deep_str({(X(),)})
    "{('An X',)}"

    ...frozen sets...

    >>> deep_str(frozenset({(X(),)}))
    "{('An X',)}"

    ...and ordered sets.

    >>> deep_str(OrderedSet({(X(),)}))
    "{('An X',)}"

    As a special gimick, the function also works for the returns library's Success
    and Failure containers:

    >>> deep_str(returns.result.Success([X(), X()]))
    "<Success: ['An X', 'An X']>"

    >>> deep_str(returns.result.Failure([X(), X()]))
    "<Failure: ['An X', 'An X']>"

    If the string representation of an object is empty, its :code:`repr` is returned:

    >>> str(StopIteration())
    ''

    >>> deep_str(StopIteration())
    'StopIteration()'

    :param obj: The object to recursively convert into a string.
    :return: A "deep" string representation of :code:`obj`.
    """

    if isinstance(obj, tuple):
        return (
            "(" + ", ".join(map(deep_str, obj)) + ("," if len(obj) == 1 else "") + ")"
        )
    elif isinstance(obj, list):
        return "[" + ", ".join(map(deep_str, obj)) + "]"
    elif (
        isinstance(obj, set)
        or isinstance(obj, OrderedSet)
        or isinstance(obj, frozenset)
    ):
        return "{" + ", ".join(map(deep_str, obj)) + "}"
    elif isinstance(obj, dict) or isinstance(obj, frozendict):
        return (
            "{"
            + ", ".join([f"{deep_str(a)}: {deep_str(b)}" for a, b in obj.items()])
            + "}"
        )
    elif isinstance(obj, Maybe):
        match obj:
            case Some(elem):
                return str(Some(deep_str(elem)))
            case returns.maybe.Nothing:
                return str(obj)
    elif isinstance(obj, Result):
        match obj:
            case Success(inner):
                return str(Success(deep_str(inner)))
            case returns.result.Failure(inner):
                return str(Failure(deep_str(inner)))
    elif not str(obj):
        return repr(obj)
    else:
        return str(obj)
