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
import random
from typing import Union, List, Optional, Dict, Tuple, Callable

from grammar_graph.gg import GrammarGraph

from isla import language
from isla.derivation_tree import DerivationTree
from isla.existential_helpers import insert_tree, DIRECT_EMBEDDING, SELF_EMBEDDING
from isla.helpers import (
    delete_unreachable,
    parent_reflexive,
    parent_or_child,
    is_nonterminal,
    canonical,
    Maybe,
    chain_functions,
)
from isla.language import (
    SemPredEvalResult,
    StructuralPredicate,
    SemanticPredicate,
    Variable,
)
from isla.parser import EarleyParser
from isla.type_defs import Grammar, Path, ParseTree


def is_before(_: Optional[DerivationTree], path_1: Path, path_2: Path) -> bool:
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
        return is_before(_, tuple(cdr_1), tuple(cdr_2))


BEFORE_PREDICATE = StructuralPredicate("before", 2, is_before)


def is_after(_: DerivationTree, path_1: Path, path_2: Path) -> bool:
    return (
        not is_before(_, path_1, path_2) and path_1 != path_2[: len(path_1)]
    )  # No prefix


AFTER_PREDICATE = StructuralPredicate("after", 2, is_after)


def is_same_position(_: Optional[DerivationTree], path_1: Path, path_2: Path) -> bool:
    return path_1 == path_2


def is_different_position(
    _: Optional[DerivationTree], path_1: Path, path_2: Path
) -> bool:
    return not is_same_position(_, path_1, path_2)


DIFFERENT_POSITION_PREDICATE = StructuralPredicate(
    "different_position", 2, is_different_position
)

SAME_POSITION_PREDICATE = StructuralPredicate("same_position", 2, is_same_position)


def is_nth(tree: DerivationTree, n: int | str, path_1: Path, path_2: Path) -> bool:
    # The tree at path_1 is the `n`-th occurrence of nonterminal `nonterminal`
    # within the tree at path_2.
    if not in_tree(None, path_1, path_2):
        return False

    assert isinstance(n, int) or n.isnumeric()

    nonterminal = tree.get_subtree(path_1).value
    assert is_nonterminal(nonterminal)

    match_idx = 0
    for path, subtree in tree.get_subtree(path_2).paths():
        if subtree.value == nonterminal:
            match_idx += 1

        if path_2 + path == path_1:
            return match_idx == int(n)

        if match_idx >= int(n):
            return False

    return False


NTH_PREDICATE = StructuralPredicate("nth", 3, is_nth)


def in_tree(_: Optional[DerivationTree], path_1: Path, path_2: Path) -> bool:
    # path_1 is inside path_2
    return path_1[: len(path_2)] == path_2


IN_TREE_PREDICATE = StructuralPredicate("inside", 2, in_tree)


def consecutive(tree: DerivationTree, path_1: Path, path_2: Path) -> bool:
    # This predicate holds for two consecutive leaves, i.e.,
    # which are not interrupted by any other tree leaves.
    assert tree is not None

    if path_1 == path_2 or not is_before(None, path_1, path_2):
        return False

    longest_common_prefix: Path = max(
        [
            path_1[:idx]
            for idx in range(max([len(path_1), len(path_2)]))
            if path_1[:idx] == path_2[:idx]
        ],
        key=len,
    )

    return not any(
        path != path_1
        and path != path_2
        and is_before(None, path_1, path)
        and is_before(None, path, path_2)
        for path, _ in tree.get_subtree(longest_common_prefix).leaves()
    )


CONSECUTIVE_PREDICATE = StructuralPredicate("consecutive", 2, consecutive)


def level_check(  # noqa: C901
    context_tree: DerivationTree,
    pred: str,
    nonterminal: str,
    path_1: Path,
    path_2: Path,
) -> bool:
    assert pred in ["EQ", "GE", "LE", "GT", "LT"]

    # There has to be a common prefix of both paths pointing to a `nonterminal` node, such that
    #
    # EQ: the remaining path fragments do not point to any `nonterminal` node.
    # GE: the remaining path fragment for `arg_1` does not point to any `nonterminal` nodes.
    # LE: the remaining path fragment for `arg_2` does not point to any `nonterminal` nodes.
    # GT: the remaining path fragment for `arg_1` does not point to any `nonterminal` nodes,
    #     and the remaining path fragment for `arg_2` points to at least one `nonterminal` node.
    # LT: the remaining path fragment for `arg_2` does not point to any `nonterminal` nodes,
    #     and the remaining path fragment for `arg_1` points to at least one `nonterminal` node.

    # It is also possible to be outside of any `nonterminal` scope; then, the arguments may still be
    # at the same of different levels. So, we also consider the empty prefix.
    common_nonterminal_prefixes: List[Path] = [tuple()]
    for idx in range(min(len(path_1), len(path_2))):
        if path_1[idx] != path_2[idx]:
            break

        prefix = path_1[:idx]
        if context_tree.get_subtree(prefix).value == nonterminal:
            common_nonterminal_prefixes.append(prefix)

    for prefix in common_nonterminal_prefixes:
        nonterminal_occs_1, nonterminal_occs_2 = [
            [
                path[:idx]
                for idx in range(len(prefix) + 1, len(path))
                if context_tree.get_subtree(path[:idx]).value == nonterminal
            ]
            for path in [path_1, path_2]
        ]

        if pred == "EQ":
            if not nonterminal_occs_1 and not nonterminal_occs_2:
                return True
        elif pred == "GE":
            if not nonterminal_occs_1:
                return True
        elif pred == "LE":
            if not nonterminal_occs_2:
                return True
        elif pred == "GT":
            if not nonterminal_occs_1 and nonterminal_occs_2:
                return True
        elif pred == "LT":
            if not nonterminal_occs_2 and nonterminal_occs_1:
                return True

    return False


LEVEL_PREDICATE = StructuralPredicate("level", 4, level_check)


def reachable(graph: GrammarGraph, fr: str, to: str) -> bool:
    f_node = graph.get_node(fr)
    t_node = graph.get_node(to)
    return graph.reachable(f_node, t_node)


def count(  # noqa: C901
    graph: GrammarGraph,
    in_tree: DerivationTree,
    needle: str,
    num: Variable | DerivationTree,
    negate: bool = False,
) -> SemPredEvalResult:
    if isinstance(in_tree, Variable):
        return SemPredEvalResult(None)

    num_needle_occurrences = len(in_tree.filter(lambda t: t.value == needle))

    leaf_nonterminals = [node.value for _, node in in_tree.open_leaves()]

    more_needles_possible = any(
        reachable(graph, leaf_nonterminal, needle)
        for leaf_nonterminal in leaf_nonterminals
    )

    if isinstance(num, Variable):
        # Return the number of needle occurrences in in_tree, or "not ready" if in_tree is not
        # closed and more needle occurrences can yet occur in in_tree
        if more_needles_possible:
            return SemPredEvalResult(None)

        if negate:
            result_num = random.choice(
                [i for i in range(15) if i != num_needle_occurrences]
            )
        else:
            result_num = num_needle_occurrences

        return SemPredEvalResult({num: DerivationTree(str(result_num), None)})

    if isinstance(num, str):
        num_value = num
    else:
        assert isinstance(num, DerivationTree)
        assert not num.children
        num_value = num.value

    try:
        target_num_needle_occurrences = int(num_value)
    except ValueError:
        assert False, f"Value {num.value} cannot be converted to an integer."

    if (
        target_num_needle_occurrences < 0
        or num_needle_occurrences > target_num_needle_occurrences
    ):
        return SemPredEvalResult(False)

    if not more_needles_possible:
        # TODO: We could also try to insert needle into already closed parts of the tree,
        #       similar to treatment of existential quantifiers...
        if num_needle_occurrences == target_num_needle_occurrences:
            return SemPredEvalResult(True)
        else:
            return SemPredEvalResult(False)

    if (
        more_needles_possible
        and num_needle_occurrences == target_num_needle_occurrences
    ):
        return SemPredEvalResult(None)

    if negate:
        try:
            target_num_needle_occurrences = random.choice(
                [
                    i
                    for i in range(
                        num_needle_occurrences + 1, target_num_needle_occurrences + 1
                    )
                    if i != target_num_needle_occurrences
                ]
            )
        except IndexError:
            return SemPredEvalResult(True)

    assert num_needle_occurrences < target_num_needle_occurrences

    # Try to add more needles to in_tree, such that no more needles can be obtained
    # in the resulting tree from expanding leaf nonterminals.

    def num_needles(candidate):
        return len(candidate.filter(lambda t: t.value == needle))

    canonical_grammar = canonical(graph.to_grammar())
    candidates = [
        candidate
        for candidate in insert_tree(
            canonical_grammar,
            DerivationTree(needle, None),
            in_tree,
            graph=graph,
            methods=DIRECT_EMBEDDING | SELF_EMBEDDING,
        )
        if num_needles(candidate) <= target_num_needle_occurrences
    ]
    already_seen = {candidate.structural_hash() for candidate in candidates}
    while candidates:
        candidate = candidates.pop(0)
        candidate_needle_occurrences = num_needles(candidate)

        candidate_more_needles_possible = any(
            reachable(graph, leaf_nonterminal, needle)
            for leaf_nonterminal in [node.value for _, node in candidate.open_leaves()]
        )

        if (
            not candidate_more_needles_possible
            and candidate_needle_occurrences == target_num_needle_occurrences
        ):
            return SemPredEvalResult({in_tree: candidate})

        if candidate_needle_occurrences < target_num_needle_occurrences:
            new_candidates = [
                new_candidate
                for new_candidate in insert_tree(
                    canonical_grammar,
                    DerivationTree(needle, None),
                    candidate,
                    graph=graph,
                    methods=DIRECT_EMBEDDING | SELF_EMBEDDING,
                )
                if (
                    num_needles(new_candidate) <= target_num_needle_occurrences
                    and not new_candidate.structural_hash() in already_seen
                )
            ]

            candidates.extend(new_candidates)
            already_seen.update(
                {new_candidate.structural_hash() for new_candidate in new_candidates}
            )

    return SemPredEvalResult(False)


COUNT_PREDICATE = SemanticPredicate("count", 3, count, binds_tree=True)


def embed_tree(
    orig: DerivationTree,
    extended: DerivationTree,
    leaves_to_match: Optional[Tuple[Path, ...]] = None,
    path_combinations: Optional[
        Tuple[Tuple[Tuple[Path, DerivationTree], Tuple[Path, DerivationTree]], ...]
    ] = None,
) -> Tuple[Dict[Path, Path], ...]:
    if path_combinations is None:
        assert leaves_to_match is None
        leaves_to_match = [path for path, _ in orig.leaves()]

        path_combinations = [
            ((orig_path, orig_tree), (extended_path, extended_tree))
            for orig_path, orig_tree in orig.paths()
            for extended_path, extended_tree in extended.paths()
            if orig_tree.structural_hash() == extended_tree.structural_hash()
        ]

    if not path_combinations:
        return

    (
        (orig_path, orig_subtree),
        (extended_path, extended_subtree),
    ), *remaining_combinations = path_combinations

    yield from embed_tree(orig, extended, leaves_to_match, remaining_combinations)

    remaining_leaves_to_match = tuple(
        path for path in leaves_to_match if not parent_reflexive(orig_path, path)
    )

    remaining_combinations = tuple(
        combination
        for combination in remaining_combinations
        if (
            other_orig_path := combination[0][0],
            other_extended_path := combination[1][0],
            not parent_or_child(orig_path, other_orig_path)
            and not parent_or_child(extended_path, other_extended_path),
        )[-1]
    )

    if not remaining_leaves_to_match:
        assert not remaining_combinations
        yield {extended_path: orig_path}
        return

    for assignment in embed_tree(
        orig, extended, remaining_leaves_to_match, remaining_combinations
    ):
        yield assignment | {extended_path: orig_path}


def crop(
    mk_parser: Callable[[str], Callable[[str], List[ParseTree]]],
    tree: DerivationTree,
    width: Variable | DerivationTree,
) -> SemPredEvalResult:
    if not tree.is_complete():
        return SemPredEvalResult(None)

    unparsed = str(tree)

    if isinstance(width, Variable):
        return SemPredEvalResult({width: DerivationTree(str(len(unparsed)), None)})

    assert isinstance(width, DerivationTree)
    if not width.is_complete():
        return SemPredEvalResult(None)

    width = int(str(width))

    if len(unparsed) <= width:
        return SemPredEvalResult(True)

    parser = mk_parser(tree.value)
    result = DerivationTree.from_parse_tree(parser(unparsed[:width])[0]).get_subtree(
        (0,)
    )
    return SemPredEvalResult({tree: result})


def just(
    ljust: bool,
    crop: bool,
    mk_parser: Callable[[str], Callable[[str], List[ParseTree]]],
    tree: DerivationTree,
    width: Union[int, DerivationTree],
    fill_char: Optional[str] = None,
) -> SemPredEvalResult:
    if not tree.is_complete():
        return SemPredEvalResult(None)

    unparsed = str(tree)

    if isinstance(width, Variable):
        return SemPredEvalResult({width: DerivationTree(str(len(unparsed)), None)})

    if fill_char is None:
        assert len(unparsed) > 0
        assert unparsed == unparsed[0].ljust(len(unparsed), unparsed[0])
        fill_char = unparsed[0]

    if len(fill_char) != 1:
        raise TypeError("The fill character must be exactly one character long")

    assert isinstance(width, DerivationTree) or isinstance(width, int)
    if isinstance(width, DerivationTree):
        if not width.is_complete():
            return SemPredEvalResult(None)

        width = int(str(width))

    if len(unparsed) == width:
        return SemPredEvalResult(True)

    parser = mk_parser(tree.value)

    unparsed_output = (
        unparsed.ljust(width, fill_char) if ljust else unparsed.rjust(width, fill_char)
    )

    assert crop or len(unparsed_output) == width

    if crop:
        unparsed_output = (
            unparsed_output[:width]
            if ljust
            else unparsed_output[len(unparsed_output) - width :]
        )

    result = DerivationTree.from_parse_tree(parser(unparsed_output)[0]).get_subtree(
        (0,)
    )

    return SemPredEvalResult({tree: result})


def mk_parser(grammar: Grammar):
    def Parser(start: str) -> Callable[[str], List[ParseTree]]:
        specialized_grammar = copy.deepcopy(grammar)
        specialized_grammar["<start>"] = [start]
        delete_unreachable(specialized_grammar)
        parser = EarleyParser(specialized_grammar)

        def result(inp: str) -> List[ParseTree]:
            return list(parser.parse(inp))

        return result

    return Parser


CROP_PREDICATE = SemanticPredicate(
    "crop",
    2,
    lambda graph, tree, width: crop(mk_parser(graph.grammar), tree, width),
    binds_tree=False,
)

LJUST_PREDICATE = SemanticPredicate(
    "ljust",
    3,
    lambda graph, tree, width, fillchar: just(
        True, False, mk_parser(graph.grammar), tree, width, fillchar
    ),
    binds_tree=False,
)

LJUST_CROP_PREDICATE = SemanticPredicate(
    "ljust_crop",
    3,
    lambda graph, tree, width, fillchar: just(
        True, True, mk_parser(graph.grammar), tree, width, fillchar
    ),
    binds_tree=False,
)

EXTEND_CROP_PREDICATE = SemanticPredicate(
    "extend_crop",
    2,
    lambda graph, tree, width: just(True, True, mk_parser(graph.grammar), tree, width),
    binds_tree=False,
)

RJUST_PREDICATE = SemanticPredicate(
    "rjust",
    3,
    lambda graph, tree, width, fillchar: just(
        False, False, mk_parser(graph.grammar), tree, width, fillchar
    ),
    binds_tree=False,
)

RJUST_CROP_PREDICATE = SemanticPredicate(
    "rjust_crop",
    3,
    lambda graph, tree, width, fillchar: just(
        False, True, mk_parser(graph.grammar), tree, width, fillchar
    ),
    binds_tree=False,
)


def octal_to_dec(
    _octal_parser: Callable[[str], List[ParseTree]],
    _decimal_parser: Callable[[str], List[ParseTree]],
    octal: language.Variable | DerivationTree,
    decimal: language.Variable | DerivationTree,
) -> SemPredEvalResult:
    assert not isinstance(octal, language.Variable) or not isinstance(
        decimal, language.Variable
    )

    def decimal_parser(inp):
        return DerivationTree.from_parse_tree(_decimal_parser(inp)[0][1][0])

    def octal_parser(inp):
        return DerivationTree.from_parse_tree(_octal_parser(inp)[0][1][0])

    monad = chain_functions(
        [
            octal_to_dec_concrete_octal,
            octal_to_dec_concrete_decimal,
            octal_to_dec_both_trees,
        ],
        octal,
        decimal,
        octal_parser,
        decimal_parser,
    )

    if not monad.is_present():
        raise NotImplementedError(
            f'Could not convert between octal "{octal}" and decimal "{decimal}"'
        )
    return monad.get()


def octal_to_dec_concrete_octal(
    octal: language.Variable | DerivationTree,
    decimal: language.Variable | DerivationTree,
    _,
    decimal_parser,
) -> Maybe[SemPredEvalResult]:
    if (
        not isinstance(octal, DerivationTree)
        or not isinstance(decimal, language.Variable)
        and decimal.is_complete()
    ):
        return Maybe.nothing()

    if not octal.is_complete():
        return Maybe(SemPredEvalResult(None))

    # Conversion to decimal
    octal_str = str(octal)

    decimal_number = 0
    for idx, digit in enumerate(reversed(octal_str)):
        decimal_number += (8**idx) * int(digit)

    return Maybe(SemPredEvalResult({decimal: decimal_parser(str(decimal_number))}))


def octal_to_dec_concrete_decimal(
    octal: language.Variable | DerivationTree,
    decimal: language.Variable | DerivationTree,
    octal_parser,
    _,
) -> Maybe[SemPredEvalResult]:
    if (
        not isinstance(decimal, DerivationTree)
        or not isinstance(octal, language.Variable)
        and octal.is_complete()
    ):
        return Maybe.nothing()

    if not decimal.is_complete():
        return Maybe(SemPredEvalResult(None))

    # Conversion to octal
    decimal_number = int(str(decimal))
    octal_str = oct(decimal_number)[2:]

    return Maybe(SemPredEvalResult({octal: octal_parser(octal_str)}))


def octal_to_dec_both_trees(
    octal: language.Variable | DerivationTree,
    decimal: language.Variable | DerivationTree,
    _1,
    _2,
) -> Maybe[SemPredEvalResult]:
    if not isinstance(decimal, DerivationTree) or not isinstance(octal, DerivationTree):
        return Maybe.nothing()

    if not decimal.is_complete() or not octal.is_complete():
        return Maybe(SemPredEvalResult(None))

    decimal_number = int(str(decimal))
    octal_number = int(str(octal))

    return Maybe(SemPredEvalResult(int(oct(octal_number)[2:]) == decimal_number))


def OCTAL_TO_DEC_PREDICATE(graph, octal_start, decimal_start):
    return SemanticPredicate(
        "octal_to_decimal",
        2,
        lambda _, octal, decimal: octal_to_dec(
            mk_parser(graph.grammar)(octal_start),
            mk_parser(graph.grammar)(decimal_start),
            octal,
            decimal,
        ),
        binds_tree=False,
    )


def is_direct_child(_: Optional[DerivationTree], path_1: Path, path_2: Path) -> bool:
    # Returns true iff `path_1` is a direct child of `path_2`
    if len(path_1) != len(path_2) + 1:
        return False

    return path_1[: len(path_2)] == path_2


DIRECT_CHILD_PREDICATE = StructuralPredicate("direct_child", 2, is_direct_child)

STANDARD_STRUCTURAL_PREDICATES = {
    AFTER_PREDICATE,
    BEFORE_PREDICATE,
    CONSECUTIVE_PREDICATE,
    DIFFERENT_POSITION_PREDICATE,
    DIRECT_CHILD_PREDICATE,
    IN_TREE_PREDICATE,
    LEVEL_PREDICATE,
    SAME_POSITION_PREDICATE,
    NTH_PREDICATE,
}

STANDARD_SEMANTIC_PREDICATES = {
    COUNT_PREDICATE,
}
