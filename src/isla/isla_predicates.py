import copy
import random
from typing import Union, List, Optional, Dict, Tuple, Callable

from grammar_graph.gg import GrammarGraph

from isla import language
from isla.existential_helpers import insert_tree, DIRECT_EMBEDDING, SELF_EMBEDDING
from isla.helpers import delete_unreachable, parent_reflexive, parent_or_child, is_nonterminal, \
    canonical
from isla.language import SemPredEvalResult, StructuralPredicate, SemanticPredicate, Variable
from isla.derivation_tree import DerivationTree
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
    return (not is_before(_, path_1, path_2)
            and path_1 != path_2[:len(path_1)])  # No prefix


AFTER_PREDICATE = StructuralPredicate("after", 2, is_after)


def is_same_position(_: Optional[DerivationTree], path_1: Path, path_2: Path) -> bool:
    return path_1 == path_2


def is_different_position(_: Optional[DerivationTree], path_1: Path, path_2: Path) -> bool:
    return not is_same_position(_, path_1, path_2)


DIFFERENT_POSITION_PREDICATE = StructuralPredicate("different_position", 2, is_different_position)

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
    return path_1[:len(path_2)] == path_2


IN_TREE_PREDICATE = StructuralPredicate("inside", 2, in_tree)


def consecutive(tree: DerivationTree, path_1: Path, path_2: Path) -> bool:
    # This predicate holds for two consecutive leaves, i.e.,
    # which are not interrupted by any other tree leaves.
    assert tree is not None

    if path_1 == path_2 or not is_before(None, path_1, path_2):
        return False

    longest_common_prefix: Path = max(
        [path_1[:idx] for idx in range(max([len(path_1), len(path_2)])) if path_1[:idx] == path_2[:idx]],
        key=len
    )

    return not any(
        path != path_1 and path != path_2 and
        is_before(None, path_1, path) and is_before(None, path, path_2)
        for path, _ in tree.get_subtree(longest_common_prefix).leaves())


CONSECUTIVE_PREDICATE = StructuralPredicate("consecutive", 2, consecutive)


def level_check(
        context_tree: DerivationTree,
        pred: str,
        nonterminal: str,
        path_1: Path,
        path_2: Path) -> bool:
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
        nonterminal_occs_1, nonterminal_occs_2 = [[
            path[:idx]
            for idx in range(len(prefix) + 1, len(path))
            if context_tree.get_subtree(path[:idx]).value == nonterminal
        ] for path in [path_1, path_2]]

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


def count(graph: GrammarGraph,
          in_tree: DerivationTree,
          needle: str,
          num: Variable | DerivationTree,
          negate: bool = False) -> SemPredEvalResult:
    if isinstance(in_tree, Variable):
        return SemPredEvalResult(None)

    num_needle_occurrences = len(in_tree.filter(lambda t: t.value == needle))

    leaf_nonterminals = [node.value for _, node in in_tree.open_leaves()]

    more_needles_possible = any(
        reachable(graph, leaf_nonterminal, needle)
        for leaf_nonterminal in leaf_nonterminals)

    if isinstance(num, Variable):
        # Return the number of needle occurrences in in_tree, or "not ready" if in_tree is not
        # closed and more needle occurrences can yet occur in in_tree
        if more_needles_possible:
            return SemPredEvalResult(None)

        if negate:
            result_num = random.choice([i for i in range(15) if i != num_needle_occurrences])
        else:
            result_num = num_needle_occurrences

        return SemPredEvalResult({num: DerivationTree(str(result_num), None)})

    assert not num.children

    try:
        target_num_needle_occurrences = int(num.value)
    except ValueError:
        assert False, f"Value {num.value} cannot be converted to integer."

    if target_num_needle_occurrences < 0 or num_needle_occurrences > target_num_needle_occurrences:
        return SemPredEvalResult(False)

    if not more_needles_possible:
        # TODO: We could also try to insert needle into already closed parts of the tree,
        #       similar to treatment of existential quantifiers...
        if num_needle_occurrences == target_num_needle_occurrences:
            return SemPredEvalResult(True)
        else:
            return SemPredEvalResult(False)

    if more_needles_possible and num_needle_occurrences == target_num_needle_occurrences:
        return SemPredEvalResult(None)

    if negate:
        try:
            target_num_needle_occurrences = random.choice([
                i for i in range(num_needle_occurrences + 1, target_num_needle_occurrences + 1)
                if i != target_num_needle_occurrences
            ])
        except IndexError:
            return SemPredEvalResult(True)

    assert num_needle_occurrences < target_num_needle_occurrences

    # Try to add more needles to in_tree, such that no more needles can be obtained
    # in the resulting tree from expanding leaf nonterminals.

    num_needles = lambda candidate: len(candidate.filter(lambda t: t.value == needle))

    canonical_grammar = canonical(graph.to_grammar())
    candidates = [candidate for candidate in insert_tree(
        canonical_grammar, DerivationTree(needle, None), in_tree, graph=graph,
        methods=DIRECT_EMBEDDING | SELF_EMBEDDING)
                  if num_needles(candidate) <= target_num_needle_occurrences]
    already_seen = {candidate.structural_hash() for candidate in candidates}
    while candidates:
        candidate = candidates.pop(0)
        candidate_needle_occurrences = num_needles(candidate)

        candidate_more_needles_possible = \
            any(reachable(graph, leaf_nonterminal, needle)
                for leaf_nonterminal in [node.value for _, node in candidate.open_leaves()])

        if not candidate_more_needles_possible and candidate_needle_occurrences == target_num_needle_occurrences:
            return SemPredEvalResult({in_tree: candidate})

        if candidate_needle_occurrences < target_num_needle_occurrences:
            new_candidates = [
                new_candidate
                for new_candidate in insert_tree(
                    canonical_grammar, DerivationTree(needle, None), candidate, graph=graph,
                    methods=DIRECT_EMBEDDING | SELF_EMBEDDING)
                if (num_needles(new_candidate) <= target_num_needle_occurrences
                    and not new_candidate.structural_hash() in already_seen)]

            candidates.extend(new_candidates)
            already_seen.update({new_candidate.structural_hash() for new_candidate in new_candidates})

    return SemPredEvalResult(False)


COUNT_PREDICATE = SemanticPredicate("count", 3, count, binds_tree=True)


def embed_tree(
        orig: DerivationTree,
        extended: DerivationTree,
        leaves_to_match: Optional[Tuple[Path, ...]] = None,
        path_combinations: Optional[Tuple[Tuple[Tuple[Path, DerivationTree], Tuple[Path, DerivationTree]], ...]] = None,
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

    ((orig_path, orig_subtree), (extended_path, extended_subtree)), *remaining_combinations = path_combinations

    yield from embed_tree(orig, extended, leaves_to_match, remaining_combinations)

    remaining_leaves_to_match = tuple(
        path for path in leaves_to_match
        if not parent_reflexive(orig_path, path)
    )

    remaining_combinations = tuple(
        combination for combination in remaining_combinations
        if (
            other_orig_path := combination[0][0],
            other_extended_path := combination[1][0],
            not parent_or_child(orig_path, other_orig_path) and
            not parent_or_child(extended_path, other_extended_path),
        )[-1]
    )

    if not remaining_leaves_to_match:
        assert not remaining_combinations
        yield {extended_path: orig_path}
        return

    for assignment in embed_tree(orig, extended, remaining_leaves_to_match, remaining_combinations):
        yield assignment | {extended_path: orig_path}


def crop(mk_parser: Callable[[str], Callable[[str], List[ParseTree]]],
         tree: DerivationTree,
         width: Union[int, DerivationTree]) -> SemPredEvalResult:
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
    result = DerivationTree.from_parse_tree(parser(unparsed[:width])[0]).get_subtree((0,))
    return SemPredEvalResult({tree: result})


def just(ljust: bool,
         crop: bool,
         mk_parser: Callable[[str], Callable[[str], List[ParseTree]]],
         tree: DerivationTree,
         width: Union[int, DerivationTree],
         fill_char: Optional[str] = None) -> SemPredEvalResult:
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

    unparsed_output = unparsed.ljust(width, fill_char) if ljust else unparsed.rjust(width, fill_char)

    assert crop or len(unparsed_output) == width

    if crop:
        unparsed_output = unparsed_output[:width] if ljust else unparsed_output[len(unparsed_output) - width:]

    result = DerivationTree.from_parse_tree(parser(unparsed_output)[0]).get_subtree((0,))

    return SemPredEvalResult({tree: result})


def mk_parser(grammar: Grammar):
    def Parser(start: str) -> Callable[[str], List[ParseTree]]:
        def result(inp: str) -> List[ParseTree]:
            specialized_grammar = copy.deepcopy(grammar)
            specialized_grammar["<start>"] = [start]
            delete_unreachable(specialized_grammar)
            parser = EarleyParser(specialized_grammar)
            return list(parser.parse(inp))

        return result

    return Parser


CROP_PREDICATE = SemanticPredicate(
    "crop", 2,
    lambda graph, tree, width: crop(mk_parser(graph.grammar), tree, width),
    binds_tree=False)

LJUST_PREDICATE = SemanticPredicate(
    "ljust", 3,
    lambda graph, tree, width, fillchar: just(True, False, mk_parser(graph.grammar), tree, width, fillchar),
    binds_tree=False)

LJUST_CROP_PREDICATE = SemanticPredicate(
    "ljust_crop", 3,
    lambda graph, tree, width, fillchar: just(True, True, mk_parser(graph.grammar), tree, width, fillchar),
    binds_tree=False)

EXTEND_CROP_PREDICATE = SemanticPredicate(
    "extend_crop", 2,
    lambda graph, tree, width: just(True, True, mk_parser(graph.grammar), tree, width),
    binds_tree=False)

RJUST_PREDICATE = SemanticPredicate(
    "rjust", 3,
    lambda graph, tree, width, fillchar: just(False, False, mk_parser(graph.grammar), tree, width, fillchar),
    binds_tree=False)

RJUST_CROP_PREDICATE = SemanticPredicate(
    "rjust_crop", 3,
    lambda graph, tree, width, fillchar: just(False, True, mk_parser(graph.grammar), tree, width, fillchar),
    binds_tree=False)


def octal_to_dec(
        _octal_parser: Callable[[str], List[ParseTree]],
        _decimal_parser: Callable[[str], List[ParseTree]],
        octal: language.Variable | DerivationTree,
        decimal: language.Variable | DerivationTree) -> SemPredEvalResult:
    assert not isinstance(octal, language.Variable) or not isinstance(decimal, language.Variable)

    decimal_parser = lambda inp: DerivationTree.from_parse_tree(_decimal_parser(inp)[0][1][0])
    octal_parser = lambda inp: DerivationTree.from_parse_tree(_octal_parser(inp)[0][1][0])

    if (isinstance(octal, DerivationTree) and
            isinstance(decimal, DerivationTree) and
            not octal.is_complete() and
            not decimal.is_complete()):
        return SemPredEvalResult(None)

    if isinstance(octal, DerivationTree) and octal.is_complete():
        # Conversion to decimal
        octal_str = str(octal)

        decimal_number = 0
        for idx, digit in enumerate(reversed(octal_str)):
            decimal_number += (8 ** idx) * int(digit)

        if isinstance(decimal, DerivationTree) and decimal_number == int(str(decimal)):
            return SemPredEvalResult(True)

        return SemPredEvalResult({decimal: decimal_parser(str(decimal_number))})

    if isinstance(decimal, DerivationTree) and decimal.is_complete():
        # Conversion to decimal
        decimal_number = int(str(decimal))

        octal_str = ""
        while decimal_number > 0:
            octal_str = str(decimal_number % 8) + octal_str
            decimal_number = decimal_number // 8

        if isinstance(octal, DerivationTree) and octal_str == str(decimal):
            return SemPredEvalResult(True)

        return SemPredEvalResult({octal: octal_parser(octal_str)})

    if isinstance(octal, language.Variable) and isinstance(decimal, DerivationTree):
        if not decimal.is_complete():
            return SemPredEvalResult(None)

        decimal_number = int(str(decimal))
        octal_str = str(oct(decimal_number))[2:]

        if isinstance(octal, DerivationTree) and octal_str == str(octal):
            return SemPredEvalResult(True)

        return SemPredEvalResult({octal: octal_parser(octal_str)})

    if isinstance(decimal, language.Variable) and isinstance(octal, DerivationTree):
        if not octal.is_complete():
            return SemPredEvalResult(None)

        decimal_str = str(int(str(octal), 8))

        if isinstance(decimal, DerivationTree) and decimal_str == str(decimal):
            return SemPredEvalResult(True)

        return SemPredEvalResult({decimal: octal_parser(decimal_str)})

    assert False


OCTAL_TO_DEC_PREDICATE = lambda graph, octal_start, decimal_start: SemanticPredicate(
    "octal_to_decimal", 2,
    lambda _, octal, decimal: octal_to_dec(
        mk_parser(graph.grammar)(octal_start),
        mk_parser(graph.grammar)(decimal_start),
        octal, decimal),
    binds_tree=False
)

STANDARD_STRUCTURAL_PREDICATES = {
    AFTER_PREDICATE,
    BEFORE_PREDICATE,
    CONSECUTIVE_PREDICATE,
    DIFFERENT_POSITION_PREDICATE,
    IN_TREE_PREDICATE,
    LEVEL_PREDICATE,
    SAME_POSITION_PREDICATE,
    NTH_PREDICATE,
}

STANDARD_SEMANTIC_PREDICATES = {
    COUNT_PREDICATE,
}
