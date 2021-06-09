import copy
from typing import Optional, Set, Callable, Generator, Tuple, List, Dict, Union

import pyswip.easy
import z3
from fuzzingbook.GrammarFuzzer import GrammarFuzzer, all_terminals
from fuzzingbook.Grammars import unreachable_nonterminals, is_nonterminal
import input_constraints.prolog_structs as pl
import input_constraints.prolog_shortcuts as psc

from input_constraints.type_defs import Path, ParseTree, Grammar, CanonicalGrammar


def traverse_tree(tree: ParseTree, action: Callable[[Path, ParseTree], None]) -> None:
    for path, subtree in path_iterator(tree):
        action(path, subtree)


def path_iterator(tree: ParseTree, path: Path = ()) -> Generator[Tuple[Path, ParseTree], None, None]:
    yield path, tree
    for i, child in enumerate(tree[1]):
        yield from path_iterator(child, path + (i,))


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


def replace_tree_path(in_tree: ParseTree, path: Path, replacement_tree: ParseTree) -> ParseTree:
    """Returns a symbolic input with a new tree where replacement_tree has been inserted at `path`"""

    def recurse(_tree, _path):
        node, children = _tree

        if not _path:
            return replacement_tree

        head = _path[0]
        new_children = (children[:head] +
                        [recurse(children[head], _path[1:])] +
                        children[head + 1:])

        return node, new_children

    return recurse(in_tree, path)


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
    """Returns the next path in the tree; does not proceed towards leaves!"""
    if not path:
        return None

    node, children = get_subtree(path[:-1], tree)
    if len(children) > path[-1] + 1:
        return path[:-1] + (path[-1] + 1,)
    else:
        return next_path(path[:-1], tree)


def prev_path_complete(path: Path, tree: ParseTree) -> Optional[Path]:
    """
    Returns the previous path in the tree. Repeated calls result in an iterator over
    the paths in the tree (in reverse order), unlike next_path.
    """
    if not path:
        return None

    if path[-1] - 1 >= 0:
        new_path = path[:-1] + (path[-1] - 1,)
        # Proceed right-most leave
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


def dfs(tree: ParseTree, action=print):
    node, children = tree
    action(tree)
    for child in children:
        dfs(child, action)


def geometric_sequence(length: int, base: float = 1.1) -> List[int]:
    return list(map(lambda x: 1.1 ** x, range(0, length)))


def is_canonical_grammar(grammar: Union[Grammar, CanonicalGrammar]) -> bool:
    return type(next(item[1] for item in grammar.items())[0]) is list


def pyswip_var_mapping(inp,
                       mapping: Optional[Dict[pyswip.easy.Variable, str]] = None) -> Dict[pyswip.easy.Variable, str]:
    if mapping is None:
        mapping = {}

    if type(inp) is pyswip.easy.Variable:
        inp: pyswip.easy.Variable
        if inp.chars is None:
            if not any(v for v in mapping if v == inp):
                mapping[inp] = f"_{inp.handle}"
        else:
            mapping[inp] = inp.chars

    elif type(inp) is list:
        inp: List
        for elem in inp:
            pyswip_var_mapping(elem, mapping)
    elif type(inp) is dict:
        inp: Dict
        for key in inp:
            pyswip_var_mapping(key, mapping)
            pyswip_var_mapping(inp[key], mapping)

    return mapping


def pyswip_clp_constraints_to_str(inp: List, var_name_mapping: Dict[pyswip.easy.Variable, str]) -> str:
    result = []
    constraint: pyswip.easy.Functor

    for constraint in inp:
        assert constraint.args[0].value == "clpfd"
        variable: pyswip.easy.Variable = constraint.args[1].args[0]
        variable_str = [var_name_mapping[v] for v in var_name_mapping if v == variable][0]

        if type(constraint.args[1]) is pyswip.easy.Functor:
            constraint_name = constraint.args[1].name.chars
            if constraint_name in ["#\\=", "#=="]:
                other_variable: pyswip.easy.Variable = constraint.args[1].args[1]
                other_variable_str = [var_name_mapping[v] for v in var_name_mapping if v == other_variable][0]
                result.append(f"{variable_str} {constraint_name} {other_variable_str}")
                continue

        functor: pyswip.easy.Functor = constraint.args[1].args[1]
        functor_name = functor.name.chars
        if functor_name == "..":
            range: List[int] = functor.args
            result.append(f"{variable_str} in {range[0]}..{range[1]}")
            continue

        raise NotImplementedError(f"Don't know how to translate constraint {constraint}")

    return ", ".join(result)


def pyswip_output_to_python(inp, var_name_mapping: Optional[Dict[pyswip.easy.Variable, str]] = None) \
        -> Union[str, List, Tuple]:
    if type(inp) is pyswip.easy.Functor and str(inp.name) == "-":
        inp: pyswip.easy.Functor
        return tuple(pyswip_output_to_python(child) for child in inp.args)
    elif type(inp) is list:
        return [pyswip_output_to_python(child) for child in inp]
    elif type(inp) is bytes:
        inp: bytes
        return inp.decode("utf-8")
    elif type(inp) is pyswip.easy.Atom:
        return str(inp)
    elif (type(inp) is str or type(inp) is bytes or type(inp) is int
          or type(inp) is pyswip.easy.Variable):
        return pyswip_output_to_str(inp, var_name_mapping)


def pyswip_output_to_str(inp, var_name_mapping: Optional[Dict[pyswip.easy.Variable, str]] = None) -> str:
    if type(inp) is str:
        return inp
    elif type(inp) is bytes:
        inp: bytes
        return f'"{inp.decode("utf-8")}"'
    elif type(inp) is int:
        inp: int
        return str(inp)
    elif type(inp) is pyswip.easy.Functor:
        assert False
    elif type(inp) is pyswip.easy.Variable:
        inp: pyswip.easy.Variable
        if inp.chars is None:
            assert var_name_mapping is not None
            matching_names = [var_name_mapping[v] for v in var_name_mapping if v == inp]
            assert matching_names
            return matching_names[0]
        else:
            return inp.chars
    elif type(inp) is pyswip.easy.Atom:
        inp: pyswip.easy.Atom
        return f"'{inp.value}'"
    elif type(inp) is list:
        inp: List
        return "[" + ", ".join([pyswip_output_to_str(child, var_name_mapping) for child in inp]) + "]"


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
