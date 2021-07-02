from typing import Dict, List, Optional, Union, Tuple

import pyswip.easy
from fuzzingbook.Grammars import is_nonterminal

from input_constraints import prolog_structs as pl, prolog_shortcuts as psc
from input_constraints.type_defs import ParseTree


def pyswip_clp_constraint_to_str(constraint: pyswip.easy.Functor,
                                 var_name_mapping: Dict[pyswip.easy.Variable, str]) -> str:
    assert constraint.args[0].value == "clpfd"
    variable: pyswip.easy.Variable = constraint.args[1].args[0]
    variable_str = [var_name_mapping[v] for v in var_name_mapping if v == variable][0]

    if type(constraint.args[1]) is pyswip.easy.Functor:
        constraint_name = constraint.args[1].name.chars
        if constraint_name in ["#\\=", "#=="]:
            other_variable: pyswip.easy.Variable = constraint.args[1].args[1]
            other_variable_str = [var_name_mapping[v] for v in var_name_mapping if v == other_variable][0]
            return f"{variable_str} {constraint_name} {other_variable_str}"

    functor: pyswip.easy.Functor = constraint.args[1].args[1]
    functor_name = functor.name.chars
    if functor_name == "..":
        range: List[int] = functor.args
        return f"{variable_str} in {range[0]}..{range[1]}"

    raise NotImplementedError(f"Don't know how to translate constraint {constraint}")


def pyswip_clp_constraints_to_str(inp: List[pyswip.easy.Functor],
                                  var_name_mapping: Dict[pyswip.easy.Variable, str]) -> str:
    return ", ".join([pyswip_clp_constraint_to_str(constraint, var_name_mapping) for constraint in inp])


def pyswip_output_to_python(inp, var_name_mapping: Optional[Dict[pyswip.easy.Variable, str]] = None) \
        -> Union[str, List, Tuple]:
    if type(inp) is pyswip.easy.Functor and str(inp.name) == "-":
        inp: pyswip.easy.Functor
        return tuple(pyswip_output_to_python(child, var_name_mapping) for child in inp.args)
    elif type(inp) is list:
        return [pyswip_output_to_python(child, var_name_mapping) for child in inp]
    elif (type(inp) is str or
          type(inp) is bytes or
          type(inp) is int or
          type(inp) is pyswip.easy.Variable or
          type(inp) is pyswip.easy.Atom):
        return pyswip_output_to_str(inp, var_name_mapping)
    elif type(inp) is pyswip.easy.Functor:
        return pyswip_clp_constraint_to_str(inp, var_name_mapping)

    assert False, f"Type {type(inp)} not supported by function pyswip_output_to_python"


def pyswip_output_to_str(inp, var_name_mapping: Optional[Dict[pyswip.easy.Variable, str]] = None) -> str:
    if type(inp) is str:
        return f'"{inp}"'
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
    elif type(inp) is pyswip.easy.Functor:
        inp: pyswip.easy.Functor
        for arg in inp.args:
            pyswip_var_mapping(arg, mapping)

    return mapping


def python_list_to_prolog_list(l: Union[List, Tuple]) -> pl.ListTerm:
    if not l:
        return psc.list_term()

    def convert_elem(elem: Union[int, str, Tuple, List]) -> pl.Term:
        if type(elem) is int:
            return pl.Number(elem)
        elif type(elem) is str:
            return pl.StringTerm(elem)
        elif type(elem) is list or type(elem) is tuple:
            return python_list_to_prolog_list(elem)

    return psc.list_term(*[convert_elem(elem) for elem in l])


def python_to_prolog_tree(tree: ParseTree) -> pl.ListTerm:
    node, children = tree

    if children is None:
        return psc.list_term(var_to_pl_nsym(node), psc.anon_var())
    elif not children:
        return psc.list_term(pl.StringTerm(node), psc.list_term())
    else:
        return psc.list_term(pl.Atom(node[1:-1]), psc.list_term(*[python_to_prolog_tree(child) for child in children]))


def var_to_pl_nsym(variable):
    # variable is either isla.Variable (not imported to avoid circular inputs) or str
    ntype = variable if type(variable) is str else variable.n_type
    if is_nonterminal(ntype):
        return pl.Atom(ntype[1:-1].lower())
    else:
        return pl.StringTerm(ntype)