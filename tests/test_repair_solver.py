import logging
import unittest

import pytest

from isla.derivation_tree import DerivationTree
from isla.fuzzer import GrammarCoverageFuzzer
from isla.isla_predicates import IN_TREE_PREDICATE, SAME_POSITION_PREDICATE
from isla.language import parse_bnf, parse_isla
from isla.parser import EarleyParser
from isla.repair_solver import RepairSolver
from isla_formalizations.xml_lang import (
    XML_WELLFORMEDNESS_CONSTRAINT,
    XML_NO_ATTR_REDEF_CONSTRAINT,
    XML_NAMESPACE_CONSTRAINT,
    XML_GRAMMAR,
    XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
    validate_xml,
)
from test_data import LANG_GRAMMAR

LOGGER = logging.getLogger(__name__)


class TestRepairSolver(unittest.TestCase):
    SIMPLIFIED_XML_NAMESPACE_GRAMMAR = """
<start> ::= <xml-tree>
<xml-tree> ::= "" | <xml-open-tag> <xml-tree> <xml-close-tag>
<xml-open-tag> ::= "<" <id> <attrs> ">"
<xml-close-tag> ::= "</" <id> ">"
<attrs> ::= "" | " " <attr> <attrs>
<attr> ::= <id> "=\\"XXX\\""
<id> ::= <letter> ":" <letter>
<letter> ::= "a" | "b" | "c" | "x"
    """

    SIMPLIFIED_XML_WELLFORMEDNESS_CONSTRAINT = parse_isla(
        """
            forall <xml-tree> tree="<{<id> opid}<attrs>><xml-tree></{<id> clid}>" in start:
                (= opid clid)
            """,
        SIMPLIFIED_XML_NAMESPACE_GRAMMAR,
    )

    SIMPLIFIED_XML_ATTRIBUTE_NAMESPACE_CONSTRAINT = parse_isla(
        r"""
            forall <attr> attribute="{<letter> prefix_use}:{<letter> maybe_def}=\"XXX\"":
              ((not prefix_use = "x" or maybe_def = "x") implies
                exists <xml-tree> outer_tag="<<id>{<attrs> cont_attribute}><xml-tree></<id>>":
                  (inside(attribute, outer_tag) and
                   exists <attr> def_attribute="x:{<letter> prefix_def}=\"XXX\"" in cont_attribute:
                     prefix_use = prefix_def))""",
        SIMPLIFIED_XML_NAMESPACE_GRAMMAR,
        structural_predicates={IN_TREE_PREDICATE},
    )

    SIMPLIFIED_XML_TAG_NAMESPACE_CONSTRAINT = parse_isla(
        r"""
            forall <xml-tree> xml_tree="<{<letter> prefix_use}:<letter>[<attrs>][/]>[<xml-tree><xml-close-tag>]":
              exists <xml-tree> outer_tag="<<id> {<attr> cont_attribute}><xml-tree></<id>>":
                (inside(xml_tree, outer_tag) and 
                 exists <attr>="x:{<letter> prefix_def}=\"XXX\"" in cont_attribute:
                   prefix_use = prefix_def)""",
        SIMPLIFIED_XML_NAMESPACE_GRAMMAR,
        structural_predicates={IN_TREE_PREDICATE},
    )

    SIMPLIFIED_XML_NAMESPACE_CONSTRAINT = (
        SIMPLIFIED_XML_TAG_NAMESPACE_CONSTRAINT
        & SIMPLIFIED_XML_ATTRIBUTE_NAMESPACE_CONSTRAINT
    )

    SIMPLIFIED_XML_NO_ATTR_REDEF_CONSTRAINT = parse_isla(
        r"""
            forall <attr> attr_outer in start:
              forall <attr> attr_inner_1="{<id> id_1}=\"XXX\"" in attr_outer:
                forall <attr> attr_inner_2="{<id> id_2}=\"XXX\"" in attr_outer: 
                  (same_position(attr_inner_1, attr_inner_2) xor
                   not (= id_1 id_2))""",
        SIMPLIFIED_XML_NAMESPACE_GRAMMAR,
        structural_predicates={IN_TREE_PREDICATE, SAME_POSITION_PREDICATE},
    )

    @pytest.mark.skip(reason="currently takes too long")
    def test_assgn_lang_def_use(self):
        constraint = """
        forall <assgn> assgn_1="{<var> lhs_1} := {<rhs> rhs_1}" in start:
          forall <var> var in rhs_1:
            exists <assgn> assgn_2="{<var> lhs_2} := {<rhs> rhs_2}" in start:
              (before(assgn_2, assgn_1) and (= lhs_2 var))
        """

        solver = RepairSolver(LANG_GRAMMAR, constraint)

        for i in range(20):
            solution = solver.solve()
            LOGGER.info(f"Found solution no. %d: %s", i + 1, solution)

    @pytest.mark.skip(reason="currently takes too long")
    def test_repair_assgn_lang_def_use(self):
        inp = "z := 1 ; e := j ; o := n ; p := s ; l := k ; x := d"

        inp_tree = DerivationTree.from_parse_tree(
            next(EarleyParser(LANG_GRAMMAR).parse(inp))
        )
        constraint = """
        forall <assgn> assgn_1="{<var> lhs_1} := {<rhs> rhs_1}" in start:
          forall <var> var in rhs_1:
            exists <assgn> assgn_2="{<var> lhs_2} := {<rhs> rhs_2}" in start:
              (before(assgn_2, assgn_1) and (= lhs_2 var))
        """
        solver = RepairSolver(LANG_GRAMMAR, constraint)

        result = solver.repair_tree(solver.instantiate_top_constant(inp_tree), inp_tree)
        print(result)
        self.assertTrue(result.value_or(False))

    def test_xml_with_prefixes_full_constraint(self):
        constraint = (
            XML_WELLFORMEDNESS_CONSTRAINT
            & XML_NO_ATTR_REDEF_CONSTRAINT
            & XML_NAMESPACE_CONSTRAINT
        )

        solver = RepairSolver(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES, constraint)

        # TODO: Increase numbert to 20. Some repair actions take far too long, suspicious!
        for i in range(10):
            solution = solver.solve()
            LOGGER.info(f"Found solution no. %d: %s", i + 1, solution)
            self.assertTrue(validate_xml(solution))

    def test_xml_balance(self):
        constraint = XML_WELLFORMEDNESS_CONSTRAINT & XML_NO_ATTR_REDEF_CONSTRAINT

        solver = RepairSolver(XML_GRAMMAR, constraint)

        for i in range(20):
            solution = solver.solve()
            LOGGER.info(f"Found solution no. %d: %s", i + 1, solution)
            self.assertTrue(validate_xml(solution))

    def test_repair_xml_not_wellformed(self):
        inp = "<a>X</b>"
        inp_tree = DerivationTree.from_parse_tree(
            next(EarleyParser(XML_GRAMMAR).parse(inp))
        )
        constraint = XML_WELLFORMEDNESS_CONSTRAINT
        solver = RepairSolver(XML_GRAMMAR, constraint)

        result = solver.repair_tree(solver.instantiate_top_constant(inp_tree), inp_tree)
        self.assertTrue(result.map(validate_xml).value_or(False))

    def test_repair_xml_namespace(self):
        inp = '<ns1:A ns3:attr="X">Hello</ns2:B>'

        inp_tree = DerivationTree.from_parse_tree(
            next(EarleyParser(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES).parse(inp))
        )
        constraint = (
            XML_WELLFORMEDNESS_CONSTRAINT
            & XML_NO_ATTR_REDEF_CONSTRAINT
            & XML_NAMESPACE_CONSTRAINT
        )
        solver = RepairSolver(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES, constraint)

        result = solver.repair_tree(solver.instantiate_top_constant(inp_tree), inp_tree)
        print(result)
        self.assertTrue(result.map(validate_xml).value_or(False))

    def test_solve_xml_with_namespace_simplified(self):
        constraint = (
            TestRepairSolver.SIMPLIFIED_XML_WELLFORMEDNESS_CONSTRAINT
            & TestRepairSolver.SIMPLIFIED_XML_NO_ATTR_REDEF_CONSTRAINT
            & TestRepairSolver.SIMPLIFIED_XML_NAMESPACE_CONSTRAINT
        )

        solver = RepairSolver(
            TestRepairSolver.SIMPLIFIED_XML_NAMESPACE_GRAMMAR,
            constraint,
            max_tries_existential_insertion=10,
        )

        for i in range(10):
            solution = solver.solve()
            LOGGER.info(f"Found solution no. %d: %s", i + 1, solution)
            self.assertTrue(validate_xml(solution))


if __name__ == "__main__":
    unittest.main()
