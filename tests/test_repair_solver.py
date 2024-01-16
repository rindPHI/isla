import logging
import unittest

from isla.derivation_tree import DerivationTree
from isla.parser import EarleyParser
from isla.repair_solver import RepairSolver
from isla_formalizations.xml_lang import (
    XML_WELLFORMEDNESS_CONSTRAINT,
    XML_NO_ATTR_REDEF_CONSTRAINT,
    XML_NAMESPACE_CONSTRAINT,
    XML_GRAMMAR,
    XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
    validate_xml,
    XML_TAG_NAMESPACE_CONSTRAINT,
)
from test_data import LANG_GRAMMAR

LOGGER = logging.getLogger(__name__)


class TestRepairSolver(unittest.TestCase):
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

        for i in range(20):
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


if __name__ == "__main__":
    unittest.main()
