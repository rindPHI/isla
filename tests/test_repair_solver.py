import logging
import random
import time
import unittest

import z3
from frozendict import frozendict

from isla.derivation_tree import DerivationTree
from isla.isla_predicates import IN_TREE_PREDICATE, SAME_POSITION_PREDICATE
from isla.language import parse_isla, SMTFormula, BoundVariable, Variable
from isla.parser import EarleyParser
from isla.repair_solver import RepairSolver, describe_subtree_structure
from isla.z3_helpers import z3_eq
from isla_formalizations import rest
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
<xml-open-tag> ::= "<" <tag-id> <attrs> ">"
<xml-close-tag> ::= "</" <tag-id> ">"
<attrs> ::= "" | " " <attr> <attrs>
<attr> ::= <attr-id> "=\\"" <randstr> "\\""
<tag-id> ::= <letter-no-x> ":" <letter>
<attr-id> ::= <letter> ":" <letter>
<letter> ::= "a" | "b" | "c" | "x"
<letter-no-x> ::= "a" | "b" | "c"
<randstr> ::= <char> <randstr> | <char>
<char> ::= "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | 
           "I" | "J" | "K" | "L" | "M" | "N" | "O" | "P" |
           "Q" | "R" | "S" | "T" | "U" | "V" | "W" | "X" |
           "Y" | "Z"
    """

    SIMPLIFIED_XML_WELLFORMEDNESS_CONSTRAINT = parse_isla(
        """
            forall <xml-tree> tree="<{<tag-id> opid}<attrs>><xml-tree></{<tag-id> clid}>" in start:
                (= opid clid)
            """,
        SIMPLIFIED_XML_NAMESPACE_GRAMMAR,
    )

    # Note: The namespace constraints ignore the "aliasing" property which lets
    #       you use different namespace prefixes for the same namespace.
    #       For example, `xmlns:a="XXX"` and `xmlns:b="XXX"` are referring to
    #       the same namespace, and having `a:a` and `b:a` in the same tag is
    #       not allowed.
    SIMPLIFIED_XML_ATTRIBUTE_NAMESPACE_CONSTRAINT = parse_isla(
        r"""
            forall <attr> attribute="{<letter> prefix_use}:{<letter> maybe_def}=\"<randstr>\"": (
                not maybe_def = "x" or
                not prefix_use = "x"
            ) and
            forall <attr> attribute="{<letter> prefix_use}:{<letter> maybe_def}=\"<randstr>\"": (
              prefix_use = "x" or
                not prefix_use = "x" and
                exists <xml-tree> outer_tag="<<tag-id>{<attrs> cont_attribute}><xml-tree></<tag-id>>":
                  (inside(attribute, outer_tag) and
                   exists <attr> def_attribute="x:{<letter> prefix_def}=\"<randstr>\"" in cont_attribute:
                     prefix_use = prefix_def)
            )""",
        SIMPLIFIED_XML_NAMESPACE_GRAMMAR,
        structural_predicates={IN_TREE_PREDICATE},
    )

    SIMPLIFIED_XML_TAG_NAMESPACE_CONSTRAINT = parse_isla(
        r"""
            forall <xml-tree> xml_tree="<{<letter-no-x> prefix_use}:<letter>[<attrs>][/]>[<xml-tree><xml-close-tag>]":
              exists <xml-tree> outer_tag="<<tag-id>{<attrs> cont_attribute}><xml-tree></<tag-id>>":
                (inside(xml_tree, outer_tag) and 
                 exists <attr>="x:{<letter> prefix_def}=\"<randstr>\"" in cont_attribute:
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
            forall <attrs> attr_outer in start:
              forall <attr> attr_inner_1="{<attr-id> id_1}=\"<randstr>\"" in attr_outer:
                forall <attr> attr_inner_2="{<attr-id> id_2}=\"<randstr>\"" in attr_outer: 
                  (same_position(attr_inner_1, attr_inner_2) xor
                   not (= id_1 id_2))""",
        SIMPLIFIED_XML_NAMESPACE_GRAMMAR,
        structural_predicates={IN_TREE_PREDICATE, SAME_POSITION_PREDICATE},
    )

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
        self.assertTrue(result.map(validate_xml).value_or(False))

    def test_solve_xml_with_namespace_simplified(self):
        random.seed(0)
        logging.getLogger("isla-language-core").setLevel(logging.WARNING)

        constraint = (
            TestRepairSolver.SIMPLIFIED_XML_WELLFORMEDNESS_CONSTRAINT
            & TestRepairSolver.SIMPLIFIED_XML_NO_ATTR_REDEF_CONSTRAINT
            & TestRepairSolver.SIMPLIFIED_XML_ATTRIBUTE_NAMESPACE_CONSTRAINT
            & TestRepairSolver.SIMPLIFIED_XML_TAG_NAMESPACE_CONSTRAINT
        )

        solver = RepairSolver(
            TestRepairSolver.SIMPLIFIED_XML_NAMESPACE_GRAMMAR,
            constraint,
            max_tries_existential_insertion=3,
        )

        for i in range(10):
            solution = solver.solve()
            LOGGER.info(f"Found solution no. %d: %s", i + 1, solution)
            self.assertTrue(
                not str(solution)
                or validate_xml(str(solution).replace(" x:", " xmlns:"))
            )

    def test_repair_simplified_xml(self):
        random.seed(0)
        logging.getLogger("isla-language-core").setLevel(logging.WARNING)

        inp = "<a:b><b:x></c:a></a:b>"

        constraint = (
            TestRepairSolver.SIMPLIFIED_XML_WELLFORMEDNESS_CONSTRAINT
            & TestRepairSolver.SIMPLIFIED_XML_NO_ATTR_REDEF_CONSTRAINT
            & TestRepairSolver.SIMPLIFIED_XML_ATTRIBUTE_NAMESPACE_CONSTRAINT
            & TestRepairSolver.SIMPLIFIED_XML_TAG_NAMESPACE_CONSTRAINT
        )

        solver = RepairSolver(
            TestRepairSolver.SIMPLIFIED_XML_NAMESPACE_GRAMMAR,
            constraint,
            max_tries_existential_insertion=3,
        )

        DerivationTree.next_id = 0
        inp_tree = solver.parse(inp).unwrap()
        result = solver.repair_tree(solver.instantiate_top_constant(inp_tree), inp_tree)

        out = []
        self.assertTrue(
            result.map(str)
            .map(lambda s: s.replace(" x:", " xmlns:"))
            .map(lambda s: validate_xml(s, out))
            .value_or(False),
            "\n".join(out),
        )

        # TODO: Turn this into a regular expression match (make XXX a wildcard).
        # self.assertEqual(
        #     '<a:b x:a="XXX" x:b="XXX"><b:x></b:x></a:b>', str(result.unwrap())
        # )

    def test_repair_simplified_xml_more_restrictive(self):
        # The following constraint is too restrictive: It explicitly requires an outer
        # tag declaring a namespace to exist, although the namespace can be declared
        # within an attribute of the tag using it. We keep this constraint here because
        # the solver should be able to find a solution for it nevertheless.
        simplified_xml_tag_namespace_constraint_too_restrictive = parse_isla(
            r"""
                forall <xml-tree> xml_tree="<{<letter-no-x> prefix_use}:<letter>[<attrs>][/]>[<xml-tree><xml-close-tag>]":
                  exists <xml-tree> outer_tag=
                      "<<tag-id> {<attr> cont_attribute}><xml-tree></<tag-id>>":  # is <attrs> in less restrictive form
                    (inside(xml_tree, outer_tag) and 
                     exists <attr>="x:{<letter> prefix_def}=\"<randstr>\"" in cont_attribute:
                       prefix_use = prefix_def)""",
            TestRepairSolver.SIMPLIFIED_XML_NAMESPACE_GRAMMAR,
            structural_predicates={IN_TREE_PREDICATE},
        )

        random.seed(0)
        logging.getLogger("isla-language-core").setLevel(logging.WARNING)

        # inp = '<b:a x:b="XXX"></c:x>'
        inp = '<b:c b:c="XXX" x:b="XXX"></b:x>'

        constraint = (
            TestRepairSolver.SIMPLIFIED_XML_WELLFORMEDNESS_CONSTRAINT
            & TestRepairSolver.SIMPLIFIED_XML_NO_ATTR_REDEF_CONSTRAINT
            & TestRepairSolver.SIMPLIFIED_XML_ATTRIBUTE_NAMESPACE_CONSTRAINT
            & simplified_xml_tag_namespace_constraint_too_restrictive
        )

        solver = RepairSolver(
            TestRepairSolver.SIMPLIFIED_XML_NAMESPACE_GRAMMAR,
            constraint,
            max_tries_existential_insertion=3,
        )

        DerivationTree.next_id = 0
        inp_tree = solver.parse(inp).unwrap()
        result = solver.repair_tree(solver.instantiate_top_constant(inp_tree), inp_tree)
        self.assertTrue(
            result.map(str)
            .map(lambda s: s.replace(" x:", " xmlns:"))
            .map(validate_xml)
            .value_or(False)
        )

    def test_describe_subtree_structure(self):
        tree_str = '<b:x x:c="XXX"></a:x>'

        solver = RepairSolver(
            TestRepairSolver.SIMPLIFIED_XML_NAMESPACE_GRAMMAR,
            TestRepairSolver.SIMPLIFIED_XML_WELLFORMEDNESS_CONSTRAINT
            & TestRepairSolver.SIMPLIFIED_XML_ATTRIBUTE_NAMESPACE_CONSTRAINT
            & TestRepairSolver.SIMPLIFIED_XML_TAG_NAMESPACE_CONSTRAINT
            & TestRepairSolver.SIMPLIFIED_XML_NO_ATTR_REDEF_CONSTRAINT,
        )

        # <b:x x:<letter>="XXX"></a:x>
        tree: DerivationTree = solver.parse(tree_str).unwrap()
        prefix_def_0_path = (0, 0, 2, 1, 0, 2)
        tree = tree.replace_path(prefix_def_0_path, DerivationTree("<letter>", None))

        prefix_def_0 = BoundVariable("prefix_def_0", "<letter>")
        prefix_use_1 = BoundVariable("prefix_use_1", "<letter_no_x>")
        prefix_use_1_path = (0, 0, 1, 0)
        opid = BoundVariable("opid", "<tag-id>")
        opid_path = (0, 0, 1)
        clid = BoundVariable("clid", "<tag-id>")
        clid_path = (0, 2, 2)

        # (prefix_use_1 == prefix_def_0, {'prefix_use_1': 'b', 'prefix_def_0': '<letter>'})
        smt_constraint_1 = SMTFormula(
            z3_eq(prefix_use_1.to_smt(), prefix_def_0.to_smt()),
            prefix_use_1,
            prefix_def_0,
            auto_eval=False,
            auto_subst=False,
        ).substitute_expressions(
            {
                prefix_use_1: tree.get_subtree(prefix_use_1_path),
                prefix_def_0: tree.get_subtree(prefix_def_0_path),
            }
        )
        self.assertEqual(
            "(prefix_use_1 == prefix_def_0, {'prefix_use_1': 'b', 'prefix_def_0': '<letter>'})",
            str(smt_constraint_1),
        )

        # (opid == clid, {'opid': 'b:x', 'clid': 'a:x'})
        smt_constraint_2 = SMTFormula(
            z3_eq(opid.to_smt(), clid.to_smt()),
            opid,
            clid,
            auto_eval=False,
            auto_subst=False,
        ).substitute_expressions(
            {
                opid: tree.get_subtree(opid_path),
                clid: tree.get_subtree(clid_path),
            }
        )
        self.assertEqual(
            "(opid == clid, {'opid': 'b:x', 'clid': 'a:x'})",
            str(smt_constraint_2),
        )

        smt_constraints = (smt_constraint_1, smt_constraint_2)

        bound_tree_paths = frozendict(
            {
                tree.find_node(subtree): variable
                for smt_formula in smt_constraints
                for variable, subtree in smt_formula.substitutions.items()
            }
        )

        prefix_def_0_fresh_vars, prefix_def_0_structure = describe_subtree_structure(
            tree.get_subtree(prefix_def_0_path),
            bound_tree_paths,
            current_path=prefix_def_0_path,
        )
        self.assertEqual(frozendict({}), prefix_def_0_fresh_vars)
        self.assertEqual((), prefix_def_0_structure)

        prefix_use_1_fresh_vars, prefix_use_1_structure = describe_subtree_structure(
            tree.get_subtree(prefix_use_1_path),
            bound_tree_paths,
            current_path=prefix_use_1_path,
        )
        self.assertEqual(frozendict({}), prefix_use_1_fresh_vars)
        self.assertEqual(("b",), prefix_use_1_structure)

        opid_fresh_vars, opid_structure = describe_subtree_structure(
            tree.get_subtree(opid_path), bound_tree_paths, current_path=opid_path
        )
        fresh_var = BoundVariable("letter", "<letter>")
        self.assertEqual(frozendict({fresh_var: "x"}), opid_fresh_vars)
        self.assertEqual((prefix_use_1, ":", fresh_var), opid_structure)

        clid_fresh_vars, clid_structure = describe_subtree_structure(
            tree.get_subtree(clid_path), bound_tree_paths, current_path=clid_path
        )
        self.assertEqual(frozendict({}), clid_fresh_vars)
        self.assertEqual(("a:x",), clid_structure)

    def test_solve_complex_numeric_formula_heartbeat(self):
        random.seed(9876)
        heartbeat_request_grammar = {
            "<start>": ["<heartbeat-request>"],
            "<heartbeat-request>": ["\x01<payload-length><payload><padding>"],
            "<payload-length>": ["<byte><byte>"],
            "<payload>": ["<bytes>"],
            "<padding>": ["<bytes>"],
            "<bytes>": ["<byte><bytes>", "<byte>"],
            "<byte>": [chr(i) for i in range(256)],
        }

        length_constraint = """
  256 * str.to_code(<payload-length>.<byte>[1])
+ str.to_code(<payload-length>.<byte>[2]) 
= str.len(<payload>) and
<payload-length>.<byte> = "\x01"
"""

        solver = RepairSolver(heartbeat_request_grammar, length_constraint)

        for i in range(10):
            solution = solver.solve()
            LOGGER.info(f"Found solution no. %d: %s", i, solution)

            payload = str(solution.get_subtree((0, 2)))
            length_msb = ord(str(solution.get_subtree((0, 1, 0))))
            length_lsb = ord(str(solution.get_subtree((0, 1, 1))))

            self.assertEqual(1, length_msb)
            self.assertEqual(len(payload), 256 * length_msb + length_lsb)

    def test_compare_optimize_and_vanilla_solver_for_simpl_xml_example(self):
        solver = RepairSolver(TestRepairSolver.SIMPLIFIED_XML_NAMESPACE_GRAMMAR)

        tree = solver.parse('<a:b x:c="XXX" x:c="XXX"><b:x></c:a></a:b>').unwrap()
        tree = tree.replace_path((0, 0, 2, 1, 0, 2), DerivationTree("<letter>"))
        tree = tree.replace_path((0, 0, 2, 2, 1, 0, 2), DerivationTree("<letter>"))

        self.assertEqual(
            '<a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>', str(tree)
        )

        letter_no_x_1 = Variable("letter_no_x_1", "<letter-no-x>")
        letter_no_x_2 = Variable("letter_no_x_2", "<letter-no-x>")
        letter_1 = Variable("letter_1", "<letter>")
        letter_2 = Variable("letter_2", "<letter>")
        attr_id_1 = Variable("attr_id_1", "<attr-id>")
        attr_id_2 = Variable("attr_id_2", "<attr-id>")
        tag_id_1 = Variable("tag_id_1", "<tag-id>")
        tag_id_2 = Variable("tag_id_2", "<tag-id>")

        # <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>
        # ^
        letter_no_x_1_tree = tree.get_subtree((0, 1, 0, 1, 0))

        # <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>
        # ^
        letter_no_x_2_tree = tree.get_subtree((0, 0, 1, 0))

        # <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>
        # ^
        letter_1_tree = tree.get_subtree((0, 0, 2, 1, 0, 2))

        # <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>
        # ^
        letter_2_tree = tree.get_subtree((0, 0, 2, 2, 1, 0, 2))

        # <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>
        # ^
        attr_id_1_tree = tree.get_subtree((0, 0, 2, 1, 0))

        # <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>
        # ^
        attr_id_2_tree = tree.get_subtree((0, 0, 2, 2, 1, 0))

        # <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>
        # ^
        tag_id_1_tree = tree.get_subtree((0, 1, 0, 1))

        # <a:b x:<letter>="XXX" x:<letter>="XXX"><b:x></c:a></a:b>
        # ^
        tag_id_2_tree = tree.get_subtree((0, 1, 2, 2))

        # - letter_no_x_1 == letter_1
        # - Not(attr_id_2 == attr_id_1)
        # - Not(letter_1 == "x")
        # - letter_no_x_2 == letter_2
        # - Not(letter_2 == "x")
        # - tag_id_1 == tag_id_2

        formula_1 = SMTFormula(
            z3_eq(letter_no_x_1.to_smt(), letter_1.to_smt()),
            letter_no_x_1,
            letter_1,
            auto_eval=False,
            auto_subst=False,
        ).substitute_expressions(
            {letter_no_x_1: letter_no_x_1_tree, letter_1: letter_1_tree}
        )

        formula_2 = SMTFormula(
            z3.Not(z3_eq(attr_id_2.to_smt(), attr_id_1.to_smt())),
            attr_id_2,
            attr_id_1,
            auto_eval=False,
            auto_subst=False,
        ).substitute_expressions({attr_id_2: attr_id_2_tree, attr_id_1: attr_id_1_tree})

        formula_3 = SMTFormula(
            z3.Not(z3_eq(letter_1.to_smt(), z3.StringVal("x"))),
            letter_1,
            auto_eval=False,
            auto_subst=False,
        ).substitute_expressions({letter_1: letter_1_tree})

        formula_4 = SMTFormula(
            z3_eq(letter_no_x_2.to_smt(), letter_2.to_smt()),
            letter_no_x_2,
            letter_2,
            auto_eval=False,
            auto_subst=False,
        ).substitute_expressions(
            {letter_no_x_2: letter_no_x_2_tree, letter_2: letter_2_tree}
        )

        formula_5 = SMTFormula(
            z3.Not(z3_eq(letter_2.to_smt(), z3.StringVal("x"))),
            letter_2,
            auto_eval=False,
            auto_subst=False,
        ).substitute_expressions({letter_2: letter_2_tree})

        formula_6 = SMTFormula(
            z3_eq(tag_id_1.to_smt(), tag_id_2.to_smt()),
            tag_id_1,
            tag_id_2,
            auto_eval=False,
            auto_subst=False,
        ).substitute_expressions({tag_id_1: tag_id_1_tree, tag_id_2: tag_id_2_tree})

        # First: vanilla solutions
        _1, _2, _3, res, model = solver.compute_solution_vanilla(
            (formula_1, formula_2, formula_3, formula_4, formula_5, formula_6), tree
        )

        self.assertEqual(z3.sat, res)
        self.assertEqual('"x:b"', str(model[attr_id_1.to_smt()]))
        self.assertEqual('"x:a"', str(model[attr_id_2.to_smt()]))
        self.assertEqual('"b:x"', str(model[tag_id_1.to_smt()]))
        self.assertEqual('"b:x"', str(model[tag_id_2.to_smt()]))

        # Second: optimized solutions
        _1, _2, _3, res, model = solver.compute_solution_optimized(
            (formula_1, formula_2, formula_3, formula_4, formula_5, formula_6), tree
        )

        self.assertEqual(z3.sat, res)
        self.assertEqual('"x:b"', str(model[attr_id_1.to_smt()]))
        self.assertEqual('"x:a"', str(model[attr_id_2.to_smt()]))
        self.assertEqual('"b:x"', str(model[tag_id_1.to_smt()]))
        self.assertEqual('"b:x"', str(model[tag_id_2.to_smt()]))

    def test_rest(self):
        solver = RepairSolver(
            rest.REST_GRAMMAR,
            rest.LENGTH_UNDERLINE
            & rest.DEF_LINK_TARGETS
            & rest.NO_LINK_TARGET_REDEF
            & rest.LIST_NUMBERING_CONSECUTIVE,
        )

        for i in range(50):
            solution = solver.solve()
            LOGGER.info(f"Found solution no. %d: %s", i, solution)
            result = rest.render_rst(solution)
            self.assertIsInstance(result, bool, result)

    def test_timeout(self):
        constraint = """
        forall <assgn> assgn_1="{<var> lhs_1} := {<rhs> rhs_1}" in start:
          forall <var> var in rhs_1:
            exists <assgn> assgn_2="{<var> lhs_2} := {<rhs> rhs_2}" in start:
              (before(assgn_2, assgn_1) and (= lhs_2 var))
        """

        solver = RepairSolver(LANG_GRAMMAR, constraint, timeout_seconds=4)
        start_time = time.time()

        for i in range(2000):
            try:
                solution = solver.solve()
                LOGGER.info(f"Found solution no. %d: %s", i + 1, solution)
            except StopIteration:
                break

        self.assertLess(time.time() - start_time, 8)


if __name__ == "__main__":
    unittest.main()
