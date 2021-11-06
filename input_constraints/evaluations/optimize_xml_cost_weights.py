import logging
import xml.etree.ElementTree as ET
from typing import Generator

from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer

import input_constraints.isla_shortcuts as sc
from input_constraints import isla
from input_constraints.evaluator import evaluate_mutated_cost_vectors, evaluate_isla_generator
from input_constraints.solver import CostWeightVector
from input_constraints.tests.test_data import XML_GRAMMAR

logging.basicConfig(level=logging.ERROR)
logging.getLogger("evaluator").setLevel(logging.INFO)

mgr = isla.VariableManager(XML_GRAMMAR)
start = mgr.const("$start", "<start>")

xml_formula: isla.Formula = mgr.create(
    sc.forall_bind(
        sc.bexpr("<") + mgr.bv("$oid", "<id>") + ">" +
        "<inner-xml-tree>" +
        "</" + mgr.bv("$cid", "<id>") + ">",
        "<xml-tree>",
        start,
        mgr.smt(mgr.bv("$oid").to_smt() == mgr.bv("$cid").to_smt())
    ) &
    sc.forall_bind(
        sc.bexpr("<") + mgr.bv("$oid", "<id>") + " " + "<xml-attribute>" + ">" +
        "<inner-xml-tree>" +
        "</" + mgr.bv("$cid", "<id>") + ">",
        "<xml-tree>",
        start,
        mgr.smt(mgr.bv("$oid").to_smt() == mgr.bv("$cid").to_smt())
    )
)


def validate_xml(inp: isla.DerivationTree) -> bool:
    try:
        ET.fromstring(str(inp))
        return True
    except ET.ParseError:
        return False


def fuzz_xml() -> Generator[isla.DerivationTree, None, None]:
    fuzzer = GrammarCoverageFuzzer(XML_GRAMMAR)
    while True:
        yield isla.DerivationTree.from_parse_tree(fuzzer.expand_tree(("<start>", None)))


# evaluate_random_cost_vectors(XML_GRAMMAR, xml_formula, validate_xml, "/tmp/xml_perf_evalpdf", 60, 30)

evaluate_isla_generator(
    XML_GRAMMAR,
    xml_formula,
    CostWeightVector(
        tree_closing_cost=14,
        vacuous_penalty=15,
        constraint_cost=18,
        derivation_depth_penalty=1,
        low_k_coverage_penalty=8),
    validate_xml,
    60,
    "/tmp/xml_perf_eval_1.pdf")

evaluate_isla_generator(
    XML_GRAMMAR,
    xml_formula,
    CostWeightVector(
        tree_closing_cost=10,
        vacuous_penalty=17,
        constraint_cost=19,
        derivation_depth_penalty=14,
        low_k_coverage_penalty=7),
    validate_xml,
    60,
    "/tmp/xml_perf_eval_2.pdf")

# evaluate_generator(
#     outfile_pdf="xml_perf_eval_random.pdf",
#     diagram_title="Coverage-Based Fuzzer Performance",
#     formula=xml_formula,
#     producer=fuzz_xml(),
#     graph=gg.GrammarGraph.from_grammar(XML_GRAMMAR),
#     validator=validate_xml,
#     timeout_seconds=60,
#     k=3)


# tune_result = auto_tune_weight_vector(
#     XML_GRAMMAR, xml_formula, validate_xml, timeout=30, population_size=20, generations=7)
# tune_result[0].plot("/tmp/xml_autotune_result_state.pdf", "XML Auto-Tune Result Config Stats")
