import logging
import string
import sys
import xml.etree.ElementTree as ET
from html import escape
from typing import Optional, List, Dict

from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import srange
from fuzzingbook.Parser import EarleyParser

from isla.language import parse_isla, DerivationTree
from isla.evaluator import evaluate
from isla.optimizer import auto_tune_weight_vector
from isla.solver import ISLaSolver, CostSettings
from isla_formalizations.xml_lang import XML_GRAMMAR_WITH_NAMESPACE_PREFIXES

XML_GRAMMAR = {
    "<start>": ["<xml-tree>"],
    "<xml-tree>": [
        "<xml-open-tag><inner-xml-tree><xml-close-tag>",
        "<xml-openclose-tag>",
    ],
    "<inner-xml-tree>": [
        "<text>",
        "<xml-tree>",
        "<inner-xml-tree><inner-xml-tree>"
    ],
    "<xml-open-tag>": ["<<id>>", "<<id> <xml-attribute>>"],
    "<xml-openclose-tag>": ["<<id>/>", "<<id> <xml-attribute>/>"],
    "<xml-close-tag>": ["</<id>>"],
    "<xml-attribute>": ["<id>=\"<text>\"", "<xml-attribute> <xml-attribute>"],

    "<id>": [
        "<id_start_char>",
        "<id_start_char><id_chars>",
        # "<id_with_prefix>"
    ],
    # "<id_with_prefix>": [
    #     "<id_start_char>:<id_chars>",
    #     "<id_start_char><id_chars>:<id_chars>"],
    "<id_start_char>": srange("_" + string.ascii_letters),
    "<id_chars>": ["<id_char>", "<id_char><id_chars>"],
    "<id_char>": ["<id_start_char>"] + srange("-." + string.digits),
    "<text>": ["<text_char><text>", "<text_char>"],
    "<text_char>": [
        escape(c, {'"': "&quot;"})
        for c in srange(string.ascii_letters + string.digits + "\"'. \t/?-,=:+")],
}


def validate_xml(inp: DerivationTree, out: Optional[List[str]] = None) -> bool:
    try:
        ET.fromstring(str(inp))
        return True
    except Exception as err:
        if out is not None:
            out.append(str(err))
        return False


if __name__ == '__main__':
    # Demonstrate that grammar fuzzer produces "wrong" inputs
    fuzzer = GrammarCoverageFuzzer(XML_GRAMMAR_WITH_NAMESPACE_PREFIXES)
    errors: Dict[str, int] = {}
    for _ in range(100):
        inp = DerivationTree.from_parse_tree(fuzzer.expand_tree(("<start>", None)))
        out = []
        if not validate_xml(inp, out):
            assert out
            error = out[0][:out[0].index(":")]
            errors.setdefault(error, 0)
            errors[error] += 1
            print(f"Invalid input produced by fuzzer ({out[0]}): {inp}", file=sys.stderr)

    print("Encountered errors: " + ", ".join({f"{e} ({n})" for e, n in errors.items()}))

    constraint = """
forall <xml-tree> tree="<{<id> opid}[ <xml-attribute>]><inner-xml-tree></{<id> clid}>" in start:
  (= opid clid)"""

    # Check whether constraint can be parsed
    parsed_constraint = parse_isla(constraint, XML_GRAMMAR)

    # Try out evaluator
    c_inp = "<a>asdf</a>"
    w_inp = "<a>asdf</b>"

    c_tree = DerivationTree.from_parse_tree(list(EarleyParser(XML_GRAMMAR).parse(c_inp))[0])
    w_tree = DerivationTree.from_parse_tree(list(EarleyParser(XML_GRAMMAR).parse(w_inp))[0])

    print(evaluate(constraint, reference_tree=c_tree, grammar=XML_GRAMMAR))
    print(evaluate(constraint, reference_tree=w_tree, grammar=XML_GRAMMAR))

    # Try out solver

    # Get optimized weight vector
    # This can take some time (~3 min).
    # When re-running the solver, the returned cost vector should be added literally.
    logging.basicConfig(level=logging.INFO)
    tune_result = auto_tune_weight_vector(
        XML_GRAMMAR,
        parsed_constraint,
        validator=validate_xml,
        timeout=30,  # How long should a single configuration be evaluated
        population_size=20,  # How many configurations should be produced at the beginning
        generations=4,  # Evolutionary tuning: How many generations should I produce using crossover / mutation
        cpu_count=-1  # Run in parallel: Use all cores (cpu_count == 1 implies single-threaded)
    )

    print(f"Optimal cost vector: {tune_result[1]}")

    # Result is something like
    # CostWeightVector(
    #     tree_closing_cost=15,
    #     vacuous_penalty=15,
    #     constraint_cost=0,
    #     derivation_depth_penalty=0,
    #     low_k_coverage_penalty=5,
    #     low_global_k_path_coverage_penalty=7)

    # Run solver
    solver = ISLaSolver(
        XML_GRAMMAR,
        constraint,
        max_number_smt_instantiations=1,  # Number of solutions for symbols bound by SMT formulas
        max_number_free_instantiations=1,  # Number of solutions for symbols not bound by any formula
        cost_settings=CostSettings(
            tune_result[1],  # Cost weight
            k=3  # For k-Path coverage: Sequences of which length in grammar graph / trees should be considered
        ),
    )

    generator = solver.solve()
    for _ in range(100):
        inp = next(generator)
        print(inp)
        if not validate_xml(inp):
            print(f"Invalid input produced by ISLa solver: {inp}", file=sys.stderr)
