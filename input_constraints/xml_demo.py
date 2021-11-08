import logging
import string
import sys
from html import escape
import xml.etree.ElementTree as ET
from typing import Optional, List

from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import srange
from fuzzingbook.Parser import EarleyParser

from input_constraints.evaluator import auto_tune_weight_vector
from input_constraints.isla import parse_isla, evaluate, DerivationTree
from input_constraints.solver import ISLaSolver, CostSettings, CostWeightVector

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
    constraint = """
    const start: <start>;
    
    vars {
        tree: <xml-tree>;
        opid, clid: <id>;
    }
    
    constraint {
        forall tree="<{opid}[ <xml-attribute>]><inner-xml-tree></{clid}>" in start:
            (= opid clid)
    }
    """

    # Check whether constraint can be parsed
    parsed_constraint = parse_isla(constraint)

    # Try out evaluator
    c_inp = "<a>asdf</a>"
    w_inp = "<a>asdf</b>"

    c_tree = DerivationTree.from_parse_tree(list(EarleyParser(XML_GRAMMAR).parse(c_inp))[0])
    w_tree = DerivationTree.from_parse_tree(list(EarleyParser(XML_GRAMMAR).parse(w_inp))[0])

    print(evaluate(constraint, reference_tree=c_tree))
    print(evaluate(constraint, reference_tree=w_tree))

    # Demonstrate that grammar fuzzer produces "wrong" inputs
    fuzzer = GrammarCoverageFuzzer(XML_GRAMMAR)
    for _ in range(30):
        inp = DerivationTree.from_parse_tree(fuzzer.expand_tree(("<start>", None)))
        out = []
        if not validate_xml(inp, out):
            assert out
            print(f"Invalid input produced by fuzzer ({out[0]}): {inp}", file=sys.stderr)

    # Try out solver

    # Get optimized weight vector
    # This can take some time (~3 min).
    # When re-running the solver, the returned cost vector should be added literally.
    logging.basicConfig(level=logging.INFO)
    tune_result = auto_tune_weight_vector(
        XML_GRAMMAR,
        parsed_constraint,
        validator=validate_xml,
        timeout=30,
        population_size=20,
        generations=4,
        cpu_count=-1  # use all cores
    )

    print(f"Optimal cost vector: {tune_result[1]}")

    # Run solver
    solver = ISLaSolver(
        XML_GRAMMAR,
        constraint,
        max_number_smt_instantiations=1,
        max_number_free_instantiations=1,
        cost_settings=CostSettings(
            (tune_result[1],),
            cost_phase_lengths=(200,),
            k=3
        ),
    )

    generator = solver.solve()
    for _ in range(100):
        inp = next(generator)
        print(inp)
        if not validate_xml(inp):
            print(f"Invalid input produced by ISLa solver: {inp}", file=sys.stderr)
