import logging
import xml.etree.ElementTree as ET

from input_constraints import isla
from input_constraints.evaluator import auto_tune_weight_vector
from input_constraints.isla import parse_isla
from input_constraints.tests.test_data import XML_GRAMMAR

logging.basicConfig(level=logging.ERROR)
logging.getLogger("evaluator").setLevel(logging.INFO)

xml_constraint_str = """
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


def validate_xml(inp: isla.DerivationTree) -> bool:
    try:
        ET.fromstring(str(inp))
        return True
    except ET.ParseError:
        return False


if __name__ == '__main__':
    # Check whether constraint can be parsed
    xml_constraint = parse_isla(xml_constraint_str)

    logging.basicConfig(level=logging.INFO)
    tune_result = auto_tune_weight_vector(
        XML_GRAMMAR,
        xml_constraint,
        validator=validate_xml,
        timeout=30,  # How long should a single configuration be evaluated
        population_size=20,  # How many configurations should be produced at the beginning
        generations=4,  # Evolutionary tuning: How many generations should I produce using crossover / mutation
        cpu_count=-1  # Run in parallel: Use all cores (cpu_count == 1 implies single-threaded)
    )

    print(f"Optimal cost vector: {tune_result[1]}")
