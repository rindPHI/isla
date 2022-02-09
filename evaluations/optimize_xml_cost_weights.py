import logging
import random
import xml.etree.ElementTree as ET

from isla.language import DerivationTree
from isla.optimizer import auto_tune_weight_vector
from isla_formalizations.xml_lang import XML_NAMESPACE_CONSTRAINT, XML_WELLFORMEDNESS_CONSTRAINT, \
    XML_GRAMMAR_WITH_NAMESPACE_PREFIXES, XML_NO_ATTR_REDEF_CONSTRAINT


def validate_xml(inp: DerivationTree) -> bool:
    try:
        ET.fromstring(str(inp))
        return True
    except ET.ParseError:
        return False


if __name__ == '__main__':
    logging.basicConfig(level=logging.ERROR)
    logging.getLogger("evaluator").setLevel(logging.INFO)

    random.seed(13468432149)

    tune_result = auto_tune_weight_vector(
        XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
        XML_WELLFORMEDNESS_CONSTRAINT & XML_NAMESPACE_CONSTRAINT & XML_NO_ATTR_REDEF_CONSTRAINT,
        validator=validate_xml,
        timeout=40,  # How long should a single configuration be evaluated
        population_size=20,  # How many configurations should be produced at the beginning
        generations=3,  # Evolutionary tuning: How many generations should I produce using crossover / mutation
        cpu_count=4,  # Run in parallel: Use all cores (cpu_count == 1 implies single-threaded)
        k=4
    )

    print(f"Optimal cost vector: {tune_result[1]}")
