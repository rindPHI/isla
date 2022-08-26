import logging
import random
import xml.etree.ElementTree as ET

from isla.derivation_tree import DerivationTree
from isla.optimizer import auto_tune_weight_vector, mutate_cost_vector
from isla.solver import CostWeightVector
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

    start_vector = CostWeightVector(
        tree_closing_cost=10,
        constraint_cost=0,
        derivation_depth_penalty=6,
        low_k_coverage_penalty=0,
        low_global_k_path_coverage_penalty=18)

    tune_result = auto_tune_weight_vector(
        XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
        XML_WELLFORMEDNESS_CONSTRAINT & XML_NAMESPACE_CONSTRAINT & XML_NO_ATTR_REDEF_CONSTRAINT,
        validator=validate_xml,
        timeout=60,
        population_size=16,
        generations=6,
        cpu_count=16,
        k=4,
        seed_population=[start_vector] + [
            mutate_cost_vector(start_vector)
            for _ in range(15)
        ]
    )

    print(f"Optimal cost vector: {tune_result[1]}")
