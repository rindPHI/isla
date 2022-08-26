import logging
import random
import sys

from isla.derivation_tree import DerivationTree
from isla.optimizer import auto_tune_weight_vector, evaluate_mutated_cost_vectors, mutate_cost_vector
from isla.solver import CostWeightVector
from isla_formalizations import rest


def validator(t: DerivationTree) -> bool:
    return rest.render_rst(t) is True


if __name__ == '__main__':
    # logging.basicConfig(level=logging.ERROR)
    logging.getLogger("evaluator").setLevel(logging.INFO)

    random.seed(123456)

    start_vector = CostWeightVector(
        tree_closing_cost=7,
        constraint_cost=1.5,
        derivation_depth_penalty=4,
        low_k_coverage_penalty=2,
        low_global_k_path_coverage_penalty=21)

    tune_result = auto_tune_weight_vector(
        rest.REST_GRAMMAR,
        rest.DEF_LINK_TARGETS & rest.LENGTH_UNDERLINE & rest.LIST_NUMBERING_CONSECUTIVE & rest.NO_LINK_TARGET_REDEF,
        validator,
        timeout=60,
        population_size=16,
        generations=6,
        cpu_count=16,
        k=4,
        seed_population=[
            mutate_cost_vector(start_vector)
            for _ in range(15)
        ] + [start_vector]
    )

    print(tune_result[1])
