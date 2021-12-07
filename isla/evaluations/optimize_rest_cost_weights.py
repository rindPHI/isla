import logging
import random

from isla import isla
from isla.evaluator import auto_tune_weight_vector
from isla.tests.subject_languages import rest


def validator(t: isla.DerivationTree) -> bool:
    return rest.render_rst(t) is True


if __name__ == '__main__':
    # logging.basicConfig(level=logging.ERROR)
    logging.getLogger("evaluator").setLevel(logging.INFO)

    random.seed(756923488)

    tune_result = auto_tune_weight_vector(
        rest.REST_GRAMMAR,
        rest.DEF_LINK_TARGETS & rest.LENGTH_UNDERLINE & rest.LIST_NUMBERING_CONSECUTIVE & rest.NO_LINK_TARGET_REDEF,
        validator,
        timeout=120,
        population_size=80,
        generations=3,
        cpu_count=-1
    )

    print(tune_result[1])
