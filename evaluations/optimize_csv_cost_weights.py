import logging
import random

from isla.derivation_tree import DerivationTree
from isla.optimizer import auto_tune_weight_vector
from isla_formalizations import csv


def validator(t: DerivationTree) -> bool:
    return csv.csv_lint(t) is True


if __name__ == '__main__':
    logging.basicConfig(level=logging.ERROR)
    # logging.getLogger("evaluator").setLevel(logging.DEBUG)

    random.seed(3519871684213)

    tune_result = auto_tune_weight_vector(
        csv.CSV_GRAMMAR,
        csv.CSV_COLNO_PROPERTY,
        validator,
        timeout=60,
        population_size=32,
        generations=5,
        cpu_count=32
    )

    print(tune_result[1])
