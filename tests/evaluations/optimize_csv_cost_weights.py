import logging
import random

from src.isla.isla import DerivationTree
from src.isla.optimizer import auto_tune_weight_vector
from tests.subject_languages import csv


def validator(t: DerivationTree) -> bool:
    return csv.csv_lint(t) is True


if __name__ == '__main__':
    logging.basicConfig(level=logging.ERROR)
    logging.getLogger("evaluator").setLevel(logging.DEBUG)

    random.seed(3519871684213)

    tune_result = auto_tune_weight_vector(
        csv.CSV_GRAMMAR,
        csv.CSV_COLNO_PROPERTY,
        validator,
        timeout=90,
        population_size=16,
        generations=5,
        cpu_count=-1
    )

    print(tune_result[1])
