import logging
import random

from input_constraints import isla
from input_constraints.evaluator import auto_tune_weight_vector
import input_constraints.tests.subject_languages.csv as CSV


def validator(t: isla.DerivationTree) -> bool:
    return CSV.csv_lint(t) is True


if __name__ == '__main__':
    logging.basicConfig(level=logging.ERROR)
    logging.getLogger("evaluator").setLevel(logging.DEBUG)

    random.seed(3519871684213)

    tune_result = auto_tune_weight_vector(
        CSV.CSV_GRAMMAR,
        CSV.CSV_COLNO_PROPERTY,
        validator,
        timeout=90,
        population_size=16,
        generations=5,
        cpu_count=-1
    )

    print(tune_result[1])
