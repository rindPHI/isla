import logging
import random

from input_constraints import isla
from input_constraints.evaluator import auto_tune_weight_vector
from input_constraints.tests.subject_languages.scriptsizec import SCRIPTSIZE_C_GRAMMAR, compile_scriptsizec_clang, \
    SCRIPTSIZE_C_DEF_USE_CONSTR, SCRIPTSIZE_C_NO_REDEF_CONSTR


def validator(t: isla.DerivationTree) -> bool:
    return compile_scriptsizec_clang(t) is True


if __name__ == '__main__':
    logging.basicConfig(level=logging.ERROR)
    logging.getLogger("evaluator").setLevel(logging.DEBUG)

    random.seed(351684321654)

    tune_result = auto_tune_weight_vector(
        SCRIPTSIZE_C_GRAMMAR,
        SCRIPTSIZE_C_DEF_USE_CONSTR & SCRIPTSIZE_C_NO_REDEF_CONSTR,
        validator,
        timeout=90,
        population_size=50,
        generations=4,
        cpu_count=-1
    )

    tune_result[0].plot("/tmp/scriptsize_c_autotune_result_state.pdf", "Scriptsize-C Auto-Tune Result Config Stats")
