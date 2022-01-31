import logging
import random

from isla.language import DerivationTree
from isla.optimizer import auto_tune_weight_vector
from tests.subject_languages.scriptsizec import SCRIPTSIZE_C_GRAMMAR, compile_scriptsizec_clang, \
    SCRIPTSIZE_C_DEF_USE_CONSTR, SCRIPTSIZE_C_NO_REDEF_CONSTR


def validator(t: DerivationTree) -> bool:
    return compile_scriptsizec_clang(t) is True


if __name__ == '__main__':
    logging.basicConfig(level=logging.ERROR)
    logging.getLogger("evaluator").setLevel(logging.DEBUG)

    random.seed(5416874352164316)

    tune_result = auto_tune_weight_vector(
        SCRIPTSIZE_C_GRAMMAR,
        SCRIPTSIZE_C_DEF_USE_CONSTR & SCRIPTSIZE_C_NO_REDEF_CONSTR,
        validator,
        timeout=120,
        population_size=110,
        generations=5,
        cpu_count=32
    )

    tune_result[0].plot("/tmp/scriptsize_c_autotune_result_state.pdf", "Scriptsize-C Auto-Tune Result Config Stats")
