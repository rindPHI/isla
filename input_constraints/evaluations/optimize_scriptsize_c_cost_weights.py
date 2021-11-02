import logging
import random

from input_constraints.evaluator import auto_tune_weight_vector
from input_constraints.tests.subject_languages.scriptsizec import SCRIPTSIZE_C_GRAMMAR, compile_scriptsizec_clang, \
    SCRIPTSIZE_C_DEF_USE_CONSTR, SCRIPTSIZE_C_NO_REDEF_CONSTR

logger = logging.getLogger("optim_scriptsize_c")
logging.basicConfig(level=logging.ERROR)
logging.getLogger("evaluator").setLevel(logging.DEBUG)
logger.setLevel(logging.DEBUG)

# seed = random.randint(-1000, 1000)
# logger.info("Seed: %d", seed)
# random.seed(seed)

tune_result = auto_tune_weight_vector(
    SCRIPTSIZE_C_GRAMMAR,
    SCRIPTSIZE_C_DEF_USE_CONSTR & SCRIPTSIZE_C_NO_REDEF_CONSTR,
    lambda t: compile_scriptsizec_clang(t) is True,
    timeout=60,
    population_size=20,
    generations=5,
)

tune_result[0].plot("/tmp/scriptsize_c_autotune_result_state.pdf", "Scriptsize-C Auto-Tune Result Config Stats")