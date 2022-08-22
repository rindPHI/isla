import logging
import random

from isla.derivation_tree import DerivationTree
from isla.optimizer import auto_tune_weight_vector
from isla.solver import CostWeightVector
from isla_formalizations.scriptsizec import SCRIPTSIZE_C_GRAMMAR, compile_scriptsizec_clang, \
    SCRIPTSIZE_C_DEF_USE_CONSTR, SCRIPTSIZE_C_NO_REDEF_CONSTR


def validator(t: DerivationTree) -> bool:
    return compile_scriptsizec_clang(t) is True


if __name__ == '__main__':
    logging.basicConfig(level=logging.ERROR)
    # logging.getLogger("evaluator").setLevel(logging.DEBUG)

    random.seed(5416874352164316)

    tune_result = auto_tune_weight_vector(
        SCRIPTSIZE_C_GRAMMAR,
        SCRIPTSIZE_C_DEF_USE_CONSTR & SCRIPTSIZE_C_NO_REDEF_CONSTR,
        validator,
        timeout=240,
        population_size=32,
        generations=10,
        cpu_count=32,
        seed_population=[
            CostWeightVector(
                tree_closing_cost=10,
                constraint_cost=0,
                derivation_depth_penalty=12,
                low_k_coverage_penalty=14,
                low_global_k_path_coverage_penalty=14)])

    tune_result[0].plot("/tmp/scriptsize_c_autotune_result_state.pdf", "Scriptsize-C Auto-Tune Result Config Stats")
