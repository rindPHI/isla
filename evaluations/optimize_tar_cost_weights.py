import logging
import random

from isla.derivation_tree import DerivationTree
from isla.optimizer import auto_tune_weight_vector
from isla.solver import CostWeightVector
from isla_formalizations import tar
from isla_formalizations.scriptsizec import SCRIPTSIZE_C_GRAMMAR, compile_scriptsizec_clang, \
    SCRIPTSIZE_C_DEF_USE_CONSTR, SCRIPTSIZE_C_NO_REDEF_CONSTR
from isla_formalizations.tar import TAR_GRAMMAR


def validator(t: DerivationTree) -> bool:
    return tar.extract_tar(t) is True


if __name__ == '__main__':
    logging.basicConfig(level=logging.ERROR)
    # logging.getLogger("evaluator").setLevel(logging.DEBUG)

    random.seed(5416874352164316)

    length_constraints_and_checksum_and_link = (
            tar.link_constraint &
            tar.file_name_length_constraint &
            tar.file_mode_length_constraint &
            tar.uid_length_constraint &
            tar.gid_length_constraint &
            tar.file_size_constr &
            tar.mod_time_length_constraint &
            tar.linked_file_name_length_constraint &
            tar.uname_length_constraint &
            tar.gname_length_constraint &
            tar.dev_maj_num_length_constraint &
            tar.dev_min_num_length_constraint &
            tar.prefix_length_constraint &
            tar.header_padding_length_constraint &
            tar.content_length_constraint &
            tar.checksum_constraint &
            tar.content_size_constr &
            tar.final_entry_length_constraint)

    tune_result = auto_tune_weight_vector(
        TAR_GRAMMAR,
        length_constraints_and_checksum_and_link,
        validator,
        timeout=60,
        population_size=16,
        generations=5,
        cpu_count=16,
        seed_population=[
            CostWeightVector(
                tree_closing_cost=4.2,
                constraint_cost=0,
                derivation_depth_penalty=7,
                low_k_coverage_penalty=10,
                low_global_k_path_coverage_penalty=20,
            )])

    tune_result[0].plot("/tmp/tar_autotune_result_state.pdf", "TAR Auto-Tune Result Config Stats")
