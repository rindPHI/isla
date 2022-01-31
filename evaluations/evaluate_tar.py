from grammar_graph.gg import GrammarGraph

from isla.evaluator import Evaluator
from isla.solver import ISLaSolver, CostSettings, CostWeightVector
from isla_formalizations import tar

max_number_free_instantiations = 10
max_number_smt_instantiations = 2
eval_k = 4

cost_vector = CostWeightVector(
    tree_closing_cost=11,
    vacuous_penalty=0,
    constraint_cost=3,
    derivation_depth_penalty=5,
    low_k_coverage_penalty=10,
    low_global_k_path_coverage_penalty=40)

length_constraints = (
    # tar.link_constraint &
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
        # tar.checksum_constraint &
        tar.content_size_constr &
        tar.final_entry_length_constraint
)

length_constraints_and_checksum = (
    # tar.link_constraint &
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
        tar.final_entry_length_constraint
)

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
        tar.final_entry_length_constraint
)

g_len = lambda timeout: ISLaSolver(
    tar.TAR_GRAMMAR,
    length_constraints,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=eval_k)
)

g_len_cs = lambda timeout: ISLaSolver(
    tar.TAR_GRAMMAR,
    length_constraints_and_checksum,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=eval_k)
)

g_len_cs_lin = lambda timeout: ISLaSolver(
    tar.TAR_GRAMMAR,
    length_constraints_and_checksum_and_link,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=eval_k)
)

if __name__ == '__main__':
    # logging.basicConfig(level=logging.DEBUG)
    generators = [tar.TAR_GRAMMAR, g_len, g_len_cs, g_len_cs_lin]
    jobnames = ["Grammar Fuzzer", "Length", "Length + Checksum", "Length + Checksum + Def-Use"]

    evaluator = Evaluator(
        "tar",
        generators,
        jobnames,
        tar.extract_tar,
        GrammarGraph.from_grammar(tar.TAR_GRAMMAR),
        default_timeout=60 * 60)

    evaluator.run()
