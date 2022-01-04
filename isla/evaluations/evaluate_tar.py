import sys

from grammar_graph.gg import GrammarGraph

from isla.evaluator import evaluate_generators, plot_proportion_valid_inputs_graph, print_statistics, Evaluator
from isla.solver import ISLaSolver, CostSettings, STD_COST_SETTINGS
from isla.tests.subject_languages import tar

timeout = 15 * 60
max_number_free_instantiations = 10
max_number_smt_instantiations = 2
eval_k = 3

cost_vector = STD_COST_SETTINGS.weight_vectors[0]

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
