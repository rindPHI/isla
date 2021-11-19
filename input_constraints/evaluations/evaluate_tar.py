import logging
import sys

from grammar_graph.gg import GrammarGraph

from input_constraints.evaluator import evaluate_generators, plot_proportion_valid_inputs_graph, print_statistics
from input_constraints.solver import ISLaSolver, CostSettings, STD_COST_SETTINGS
from input_constraints.tests.subject_languages import tar

timeout = 60 * 60
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

g_len = ISLaSolver(
    tar.TAR_GRAMMAR,
    length_constraints,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=eval_k)
)

g_len_cs = ISLaSolver(
    tar.TAR_GRAMMAR,
    length_constraints_and_checksum,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=eval_k)
)

g_len_cs_lin = ISLaSolver(
    tar.TAR_GRAMMAR,
    length_constraints_and_checksum_and_link,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=eval_k)
)


def evaluate_validity(out_dir: str, base_name: str, generators, jobnames):
    results = evaluate_generators(
        generators,
        None,
        GrammarGraph.from_grammar(tar.TAR_GRAMMAR),
        tar.extract_tar,
        timeout,
        k=3,
        cpu_count=len(generators),
        jobnames=jobnames,
        compute_vacuity=False,
        compute_kpath_coverage=False
    )

    for result, jobname in zip(results, jobnames):
        result.save_to_csv_file(out_dir, base_name + jobname)


if __name__ == '__main__':
    # logging.basicConfig(level=logging.DEBUG)
    generators = [g_len, g_len_cs, g_len_cs_lin]
    jobnames = ["Length", "Length + Checksum", "Length + Checksum + Def-Use"]

    if len(sys.argv) > 1 and sys.argv[1] in jobnames:
        idx = jobnames.index(sys.argv[1])
        generators = [generators[idx]]
        jobnames = [jobnames[idx]]

    out_dir = "../../eval_results/tar"
    base_name = "input_validity_tar_"

    # evaluate_validity(out_dir, base_name, generators, jobnames)
    # plot_proportion_valid_inputs_graph(out_dir, base_name, jobnames, f"{out_dir}/input_validity_tar.pdf")
    print_statistics(out_dir, base_name, jobnames)
