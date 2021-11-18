import logging

from grammar_graph.gg import GrammarGraph

from input_constraints.evaluator import evaluate_generators, plot_proportion_valid_inputs_graph
from input_constraints.solver import ISLaSolver, CostSettings, STD_COST_SETTINGS
from input_constraints.tests.subject_languages import tar

timeout = 90

cost_vector = STD_COST_SETTINGS.weight_vectors[0]

k = 3

g_full = ISLaSolver(
    tar.TAR_GRAMMAR,
    tar.TAR_CONSTRAINTS,
    max_number_free_instantiations=1,
    max_number_smt_instantiations=1,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=k)
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
    # generators = [tar.TAR_GRAMMAR, g_full]
    # jobnames = ["Grammar Fuzzer", "Full Constraint"]
    generators = [g_full]
    jobnames = ["Full Constraint"]

    out_dir = "../../eval_results/tar"
    base_name = "input_validity_tar_"

    evaluate_validity(out_dir, base_name, generators, jobnames)
    plot_proportion_valid_inputs_graph(out_dir, base_name, jobnames, f"{out_dir}/input_validity_tar.pdf")
