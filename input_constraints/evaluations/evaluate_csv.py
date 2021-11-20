import sys

from grammar_graph.gg import GrammarGraph

from input_constraints.tests.subject_languages import csv
from input_constraints.evaluator import evaluate_generators, plot_proportion_valid_inputs_graph, print_statistics
from input_constraints.solver import ISLaSolver, CostSettings, CostWeightVector, STD_COST_SETTINGS

timeout = 60 * 60
max_number_free_instantiations = 10
max_number_smt_instantiations = 2
eval_k = 3

cost_vector = STD_COST_SETTINGS.weight_vectors[0]

g_colno = ISLaSolver(
    csv.CSV_GRAMMAR,
    csv.CSV_COLNO_PROPERTY,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=eval_k)
)


def evaluate_validity(out_dir: str, base_name: str, generators, jobnames):
    results = evaluate_generators(
        generators,
        None,
        GrammarGraph.from_grammar(csv.CSV_GRAMMAR),
        csv.csv_lint,
        timeout,
        k=3,
        cpu_count=len(generators),
        jobnames=jobnames
    )

    for result, jobname in zip(results, jobnames):
        result.save_to_csv_file(out_dir, base_name + jobname)


if __name__ == '__main__':
    generators = [csv.CSV_GRAMMAR, g_colno]
    jobnames = ["Grammar Fuzzer", "Cnt-Columns"]

    if len(sys.argv) > 1 and sys.argv[1] in jobnames:
        idx = jobnames.index(sys.argv[1])
        generators = [generators[idx]]
        jobnames = [jobnames[idx]]

    out_dir = "../../eval_results/csv"
    base_name = "input_validity_csv_"

    # evaluate_validity(out_dir, base_name, generators, jobnames)
    # plot_proportion_valid_inputs_graph(out_dir, base_name, jobnames, f"{out_dir}/input_validity_csv.pdf")
    print_statistics(out_dir, base_name, jobnames)
