from grammar_graph.gg import GrammarGraph

from input_constraints.tests.subject_languages import rest
from input_constraints.evaluator import evaluate_generators, plot_proportion_valid_inputs_graph
from input_constraints.solver import ISLaSolver, CostSettings, CostWeightVector, STD_COST_SETTINGS

timeout = 60 * 60

cost_vector = STD_COST_SETTINGS.weight_vectors[0]

k = 3

g_title_len = ISLaSolver(
    rest.REST_GRAMMAR,
    rest.LENGTH_UNDERLINE,
    max_number_free_instantiations=1,
    max_number_smt_instantiations=1,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=k)
)

g_link_defuse = ISLaSolver(
    rest.REST_GRAMMAR,
    rest.DEF_LINK_TARGETS,
    max_number_free_instantiations=1,
    max_number_smt_instantiations=1,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=k)
)

g_no_link_redef = ISLaSolver(
    rest.REST_GRAMMAR,
    rest.NO_LINK_TARGET_REDEF,
    max_number_free_instantiations=1,
    max_number_smt_instantiations=1,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=k)
)

g_list_numbers_consecutive = ISLaSolver(
    rest.REST_GRAMMAR,
    rest.LIST_NUMBERING_CONSECUTIVE,
    max_number_free_instantiations=1,
    max_number_smt_instantiations=1,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=k)
)

g_link_defuse_len = ISLaSolver(
    rest.REST_GRAMMAR,
    rest.DEF_LINK_TARGETS & rest.LENGTH_UNDERLINE,
    max_number_free_instantiations=1,
    max_number_smt_instantiations=1,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=k)
)

g_link_defuse_len_numbering = ISLaSolver(
    rest.REST_GRAMMAR,
    rest.DEF_LINK_TARGETS & rest.LENGTH_UNDERLINE & rest.LIST_NUMBERING_CONSECUTIVE,
    max_number_free_instantiations=1,
    max_number_smt_instantiations=1,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=k)
)

g_link_defuse_len_numbering_no_redef = ISLaSolver(
    rest.REST_GRAMMAR,
    rest.DEF_LINK_TARGETS & rest.LENGTH_UNDERLINE & rest.LIST_NUMBERING_CONSECUTIVE & rest.NO_LINK_TARGET_REDEF,
    max_number_free_instantiations=1,
    max_number_smt_instantiations=1,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=k)
)


def evaluate_validity(out_dir: str, base_name: str, generators, jobnames):
    results = evaluate_generators(
        generators,
        None,
        GrammarGraph.from_grammar(rest.REST_GRAMMAR),
        rest.render_rst,
        timeout,
        k=3,
        cpu_count=len(generators),
        jobnames=jobnames
    )

    for result, jobname in zip(results, jobnames):
        result.save_to_csv_file(out_dir, base_name + jobname)


if __name__ == '__main__':
    generators = [
        rest.REST_GRAMMAR,
        g_link_defuse,
        g_link_defuse_len,
        g_link_defuse_len_numbering,
        g_link_defuse_len_numbering_no_redef

        # g_title_len,
        # g_no_link_redef,
        # g_list_numbers_consecutive,
    ]

    jobnames = [
        "Grammar Fuzzer",
        "Def-Use",
        "Def-Use + Len",
        "Def-Use + Len + List Numbering",
        "Def-Use + Len + List Numbering + No-Redef",

        # "List Numbering",
        # "Len",
        # "No-Redef",
    ]

    out_dir = "../../eval_results/rest"
    base_name = "input_validity_rest_"

    evaluate_validity(out_dir, base_name, generators, jobnames)
    plot_proportion_valid_inputs_graph(out_dir, base_name, jobnames, f"{out_dir}/input_validity_rest.pdf")
