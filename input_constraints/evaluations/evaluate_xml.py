import sys

from grammar_graph.gg import GrammarGraph

from input_constraints.tests.subject_languages import xml_lang
from input_constraints.evaluator import evaluate_generators, plot_proportion_valid_inputs_graph, print_statistics
from input_constraints.solver import ISLaSolver, CostSettings, CostWeightVector

timeout = 60 * 60

cost_vector = CostWeightVector(
    tree_closing_cost=15,
    vacuous_penalty=15,
    constraint_cost=0,
    derivation_depth_penalty=0,
    low_k_coverage_penalty=5,
    low_global_k_path_coverage_penalty=7)

k = 4

g_wf = ISLaSolver(
    xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
    xml_lang.XML_WELLFORMEDNESS_CONSTRAINT,
    max_number_free_instantiations=1,
    max_number_smt_instantiations=1,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=k)
)

g_ns = ISLaSolver(
    xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
    xml_lang.XML_NAMESPACE_CONSTRAINT,
    max_number_free_instantiations=1,
    max_number_smt_instantiations=1,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=k)
)

g_redef = ISLaSolver(
    xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
    xml_lang.XML_NO_ATTR_REDEF_CONSTRAINT,
    max_number_free_instantiations=1,
    max_number_smt_instantiations=1,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=k)
)

g_wf_ns = ISLaSolver(
    xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
    xml_lang.XML_WELLFORMEDNESS_CONSTRAINT & xml_lang.XML_NAMESPACE_CONSTRAINT,
    max_number_free_instantiations=1,
    max_number_smt_instantiations=1,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=k)
)

g_wf_ns_redef = ISLaSolver(
    xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
    xml_lang.XML_WELLFORMEDNESS_CONSTRAINT &
    xml_lang.XML_NAMESPACE_CONSTRAINT &
    xml_lang.XML_NO_ATTR_REDEF_CONSTRAINT,
    max_number_free_instantiations=1,
    max_number_smt_instantiations=1,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=k)
)


def evaluate_validity(out_dir: str, base_name: str, generators, jobnames):
    results = evaluate_generators(
        generators,
        None,
        GrammarGraph.from_grammar(xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES),
        xml_lang.validate_xml,
        timeout,
        k=3,
        cpu_count=len(generators),
        jobnames=jobnames
    )

    for result, jobname in zip(results, jobnames):
        result.save_to_csv_file(out_dir, base_name + jobname)


if __name__ == '__main__':
    generators = [xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES, g_wf, g_ns, g_redef, g_wf_ns, g_wf_ns_redef]
    jobnames = ["Grammar Fuzzer", "Balance", "Def-Use", "No-Redef", "Balance + Def-Use", "Balance + Def-Use + No-Redef"]

    if len(sys.argv) > 1 and sys.argv[1] in jobnames:
        idx = jobnames.index(sys.argv[1])
        generators = [generators[idx]]
        jobnames = [jobnames[idx]]

    out_dir = "../../eval_results/xml"
    base_name = "input_validity_xml_"

    # evaluate_validity(out_dir, base_name, generators, jobnames)
    # plot_proportion_valid_inputs_graph(out_dir, base_name, jobnames, f"{out_dir}/input_validity_xml.pdf")
    print_statistics(out_dir, base_name, jobnames)
