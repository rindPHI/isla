import os
import sys

from grammar_graph.gg import GrammarGraph
import pathos.multiprocessing as pmp

from isla.evaluator import evaluate_generators, plot_proportion_valid_inputs_graph, print_statistics, generate_inputs, \
    store_inputs, evaluate_validity, evaluate_kpaths, Evaluator
from isla.solver import ISLaSolver, CostSettings, CostWeightVector
from isla.tests.subject_languages import scriptsizec

# timeout = 60 * 60
timeout = 6
max_number_free_instantiations = 10
max_number_smt_instantiations = 2
eval_k = 4

cost_vector = CostWeightVector(
    tree_closing_cost=10,
    vacuous_penalty=0,
    constraint_cost=0,
    derivation_depth_penalty=9,
    low_k_coverage_penalty=28,
    low_global_k_path_coverage_penalty=4)

g_defuse = ISLaSolver(
    scriptsizec.SCRIPTSIZE_C_GRAMMAR,
    scriptsizec.SCRIPTSIZE_C_DEF_USE_CONSTR,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=eval_k)
)

g_redef = ISLaSolver(
    scriptsizec.SCRIPTSIZE_C_GRAMMAR,
    scriptsizec.SCRIPTSIZE_C_NO_REDEF_CONSTR,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=eval_k)
)

g_defuse_redef = ISLaSolver(
    scriptsizec.SCRIPTSIZE_C_GRAMMAR,
    scriptsizec.SCRIPTSIZE_C_DEF_USE_CONSTR & scriptsizec.SCRIPTSIZE_C_NO_REDEF_CONSTR,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_settings=CostSettings((cost_vector,), (1000,), k=eval_k)
)

# def evaluate_validity(out_dir: str, base_name: str, generators, jobnames):
#     results = evaluate_generators(
#         generators,
#         None,
#         GrammarGraph.from_grammar(scriptsizec.SCRIPTSIZE_C_GRAMMAR),
#         scriptsizec.compile_scriptsizec_clang,
#         timeout,
#         k=3,
#         cpu_count=len(generators),
#         jobnames=jobnames
#     )
#
#     for result, jobname in zip(results, jobnames):
#         result.save_to_csv_file(out_dir, base_name + jobname)


if __name__ == '__main__':
    generators = [scriptsizec.SCRIPTSIZE_C_GRAMMAR, g_defuse, g_redef, g_defuse_redef]
    jobnames = ["Grammar Fuzzer", "Def-Use", "No-Redef", "Def-Use + No-Redef"]

    evaluator = Evaluator(
        "Scriptsize-C",
        generators,
        jobnames,
        scriptsizec.compile_scriptsizec_clang,
        GrammarGraph.from_grammar(scriptsizec.SCRIPTSIZE_C_GRAMMAR))

    evaluator.run()

    # with pmp.Pool(processes=16) as pool:
    #     pool.starmap(
    #         lambda generator, jobname:
    #         store_inputs(jobname, generate_inputs(generator, timeout, jobname)),
    #         [(generator, jobname)
    #          for jobname, generator in zip(jobnames, generators)])

    # for jobname, generator in zip(jobnames, generators):
    #     timeout = 6  # TODO Remove
    #     inputs = generate_inputs(generator, timeout)
    #     store_inputs(jobname, inputs)

    # for jobname in jobnames:
    #     evaluate_validity(jobname, scriptsizec.compile_scriptsizec_clang)

    # for jobname in jobnames:
    #     evaluate_kpaths(jobname, graph=GrammarGraph.from_grammar(scriptsizec.SCRIPTSIZE_C_GRAMMAR), k=3)

    # out_dir = "../../eval_results/scriptsizec"
    # base_name = "input_validity_scriptsizec_"
    #
    # evaluate_validity(out_dir, base_name, generators, jobnames)
    # plot_proportion_valid_inputs_graph(out_dir, base_name, jobnames, f"{out_dir}/input_validity_scriptsizec.pdf")
    # print_statistics(out_dir, base_name, jobnames)
