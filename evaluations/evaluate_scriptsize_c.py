from grammar_graph import gg
from grammar_graph.gg import GrammarGraph

from isla.performance_evaluator import Evaluator
from isla.solver import ISLaSolver, CostSettings, CostWeightVector, GrammarBasedBlackboxCostComputer
from isla_formalizations import scriptsizec

max_number_free_instantiations = 10
max_number_smt_instantiations = 2
eval_k = 4

cost_vector = CostWeightVector(
    tree_closing_cost=10,
    constraint_cost=0,
    derivation_depth_penalty=9,
    low_k_coverage_penalty=28,
    low_global_k_path_coverage_penalty=14,
)

g_defuse = lambda timeout: ISLaSolver(
    scriptsizec.SCRIPTSIZE_C_GRAMMAR,
    scriptsizec.SCRIPTSIZE_C_DEF_USE_CONSTR,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_computer=GrammarBasedBlackboxCostComputer(
        CostSettings(cost_vector, k=eval_k),
        gg.GrammarGraph.from_grammar(scriptsizec.SCRIPTSIZE_C_GRAMMAR)),
)

g_redef = lambda timeout: ISLaSolver(
    scriptsizec.SCRIPTSIZE_C_GRAMMAR,
    scriptsizec.SCRIPTSIZE_C_NO_REDEF_CONSTR,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_computer=GrammarBasedBlackboxCostComputer(
        CostSettings(cost_vector, k=eval_k),
        gg.GrammarGraph.from_grammar(scriptsizec.SCRIPTSIZE_C_GRAMMAR)),
)

g_defuse_redef = lambda timeout: ISLaSolver(
    scriptsizec.SCRIPTSIZE_C_GRAMMAR,
    scriptsizec.SCRIPTSIZE_C_DEF_USE_CONSTR & scriptsizec.SCRIPTSIZE_C_NO_REDEF_CONSTR,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_computer=GrammarBasedBlackboxCostComputer(
        CostSettings(cost_vector, k=eval_k),
        gg.GrammarGraph.from_grammar(scriptsizec.SCRIPTSIZE_C_GRAMMAR)),
)

if __name__ == '__main__':
    # logging.basicConfig(level=logging.DEBUG)
    generators = [scriptsizec.SCRIPTSIZE_C_GRAMMAR, g_defuse, g_redef, g_defuse_redef]
    jobnames = ["Grammar Fuzzer", "Def-Use", "No-Redef", "Def-Use + No-Redef"]

    evaluator = Evaluator(
        "Scriptsize-C",
        generators,
        jobnames,
        scriptsizec.compile_scriptsizec_clang,
        GrammarGraph.from_grammar(scriptsizec.SCRIPTSIZE_C_GRAMMAR),
        default_timeout=60 * 60)

    evaluator.run()
