from grammar_graph import gg
from grammar_graph.gg import GrammarGraph

from isla.performance_evaluator import Evaluator
from isla.solver import ISLaSolver, CostSettings, GrammarBasedBlackboxCostComputer, CostWeightVector
from isla_formalizations import rest

max_number_free_instantiations = 10
max_number_smt_instantiations = 2
eval_k = 4

cost_vector = CostWeightVector(
    tree_closing_cost=7,
    constraint_cost=1.5,
    derivation_depth_penalty=2.5,
    low_k_coverage_penalty=2,
    low_global_k_path_coverage_penalty=18)

cost_computer = GrammarBasedBlackboxCostComputer(
    CostSettings(cost_vector, k=eval_k),
    gg.GrammarGraph.from_grammar(rest.REST_GRAMMAR),
    reset_coverage_after_n_round_with_no_coverage=1500)

g_link_defuse = lambda timeout: ISLaSolver(
    rest.REST_GRAMMAR,
    rest.DEF_LINK_TARGETS,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_computer=cost_computer,
)

g_link_defuse_len = lambda timeout: ISLaSolver(
    rest.REST_GRAMMAR,
    rest.DEF_LINK_TARGETS & rest.LENGTH_UNDERLINE,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_computer=cost_computer,
)

g_link_defuse_len_numbering = lambda timeout: ISLaSolver(
    rest.REST_GRAMMAR,
    rest.DEF_LINK_TARGETS & rest.LENGTH_UNDERLINE & rest.LIST_NUMBERING_CONSECUTIVE,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_computer=cost_computer,
)

g_link_defuse_len_numbering_no_redef = lambda timeout: ISLaSolver(
    rest.REST_GRAMMAR,
    rest.DEF_LINK_TARGETS & rest.LENGTH_UNDERLINE & rest.LIST_NUMBERING_CONSECUTIVE & rest.NO_LINK_TARGET_REDEF,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_computer=cost_computer,
)

if __name__ == '__main__':
    # logging.basicConfig(level=logging.DEBUG)
    generators = [
        rest.REST_GRAMMAR,
        g_link_defuse,
        g_link_defuse_len,
        g_link_defuse_len_numbering,
        g_link_defuse_len_numbering_no_redef
    ]

    jobnames = [
        "Grammar Fuzzer",
        "Def-Use",
        "Def-Use + Len",
        "Def-Use + Len + List Numbering",
        "Def-Use + Len + List Numbering + No-Redef",
    ]

    evaluator = Evaluator(
        "reST",
        generators,
        jobnames,
        rest.render_rst,
        GrammarGraph.from_grammar(rest.REST_GRAMMAR),
        default_timeout=60 * 60)

    evaluator.run()
