from grammar_graph.gg import GrammarGraph

from isla.performance_evaluator import Evaluator
from isla.solver import ISLaSolver, CostSettings, STD_COST_SETTINGS
from isla_formalizations import rest

max_number_free_instantiations = 10
max_number_smt_instantiations = 2
eval_k = 4

cost_vector = STD_COST_SETTINGS.weight_vectors[0]

g_link_defuse = lambda timeout: ISLaSolver(
    rest.REST_GRAMMAR,
    rest.DEF_LINK_TARGETS,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_settings=CostSettings(cost_vector, k=eval_k)
)

g_link_defuse_len = lambda timeout: ISLaSolver(
    rest.REST_GRAMMAR,
    rest.DEF_LINK_TARGETS & rest.LENGTH_UNDERLINE,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_settings=CostSettings(cost_vector, k=eval_k)
)

g_link_defuse_len_numbering = lambda timeout: ISLaSolver(
    rest.REST_GRAMMAR,
    rest.DEF_LINK_TARGETS & rest.LENGTH_UNDERLINE & rest.LIST_NUMBERING_CONSECUTIVE,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_settings=CostSettings(cost_vector, k=eval_k)
)

g_link_defuse_len_numbering_no_redef = lambda timeout: ISLaSolver(
    rest.REST_GRAMMAR,
    rest.DEF_LINK_TARGETS & rest.LENGTH_UNDERLINE & rest.LIST_NUMBERING_CONSECUTIVE & rest.NO_LINK_TARGET_REDEF,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_settings=CostSettings(cost_vector, k=eval_k)
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
