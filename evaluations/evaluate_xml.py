from grammar_graph import gg
from grammar_graph.gg import GrammarGraph

from isla.performance_evaluator import Evaluator
from isla.solver import ISLaSolver, CostSettings, CostWeightVector, GrammarBasedBlackboxCostComputer
from isla_formalizations import xml_lang

max_number_free_instantiations = 10
max_number_smt_instantiations = 2
eval_k = 4

cost_vector = CostWeightVector(
    tree_closing_cost=10,
    constraint_cost=0,
    derivation_depth_penalty=6,
    low_k_coverage_penalty=0,
    low_global_k_path_coverage_penalty=13)

g_wf = lambda timeout: ISLaSolver(
    xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
    xml_lang.XML_WELLFORMEDNESS_CONSTRAINT,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_computer=GrammarBasedBlackboxCostComputer(
        CostSettings(cost_vector, k=eval_k),
        gg.GrammarGraph.from_grammar(xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES)),
)

g_ns = lambda timeout: ISLaSolver(
    xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
    xml_lang.XML_NAMESPACE_CONSTRAINT,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_computer=GrammarBasedBlackboxCostComputer(
        CostSettings(cost_vector, k=eval_k),
        gg.GrammarGraph.from_grammar(xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES)),
)

g_redef = lambda timeout: ISLaSolver(
    xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
    xml_lang.XML_NO_ATTR_REDEF_CONSTRAINT,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_computer=GrammarBasedBlackboxCostComputer(
        CostSettings(cost_vector, k=eval_k),
        gg.GrammarGraph.from_grammar(xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES)),
)

g_wf_ns = lambda timeout: ISLaSolver(
    xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
    xml_lang.XML_WELLFORMEDNESS_CONSTRAINT & xml_lang.XML_NAMESPACE_CONSTRAINT,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_computer=GrammarBasedBlackboxCostComputer(
        CostSettings(cost_vector, k=eval_k),
        gg.GrammarGraph.from_grammar(xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES)),
)

g_wf_ns_redef = lambda timeout: ISLaSolver(
    xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
    xml_lang.XML_WELLFORMEDNESS_CONSTRAINT &
    xml_lang.XML_NAMESPACE_CONSTRAINT &
    xml_lang.XML_NO_ATTR_REDEF_CONSTRAINT,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_computer=GrammarBasedBlackboxCostComputer(
        CostSettings(cost_vector, k=eval_k),
        gg.GrammarGraph.from_grammar(xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES)),
)

if __name__ == '__main__':
    # logging.basicConfig(level=logging.DEBUG)
    generators = [xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES, g_wf, g_ns, g_redef, g_wf_ns, g_wf_ns_redef]
    jobnames = ["Grammar Fuzzer", "Balance", "Def-Use", "No-Redef", "Balance + Def-Use", "Balance + Def-Use + No-Redef"]

    evaluator = Evaluator(
        "XML",
        generators,
        jobnames,
        xml_lang.validate_xml,
        GrammarGraph.from_grammar(xml_lang.XML_GRAMMAR_WITH_NAMESPACE_PREFIXES),
        default_timeout=60 * 60)

    evaluator.run()
