from grammar_graph import gg
from grammar_graph.gg import GrammarGraph

from isla.performance_evaluator import Evaluator
from isla.repair_solver import RepairSolver
from isla.solver import (
    ISLaSolver,
    CostSettings,
    CostWeightVector,
    GrammarBasedBlackboxCostComputer,
)
from isla_formalizations import scriptsizec

max_number_free_instantiations = 10
max_number_smt_instantiations = 2
eval_k = 3

cost_vector = CostWeightVector(
    tree_closing_cost=5,
    constraint_cost=2,
    derivation_depth_penalty=6,
    low_k_coverage_penalty=2,
    low_global_k_path_coverage_penalty=21,
)

cost_computer = GrammarBasedBlackboxCostComputer(
    CostSettings(cost_vector, k=eval_k),
    gg.GrammarGraph.from_grammar(scriptsizec.SCRIPTSIZE_C_GRAMMAR),
)

g_defuse = lambda timeout: ISLaSolver(
    scriptsizec.SCRIPTSIZE_C_GRAMMAR,
    scriptsizec.SCRIPTSIZE_C_DEF_USE_CONSTR,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_computer=cost_computer,
)

g_redef = lambda timeout: ISLaSolver(
    scriptsizec.SCRIPTSIZE_C_GRAMMAR,
    scriptsizec.SCRIPTSIZE_C_NO_REDEF_CONSTR,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_computer=cost_computer,
)

g_defuse_redef = lambda timeout: ISLaSolver(
    scriptsizec.SCRIPTSIZE_C_GRAMMAR,
    scriptsizec.SCRIPTSIZE_C_DEF_USE_CONSTR & scriptsizec.SCRIPTSIZE_C_NO_REDEF_CONSTR,
    max_number_free_instantiations=max_number_free_instantiations,
    max_number_smt_instantiations=max_number_smt_instantiations,
    timeout_seconds=timeout,
    cost_computer=cost_computer,
)

repair_defuse_redef = lambda timeout: RepairSolver(
    scriptsizec.SCRIPTSIZE_C_GRAMMAR,
    scriptsizec.SCRIPTSIZE_C_DEF_USE_CONSTR & scriptsizec.SCRIPTSIZE_C_NO_REDEF_CONSTR,
    timeout_seconds=timeout,
).solve_iterator


if __name__ == "__main__":
    # logging.basicConfig(level=logging.DEBUG)
    generators = [
        scriptsizec.SCRIPTSIZE_C_GRAMMAR,
        g_defuse,
        g_redef,
        g_defuse_redef,
        repair_defuse_redef,
    ]
    jobnames = [
        "Grammar Fuzzer",
        "Def-Use",
        "No-Redef",
        "Def-Use + No-Redef",
        "Def-Use + No-Redef (RepairSolver)",
    ]

    evaluator = Evaluator(
        "Scriptsize-C",
        generators,
        jobnames,
        scriptsizec.compile_scriptsizec_clang,
        GrammarGraph.from_grammar(scriptsizec.SCRIPTSIZE_C_GRAMMAR),
        default_timeout=60 * 60,
    )

    evaluator.run()
