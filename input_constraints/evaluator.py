import copy
import datetime
import logging
import math
import multiprocessing as mp
import random
import subprocess
import time
from textwrap import wrap
from typing import List, Generator, Dict, Callable, Set, Tuple, Optional

import matplotlib
import matplotlib.pyplot as plt
import z3
from grammar_graph import gg

import input_constraints.isla_shortcuts as sc
from input_constraints import isla, solver
from input_constraints.solver import ISLaSolver, CostWeightVector, CostSettings
from input_constraints.type_defs import Grammar

logger = logging.getLogger("evaluator")


def set_smt_auto_eval(formula: isla.Formula, auto_eval: bool = False):
    class AutoEvalVisitor(isla.FormulaVisitor):
        def visit_smt_formula(self, formula: isla.SMTFormula):
            formula.auto_eval = auto_eval

    formula.accept(AutoEvalVisitor())


def vacuously_satisfies(inp: isla.DerivationTree, formula: isla.Formula) -> bool:
    # Note: This assumes that `inp` *does* satisfy `formula`!
    assert isla.evaluate(formula, inp)

    formula = copy.deepcopy(formula)
    set_smt_auto_eval(formula, False)

    constant = next(
        c for c in isla.VariablesCollector.collect(formula)
        if isinstance(c, isla.Constant))

    qfr_free: List[isla.Formula] = isla.eliminate_quantifiers(formula.substitute_expressions({constant: inp}))
    qfr_free_dnf: List[isla.Formula] = [isla.convert_to_dnf(isla.convert_to_nnf(f)) for f in qfr_free]
    clauses: List[List[isla.Formula]] = [
        isla.split_conjunction(_f)
        for f in qfr_free_dnf
        for _f in isla.split_disjunction(f)
    ]

    # There needs to be one non-trivial clause for non-vacuous satisfaction
    clauses = [
        clause for clause in clauses
        if all(f != sc.false() for f in clause)
           and any(not isinstance(f, isla.SMTFormula) or not z3.is_true(f.formula) for f in clause)
    ]

    return not clauses


def collect_data(
        generator: Generator[isla.DerivationTree, None, None],
        timeout_seconds: int = 60) -> Dict[float, isla.DerivationTree]:
    start_time = time.time()
    result: Dict[float, isla.DerivationTree] = {}
    logger.info("Collecting data for %d seconds", timeout_seconds)

    while int(time.time()) - int(start_time) <= timeout_seconds:
        try:
            inp = next(generator)
        except StopIteration:
            break

        logger.debug("Input: %s", str(inp))
        curr_relative_time = time.time() - start_time
        assert curr_relative_time not in result
        result[curr_relative_time] = inp

    logger.info("Collected %d inputs in %d seconds", len(result), timeout_seconds)
    return result


class PerformanceEvaluationResult:
    def __init__(
            self,
            accumulated_valid_inputs: Dict[float, int],
            accumulated_k_path_coverage: Dict[float, int],
            accumulated_non_vacuous_index: Dict[float, float]):
        self.accumulated_valid_inputs = accumulated_valid_inputs
        self.accumulated_k_path_coverage = accumulated_k_path_coverage
        self.accumulated_non_vacuous_index = accumulated_non_vacuous_index

        max_time = max(accumulated_valid_inputs.keys())
        self.final_product_value: float = self.single_product_value(max_time)

    def mean_data(self) -> Dict[float, float]:
        return {
            seconds: self.single_product_value(seconds)
            for seconds in self.accumulated_valid_inputs}

    def single_product_value(self, seconds: float, weights: tuple[int, ...] = (4, 3, 1)) -> float:
        return ((self.accumulated_valid_inputs[seconds] + 1) *
                (self.accumulated_k_path_coverage[seconds] + 1) *
                (self.accumulated_non_vacuous_index[seconds] + 1)) ** (1 / float(3)) - 1

    def plot(self, outfile_pdf: str, title: str = "Performance Data"):
        assert outfile_pdf.endswith(".pdf")
        matplotlib.use("PDF")

        fig, ax = plt.subplots()
        ax.plot(
            list(self.accumulated_valid_inputs.keys()),
            list(self.accumulated_valid_inputs.values()),
            label="Valid Inputs")
        ax.plot(
            list(self.accumulated_k_path_coverage.keys()),
            list(self.accumulated_k_path_coverage.values()),
            label="k-Path Coverage (%)")
        ax.plot(
            list(self.accumulated_non_vacuous_index.keys()),
            list(self.accumulated_non_vacuous_index.values()),
            label="Non-Vacuity Index")

        mean = self.mean_data()
        ax.plot(
            list(mean.keys()),
            list(mean.values()),
            label="Geometric Mean")

        for values in [
            self.accumulated_valid_inputs.values(),
            self.accumulated_k_path_coverage.values(),
            self.accumulated_non_vacuous_index.values(),
            mean.values()
        ]:
            plt.annotate(
                max(values),
                xy=(1, max(values)),
                xytext=(8, 0),
                xycoords=('axes fraction', 'data'),
                textcoords='offset points')

        ax.set_xlabel("Seconds")
        ax.set_title(title)
        ax.legend()
        fig.tight_layout()
        plt.plot()

        logger.info("Saving performance analysis plot to %s", outfile_pdf)
        matplotlib.pyplot.savefig(outfile_pdf)

    def __repr__(self):
        return (f"PerformanceEvaluationResult(accumulated_valid_inputs={self.accumulated_valid_inputs}, "
                f"accumulated_k_path_coverage={self.accumulated_k_path_coverage}, "
                f"accumulated_non_vacuous_index={self.accumulated_non_vacuous_index})")

    def __str__(self):
        return f"Performance: {self.final_product_value} (" \
               f"valid inputs: {list(self.accumulated_valid_inputs.values())[-1]}, " \
               f"k-Path Coverage: {list(self.accumulated_k_path_coverage.values())[-1]}, " \
               f"Non-Vacuity Index: {list(self.accumulated_non_vacuous_index.values())[-1]})"


def evaluate_data(
        data: Dict[float, isla.DerivationTree],
        formula: isla.Formula,
        graph: gg.GrammarGraph,
        validator: Callable[[isla.DerivationTree], bool],
        k: int = 3) -> PerformanceEvaluationResult:
    accumulated_valid_inputs: Dict[float, int] = {}
    accumulated_k_path_coverage: Dict[float, int] = {}
    accumulated_non_vacuous_index: Dict[float, float] = {}

    quantifier_chains: List[Tuple[isla.ForallFormula, ...]] = [
        tuple([f for f in c if isinstance(f, isla.ForallFormula)])
        for c in solver.get_quantifier_chains(formula)]

    valid_inputs: int = 0
    covered_kpaths: Set[Tuple[gg.Node, ...]] = set()
    chains_satisfied: Dict[Tuple[isla.ForallFormula, ...], int] = {c: 0 for c in quantifier_chains}

    for seconds, inp in data.items():
        if validator(inp):
            valid_inputs += 1
        else:
            logger.debug("Input %s invalid", str(inp))
            continue

        if quantifier_chains:
            vacuously_matched_quantifiers = set()
            isla.eliminate_quantifiers(
                isla.instantiate_top_constant(formula, inp),
                vacuously_matched_quantifiers, graph.to_grammar())

            non_vacuous_chains = {
                c for c in quantifier_chains if
                all(of.id != f.id
                    for of in vacuously_matched_quantifiers
                    for f in c)}

            for c in non_vacuous_chains:
                assert c in chains_satisfied
                chains_satisfied[c] += 1

        # if not vacuously_satisfies(inp, formula):
        #     non_vacuous_inputs += 1

        covered_kpaths.update(graph.k_paths_in_tree(inp.to_parse_tree(), k))
        accumulated_valid_inputs[seconds] = valid_inputs
        accumulated_k_path_coverage[seconds] = int(len(covered_kpaths) * 100 / len(graph.k_paths(k)))

        if quantifier_chains:
            # Values in chains_satisfied range between 0 and `valid_inputs`, and thus the mean, too.
            chains_satisfied_mean = (
                    math.prod([v + 1 for v in chains_satisfied.values()]) ** (1 / len(chains_satisfied)) - 1)
            assert 0 <= chains_satisfied_mean <= valid_inputs
            # We normalize to a percentage-like value between 0 and 100
            accumulated_non_vacuous_index[seconds] = 100 * chains_satisfied_mean / valid_inputs
            assert 0 <= accumulated_non_vacuous_index[seconds] <= 100
        else:
            accumulated_non_vacuous_index[seconds] = 0

    result = PerformanceEvaluationResult(
        accumulated_valid_inputs,
        accumulated_k_path_coverage,
        accumulated_non_vacuous_index)

    logger.info(
        "Final evaluation values: %d valid inputs, %d %% coverage, %f non-vacuous index, final mean: %f",
        valid_inputs,
        int(len(covered_kpaths) * 100 / len(graph.k_paths(k))),
        list(accumulated_non_vacuous_index.values())[-1],
        list(result.mean_data().values())[-1]
    )

    return result


def evaluate_generator(
        producer: Generator[isla.DerivationTree, None, None],
        formula: isla.Formula,
        graph: gg.GrammarGraph,
        validator: Callable[[isla.DerivationTree], bool],
        outfile_pdf: Optional[str] = None,
        timeout_seconds: int = 60,
        diagram_title: str = "Performance Data",
        k=3) -> PerformanceEvaluationResult:
    logger.info("Collecting performance data")
    data = collect_data(producer, timeout_seconds=timeout_seconds)
    logger.info("Evaluating Data")
    evaluation_result = evaluate_data(data, formula, graph, validator, k)

    if outfile_pdf:
        logger.info(f"Plotting result to {outfile_pdf}")
        evaluation_result.plot(outfile_pdf, title=diagram_title)

    return evaluation_result


def evaluate_isla_generator(
        grammar: Grammar,
        formula: isla.Formula,
        v: CostWeightVector,
        validator: Callable[[isla.DerivationTree], bool],
        timeout: int,
        outfile_name: Optional[str] = None,
        k=3) -> PerformanceEvaluationResult:
    logger.info("Evaluating weight vector %s", v)
    isla_producer = ISLaSolver(
        grammar,
        formula,
        max_number_free_instantiations=1,
        max_number_smt_instantiations=1,
        timeout_seconds=timeout,
        cost_settings=CostSettings((v,), (200,))
    ).solve()

    return evaluate_generator(
        outfile_pdf=outfile_name,
        diagram_title="\n".join(wrap(str(v), 60)),
        producer=isla_producer,
        formula=formula,
        graph=gg.GrammarGraph.from_grammar(grammar),
        validator=validator,
        timeout_seconds=timeout,
        k=k)


def randno(maxno: int = 40) -> int:
    return random.choices(range(maxno + 1), weights=list(reversed([n // 10 + 1 for n in range(maxno + 1)])))[0]


def evaluate_random_cost_vectors(
        grammar: Grammar,
        formula: isla.Formula,
        validator: Callable[[isla.DerivationTree], bool],
        final_out_file_name: str,
        timeout: int = 60,
        rounds: int = 30,
        k: int = 3):
    for i in range(rounds):
        v = CostWeightVector(
            tree_closing_cost=randno(),
            vacuous_penalty=randno(),
            constraint_cost=randno(),
            derivation_depth_penalty=randno(),
            low_k_coverage_penalty=randno()
        )
        logger.info("Round %d, cost vector %s", i + 1, str(v))
        outfile_name = f"/tmp/xml_perf_eval_{str((i + 1)).rjust(len(str(rounds)), '0')}.pdf"

        evaluate_isla_generator(grammar, formula, v, validator, timeout, outfile_name, k)

    process = subprocess.run(
        ["pdfjam"] +
        [f"/tmp/xml_perf_eval_{str((i + 1)).rjust(len(str(rounds)), '0')}.pdf" for i in range(rounds)] +
        ["--nup", "4x3", "--landscape", "--outfile", final_out_file_name],
        stderr=subprocess.PIPE)

    if process.returncode != 0:
        logger.error("Combining output PDFs did not work, error message: %s", process.stderr)
    else:
        logger.info("Saved combined output file at %s", final_out_file_name)


def mutate_cost_weight(w: float, max_add: int = 5, max_factor: int = 3) -> float:
    if w == 0:
        return w + random.choices(
            range(1, max_add + 1),
            list(reversed(list(map(lambda x: 1.2 ** x, range(max_add))))))[0]

    else:
        factor = random.choices(
            range(1, max_factor + 1),
            list(reversed(list(map(lambda x: 1.2 ** x, range(max_factor))))))[0] + .5

        return w * factor if random.random() < .5 else w / factor


def evaluate_mutated_cost_vectors(
        grammar: Grammar,
        formula: isla.Formula,
        base_vector: CostWeightVector,
        validator: Callable[[isla.DerivationTree], bool],
        final_out_file_name: str,
        timeout: int = 60,
        rounds: int = 30,
        k: int = 3):
    args = {
        "tree_closing_cost": base_vector.tree_closing_cost,
        "vacuous_penalty": base_vector.vacuous_penalty,
        "constraint_cost": base_vector.constraint_cost,
        "derivation_depth_penalty": base_vector.derivation_depth_penalty,
        "low_coverage_penalty": base_vector.low_k_coverage_penalty,
        "low_global_k_path_coverage_penalty": base_vector.low_global_k_path_coverage_penalty
    }

    for i in range(rounds):
        num_mutated_elements = random.choices(range(1, 6), weights=[400, 200, 100, 50, 25], k=1)[0]
        mutated_elements = random.sample(args.keys(), k=num_mutated_elements)

        new_args = copy.copy(args)
        new_args.update({elem: mutate_cost_weight(args[elem]) for elem in mutated_elements})
        v = CostWeightVector(**new_args)

        logger.info("Round %d, cost vector %s", i + 1, str(v))
        outfile_name = f"/tmp/xml_perf_eval_{str((i + 1)).rjust(len(str(rounds)), '0')}.pdf"

        evaluate_isla_generator(grammar, formula, v, validator, timeout, outfile_name, k)

    process = subprocess.run(
        ["pdfjam"] +
        [f"/tmp/xml_perf_eval_{str((i + 1)).rjust(len(str(rounds)), '0')}.pdf" for i in range(rounds)] +
        ["--nup", "4x3", "--landscape", "--outfile", final_out_file_name],
        stderr=subprocess.PIPE)

    if process.returncode != 0:
        logger.error("Combining output PDFs did not work, error message: %s", process.stderr)
    else:
        logger.info("Saved combined output file at %s", final_out_file_name)


def evaluate_cost_vectors_isla(
        population: List[CostWeightVector],
        grammar: Grammar,
        formula: isla.Formula,
        validator: Callable[[isla.DerivationTree], bool],
        timeout: int,
        cpu_count: int = -1,
        k=3) -> List[PerformanceEvaluationResult]:
    if cpu_count < 0:
        cpu_count = mp.cpu_count()

    if cpu_count < 2:
        return [
            evaluate_isla_generator(grammar, formula, vector, validator, timeout, None, k)
            for vector in population]

    with mp.Pool(processes=cpu_count) as pool:
        start_time = datetime.datetime.now()
        result = pool.starmap(evaluate_isla_generator, [
            (grammar, formula, vector, validator, timeout, None, k)
            for vector in population])
        logger.debug(
            "Time taken for evaluating population w/ parallel processing: %s",
            (datetime.datetime.now() - start_time))
        return result


def auto_tune_weight_vector(
        grammar: Grammar,
        formula: isla.Formula,
        validator: Callable[[isla.DerivationTree], bool],
        timeout: int = 60,
        population_size: int = 10,
        generations: int = 10,
        k: int = 3,
        seed_population: List[CostWeightVector] = None,
        cpu_count: int = -1) -> Tuple[PerformanceEvaluationResult, CostWeightVector]:
    assert population_size >= 4
    assert population_size % 2 == 0
    assert seed_population is None or len(seed_population) == population_size

    time_estimate = 2.5 * (
            timeout * population_size / mp.cpu_count() +
            (generations - 1) * (population_size // 2) * timeout / mp.cpu_count())
    logger.info(
        "Autotuning, estimated time > %ds, end: %s",
        time_estimate,
        (datetime.datetime.now() + datetime.timedelta(seconds=time_estimate)).strftime("%d/%m/%Y %H:%M:%S")
    )

    # Create initial population
    if not seed_population:
        seed_population = [
            CostWeightVector(
                tree_closing_cost=randno(),
                vacuous_penalty=randno(),
                constraint_cost=randno(),
                derivation_depth_penalty=randno(),
                low_k_coverage_penalty=randno(),
                low_global_k_path_coverage_penalty=randno()
            )
            for _ in range(population_size)]

    current_population = sorted(zip(
        evaluate_cost_vectors_isla(
            seed_population,
            grammar,
            formula,
            validator,
            timeout,
            k=k,
            cpu_count=cpu_count
        ),
        seed_population),
        key=lambda t: t[0].final_product_value)

    logger.info(
        "Initial population:\n%s\n",
        "\n".join([f'{str(v)}, {str(r)}' for r, v in current_population]))

    for generation in range(generations - 1):
        # Remove the five least fittest elements
        current_population = current_population[population_size // 2:]

        # Crossover
        offspring: List[CostWeightVector] = []
        idx = 0
        while len(offspring) < population_size // 2:
            first_parent = current_population[idx % len(current_population)]
            second_parent = current_population[(idx + 1) % len(current_population)]

            # We take two features from the first, and three from the second parent
            all_features = list(first_parent[1].__dict__.keys())
            first_parent_features = random.sample(all_features, 2)
            child = CostWeightVector(**{
                feature:
                    first_parent[1].__dict__[feature]
                    if feature in first_parent_features
                    else second_parent[1].__dict__[feature]
                for feature in all_features
            })

            logger.debug("Crossover of\n%s\nand\n%s:\n%s", first_parent[1], second_parent[1], child)

            # Mutate one child feature
            mutated_feature = random.choice(all_features)
            current_feature_value: int = getattr(child, mutated_feature)
            setattr(child, mutated_feature, mutate_cost_weight(current_feature_value, max_add=10, max_factor=5))

            logger.debug("After Mutation: %s", child)

            offspring.append(child)

        eval_results = evaluate_cost_vectors_isla(
            offspring, grammar, formula, validator, timeout, k=k, cpu_count=cpu_count)
        current_population.extend(list(zip(eval_results, seed_population)))
        current_population = sorted(current_population, key=lambda t: t[0].final_product_value)

        logger.info(
            "Generation %d:\n%s\n",
            generation + 1,
            "\n".join([f'{str(v)}, {str(r)}' for r, v in current_population]))

        idx += 1

    result = current_population[-1]
    logger.info("Auto-tuning finished. Result: %s, %s", result[1], result[0])
    return result
