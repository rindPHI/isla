import copy
import datetime
import multiprocessing as mp
import random
import subprocess
import sys
from textwrap import wrap
from typing import Callable, List, Tuple, Optional

from grammar_graph import gg
from pathos import multiprocessing as pmp

from isla import isla
from isla.evaluator import PerformanceEvaluationResult, logger, evaluate_producer
from isla.solver import CostWeightVector, ISLaSolver, CostSettings
from isla.type_defs import Grammar


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

    if cpu_count < 1:
        cpu_count = mp.cpu_count()

    time_estimate = 2.5 * (
            timeout * population_size / cpu_count +
            (generations - 1) * (population_size // 2) * timeout / cpu_count)
    endtime = (datetime.datetime.now() + datetime.timedelta(seconds=time_estimate)).strftime("%d/%m/%Y %H:%M:%S")
    print(f"Autotuning, estimated time > {time_estimate}s, end: {endtime}", )

    # Create initial population
    if not seed_population:
        seed_population = [
            CostWeightVector(
                tree_closing_cost=randno(),
                vacuous_penalty=0,
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

    print(
        "Initial population:\n" +
        "\n".join([f'{str(v)}, {str(r)}' for r, v in current_population]) + "\n")

    for generation in range(generations - 1):
        # Remove the five least fittest elements
        current_population = current_population[population_size // 2:]

        # Crossover
        offspring: List[CostWeightVector] = []
        idx = 0
        while len(offspring) < population_size // 2:
            # first_parent, second_parent = random.sample(current_population, k=2)

            first_parent = current_population[idx % len(current_population)]
            second_parent = current_population[(idx + 1) % len(current_population)]

            # We take two features from the first, and three from the second parent
            all_features = list(set(first_parent[1].__dict__.keys()) - {"vacuous_penalty"})
            first_parent_features = random.sample(all_features, 2)
            child = CostWeightVector(**{
                feature:
                    first_parent[1].__dict__[feature]
                    if feature in first_parent_features
                    else second_parent[1].__dict__[feature]
                for feature in all_features
            })

            logger.debug(f"Crossover of\n{first_parent[1]}\nand\n{second_parent[1]}:\n{child}")

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

        print(
            f"Generation {generation + 1}:\n" +
            "\n".join([f'{str(v)}, {str(r)}' for r, v in current_population]) + "\n")

        idx += 1

    result = current_population[-1]
    print(f"Auto-tuning finished. Result: {result[1]}, {result[0]}")
    return result


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

    with pmp.Pool(processes=cpu_count) as pool:
        start_time = datetime.datetime.now()
        result = pool.starmap(evaluate_isla_generator, [
            (grammar, formula, vector, validator, timeout, None, k)
            for vector in population])
        logger.debug(
            "Time taken for evaluating population w/ parallel processing: %s",
            (datetime.datetime.now() - start_time))
        return result


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

        print(f"Round {i + 1}, cost vector {v}")
        outfile_name = f"/tmp/xml_perf_eval_{str((i + 1)).rjust(len(str(rounds)), '0')}.pdf"

        evaluate_isla_generator(grammar, formula, v, validator, timeout, outfile_name, k)

    process = subprocess.run(
        ["pdfjam"] +
        [f"/tmp/xml_perf_eval_{str((i + 1)).rjust(len(str(rounds)), '0')}.pdf" for i in range(rounds)] +
        ["--nup", "4x3", "--landscape", "--outfile", final_out_file_name],
        stderr=subprocess.PIPE)

    if process.returncode != 0:
        print(f"Combining output PDFs did not work, error message: {process.stderr}", file=sys.stderr)
    else:
        print("Saved combined output file at " + final_out_file_name)


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
        print(f"Round {i + i}, cost vector {v}")
        outfile_name = f"/tmp/xml_perf_eval_{str((i + 1)).rjust(len(str(rounds)), '0')}.pdf"

        evaluate_isla_generator(grammar, formula, v, validator, timeout, outfile_name, k)

    process = subprocess.run(
        ["pdfjam"] +
        [f"/tmp/xml_perf_eval_{str((i + 1)).rjust(len(str(rounds)), '0')}.pdf" for i in range(rounds)] +
        ["--nup", "4x3", "--landscape", "--outfile", final_out_file_name],
        stderr=subprocess.PIPE)

    if process.returncode != 0:
        print(f"Combining output PDFs did not work, error message: {process.stderr}", file=sys.stderr)
    else:
        print("Saved combined output file at " + final_out_file_name)


def randno(maxno: int = 40) -> int:
    return random.choices(range(maxno + 1), weights=list(reversed([n // 10 + 1 for n in range(maxno + 1)])))[0]


def evaluate_isla_generator(
        grammar: Grammar,
        formula: isla.Formula,
        v: CostWeightVector,
        validator: Callable[[isla.DerivationTree], bool],
        timeout: int,
        outfile_name: Optional[str] = None,
        k=3) -> PerformanceEvaluationResult:
    print(f"Evaluating weight vector {v}")
    isla_producer = ISLaSolver(
        grammar,
        formula,
        max_number_free_instantiations=1,
        max_number_smt_instantiations=1,
        timeout_seconds=timeout,
        cost_settings=CostSettings((v,), (200,))
    ).solve()

    return evaluate_producer(
        outfile_pdf=outfile_name,
        diagram_title="\n".join(wrap(str(v), 60)),
        producer=isla_producer,
        formula=formula,
        graph=gg.GrammarGraph.from_grammar(grammar),
        validator=validator,
        timeout_seconds=timeout,
        k=k)