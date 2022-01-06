import argparse
import itertools
import json
import logging
import multiprocessing as mp
import multiprocessing.pool
import os
import os.path
import sqlite3
import sys
import time
import traceback
from datetime import datetime
from typing import List, Generator, Dict, Callable, Set, Tuple, Optional, cast

import pathos.multiprocessing as pmp
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from grammar_graph import gg

from isla import isla
from isla.solver import ISLaSolver
from isla.type_defs import Grammar

logger = logging.getLogger("evaluator")


def std_db_file() -> str:
    return os.path.join(
        *os.path.split(os.path.dirname(os.path.realpath(__file__)))[:-1],
        "isla_evaluation.sqlite")


# Non-Deamon solution from https://stackoverflow.com/questions/6974695/python-process-pool-non-daemonic#answer-53180921
# to enable spawning subprocesses inside spawned subprocesses.
class NoDaemonProcess(multiprocessing.Process):
    @property
    def daemon(self):
        return False

    @daemon.setter
    def daemon(self, value):
        pass


class NoDaemonContext(type(multiprocessing.get_context())):
    Process = NoDaemonProcess


# We sub-class multiprocessing.pool.Pool instead of multiprocessing.Pool
# because the latter is only a wrapper function, not a proper class.
class NestablePool(multiprocessing.pool.Pool):
    def __init__(self, *args, **kwargs):
        kwargs['context'] = NoDaemonContext()
        super(NestablePool, self).__init__(*args, **kwargs)


class Evaluator:
    def __init__(
            self,
            jobname_prefix: str,
            generators: List[Callable[[int], ISLaSolver] | Grammar],
            jobnames: List[str],
            validator: Callable[[isla.DerivationTree], bool],
            graph: gg.GrammarGraph,
            db_file: str = std_db_file(),
            default_timeout: int = 60 * 60,
            default_sessions: int = 1):
        self.validator = validator
        self.graph = graph

        args, print_help = self.parse_command_line(
            jobname_prefix, db_file, jobnames, default_sessions, default_timeout)

        if args.listjobs:
            print(f"Available jobs for {jobname_prefix}: " + ", ".join(jobnames))
            exit(0)

        self.db_file: str = args.db

        chosen_jobs = [name.strip() for name in args.jobs.split(",")]
        if any(job not in jobnames for job in chosen_jobs):
            print("ERROR: Unknown job specified.", file=sys.stderr)
            print_help()
            exit(1)

        if not chosen_jobs:
            print("ERROR: You have to choose at least one job.", file=sys.stderr)
            print_help()
            exit(1)

        try:
            self.timeout: int = int(args.timeout)
        except ValueError:
            print("ERROR: timeout value must be an integer.", file=sys.stderr)
            print_help()
            exit(1)

        self.jobs_and_generators = {
            f"{jobname_prefix} {job}":
                generator if isinstance(generator, dict) else generator(self.timeout)
            for job, generator in
            zip(jobnames, generators) if job in chosen_jobs
        }

        try:
            self.num_sessions: int = int(args.numsessions)
        except ValueError:
            print("ERROR: numsessions value must be an integer.", file=sys.stderr)
            print_help()
            exit(1)

        self.do_clean: bool = args.clean
        self.do_analyze: bool = args.analyze
        self.do_generate: bool = args.generate
        self.do_evaluate_validity: bool = args.validity
        self.do_compute_kpaths: bool = args.kpaths
        self.dry_run: bool = args.dryrun

        max_ids = {jobname: (get_max_sid(jobname, self.db_file) or 0) for jobname in self.jobs_and_generators}
        session_out_of_bounds = [
            jobname for jobname in self.jobs_and_generators
            if (max_ids[jobname] < self.num_sessions
                and not self.do_generate
                and not (self.do_clean and
                         not (self.do_generate or self.do_evaluate_validity or self.do_compute_kpaths)))
        ]

        if session_out_of_bounds:
            print(f"ERROR: Too large numsessions value (for job(s) {', '.join(session_out_of_bounds)}).",
                  file=sys.stderr)
            print_help()
            exit(1)

        try:
            self.kvalues: List[int] = [int(val.strip()) for val in cast(str, args.kvalues).split(",")]
        except ValueError:
            print("ERROR: kvalues must be a comma-separated list of integers.", file=sys.stderr)
            print_help()
            exit(1)

        if not (self.do_clean or self.do_analyze or self.do_generate
                or self.do_evaluate_validity or self.do_compute_kpaths):
            print("ERROR: You have to set at least one of -c, -a, -g, -v, or -p.", file=sys.stderr)
            print_help()
            exit(1)

    def parse_command_line(
            self,
            jobname_prefix: str,
            db_file: str,
            jobnames: List[str],
            default_sessions: int, default_timeout: int
    ) -> Tuple[argparse.Namespace, Callable[[], None]]:
        parser = argparse.ArgumentParser(
            description=f"Evaluating the ISLa producer with case study {jobname_prefix}.",
            formatter_class=argparse.ArgumentDefaultsHelpFormatter)
        parser.add_argument("--db", default=db_file, help="Path to the sqlite database file.")
        parser.add_argument(
            "-n", "--numsessions", default=default_sessions,
            help="The number of sessions to generate or analyze.")

        parser.add_argument(
            "-l", "--listjobs", action="store_true", default=False,
            help="Shows all jobs for this evaluator.")
        parser.add_argument(
            "-g", "--generate", action="store_true", default=False,
            help="Generate inputs with a timeout of [timeout] seconds, [numsessions] times.")
        parser.add_argument(
            "-v", "--validity", action="store_true", default=False,
            help="Compute validity of the inputs of the previous [numsessions] sessions.")
        parser.add_argument(
            "-p", "--kpaths", action="store_true", default=False,
            help="Compute k-paths for the inputs of the previous [numsessions] sessions.")
        parser.add_argument(
            "-a", "--analyze", action="store_true", default=False,
            help="Analyze the accumulated results of the previous [numsessions] sessions.")

        g = parser.add_mutually_exclusive_group()
        g.add_argument(
            "-c", "--clean", action="store_true", default=False,
            help="Removes all data related to the given job(s) from the database. WARNING: This cannot be undone!")
        g.add_argument(
            "-d", "--dryrun", action="store_true", default=False,
            help="Does not write results to database when *generating* (-g). Does not affect -v and -p.")

        parser.add_argument(
            "-j", "--jobs", default=", ".join(jobnames),
            help="Comma-separated list of jobs to run / evaluate.")
        parser.add_argument(
            "-t", "--timeout", default=default_timeout,
            help="The timeout for test input generation. Useful with the '-g' option.")
        parser.add_argument(
            "-k", "--kvalues", default="3,4",
            help="Comma-separated list of the values 'k' for which to compute k-path coverage. "
                 "Useful with the '-p' option.")
        args = parser.parse_args()

        return args, lambda: parser.print_help(file=sys.stderr)

    def run(self):
        if self.do_clean:
            truncate_db_tables(list(self.jobs_and_generators.keys()), self.db_file)

        if self.do_generate:
            self.generate()

        if self.do_evaluate_validity:
            self.evaluate_validity()

        if self.do_compute_kpaths:
            self.compute_kpaths()

        if self.do_analyze:
            self.analyze()

    def generate(self) -> None:
        for _ in range(self.num_sessions):
            # We do not run the actual test data generation in parallel (at least not if only one job
            # is specified) to not negatively affect the performance. Thus, one session at a time.
            if len(self.jobs_and_generators) == 1:
                for jobname, generator in self.jobs_and_generators.items():
                    inputs = generate_inputs(generator, self.timeout, jobname)
                    if not self.dry_run:
                        store_inputs(jobname, self.timeout, inputs, self.db_file)
                continue

            with pmp.Pool(processes=pmp.cpu_count()) as pool:
                pool.starmap(
                    lambda jobname, generator:
                    generate_inputs(generator, self.timeout, jobname) if self.dry_run
                    else store_inputs(
                        jobname, self.timeout, generate_inputs(generator, self.timeout, jobname), self.db_file),
                    list(self.jobs_and_generators.items()))

    def evaluate_validity(self) -> None:
        args: List[Tuple[List[str], List[Callable[[isla.DerivationTree], bool]], List[str], List[int]]] = [
            (
                [jobname],
                [self.validator],
                [self.db_file],
                [i for i in range((get_max_sid(jobname, self.db_file) or 0) - self.num_sessions + 1,
                                  (get_max_sid(jobname, self.db_file) or 0) + 1)])
            for jobname in self.jobs_and_generators
        ]

        args: List[Tuple[str, Callable[[isla.DerivationTree], bool], str, int]] = [
            rt for t in args for rt in tuple(itertools.product(*t))]

        with NestablePool(processes=pmp.cpu_count()) as pool:
            pool.starmap(evaluate_validity, args)

    def compute_kpaths(self) -> None:
        args: List[Tuple[List[str], List[gg.GrammarGraph], List[int], List[str], List[int]]] = [
            (
                [jobname],
                [self.graph],
                [k],
                [self.db_file],
                [i for i in range((get_max_sid(jobname, self.db_file) or 0) - self.num_sessions + 1,
                                  (get_max_sid(jobname, self.db_file) or 0) + 1)])
            for jobname in self.jobs_and_generators
            for k in self.kvalues
        ]

        args: List[Tuple[str, gg.GrammarGraph, int, str, int]] = [
            rt for t in args for rt in tuple(itertools.product(*t))]

        with NestablePool(processes=pmp.cpu_count()) as pool:
            pool.starmap(evaluate_kpaths, args)

    def analyze(self):
        con = sqlite3.connect(self.db_file)
        cur = con.cursor()

        efficiency: Dict[str, float] = {}
        precision: Dict[str, float] = {}
        diversity: Dict[str, float] = {}

        for job in self.jobs_and_generators:
            maxsid = get_max_sid(job, self.db_file)
            assert maxsid > 0 and maxsid >= self.num_sessions

            # Analyze efficiency: Inputs / s
            cur.execute(
                "SELECT COUNT(*) FROM inputs WHERE testId = ? AND sid >= ? AND sid <= ?",
                (job, maxsid - self.num_sessions + 1, maxsid))
            total_inputs: int = cur.fetchone()[0]
            cur.execute(
                "SELECT SUM(seconds) FROM session_lengths WHERE testId = ? AND sid >= ? AND sid <= ?",
                (job, maxsid - self.num_sessions + 1, maxsid))
            time: int = cur.fetchone()[0]
            efficiency[job] = total_inputs / time

            # Analyze precision: Fraction of valid inputs
            cur.execute(
                "SELECT COUNT(*) FROM inputs NATURAL JOIN valid WHERE testId = ? AND sid >= ? AND sid <= ?",
                (job, maxsid - self.num_sessions + 1, maxsid))
            valid_inputs: int = cur.fetchone()[0]
            precision[job] = valid_inputs / total_inputs

            # Analyze diversity: Fraction of covered k-paths
            total_num_kpaths = {k: len(self.graph.k_paths(k)) for k in self.kvalues}
            diversity_by_sid: Dict[int, float] = {}
            for sid in range(maxsid - self.num_sessions + 1, maxsid + 1):
                diversity_by_k: Dict[int, float] = {}
                for k in self.kvalues:
                    cur.execute(
                        "SELECT paths FROM inputs NATURAL JOIN kpaths WHERE testId = ? AND sid = ? AND k = ?",
                        (job, sid, k))
                    path_hashes: Set[int] = set([])
                    for row in cur:
                        path_hashes.update({int(path_hash) for path_hash in json.loads(row[0])})

                    diversity_by_k[k] = len(path_hashes) / total_num_kpaths[k]
                    assert len(path_hashes) < total_num_kpaths[k]

                diversity_by_sid[sid] = sum(diversity_by_k.values()) / len(diversity_by_k)

            diversity[job] = sum(diversity_by_sid.values()) / len(diversity_by_sid)

        con.close()

        def perc(inp: float) -> str:
            return frac(inp * 100) + " %"

        def frac(inp: float) -> str:
            return "{:8.2f}".format(inp)

        col_1_len = max([len(job) for job in self.jobs_and_generators])
        row_1 = f"| {'Job'.ljust(col_1_len)} | Efficiency | Precision  | Diversity  |"
        sepline = f"+-{'-'.ljust(col_1_len, '-')}-+------------+------------+------------+"

        print(sepline)
        print(row_1)
        print(sepline)

        for job in self.jobs_and_generators:
            print(f"| {job.ljust(col_1_len)} |   {frac(efficiency[job])} | "
                  f"{perc(precision[job])} | {perc(diversity[job])} |")

        print(sepline)


def strtime() -> str:
    return datetime.now().strftime("%H:%M:%S")


def generate_inputs(
        generator: Generator[isla.DerivationTree, None, None] | ISLaSolver | Grammar,
        timeout_seconds: int = 60,
        jobname: Optional[str] = None) -> Dict[float, isla.DerivationTree]:
    start_time = time.time()
    result: Dict[float, isla.DerivationTree] = {}
    jobname = "" if not jobname else f" ({jobname})"
    print(f"[{strtime()}] Collecting data for {timeout_seconds} seconds{jobname}")

    if isinstance(generator, ISLaSolver):
        generator = generator.solve()
    elif isinstance(generator, dict):
        grammar = generator

        def gen():
            fuzzer = GrammarCoverageFuzzer(grammar)
            while True:
                yield isla.DerivationTree.from_parse_tree(
                    fuzzer.expand_tree(("<start>", None)))

        generator = gen()

    while int(time.time()) - int(start_time) <= timeout_seconds:
        try:
            inp = next(generator)
        except StopIteration:
            break
        except Exception as exp:
            print(f"{type(exp).__name__} occurred while executing solver; I'll stop here:\n" + str(exp), file=sys.stderr)
            print(traceback.format_exc())
            return result

        logger.debug("Input: %s", str(inp))
        curr_relative_time = time.time() - start_time
        assert curr_relative_time not in result
        result[curr_relative_time] = inp

    print(f"[{strtime()}] Collected {len(result)} inputs in {timeout_seconds} seconds{jobname}")
    return result


def create_db_tables(db_file: str = std_db_file()) -> None:
    inputs_table_sql = \
        """CREATE TABLE IF NOT EXISTS inputs (
    inpId INTEGER PRIMARY KEY ASC, 
    testId TEXT,
    sid INT,
    reltime REAL,
    inp TEXT
)"""
    valid_inputs_table_sql = "CREATE TABLE IF NOT EXISTS valid(inpId INTEGER PRIMARY KEY ASC)"
    kpaths_table_sql = "CREATE TABLE IF NOT EXISTS kpaths(inpId INT, k INT, paths TEXT, UNIQUE(inpId, k))"
    session_length_sql = "CREATE TABLE IF NOT EXISTS session_lengths(testId TEXT, sid INT, seconds INT)"

    tables = {
        "inputs": inputs_table_sql,
        "valid": valid_inputs_table_sql,
        "kpaths": kpaths_table_sql,
        "session_lengths": session_length_sql
    }

    con = sqlite3.connect(db_file)

    for tbl_name, cmd in tables.items():
        with con:
            con.execute(cmd)

        # Check integrity of table definitions (if could fail if tables already existed)
    for tbl_name, cmd in tables.items():
        with con:
            for row in con.execute("SELECT sql FROM sqlite_master WHERE name = ?", (tbl_name,)):
                cmd = cmd.replace(" IF NOT EXISTS", "")
                sql: str = row[0]
                assert sql == cmd, f"Table SQL\n---\n{sql}\n---\n" \
                                   f"does not equal required definition\n---\n{cmd}\n---"

    con.close()


def truncate_db_tables(jobs: List[str], db_file: str = std_db_file()) -> None:
    create_db_tables(db_file)
    con = sqlite3.connect(db_file)

    for job in jobs:
        with con:
            for row in con.execute("SELECT inpId FROM inputs WHERE testId = ?", (job,)):
                con.execute("DELETE FROM valid WHERE inpId = ?", (row[0],))
                con.execute("DELETE FROM kpaths WHERE inpId = ?", (row[0],))

            con.execute("DELETE FROM inputs WHERE testId = ?", (job,))

    con.close()


def get_max_sid(test_id: str, db_file: str = std_db_file()) -> Optional[int]:
    create_db_tables(db_file)
    con = sqlite3.connect(db_file)

    with con:
        sid = None
        for row in con.execute("SELECT MAX(sid) FROM inputs WHERE testId = ?", (test_id,)):
            if row[0]:
                sid = row[0]
            break

    con.close()
    return sid


def get_session_length(test_id: str, sid: int, db_file: str = std_db_file()) -> int:
    create_db_tables(db_file)
    con = sqlite3.connect(db_file)
    result = None

    with con:
        result = None
        for row in con.execute("SELECT seconds FROM session_lengths WHERE testId = ? AND sid = ?", (test_id, sid)):
            result = row[0]
            break

    assert result is not None
    con.close()
    return result


def store_inputs(
        test_id: str,
        timeout: int,
        inputs: Dict[float, isla.DerivationTree],
        db_file: str = std_db_file()) -> None:
    sid = (get_max_sid(test_id, db_file) or 0) + 1

    create_db_tables(db_file)
    con = sqlite3.connect(db_file)

    reltime: float
    inp: isla.DerivationTree
    for reltime, inp in inputs.items():
        with con:
            con.execute(
                "INSERT INTO inputs(testId, sid, reltime, inp) VALUES (?, ?, ?, ?)",
                (test_id, sid, reltime, json.dumps(inp.to_parse_tree())))

    with con:
        con.execute(
            "INSERT INTO session_lengths(testId, sid, seconds) VALUES (?, ?, ?)",
            (test_id, sid, timeout))

    con.close()


def get_inputs_from_db(
        test_id: str,
        sid: Optional[int] = None,
        db_file: str = std_db_file(),
        only_valid: bool = False
) -> Dict[int, isla.DerivationTree]:
    all_inputs_query = \
        """
        SELECT inpId, inp FROM inputs
        WHERE testId = ? AND sid = ?
        """

    valid_inputs_query = \
        """
        SELECT inpId, inp FROM inputs
        NATURAL JOIN valid
        WHERE testId = ? AND sid = ?
        """

    inputs: Dict[int, isla.DerivationTree] = {}

    # Get newest session ID if not present
    if sid is None:
        sid = get_max_sid(test_id, db_file)
        assert sid

    query = valid_inputs_query if only_valid else all_inputs_query
    con = sqlite3.connect(db_file)
    with con:
        for row in con.execute(query, (test_id, sid)):
            inputs[row[0]] = isla.DerivationTree.from_parse_tree(json.loads(row[1]))
    con.close()

    return inputs


def evaluate_validity(
        test_id: str,
        validator: Callable[[isla.DerivationTree], bool],
        db_file: str = std_db_file(),
        sid: Optional[int] = None) -> None:
    create_db_tables(db_file)

    # Get newest session ID if not present
    if sid is None:
        sid = get_max_sid(test_id, db_file)
        assert sid

    print(f"[{strtime()}] Evaluating validity for session {sid} of {test_id}")

    # Obtain inputs from session
    inputs = get_inputs_from_db(test_id, sid, db_file)

    # Evaluate (in parallel)
    def evaluate(inp_id: int, inp: isla.DerivationTree, queue: mp.Queue):
        try:
            if validator(inp) is True:
                queue.put(inp_id)
        except Exception as err:
            print(f"Exception {err} raise when validating input {inp}, tree: {repr(inp)}")

    manager = mp.Manager()
    queue = manager.Queue()
    with pmp.Pool(processes=pmp.cpu_count()) as pool:
        pool.starmap(evaluate, [(inp_id, inp, queue) for inp_id, inp in inputs.items()])

    # Insert into DB
    con = sqlite3.connect(db_file)
    with con:
        while not queue.empty():
            con.execute("INSERT INTO valid(inpId) VALUES (?)", (queue.get(),))
    con.close()

    print(f"[{strtime()}] DONE Evaluating validity for session {sid} of {test_id}")


def evaluate_kpaths(
        test_id: str,
        graph: gg.GrammarGraph,
        k: int = 3,
        db_file: str = std_db_file(),
        sid: Optional[int] = None) -> None:
    if os.environ.get("PYTHONHASHSEED") is None:
        print("WARNING: Environment variable PYTHONHASHSEED not set, "
              "should be set to 0 for deterministic hashing of k-paths", file=sys.stderr)
    if os.environ.get("PYTHONHASHSEED") is not None and os.environ["PYTHONHASHSEED"] != "0":
        print("WARNING: Environment variable PYTHONHASHSEED not set, "
              "should be set to 0 for deterministic hashing of k-paths", file=sys.stderr)

    create_db_tables(db_file)

    # Get newest session ID if not present
    if sid is None:
        sid = get_max_sid(test_id, db_file)
        assert sid

    print(f"[{strtime()}] Evaluating {k}-paths for session {sid} of {test_id}")

    # Obtain inputs from session
    inputs = get_inputs_from_db(test_id, sid, db_file, only_valid=True)

    # Evaluate (in parallel)
    def compute_k_paths(inp_id: int, inp: isla.DerivationTree, queue: mp.Queue):
        queue.put((inp_id, [hash(path) for path in graph.k_paths_in_tree(inp.to_parse_tree(), k)]))

    manager = mp.Manager()
    queue = manager.Queue()
    with pmp.Pool(processes=pmp.cpu_count()) as pool:
        pool.starmap(compute_k_paths, [(inp_id, inp, queue) for inp_id, inp in inputs.items()])

    # Insert into DB
    con = sqlite3.connect(db_file)
    with con:
        while not queue.empty():
            inp_id, path_hashes = queue.get()
            con.execute("INSERT INTO kpaths(inpId, k, paths) VALUES (?, ?, ?)", (inp_id, k, json.dumps(path_hashes)))
    con.close()

    print(f"[{strtime()}] DONE Evaluating {k}-paths for session {sid} of {test_id}")
