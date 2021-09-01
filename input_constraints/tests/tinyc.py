import string
from typing import cast

import z3
from fuzzingbook.Grammars import srange
from input_constraints import isla
from input_constraints import isla_shortcuts as sc

# TODO: Switch to full grammar again

TINYC_GRAMMAR = {
    "<start>": ["<mwss><statements><mwss>"],
    "<statements>": [
        "<statement><statement>",
        "<statement><wss><statements>"
    ],
    "<statement>": [
        # "if<wss><paren_expr><wss><statement>",
        # "if<wss><paren_expr><wss><statement><wss>else<wss><statement>",
        # "while<wss><paren_expr><wss><statement>",
        # "do<wss><statement>while<wss><paren_expr>",
        # "{<mwss>}",
        # "{<statement>}",
        "<mwss><expr><mwss>;",
        # ";"
    ],
    # "<paren_expr>": ["(<mwss><expr><mwss>)"],
    "<expr>": ["<test>", "<id><mwss>=<mwss><expr>"],
    "<test>": [
        "<sum>",
        # "<sum><mwss><<mwss><sum>"
    ],
    "<sum>": [
        "<term>",
        # "<sum><mwss>+<mwss><term>",
        # "<sum><mwss>-<mwss><term>"
    ],
    "<term>": [
        "<id>",
        "<int>",
        # "<paren_expr>"
    ],
    "<id>": srange(string.ascii_lowercase),
    "<int>": [
        "<digit>",
        # "<digit><int>"
    ],
    "<digit>": srange(string.digits),
    "<mwss>": ["", "<wss>"],
    "<wss>": ["<ws>", "<ws><wss>"],
    "<ws>": srange(" \n\t"),
}

mgr = isla.VariableManager()
TINYC_DEF_BEFORE_USE_CONSTRAINT = mgr.create(sc.forall(
    mgr.bv("$test", "<test>"),
    mgr.const("$start", "<start>"),
    sc.forall(
        mgr.bv("$id_1", "<id>"),
        mgr.bv("$test"),
        sc.exists_bind(
            mgr.bv("$id_2", "<id>") + "<mwss>=<mwss><expr>",
            mgr.bv("$expr", "<expr>"),
            mgr.const("$start"),
            sc.before(mgr.bv("$expr"), mgr.bv("$test")) &
            mgr.smt(cast(z3.BoolRef, mgr.bv("$id_1").to_smt() == mgr.bv("$id_2").to_smt()))
        )
    )
))
