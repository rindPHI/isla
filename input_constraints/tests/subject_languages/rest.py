import os
import string
import subprocess
import tempfile
from typing import Union

from fuzzingbook.Grammars import srange

from input_constraints import isla
from input_constraints.isla import parse_isla
from input_constraints.isla_predicates import LJUST_CROP_PREDICATE, EXTEND_CROP_PREDICATE

REST_GRAMMAR = {
    "<start>": ["<body-elements>"],
    "<body-elements>": ["", "<body-element>\n<body-elements>"],
    "<body-element>": [
        "<section-title>\n",
    ],
    "<section-title>": ["<title-text>\n<underline>"],
    "<title-text>": ["<title-first-char>", "<title-first-char><nobr-string>"],
    "<nobr-string>": ["<nobr-char>", "<nobr-char><nobr-string>"],
    # Exclude tab in <nobr-char> since otherwise, title can get too long (counts more than one character)
    # Remove _, { to exclude back references and inline substitutions
    # Remove ` to exclude inline interpreted text
    "<nobr-char>": list(set(srange(string.printable)) - set(srange("\n\r\t_{}`"))),
    "<title-first-char>": list(set(srange(string.printable)) - set(srange(string.whitespace + "\b\f\v-*+_{}`|=-"))),
    "<underline>": ["<eqs>", "<dashes>"],
    "<eqs>": ["=", "=<eqs>"],
    "<dashes>": ["-", "-<dashes>"],
}

start = isla.Constant("$start", "<start>")

# The below encoding is the most efficient one, but heavily uses semantic predicates
LENGTH_UNDERLINE = parse_isla("""
const start: <start>;

vars {
  title_length: NUM;
  underline_length: NUM;
  title: <section-title>;
  titletxt: <title-text>;
  underline: <underline>;
}

constraint {
  forall title="{titletxt}\n{underline}" in start:
    num title_length:
      num underline_length:
        ((> (str.to_int title_length) 0) and
        ((<= (str.to_int title_length) (str.to_int underline_length)) and
        (ljust_crop(titletxt, title_length, " ") and
         extend_crop(underline, underline_length))))
}
""", semantic_predicates={LJUST_CROP_PREDICATE, EXTEND_CROP_PREDICATE})


# TODO: Further rst properties:
#   - Bullet lists: Continuing text must be aligned after the bullet and whitespace
#   - Footnotes: For auto-numbered footnote references without autonumber labels ("[#]_"), the references and footnotes
#                must be in the same relative order. Similarly for auto-symbol footnotes ("[*]_").

def render_rst(tree: isla.DerivationTree) -> Union[bool, str]:
    with tempfile.NamedTemporaryFile(suffix=".rst") as tmp:
        tmp.write(str(tree).encode())
        tmp.flush()
        cmd = ["rst2html.py", tmp.name]
        process = subprocess.Popen(cmd, stderr=subprocess.PIPE, stdout=open(os.devnull, "w"))
        (stdout, stderr) = process.communicate()
        exit_code = process.wait()

        return True if exit_code == 0 and not stderr else stderr.decode("utf-8")

# Below encoding results in timeouts for more complex input scaffolds, uses only SMT formulas,
# but depends on an auxiliary numeric constant for better efficiency & more diversity.
#
# LENGTH_UNDERLINE = parse_isla("""
# const start: <start>;
#
# vars {
#   length: NUM;
#   title: <section-title>;
#   titletxt: <nobr-string>;
#   underline: <underline>;
# }
#
# constraint {
#   forall title="{titletxt}\n{underline}" in start:
#     num length:
#       ((> (str.to_int length) 1) and
#       ((< (str.to_int length) 5) and
#       ((= (str.len titletxt) (str.to_int length)) and
#        (>= (str.len underline) (str.to_int length)))))
# }
# """)

# Below encoding, which is the conceptually cleanest one, sometimes results in timeouts
# and produces same lengths per input... The latter seems to be the SMT solver's fault,
# the processing in the solver seems correct.
#
# LENGTH_UNDERLINE = parse_isla("""
# const start: <start>;
#
# vars {
#   title: <section-title>;
#   titletxt: <nobr-string>;
#   underline: <underline>;
# }
#
# constraint {
#   forall title="{titletxt}\n{underline}" in start:
#     (>= (str.len underline) (str.len titletxt))
# }
# """)
