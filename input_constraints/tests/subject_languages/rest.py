import string

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
    "<section-title>": ["<nobr-string>\n<underline>"],
    "<nobr-string>": ["<nobr-char>", "<nobr-char><nobr-string>"],
    "<nobr-char>": list(set(srange(string.printable)) - {"\n", "\r"}),
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
  titletxt: <nobr-string>;
  underline: <underline>;
}

constraint {
  forall title="{titletxt}\n{underline}" in start:
    num title_length:
      num underline_length:
        ((> (str.to_int title_length) 1) and
        ((<= (str.to_int title_length) (str.to_int underline_length)) and
        (ljust_crop(titletxt, title_length, " ") and
         extend_crop(underline, underline_length))))
}
""", semantic_predicates={
    "ljust_crop": LJUST_CROP_PREDICATE(REST_GRAMMAR),
    "extend_crop": EXTEND_CROP_PREDICATE(REST_GRAMMAR)})

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
