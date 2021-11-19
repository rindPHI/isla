import os
import string
import subprocess
import tempfile
from typing import Union
import xml.etree.ElementTree as ET

from fuzzingbook.Grammars import srange

from input_constraints import isla
from input_constraints.isla import parse_isla
from input_constraints.isla_predicates import LJUST_CROP_PREDICATE, EXTEND_CROP_PREDICATE, SAME_POSITION_PREDICATE, \
    CONSECUTIVE_PREDICATE

# NOTE: The following special characters are removed from general text.
# Remove _, {, | to exclude back references and inline substitutions
# Remove ` to exclude inline interpreted text
# * is inline emphasis and needs to be closed: Remove from standard text
REST_GRAMMAR = {
    "<start>": ["<body-elements>"],
    "<body-elements>": ["", "<body-element>\n<body-elements>"],
    "<body-element>": [
        "<section-title>\n",
        "<labeled_paragraph>",
        "<paragraph>",
        "<enumeration>",
    ],

    "<section-title>": ["<title-text>\n<underline>"],
    "<title-text>": ["<title-first-char>", "<title-first-char><nobr-string>"],

    "<paragraph>": ["<first_paragraph_element><paragraph_elements>\n"],
    "<labeled_paragraph>": ["<label>\n\n<paragraph>"],
    "<label>": [".. _<id>:"],

    "<paragraph_elements>": ["<paragraph_element><paragraph_elements>", "<paragraph_element>"],
    "<first_paragraph_element>": ["<paragraph_chars_nospace>", "<internal_reference_nospace>"],
    "<paragraph_element>": ["<paragraph_chars>", "<internal_reference>"],
    "<internal_reference>": ["<presep><id>_<postsep>"],
    "<internal_reference_nospace>": ["<id>_<postsep>"],

    "<enumeration>": ["<enumeration_items>\n"],
    "<enumeration_items>": ["<enumeration_item>\n<enumeration_items>", "<enumeration_item>"],
    "<enumeration_item>": ["<number>. <nobr-string>"],

    "<paragraph_chars>": ["<paragraph_char><paragraph_chars>", "<paragraph_char>"],
    "<paragraph_chars_nospace>": ["<paragraph_char_nospace><paragraph_chars_nospace>", "<paragraph_char_nospace>"],
    "<paragraph_char>": list(set(srange(string.printable)) - set(srange("_{}`|*"))),
    "<paragraph_char_nospace>": list(set(srange(string.printable)) - set(srange("_{}`|*" + string.whitespace))),

    "<presep>": srange(" \t,;()"),
    "<postsep>": srange(" \t,.;()"),
    "<id>": srange(string.ascii_lowercase),
    "<number>": ["<digit_nonzero><digits>", "<digit>"],
    "<digit_nonzero>": srange("123456789"),
    "<digits>": ["<digit><digits>", "<digit>"],
    "<digit>": srange(string.digits),
    "<nobr-string>": ["<nobr-char>", "<nobr-char><nobr-string>"],
    # Exclude tab in <nobr-char> since otherwise, title can get too long (counts more than one character)
    "<nobr-char>": list(set(srange(string.printable)) - set(srange("\n\r\t_{}`|"))),
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

DEF_LINK_TARGETS = parse_isla("""
const start: <start>;

vars {
  ref: <internal_reference>;
  fref: <internal_reference_nospace>;
  use_id, def_id: <id>;
  labeled_par: <labeled_paragraph>;
}

constraint {
  (forall ref="<presep>{use_id}_<postsep>" in start:
     exists labeled_par=".. _{def_id}:\n\n<paragraph>" in start:
       (= use_id def_id) and
   forall fref="{use_id}_<postsep>" in start:
     exists labeled_par=".. _{def_id}:\n\n<paragraph>" in start:
       (= use_id def_id))
}
""")

NO_LINK_TARGET_REDEF = parse_isla("""
const start: <start>;

vars {
  label_1, label_2: <label>;
  id_1, id_2: <id>;
}

constraint {
  forall label_1=".. _{id_1}:" in start:
    forall label_2=".. _{id_2}:" in start:
      (same_position(label_1, label_2) or
       not (= id_1 id_2))
}
""", structural_predicates={SAME_POSITION_PREDICATE})

LIST_NUMBERING_CONSECUTIVE = parse_isla("""
const start: <start>;

vars {
  enumeration: <enumeration>;
  item_1, item_2: <enumeration_item>;
  number_1, number_2: <number>;
}

constraint {
  forall enumeration in start:
    forall item_1="{number_1}. <paragraph_chars>" in enumeration:
      forall item_2="{number_2}. <paragraph_chars>" in enumeration:
        (not consecutive(item_1, item_2) or
          (consecutive(item_1, item_2) and 
          ((= (str.to_int number_2) (+ (str.to_int number_1) 1)) and
           (> (str.to_int number_1) 0))))
}
""", structural_predicates={CONSECUTIVE_PREDICATE})


# TODO: Further rst properties:
#   - Bullet lists: Continuing text must be aligned after the bullet and whitespace
#   - Footnotes: For auto-numbered footnote references without autonumber labels ("[#]_"), the references and footnotes
#                must be in the same relative order. Similarly for auto-symbol footnotes ("[*]_").
#   - Itemized lists: List items should be sequentially numbered, but need not start at 1

def render_rst(tree: isla.DerivationTree) -> Union[bool, str]:
    with tempfile.NamedTemporaryFile(suffix=".rst") as tmp:
        tmp.write(str(tree).encode())
        tmp.flush()
        cmd = ["rst2html.py", tmp.name]
        process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        (stdout, stderr) = process.communicate()
        exit_code = process.wait()

        output = stdout.decode("utf-8")
        err_msg = stderr.decode("utf-8")

        if not err_msg:
            # Compare headings count
            assert output

            section_titles_in_tree = tree.filter(lambda n: n.value == "<section-title>")

            doc = ET.fromstring(output)
            headings_in_output = doc.findall(".//{*}h1") + doc.findall(".//{*}h2")

            if len(section_titles_in_tree) != len(headings_in_output):
                err_msg = f"Incorrect heading underlines: {len(section_titles_in_tree)} titles " \
                          f"were rendered to {len(headings_in_output)} HTML headings."
            else:
                enumerations_in_tree = tree.filter(lambda n: n.value == "<enumeration>")
                enumerations_in_output = doc.findall(".//{*}ol")

                if len(enumerations_in_tree) != len(enumerations_in_output):
                    err_msg = f"Incorrect enumeration numbering: {len(enumerations_in_tree)} enumerations " \
                              f"were rendered to {len(enumerations_in_output)} HTML ordered lists."

        has_error = exit_code != 0 or err_msg

        # if has_error:
        #     with tempfile.NamedTemporaryFile(suffix=".rst", delete=False) as perm_tmp:
        #         perm_tmp.write(str(tree).encode())
        #         perm_tmp.flush()
        #         print(f"Written wrong input to file {perm_tmp.name}")

        return True if not has_error else err_msg

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
