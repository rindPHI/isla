import string
import string
import xml.etree.ElementTree as ET
from html import escape
from typing import Optional, List

from fuzzingbook.Grammars import srange

from input_constraints.isla import parse_isla, DerivationTree

XML_GRAMMAR = {
    "<start>": ["<xml-tree>"],
    "<xml-tree>": [
        "<xml-open-tag><inner-xml-tree><xml-close-tag>",
        "<xml-openclose-tag>",
    ],
    "<inner-xml-tree>": [
        "<text>",
        "<xml-tree>",
        "<inner-xml-tree><inner-xml-tree>"
    ],
    "<xml-open-tag>": ["<<id>>", "<<id> <xml-attribute>>"],
    "<xml-openclose-tag>": ["<<id>/>", "<<id> <xml-attribute>/>"],
    "<xml-close-tag>": ["</<id>>"],
    "<xml-attribute>": ["<id>=\"<text>\"", "<xml-attribute> <xml-attribute>"],

    "<id>": [
        "<id_start_char>",
        "<id_start_char><id_chars>",
        # "<id_with_prefix>"
    ],
    # "<id_with_prefix>": [
    #     "<id_start_char>:<id_chars>",
    #     "<id_start_char><id_chars>:<id_chars>"],
    "<id_start_char>": srange("_" + string.ascii_letters),
    "<id_chars>": ["<id_char>", "<id_char><id_chars>"],
    "<id_char>": ["<id_start_char>"] + srange("-." + string.digits),
    "<text>": ["<text_char><text>", "<text_char>"],
    "<text_char>": [
        escape(c, {'"': "&quot;"})
        for c in srange(string.ascii_letters + string.digits + "\"'. \t/?-,=:+")],
}


def validate_xml(inp: DerivationTree, out: Optional[List[str]] = None) -> bool:
    try:
        ET.fromstring(str(inp))
        return True
    except Exception as err:
        if out is not None:
            out.append(str(err))
        return False


xml_constraint = """
const start: <start>;

vars {
    tree: <xml-tree>;
    opid, clid: <id>;
}

constraint {
    forall tree="<{opid}[ <xml-attribute>]><inner-xml-tree></{clid}>" in start:
        (= opid clid)
}
"""

XML_CONSTRAINT = parse_isla(xml_constraint)
