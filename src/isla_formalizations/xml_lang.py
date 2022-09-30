# Copyright © 2022 CISPA Helmholtz Center for Information Security.
# Author: Dominic Steinhöfel.
#
# This file is part of ISLa.
#
# ISLa is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# ISLa is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with ISLa.  If not, see <http://www.gnu.org/licenses/>.

import copy
import string
import xml.etree.ElementTree as ET
from html import escape
from typing import Optional, List

from isla.helpers import srange
from isla.isla_predicates import IN_TREE_PREDICATE, SAME_POSITION_PREDICATE
from isla.language import parse_isla
from isla.derivation_tree import DerivationTree

XML_GRAMMAR = {
    "<start>": ["<xml-tree>"],
    "<xml-tree>": [
        "<xml-open-tag><inner-xml-tree><xml-close-tag>",
        "<xml-openclose-tag>",
    ],
    "<inner-xml-tree>": [
        "<xml-tree><inner-xml-tree>",
        "<xml-tree>",
        "<text>",
    ],
    "<xml-open-tag>": ["<<id> <xml-attribute>>", "<<id>>"],
    "<xml-openclose-tag>": ["<<id> <xml-attribute>/>", "<<id>/>"],
    "<xml-close-tag>": ["</<id>>"],
    "<xml-attribute>": ["<xml-attribute> <xml-attribute>", '<id>="<text>"'],
    "<id>": [
        "<id-start-char><id-chars>",
        "<id-start-char>",
    ],
    "<id-start-char>": srange("_" + string.ascii_letters),
    "<id-chars>": ["<id-char><id-chars>", "<id-char>"],
    "<id-char>": ["<id-start-char>"] + srange("-." + string.digits),
    "<text>": ["<text-char><text>", "<text-char>"],
    "<text-char>": [
        escape(c)
        for c in srange(string.ascii_letters + string.digits + "\"'. \t/?-,=:+")
    ],
}

XML_GRAMMAR_WITH_NAMESPACE_PREFIXES = copy.deepcopy(XML_GRAMMAR)
XML_GRAMMAR_WITH_NAMESPACE_PREFIXES.update(
    {
        "<id>": [
            "<id-with-prefix>",
            "<id-no-prefix>",
        ],
        "<id-no-prefix>": [
            "<id-start-char><id-chars>",
            "<id-start-char>",
        ],
        "<id-with-prefix>": ["<id-no-prefix>:<id-no-prefix>"],
    }
)


def validate_xml(inp: DerivationTree, out: Optional[List[str]] = None) -> bool:
    try:
        ET.fromstring(str(inp))
        return True
    except Exception as err:
        if out is not None:
            out.append(str(err))
        return False


xml_wellformedness_constraint = """
forall <xml-tree> tree="<{<id> opid}[ <xml-attribute>]><inner-xml-tree></{<id> clid}>" in start:
    (= opid clid)
"""

XML_WELLFORMEDNESS_CONSTRAINT = parse_isla(
    xml_wellformedness_constraint, XML_GRAMMAR_WITH_NAMESPACE_PREFIXES
)

xml_attribute_namespace_constraint = r"""
forall <xml-attribute> attribute="{<id-no-prefix> prefix_use}:{<id-no-prefix> maybe_def}=\"<text>\"":
  ((not prefix_use = "xmlns" or maybe_def = "xmlns") implies
    exists <xml-tree> outer_tag="<<id> {<xml-attribute> cont_attribute}><inner-xml-tree></<id>>":
      (inside(attribute, outer_tag) and
       exists <xml-attribute> def_attribute="xmlns:{<id-no-prefix> prefix_def}=\"<text>\"" in cont_attribute:
         (not (= prefix_def "xmlns") and (= prefix_use prefix_def))))"""

XML_ATTRIBUTE_NAMESPACE_CONSTRAINT = parse_isla(
    xml_attribute_namespace_constraint,
    XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
    structural_predicates={IN_TREE_PREDICATE},
)

xml_tag_namespace_constraint = r"""
forall <xml-tree> xml_tree="<{<id-no-prefix> prefix_use}:<id-no-prefix>[ <xml-attribute>][/]>[<inner-xml-tree><xml-close-tag>]":
  exists <xml-tree> outer_tag="<<id> {<xml-attribute> cont_attribute}><inner-xml-tree></<id>>":
    (inside(xml_tree, outer_tag) and 
     exists <xml-attribute>="xmlns:{<id-no-prefix> prefix_def}=\"<text>\"" in cont_attribute:
       prefix_use = prefix_def)"""

# xml_tag_namespace_constraint = r'''
# forall <xml-tree> xml_tree="<{<id-no-prefix> prefix_use}:<id-no-prefix>[ <xml-attribute>][/]>[<inner-xml-tree><xml-close-tag>]":
#   exists <xml-tree> outer_tag="<<id> {<xml-attribute> cont_attribute}><inner-xml-tree></<id>>": (
#     inside(xml_tree, outer_tag) and
#     exists <xml-attribute> in cont_attribute: (
#       <xml-attribute>.<id>.<id-with-prefix>.<id-no-prefix>[1] = "xmlns" and
#       prefix_use = <xml-attribute>.<id>.<id-with-prefix>.<id-no-prefix>[2]))'''

XML_TAG_NAMESPACE_CONSTRAINT = parse_isla(
    xml_tag_namespace_constraint,
    XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
    structural_predicates={IN_TREE_PREDICATE},
)

XML_NAMESPACE_CONSTRAINT = (
    XML_TAG_NAMESPACE_CONSTRAINT & XML_ATTRIBUTE_NAMESPACE_CONSTRAINT
)

xml_no_attr_redef_constraint = r"""
forall <xml-attribute> attr_outer in start:
  forall <xml-attribute> attr_inner_1="{<id> id_1}=\"<text>\"" in attr_outer:
    forall <xml-attribute> attr_inner_2="{<id> id_2}=\"<text>\"" in attr_outer: 
      (same_position(attr_inner_1, attr_inner_2) xor
       not (= id_1 id_2))"""

XML_NO_ATTR_REDEF_CONSTRAINT = parse_isla(
    xml_no_attr_redef_constraint,
    XML_GRAMMAR_WITH_NAMESPACE_PREFIXES,
    structural_predicates={IN_TREE_PREDICATE, SAME_POSITION_PREDICATE},
)
