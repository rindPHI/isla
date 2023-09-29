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

from typing import Tuple, Optional, List, TypeVar, TypeAlias, Mapping, Sequence

from frozendict import frozendict

S = TypeVar("S")
T = TypeVar("T")

ImmutableList: TypeAlias = tuple[T, ...]
Pair: TypeAlias = Tuple[S, T]

ParseTree = Tuple[str, Optional[List["ParseTree"]]]
Path = Tuple[int, ...]

Grammar = Mapping[str, Sequence[str]]
CanonicalGrammar = Mapping[str, Sequence[Sequence[str]]]

FrozenGrammar = frozendict[str, Tuple[str, ...]]
FrozenCanonicalGrammar = frozendict[str, Tuple[Tuple[str, ...], ...]]

# DEPRECATED! # TODO remove and replace with FrozenGrammar
ImmutableGrammar = Tuple[Tuple[str, Tuple[str, ...]], ...]
