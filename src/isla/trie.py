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

from typing import List, Dict, Optional, Tuple, Generic, TypeVar

import datrie

from isla.helpers import is_path
from isla.type_defs import Path

T = TypeVar("T")


class SubtreesTrie(Generic[T]):
    def __init__(
        self,
        init_map: Optional[Dict[Path, Tuple[Path, T]]] = None,
        init_trie: Optional[datrie.Trie] = None,
        root_path: Optional[Path] = None,
    ):
        if init_trie:
            self.trie = init_trie
        else:
            self.trie = datrie.Trie([chr(i) for i in range(30)])
            for path in init_map or {}:
                self.trie[path_to_trie_key(path)] = init_map[path]

        if root_path is not None:
            self.root_path: str = path_to_trie_key(root_path)
        else:
            self.root_path: str = ""

    def __setitem__(self, key: Path, value: Tuple[Path, T]):
        assert is_path(key)
        self.trie[path_to_trie_key(key)] = value

    def __getitem__(self, item: Path) -> Tuple[Path, T]:
        assert is_path(item)
        return self.trie[path_to_trie_key(item)]

    def keys(self) -> List[Path]:
        return [
            trie_key_to_path(chr(1) + suffix)
            for suffix in self.trie.suffixes(self.root_path)
        ]

    def values(self) -> List[Tuple[Path, T]]:
        return [
            (
                value := self.trie[self.root_path + suffix],
                (value[0][len(self.root_path) - 1 :], value[1]),
            )[-1]
            for suffix in self.trie.suffixes(self.root_path)
        ]

    def items(self) -> List:
        return [
            (
                trie_key_to_path(chr(1) + suffix),
                (
                    value := self.trie[self.root_path + suffix],
                    (value[0][len(self.root_path) - 1 :], value[1]),
                )[-1],
            )
            for suffix in self.trie.suffixes(self.root_path)
        ]

    def get_subtrie(self, new_root_path: Path) -> "SubtreesTrie":
        assert is_path(new_root_path)
        return SubtreesTrie(init_trie=self.trie, root_path=new_root_path)


def path_to_trie_key(path: Path) -> str:
    # 0-bytes are ignored by the trie ==> +1
    # To represent the empty part, reserve chr(1) ==> +2
    if not path:
        return chr(1)

    return chr(1) + "".join([chr(i + 2) for i in path])


def trie_key_to_path(key: str) -> Path:
    if not key or key[0] != chr(1):
        raise RuntimeError(
            f"Invalid trie key '{key}' ({[ord(c) for c in key]}), should start with 1"
        )

    if key == chr(1):
        return ()

    return tuple([ord(c) - 2 for c in key if ord(c) != 1])
