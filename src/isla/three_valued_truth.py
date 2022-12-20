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

from dataclasses import dataclass
from typing import Iterable


@dataclass(frozen=True)
class ThreeValuedTruth:
    val: int

    FALSE = 0
    TRUE = 1
    UNKNOWN = 2

    def to_bool(self) -> bool:
        assert self.val != ThreeValuedTruth.UNKNOWN
        return bool(self.val)

    def __bool__(self):
        return self.to_bool()

    def is_false(self):
        return self.val == ThreeValuedTruth.FALSE

    def is_true(self):
        return self.val == ThreeValuedTruth.TRUE

    def is_unknown(self):
        return self.val == ThreeValuedTruth.UNKNOWN

    @staticmethod
    def from_bool(b: bool) -> "ThreeValuedTruth":
        return ThreeValuedTruth(int(b))

    @staticmethod
    def all(args: Iterable["ThreeValuedTruth"]) -> "ThreeValuedTruth":
        args = list(args)
        if any(elem.is_false() for elem in args):
            return ThreeValuedTruth.false()
        if any(elem.is_unknown() for elem in args):
            return ThreeValuedTruth.unknown()
        return ThreeValuedTruth.true()

    @staticmethod
    def any(args: Iterable["ThreeValuedTruth"]) -> "ThreeValuedTruth":
        args = list(args)
        if any(elem.is_true() for elem in args):
            return ThreeValuedTruth.true()
        if any(elem.is_unknown() for elem in args):
            return ThreeValuedTruth.unknown()
        return ThreeValuedTruth.false()

    @staticmethod
    def not_(arg: "ThreeValuedTruth") -> "ThreeValuedTruth":
        if arg.is_true():
            return ThreeValuedTruth.false()
        if arg.is_false():
            return ThreeValuedTruth.true()
        return ThreeValuedTruth.unknown()

    @staticmethod
    def true():
        return ThreeValuedTruth(ThreeValuedTruth.TRUE)

    @staticmethod
    def false():
        return ThreeValuedTruth(ThreeValuedTruth.FALSE)

    @staticmethod
    def unknown():
        return ThreeValuedTruth(ThreeValuedTruth.UNKNOWN)

    def __neg__(self):
        if self.is_unknown():
            return self

        return ThreeValuedTruth(not bool(self))

    def __and__(self, other: "ThreeValuedTruth") -> "ThreeValuedTruth":
        if self.is_unknown() or other.is_unknown():
            return ThreeValuedTruth.unknown()

        return ThreeValuedTruth.from_bool(bool(self) and bool(other))

    def __or__(self, other: "ThreeValuedTruth") -> "ThreeValuedTruth":
        if self.is_unknown() or other.is_unknown():
            return ThreeValuedTruth.unknown()

        return ThreeValuedTruth.from_bool(bool(self) or bool(other))

    def __str__(self):
        return "TRUE" if self.is_true() else "FALSE" if self.is_false() else "UNKNOWN"
