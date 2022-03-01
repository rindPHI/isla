from typing import Iterable


class ThreeValuedTruth:
    FALSE = 0
    TRUE = 1
    UNKNOWN = 2

    def __init__(self, val: int):
        assert 0 <= val <= 2
        self.val = val

    def __eq__(self, other):
        return self.val == other.val

    def __hash__(self):
        return self.val

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
    def from_bool(b: bool) -> 'ThreeValuedTruth':
        return ThreeValuedTruth(int(b))

    @staticmethod
    def all(args: Iterable['ThreeValuedTruth']) -> 'ThreeValuedTruth':
        args = list(args)
        if any(elem.is_false() for elem in args):
            return ThreeValuedTruth.false()
        if any(elem.is_unknown() for elem in args):
            return ThreeValuedTruth.unknown()
        return ThreeValuedTruth.true()

    @staticmethod
    def any(args: Iterable['ThreeValuedTruth']) -> 'ThreeValuedTruth':
        args = list(args)
        if any(elem.is_true() for elem in args):
            return ThreeValuedTruth.true()
        if any(elem.is_unknown() for elem in args):
            return ThreeValuedTruth.unknown()
        return ThreeValuedTruth.false()

    @staticmethod
    def not_(arg: 'ThreeValuedTruth') -> 'ThreeValuedTruth':
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

        return ThreeValuedTruth(bool(self))

    def __and__(self, other: 'ThreeValuedTruth') -> 'ThreeValuedTruth':
        if self.is_unknown() or other.is_unknown():
            return ThreeValuedTruth.unknown()

        return ThreeValuedTruth.from_bool(bool(self) and bool(other))

    def __or__(self, other: 'ThreeValuedTruth') -> 'ThreeValuedTruth':
        if self.is_unknown() or other.is_unknown():
            return ThreeValuedTruth.unknown()

        return ThreeValuedTruth.from_bool(bool(self) or bool(other))

    def __repr__(self):
        return f"ThreeValuedTruth({self.val})"

    def __str__(self):
        return ("TRUE" if self.is_true() else
                "FALSE" if self.is_false() else
                "UNKNOWN")