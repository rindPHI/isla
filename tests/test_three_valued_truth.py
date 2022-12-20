import itertools
import unittest

from isla.three_valued_truth import ThreeValuedTruth


class TestThreeValuedTruth(unittest.TestCase):
    def test_neg(self):
        tval = ThreeValuedTruth.unknown()
        try:
            result = not tval
            self.fail("AssertionError expected")
        except AssertionError:
            pass

        tval = ThreeValuedTruth.true()
        self.assertTrue((-tval).is_false())

        tval = ThreeValuedTruth.false()
        self.assertTrue((-tval).is_true())

    def test_and(self):
        values = [
            ThreeValuedTruth.unknown(),
            ThreeValuedTruth.true(),
            ThreeValuedTruth.false(),
        ]

        for val_1, val_2 in itertools.combinations_with_replacement(values, 2):
            result = val_1 & val_2
            self.assertTrue(
                not val_1.is_unknown() and not val_2.is_unknown() or result.is_unknown()
            )
            self.assertTrue(
                val_1.is_unknown()
                or val_2.is_unknown()
                or bool(result) == (bool(val_1) and bool(val_2))
            )

    def test_or(self):
        values = [
            ThreeValuedTruth.unknown(),
            ThreeValuedTruth.true(),
            ThreeValuedTruth.false(),
        ]

        for val_1, val_2 in itertools.combinations_with_replacement(values, 2):
            result = val_1 | val_2
            self.assertTrue(
                not val_1.is_unknown() and not val_2.is_unknown() or result.is_unknown()
            )
            self.assertTrue(
                val_1.is_unknown()
                or val_2.is_unknown()
                or bool(result) == (bool(val_1) or bool(val_2))
            )

    def test_str(self):
        self.assertEqual("TRUE", str(ThreeValuedTruth.true()))
        self.assertEqual("FALSE", str(ThreeValuedTruth.false()))
        self.assertEqual("UNKNOWN", str(ThreeValuedTruth.unknown()))


if __name__ == "__main__":
    unittest.main()
