import unittest

from cozy.common import (
    divide_integers_and_round_up, integer_log2_round_up,
    FrozenDict)

class TestCommonUtils(unittest.TestCase):

    def test_frozendict_unordered(self):
        d1 = FrozenDict([('a', 1), ('b', 2)])
        d2 = FrozenDict([('b', 2), ('a', 1)])
        assert hash(d1) == hash(d2)
        assert d1 == d2

    def test_frozendict_sortable(self):
        d1 = FrozenDict([('a', 1)])
        d2 = FrozenDict([('b', 2)])
        assert (d1 < d2) != (d1 > d2)
        assert d1 <= d1

    def test_divide_and_round_up(self):
        self.assertEqual(divide_integers_and_round_up(1, 2), 1)
        self.assertEqual(divide_integers_and_round_up(2, 2), 1)
        self.assertEqual(divide_integers_and_round_up(3, 2), 2)

    def test_integer_log2_round_up(self):
        self.assertEqual(integer_log2_round_up(1), 1)
        self.assertEqual(integer_log2_round_up(2), 1)
        self.assertEqual(integer_log2_round_up(3), 2)
        self.assertEqual(integer_log2_round_up(4), 2)
        self.assertEqual(integer_log2_round_up(5), 3)
