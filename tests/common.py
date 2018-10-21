import itertools
import os
import tempfile
import unittest

from cozy.common import (
    divide_integers_and_round_up, integer_log2_round_up,
    FrozenDict, AtomicWriteableFile, read_file,
    pick_to_sum)

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

    def test_frozendict_repr(self):
        for items in itertools.permutations([('a', 1), ('b', 2)]):
            d = FrozenDict(items)
            assert eval(repr(d)) == d

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

    def test_atomic_writeable_file(self):
        fd, path = tempfile.mkstemp(text=True)
        with os.fdopen(fd, "w") as f:
            f.write("contents0")

        # (1) normal writing works
        with AtomicWriteableFile(path) as f:
            f.write("contents1")
        assert read_file(path) == "contents1"

        # (2) if an error happens, no writing happens
        class CustomExc(Exception):
            pass
        try:
            with AtomicWriteableFile(path) as f:
                f.write("con")
                raise CustomExc()
                f.write("tents2")
        except CustomExc:
            pass
        assert read_file(path) == "contents1"

    def test_pick_to_sum_1_2(self):
        self.assertEqual(list(pick_to_sum(1, total_size=2)), [(2,)])

    def test_pick_to_sum_2_2(self):
        self.assertEqual(list(pick_to_sum(2, total_size=2)), [(0,2), (1,1), (2,0)])

    def test_pick_to_sum_2_3(self):
        self.assertEqual(list(pick_to_sum(2, total_size=3)), [(0,3), (1,2), (2,1), (3,0)])
