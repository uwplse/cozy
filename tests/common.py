import unittest

from cozy.common import divide_integers_and_round_up, integer_log2_round_up

class TestCommonUtils(unittest.TestCase):

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
