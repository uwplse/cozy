import unittest

from cozy.polynomials import Polynomial

class TestPolynomials(unittest.TestCase):

    def test_sorting(self):
        self.assertLess(Polynomial([2019, 944, 95]), Polynomial([2012, 945, 95]))
        self.assertGreater(Polynomial([2012, 945, 95]), Polynomial([2019, 944, 95]))
