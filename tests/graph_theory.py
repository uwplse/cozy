import unittest

from cozy.graph_theory import DirectedGraph

class TestGraphAlgorithms(unittest.TestCase):

    def test_feedback_arcs_empty(self):
        g = DirectedGraph([], lambda n: [])
        assert g.minimum_feedback_arc_set() == []

    def test_feedback_arcs_singleton(self):
        g = DirectedGraph([1], lambda n: [])
        assert g.minimum_feedback_arc_set() == []

    def test_feedback_arcs_1self(self):
        g = DirectedGraph([1], lambda n: [1])
        assert g.minimum_feedback_arc_set() == [0]

    def test_feedback_arcs_binary(self):
        g = DirectedGraph([1, 2], lambda n: [3 - n])
        # either edge will work
        assert g.minimum_feedback_arc_set() in ([0], [1])

    def test_feedback_arcs_point_cloud(self):
        g = DirectedGraph(list(range(10)), lambda n: [])
        assert g.minimum_feedback_arc_set() == []
