"""Functions for working with graphs of nodes and edges."""

# This module provides a nicer interface to igraph.  It also serves as an
# abstraction layer that lets us to switch to a different graph library later,
# if we want.

import igraph

def _safe_feedback_arc_set(g, method="ip"):
    """
    Compute the feedback arc set for directed graph `g`.
    This is a set of edges that, when removed, break cycles and
    convert the graph `g` into a DAG.

    This function works around a potential segfault in igraph:
    https://github.com/igraph/igraph/issues/858
    """

    assert g.is_directed()

    # No verts? No problem!
    if g.vcount() == 0:
        return []

    orig_g = g
    g = g.copy()

    # Add a "terminal" node with an edge from every vertex.
    # This should not affect the feedback arc set.
    new_vertex_id = g.vcount()
    g.add_vertices(1)
    g.add_edges([(v, new_vertex_id) for v in range(new_vertex_id)])

    edge_ids = g.feedback_arc_set(method=method)

    # I assume the edge ids are the same between g and its copy?
    # Let's do a little bit of checking just in case.
    g.delete_vertices([new_vertex_id])
    to_check = [g.es[e].source for e in edge_ids]
    d1 = orig_g.degree(to_check)
    d2 = g.degree(to_check)
    assert d1 == d2, "{!r} vs {!r}".format(d1, d2)

    return edge_ids

class DirectedGraph(object):

    def __init__(self, nodes, successors):
        """Create a new directed graph.

        Parameters:
            nodes - an iterable set of objects to use as nodes of the graph
            successors - a function that takes a node n and returns an iterable
                collection of successors of n (nodes m where n->m is an edge)
        """

        self.nodes = list(nodes)
        self.g = igraph.Graph().as_directed()
        self.g.add_vertices(len(self.nodes))
        for i in range(len(self.nodes)):
            self.g.add_edges([(i, self._vertex_id(n)) for n in successors(self.nodes[i])])

    def _vertex_id(self, label):
        """Return the igraph ID for the given vertex label."""
        return self.nodes.index(label)

    def minimum_feedback_arc_set(self):
        """Compute the smallest feedback arc set for directed graph `g`.

        This is a set of edges that, when removed, break all cycles and convert
        `g` into a DAG.
        """
        return _safe_feedback_arc_set(self.g)

    def delete_edges(self, edge_ids):
        """Delete a set of edges."""
        self.g.delete_edges(edge_ids)

    def toposort(self):
        """Iterate over the nodes in topologically-sorted order."""
        for node_id in self.g.topological_sorting(mode="OUT"):
            yield self.nodes[node_id]

    def reachable_nodes(self, roots):
        """Iterate over the nodes reachable from any of the given roots."""
        # incredibly, igraph has no method for this
        seen = set()
        stk = [self._vertex_id(r) for r in roots]
        while stk:
            n = stk.pop()
            if n in seen:
                continue
            yield self.nodes[n]
            seen.add(n)
            stk.extend(self.g.successors(n))
