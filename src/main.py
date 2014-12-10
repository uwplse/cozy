#!/usr/bin/env python2

"""
Reads a query from stdin, writes nice output to stdout.
"""

import sys
from synthesis import SolverContext
from parse import parseQuery

def mkQuery(sc, ast):
    n = getattr(sc.Query, ast[0])
    if ast[0] in ["TrueQuery", "FalseQuery"]:
        return n
    elif ast[0] in ["And", "Or"]:
        return n(mkQuery(sc, ast[1]), mkQuery(sc, ast[2]))
    elif ast[0] == "Not":
        return n(mkQuery(sc, ast[1]))
    elif ast[0] == "Cmp":
        return n(
            getattr(sc.Field, ast[1]),
            getattr(sc.Comparison, ast[2]),
            getattr(sc.QueryVar, ast[3]))
    else:
        raise Exception("failed to make query from {}".format(ast))

if __name__ == '__main__':
    fields, qvars, q_ast = parseQuery(sys.stdin.read())

    sc = SolverContext(varNames = qvars, fieldNames = fields)
    q = mkQuery(sc, q_ast)
    print "Query:", q
    print "Query size:", str(q).count('Cmp')

    bestCost = None
    bestPlan = None

    try:
        for p in sc.synthesizePlansByEnumeration(q):
            cost = sc.computeCost(p)[0]
            print "FOUND PLAN: ", p, "; cost = ", cost
            if bestCost is None or cost < bestCost:
                bestPlan = p
                bestCost = cost
    except KeyboardInterrupt as e:
        print "stopping due to keyboard interrupt"

    print "="*60
    print "Best plan found: ", bestPlan
    print "Best plan size: ", sc.size(bestPlan)
    print "Cost: ", bestCost
