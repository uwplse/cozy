#!/usr/bin/env python2

"""
Reads a query from stdin, writes nice output to stdout.
"""

import sys
from synthesis import SolverContext
from parse import parseQuery
import cost_model

if __name__ == '__main__':
    fields, qvars, q = parseQuery(sys.stdin.read())

    sc = SolverContext(varNames = qvars, fieldNames = fields)
    print "Query:", q

    bestCost = None
    bestPlan = None

    try:
        for p in sc.synthesizePlansByEnumeration(q):
            cost = cost_model.cost(p)
            print "FOUND PLAN: ", p, "; cost = ", cost
            if bestCost is None or cost < bestCost:
                bestPlan = p
                bestCost = cost
    except KeyboardInterrupt as e:
        print "stopping due to keyboard interrupt"

    print "="*60
    print "Best plan found: ", bestPlan
    print "Best plan size: ", bestPlan.size()
    print "Cost: ", bestCost
