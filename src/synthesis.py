#!/usr/bin/env python2

import datetime
import itertools
import math
import random
import sys
from collections import defaultdict
from z3 import *

import predicates
import plans
import cost_model

class SolverContext:

    def __init__(self, varNames, fieldNames, assumptions=()):
        self.varNames = varNames
        self.fieldNames = fieldNames
        self.z3ctx = Context()
        self.z3solver = SolverFor("QF_LIA", ctx=self.z3ctx)
        for a in assumptions:
            self.z3solver.add(a.toZ3(self.z3ctx))

    def synthesizePlansByEnumeration(self, query, maxSize=1000):
        examples = []
        query = query.toNNF()
        while True:
            # print "starting synthesis using", len(examples), "examples"
            for responseType, response in self._synthesizePlansByEnumeration(query, maxSize, examples):
                if responseType == "counterexample":
                    example, plan = response
                    print "found counterexample", example, "\n\tfor", plan
                    if example in examples:
                        raise Exception("error: already saw counterexample!")
                    examples.append(example)
                    break
                elif responseType == "validPlan":
                    yield response
                elif responseType == "stop":
                    return

    def _synthesizePlansByEnumeration(self, query, maxSize, examples):
        """note: query should be in NNF"""

        def outputvector(predicate):
            return tuple([predicate.eval(dict(itertools.chain(zip(self.varNames, vs), zip(self.fieldNames, fs)))) for fs,vs in examples])

        def isValid(plan):
            """returns True, False, or a new counterexample"""
            planPred = plan.toPredicate()
            if outputvector(planPred) != queryVector:
                return False

            result = False
            s = self.z3solver
            s.push()
            s.add(planPred.toZ3(self.z3ctx) != query.toZ3(self.z3ctx))
            if str(s.check()) == 'unsat':
                result = True
            else:
                m = s.model()
                result = (
                    [int(str(m[Int(f, self.z3ctx)] or 0)) for f in self.fieldNames],
                    [int(str(m[Int(v, self.z3ctx)] or 0)) for v in self.varNames])
            s.pop()
            return result

        def consider(plan, size):
            assert plan.size() == size
            if not plan.wellFormed():
                return None, None
            cost = cost_model.cost(plan)
            if bestCost[0] is not None and cost >= bestCost[0]:
                # oops! this can't possibly be part of a better plan
                return None, None
            x = isValid(plan)
            if x is True:
                if bestCost[0] is None or cost < bestCost[0]:
                    productive[0] = True
                    bestPlan[0] = plan
                    bestCost[0] = cost
                    # evict big cached items
                    for val, p in cache.items():
                        if cost_model.cost(p) >= cost:
                            del cache[val]
                    for i in xrange(size + 1):
                        plansOfSize[i] = [p for p in plansOfSize[i] if cost_model.cost(p) < cost]
                return "validPlan", plan
            elif x is False:
                vec = outputvector(plan.toPredicate())
                old_plan = cache.get(vec)
                if old_plan is None or cost_model.cost(old_plan) > cost:
                    productive[0] = True
                    cache[vec] = plan
                    plansOfSize[size].append(plan)
                    if old_plan is not None:
                        plansOfSize[old_plan.size()].remove(old_plan)
                return None, None
            else:
                # x is new example!
                productive[0] = True
                return "counterexample", (x, plan)

        queryVector = outputvector(query)
        comps = set(query.comparisons())

        # cache maps output vectors to the best known plan implementing them
        cache = {}

        # plansOfSize[s] contains all interesting plans of size s
        plansOfSize = [[], []]

        # the stupidest possible plan: linear search
        dumbestPlan = plans.Filter(plans.All(), query)

        # these are lists so that the closures can modify their values
        # (grumble grumble "nonlocal" keyword missing grumble)
        bestPlan = [dumbestPlan] # best plan found so far
        bestCost = [cost_model.cost(dumbestPlan)] # cost of bestPlan
        if not examples:
            yield "validPlan", dumbestPlan
        productive = [False]

        print "round 1"
        for plan in [plans.All(), plans.Empty()]:
            yield consider(plan, 1)

        roundsWithoutProgress = 0
        maxRoundsWithoutProgress = 3

        for size in xrange(2, maxSize + 1):
            assert len(plansOfSize) == size
            plansOfSize.append([])
            productive[0] = False
            print "round", size, "cache size {}/{}".format(len(cache), 2**len(examples))
            for plan in (plans.HashLookup(p, f, v) for p in plansOfSize[size-1] for f in self.fieldNames for v in self.varNames if (f, v) in comps):
                yield consider(plan, size)
            for plan in (plans.BinarySearch(p, f, op, v) for p in plansOfSize[size-1] for f in self.fieldNames for v in self.varNames if (f, v) in comps for op in predicates.operators if op is not predicates.Ne):
                yield consider(plan, size)
            # TODO: more elaborate filters
            for plan in (plans.Filter(p, predicates.Compare(predicates.Var(f), op, predicates.Var(v))) for p in plansOfSize[size-1] for f in self.fieldNames for v in self.varNames if (f, v) in comps for op in predicates.operators):
                yield consider(plan, size)
            for plan in (ty(p1, p2) for ty in [plans.Intersect, plans.Union] for split in xrange(1, size-1) for p1 in plansOfSize[split] if not p1.isTrivial() for p2 in plansOfSize[size-split-1] if not p2.isTrivial() and p1 < p2):
                yield consider(plan, size)
            if not productive[0]:
                roundsWithoutProgress += 1
                if roundsWithoutProgress >= maxRoundsWithoutProgress:
                    print "last {} rounds were not productive; stopping".format(roundsWithoutProgress)
                    yield "stop", None
