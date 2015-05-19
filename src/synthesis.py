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

class SolverContext:

    def __init__(self, varNames, fieldNames, cost_model, assumptions=()):
        self.varNames = varNames
        self.fieldNames = fieldNames
        self.z3ctx = Context()
        self.z3solver = SolverFor("QF_LIA", ctx=self.z3ctx)
        for a in assumptions:
            self.z3solver.add(a.toZ3(self.z3ctx))
        self.cost_model = cost_model

    def cost(self, plan):
        if not hasattr(plan, "_cost"):
            plan._cost = self.cost_model(plan)
        return plan._cost

    def synthesizePlansByEnumeration(self, query, sort_field=None, maxSize=1000):
        examples = []
        query = query.toNNF()

        dumbestPlan = plans.Filter(plans.All(), query)
        self.bestCost = self.cost(dumbestPlan) # cost of best valid plan found so far
        self.productive = False # was progress made this iteration
        yield dumbestPlan

        while True:
            # print "starting synthesis using", len(examples), "examples"
            for responseType, response in self._synthesizePlansByEnumeration(query, sort_field, maxSize, examples):
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

    def _synthesizePlansByEnumeration(self, query, sort_field, maxSize, examples):
        """note: query should be in NNF"""

        def outputvector(predicate):
            correct_sorting = True
            if isinstance(predicate, plans.Plan):
                if sort_field is not None:
                    correct_sorting = predicate.isSortedBy(sort_field)
                predicate = predicate.toPredicate()
            if not hasattr(predicate, "_outputvector") or len(predicate._outputvector) != len(examples) + 1:
                vec = [predicate.eval(dict(itertools.chain(zip(self.varNames, vs), zip(self.fieldNames, fs)))) for fs,vs,_ in examples]
                if sort_field is not None:
                    vec.append(correct_sorting)
                predicate._outputvector = tuple(vec)
            return predicate._outputvector

        def stupid(plan):
            if type(plan) is plans.Filter and type(plan.plan) is plans.Filter and plan.predicate < plan.plan.predicate:
                return True
            if type(plan) in [plans.HashLookup, plans.BinarySearch, plans.Filter]:
                return outputvector(plan) == outputvector(plan.plan) or stupid(plan.plan)
            if type(plan) in [plans.Intersect, plans.Union]:
                return (outputvector(plan) == outputvector(plan.plan1) or
                    outputvector(plan) == outputvector(plan.plan2) or
                    outputvector(plan.plan1) == outputvector(plan.plan2) or
                    stupid(plan.plan1) or stupid(plan.plan2))

        def isValid(plan):
            """returns True, False, or a new counterexample"""
            assert len(outputvector(plan)) == len(queryVector)
            if outputvector(plan) != queryVector:
                return False

            result = False
            s = self.z3solver
            s.push()
            s.add(plan.toPredicate().toZ3(self.z3ctx) != query.toZ3(self.z3ctx))
            if str(s.check()) == 'unsat':
                result = True
            else:
                m = s.model()
                result = (
                    [int(str(m[Int(f, self.z3ctx)] or 0)) for f in self.fieldNames],
                    [int(str(m[Int(v, self.z3ctx)] or 0)) for v in self.varNames],
                    plan.isSortedBy(sort_field) if sort_field is not None else True)
            s.pop()

            return result

        def consider(plan, size):
            assert plan.size() == size
            if not plan.wellFormed() or stupid(plan):
                return None, None
            x = isValid(plan)
            cost = self.cost(plan)

            # too expensive? it can't possibly be part of a great plan!
            if self.bestCost is not None and cost > self.bestCost:
                return None, None

            if x is True:
                self.productive = True
                self.bestCost = cost
                # evict big cached items
                for val, p in cache.items():
                    if self.cost(p) > cost:
                        del cache[val]
                for i in xrange(size + 1):
                    plansOfSize[i] = [p for p in plansOfSize[i] if self.cost(p) <= cost]
                return "validPlan", plan
            elif x is False:
                vec = outputvector(plan)
                old_plan = cache.get(vec)

                # new possibility
                if old_plan is None:
                    cache[vec] = plan
                    plansOfSize[size].append(plan)
                    self.productive = True

                # better than previous options
                # TODO: this eviction doesn't handle sort_field properly...
                elif cost < self.cost(old_plan):
                    cache[vec] = plan
                    for i in xrange(size + 1):
                        plansOfSize[i] = [p for p in plansOfSize[i] if outputvector(p) != vec]
                    plansOfSize[size].append(plan)
                    self.productive = True

                # as good as previous options
                elif cost == self.cost(old_plan):
                    plansOfSize[size].append(plan)
                    self.productive = True

                return None, None
            else:
                # x is new example!
                self.productive = True
                return "counterexample", (x, plan)

        queryVector = outputvector(query)
        comps = set(query.comparisons())
        for a, b in list(comps):
            comps.add((b, a))

        # cache maps output vectors to the best known plan implementing them
        cache = {}

        # plansOfSize[s] contains all interesting plans of size s
        plansOfSize = [[], []]

        print "round 1"
        for plan in [plans.All(), plans.Empty()]:
            yield consider(plan, 1)

        roundsWithoutProgress = 0
        maxRoundsWithoutProgress = 3

        for size in xrange(2, maxSize + 1):
            assert len(plansOfSize) == size
            plansOfSize.append([])
            self.productive = False
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
            if not self.productive:
                roundsWithoutProgress += 1
                if roundsWithoutProgress >= maxRoundsWithoutProgress:
                    print "last {} rounds were not productive; stopping".format(roundsWithoutProgress)
                    yield "stop", None
