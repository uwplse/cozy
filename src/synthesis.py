#!/usr/bin/env python2

from __future__ import print_function
import datetime
import itertools
import math
import random
import sys
import time
from collections import defaultdict
import traceback
from z3 import *

from common import ADT
from cache import Cache
import predicates
import plans

class Timeout(Exception):
    pass

class SolverContext(object):

    def __init__(self, varNames, fieldNames, cost_model, assumptions=()):
        self.varNames = varNames
        self.fieldNames = fieldNames
        self.z3ctx = Context()
        self.z3solver = SolverFor("QF_LIA", ctx=self.z3ctx)
        self.assumptions = assumptions
        for a in assumptions:
            self.z3solver.add(a.toZ3(self.z3ctx))
        self.cost_model = cost_model

    def cost(self, plan):
        if not hasattr(plan, "_cost"):
            plan._cost = self.cost_model(plan)
            # This small bump is to ensure we favor simpler plans
            plan._cost += plan.size() / 10000.0
        return plan._cost

    def _check_timeout(self):
        if self.timeout is not None and (time.time() - self.startTime) > self.timeout:
            raise Timeout()

    def synthesizePlansByEnumeration(self, query, sort_field=None, maxSize=1000, timeout=None):
        examples = []
        query = query.toNNF()

        dumbestPlan = plans.Filter(plans.AllWhere(predicates.Bool(True)), query)
        self.bestCost = self.cost(dumbestPlan) # cost of best valid plan found so far
        self.bestPlans = set([dumbestPlan]) # set of valid plans with cost == self.bestCost
        self.startTime = time.time()
        self.timeout = timeout
        proceed = True

        try:
            while proceed:
                # print("starting synthesis using", len(examples), "examples")
                for responseType, response in self._synthesizePlansByEnumeration(query, sort_field, maxSize, examples):
                    if responseType == "counterexample":
                        example, plan = response
                        print("found counterexample", example, "\n\tfor", plan)
                        if example in examples:
                            raise Exception("error: already saw counterexample!")
                        examples.append(example)
                        break
                    elif responseType == "validPlan":
                        pass
                    elif responseType == "stop":
                        proceed = False
                        break
        except:
            print("stopping due to exception")
            traceback.print_exc()

        for plan in self.bestPlans:
            yield plan

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

        def isValid(plan):
            """returns True, False, or a new counterexample"""
            assert len(outputvector(plan)) == len(queryVector)
            if outputvector(plan) != queryVector:
                return False

            result = False
            s = self.z3solver
            s.push()
            try:
                s.add(plan.toPredicate().toZ3(self.z3ctx) != query.toZ3(self.z3ctx))
            except Exception as e:
                print(plan, e, plan.toPredicate())
                raise e
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

        def implies(vec1, vec2):
            """Every element of vec1 implies corresponding element in vec2"""
            return all(v2 if v1 else True for (v1, v2) in zip(vec1, vec2))

        def on_valid_plan(plan, cost):
            if cost > self.bestCost:
                return
            print("found good valid plan: {}, cost={}".format(plan, cost))
            if cost < self.bestCost:
                self.bestCost = cost
                self.bestPlans = set()
            self.bestPlans.add(plan)
            plan_cache.evict_higher_cost_entries(cost)

        def consider(plan):
            self._check_timeout()
            size = plan.size()
            if not plan.wellFormed(self.z3ctx, self.z3solver, self.fieldNames, self.varNames):
                return None, None
            x = isValid(plan)
            cost = self.cost(plan)

            # too expensive? it can't possibly be part of a great plan!
            if self.bestCost is not None and cost > self.bestCost:
                return None, None

            if x is True:
                on_valid_plan(plan, cost)
                return "validPlan", plan
            elif x is False:
                vec = outputvector(plan)

                # fastforward
                if implies(queryVector, vec):
                    plan2 = plans.Filter(plan, query)
                    x2 = isValid(plan2)
                    if x2 is True:
                        on_valid_plan(plan2, self.cost(plan2))
                    elif x2 is False:
                        # This case can happen if plan2 is correct BUT not
                        # not sorted correctly.
                        pass
                    else:
                        return "counterexample", (x2, plan2)

                plan_cache.put(plan, key=vec)
                return None, None
            else:
                # x is new example!
                return "counterexample", (x, plan)

        def registerExp(e, cull=True, size=None):
            self._check_timeout()
            return expr_cache.put(e, size=size)

        def pickToSum(cache1, cache2, sum):
            return ((x1, x2) for split in range(1, sum-1)
                for x1 in cache1.entries_of_size(split)
                for x2 in cache2.entries_of_size(sum-split-1))

        queryVector = outputvector(query)
        comps = set(query.comparisons())
        for a in self.assumptions:
            # print("A ==> {}".format(a))
            for c in a.comparisons():
                comps.add(c)
        for a, b in list(comps):
            comps.add((b, a))

        def transitively_related(x1, x2, comps, visited=None):
            if x1 == x2:
                return True
            if visited is None:
                visited = set()
            elif x1 in visited:
                return False
            visited.add(x1)
            for a, b in comps:
                if a == x1:
                    if transitively_related(b, x2, comps, visited):
                        return True
            return False

        plan_cache = Cache(cost_func=self.cost,   size_func=ADT.size, key_func=outputvector, allow_multi=True)
        expr_cache = Cache(cost_func=lambda e: 1, size_func=ADT.size, key_func=outputvector, allow_multi=False)

        print("starting with {} examples".format(len(examples)))
        print("round 1")
        for f1 in self.fieldNames:
            for f2 in self.fieldNames:
                if f1 < f2 and transitively_related(f1, f2, comps):
                    for op in predicates.operators:
                        plan = plans.AllWhere(predicates.Compare(
                            predicates.Var(f1), op, predicates.Var(f2)))
                        yield consider(plan)
        for b in (True, False):
            plan = plans.AllWhere(predicates.Bool(b))
            yield consider(plan)

        for v in self.varNames:
            for f in self.fieldNames:
                if transitively_related(v, f, comps):
                    for op in predicates.operators:
                        registerExp(
                            predicates.Compare(predicates.Var(v), op, predicates.Var(f)),
                            cull=False)
        for b in (True, False):
            registerExp(predicates.Bool(b), cull=False)

        q = registerExp(query)

        yield consider(plans.BinarySearch(plans.AllWhere(predicates.Bool(True)), q))
        yield consider(plans.HashLookup(plans.AllWhere(predicates.Bool(True)), q))

        if all(type(x) is predicates.Compare for x in predicates.break_conj(query)):
            eqs = [x for x in predicates.break_conj(query) if x.op == plans.Eq]
            others = [x for x in predicates.break_conj(query) if x.op != plans.Eq]
            if eqs and others:
                hashcond = predicates.conjunction(eqs)
                bscond = predicates.conjunction(others)
                plan = plans.BinarySearch(plans.HashLookup(plans.AllWhere(predicates.Bool(True)), hashcond), bscond)
                yield consider(plan)

        roundsWithoutProgress = 0
        maxRoundsWithoutProgress = 10

        for size in range(2, maxSize + 1):
            # termination criterion: no plans can ever be formed above this point
            halfsize = int(size/2)
            if all((sz > 2 and not plan_cache.entries_of_size(sz-1) and all((not plan_cache.entries_of_size(i) or (not plan_cache.entries_of_size(sz - i - 1) and not plan_cache.entries_of_size(sz - i - 1))) for i in range(1, sz - 1))) for sz in range(halfsize, size+1)):
                yield ("stop", None)

            # exprs
            # Since we have all operators and their negations, we will never
            # generate anything interesting involving Not.
            for e1, e2 in pickToSum(expr_cache, expr_cache, size):
                registerExp(predicates.And(e1, e2), size=size)
                registerExp(predicates.Or(e1, e2),  size=size)

            # plans
            print("round {}; cache={}/{max}; ecache={}/{max}; bestCost={}".format(size, len(plan_cache), len(expr_cache), self.bestCost, max=2**len(examples)))
            for plan in (plans.HashLookup(p, e) for p, e in pickToSum(plan_cache, expr_cache, size)):
                yield consider(plan)
            for plan in (plans.BinarySearch(p, e) for p, e in pickToSum(plan_cache, expr_cache, size)):
                yield consider(plan)
            for plan in (plans.Filter(p, e) for p, e in pickToSum(plan_cache, expr_cache, size)):
                yield consider(plan)
            for plan in (plans.Concat(p1, p2) for p1, p2 in pickToSum(plan_cache, plan_cache, size)):
                yield consider(plan)
