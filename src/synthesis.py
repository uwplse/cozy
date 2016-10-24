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

    def _planIsValidForQuery(self, plan, query, sort_field=None):
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
                [m.eval(Int(f, self.z3ctx)).as_long() for f in self.fieldNames],
                [m.eval(Int(v, self.z3ctx)).as_long() for v in self.varNames],
                plan.isSortedBy(sort_field) if sort_field is not None else True)
        s.pop()

        return result

    def _initialGuesses(self, query, sort_field):
        """
        Attempts to devise a clever starting point. This can greatly accelerate
        the search.
        NOTE: query must be in NNF
        """

        yield plans.Filter(plans.AllWhere(predicates.Bool(True)), query)

        def dnf(p):
            if isinstance(p, predicates.Or):
                return dnf(p.lhs) + dnf(p.rhs)
            elif isinstance(p, predicates.And):
                cases1 = dnf(p.lhs)
                cases2 = dnf(p.rhs)
                return tuple(c1 + c2
                    for c1 in cases1
                    for c2 in cases2)
            else:
                return ((p,),)

        def venn_regions(cases):
            if len(cases) > 10:
                return
            for n in range(2**len(cases)):
                if n: # all conditions false ---> exclude
                    yield tuple(
                        predicates.conjunction(cases[i]) if (n & (1 << i)) else predicates.Not(predicates.conjunction(cases[i])).toNNF()
                        for i in range(len(cases)))

        def make_plan(parts):
            empty = plans.AllWhere(predicates.Bool(False))
            if self._planIsValidForQuery(empty, predicates.conjunction(parts), sort_field) is True:
                return None
            parts = (x for p in parts for x in predicates.break_conj(p))
            filter_parts = []
            field_parts = []
            eq_parts = []
            cmp_parts = []
            for p in parts:
                if isinstance(p, predicates.Compare):
                    if p.lhs.name in self.fieldNames and p.rhs.name in self.fieldNames:
                        # print("field part: {}".format(p))
                        field_parts.append(p)
                    elif (p.lhs.name in self.fieldNames) != (p.rhs.name in self.fieldNames):
                        if p.op == predicates.Eq:
                            eq_parts.append(p)
                        elif p.op in [predicates.Lt, predicates.Le, predicates.Gt, predicates.Ge]:
                            cmp_parts.append(p)
                        else:
                            # print("filter part (Ne): {}".format(p))
                            filter_parts.append(p)
                    else:
                        # print("filter part (vars only): {}".format(p))
                        filter_parts.append(p)
                else:
                    # print("filter part (not cmp): {}".format(p))
                    filter_parts.append(p)
            plan = plans.AllWhere(predicates.conjunction(field_parts))
            if eq_parts:
                plan = plans.HashLookup(plan, predicates.conjunction(eq_parts))
            if cmp_parts:
                plan = plans.BinarySearch(plan, predicates.conjunction(cmp_parts))
            if filter_parts:
                plan = plans.Filter(plan, predicates.conjunction(filter_parts))
            return plan

        cases = dnf(query)
        parts = []
        for rgn in venn_regions(cases):
            plan = make_plan(rgn)
            if plan:
                parts.append(plan)

        if parts:
            p1 = parts[0]
            for p2 in parts[1:]:
                p1 = plans.Concat(p1, p2) if p1 < p2 else plans.Concat(p2, p1)
            print(p1)
            if p1.wellFormed(self.z3ctx, self.z3solver, self.fieldNames, self.varNames):
                yield p1
            else:
                print("WARNING: guess was not well-formed: {}".format(p1))

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
            return self._planIsValidForQuery(plan, query, sort_field)

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

                plan_cache.put(plan, key=vec, size=size, cost=cost)
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
        for b in (True, False):
            registerExp(predicates.Bool(b), cull=False)

        all_names = self.varNames + self.fieldNames
        for v in all_names:
            for f in all_names:
                if v < f and transitively_related(v, f, comps):
                    for op in predicates.operators:
                        registerExp(
                            predicates.Compare(predicates.Var(v), op, predicates.Var(f)),
                            cull=False)

        q = registerExp(query)

        for p in self._initialGuesses(query, sort_field):
            yield consider(p)
            for e in p.expressions():
                registerExp(e, size=1)
                pass

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
            for e in expr_cache.entries_of_size(size - 1):
                if all(v.name in self.fieldNames for v in e.vars()):
                    yield consider(plans.AllWhere(e))
            for plan in (plans.HashLookup(p, e) for p, e in pickToSum(plan_cache, expr_cache, size)):
                yield consider(plan)
            for plan in (plans.BinarySearch(p, e) for p, e in pickToSum(plan_cache, expr_cache, size)):
                yield consider(plan)
            for plan in (plans.Filter(p, e) for p, e in pickToSum(plan_cache, expr_cache, size)):
                yield consider(plan)
            for plan in (plans.Concat(p1, p2) for p1, p2 in pickToSum(plan_cache, plan_cache, size)):
                yield consider(plan)
