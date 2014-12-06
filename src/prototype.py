#!/usr/bin/env python2

import datetime
import math
import random
import sys
from collections import defaultdict
from z3 import *

MAX_PLAN_DEPTH = 2
MAX_QUERY_DEPTH = 2
COST_ITEM_COUNT = 1000
COST_BITS = 11

# TODO Is it possible (easy) to make an @z3Typed(Int, Int, Bool) annotation
#       that will convert a Python function to z3? Recursion would be tricky
#       ... maybe be slightly ugly... or use a type overriding callable?

def iteCases(default, *caseList):
    try:
        res = default
        for (test, val) in caseList:
            res = If(test, val, res)
        return res
    except ValueError:
        print caseList
        raise
def iteAllCases(*caseList):
    return iteCases(False, *caseList)

def getConstructorIdx(Type, name):
    for idx in range(0, Type.num_constructors()):
        if Type.constructor(idx).name() == name:
            return idx
    raise Exception("Type %s has no constructor named %s." % (Type, name))
def getRecognizer(Type, name):
    return Type.recognizer(getConstructorIdx(Type, name))
def allRecognizers(Type):
    return [Type.recognizer(i) for i in range(0, Type.num_constructors())]

def doSymbolTableLookup(Type, variable, vals):
    res = vals[0]
    for idx in range(1, Type.num_constructors()):
        res = If(Type.recognizer(idx)(variable), vals[idx], res)
    return res

def getArgNum(value, Type, argIdx, ArgType, default):
    res = default
    for idx in range(0, Type.num_constructors()):
        if Type.constructor(idx).arity() > argIdx:
            accessor = Type.accessor(idx, argIdx)
            if accessor.range() == ArgType:
                res = If(Type.recognizer(idx)(value), accessor(value), res)
    return res
    res = default
    for (test, val) in caseList:
        res = If(test, val, res)
    return res

def Min(a, b):
    return If(a < b, a, b)

def z3Log(bv):
    size = bv.size()
    return iteCases(BitVecVal(0, size),
                    *[(Extract(bit, bit, bv) == BitVecVal(1, 1),
                       BitVecVal(bit, size))
                      for bit in range(0, size)])

class SolverContext:
    def declareDatatype(self, name, values):
        if isinstance(name, Datatype):
            Type = name
        else:
            Type = Datatype(name)
        for (value, args) in values:
            Type.declare(value, *args)
        return Type.create()

    def declareSimpleDatatype(self, name, values):
        return self.declareDatatype(name, [(v, []) for v in values])


    def __init__(self, varNames, fieldNames):
        self.varNames = varNames
        self.fieldNames = fieldNames

        QueryVar = self.QueryVar = self.declareSimpleDatatype('QueryVar',
                                                              varNames)
        Field = self.Field = self.declareSimpleDatatype('Field', fieldNames)

        comparisonOperators = ['Eq', 'Gt', 'Ge', 'Lt', 'Le']
        self.Comparison = self.declareSimpleDatatype('Comparison',
                                                     comparisonOperators)
        Comparison = self.Comparison

        Val = self.Val = self.declareSimpleDatatype('Val', ['lo', 'mid', 'hi'])

        # Need to do this for recursive datatype
        Query = Datatype('Query')
        Query = self.Query = self.declareDatatype(Query, [
            ('TrueQuery', []),
            ('FalseQuery', []),
            ('Cmp', [
                ('cmpField', Field),
                ('cmpOp', Comparison),
                ('cmpVar', QueryVar)]),
            ('And', [('andLeft', Query), ('andRight', Query)]),
            ('Or', [('orLeft', Query), ('orRight', Query)]),
            ('Not', [('notQ', Query)]),
            ])

        Plan = Datatype('Plan')
        Plan = self.Plan = self.declareDatatype(Plan, [
            ('All', []),
            ('None', []),
            ('HashLookup', [
                ('hashPlan', Plan),
                ('hashField', Field),
                ('hashVar', QueryVar)]),
            ('BinarySearch', [
                ('bsPlan', Plan), ('bsField', Field),
                ('bsOp', Comparison), ('bsVar', QueryVar)]),
            ('Filter', [('filterPlan', Plan), ('filterQuery', Query)]),
            ('Intersect', [('isectFirstPlan', Plan),
                           ('isectSecondPlan', Plan)]),
            ('Union', [('uFirstPlan', Plan), ('uSecondPlan', Plan)]),
            ])

        self.CostResult = self.declareDatatype('CostResult', [
            ('CostRes', [('cost', BitVecSort(COST_BITS)),
                         ('costN', BitVecSort(COST_BITS))])
            ])

    # Note: define-fun is a macro, so the Z3 libary doesn't provide it because
    #       Python is our macro language.
    def isSortedBy(self, p, f):
        Plan = self.Plan
        return iteAllCases(
                (Plan.is_All(p), True),
                (Plan.is_None(p), True),
                (Plan.is_BinarySearch(p), Plan.bsField(p) == f),
                (Plan.is_HashLookup(p), True),
                )

    def planLe(self, p1, p2):
        # Order plans by the definition order of the constructors.
        recs = allRecognizers(self.Plan)
        return And([Implies(l[0](p1), Or([rec(p2) for rec in l])) for l in
                    # all of the tails of recs (whole list is a trivial case)
                    [recs[i:] for i in range(1, len(recs))]])

    def queryLe(self, q1, q2):
        # Order queries by the definition order of the constructors.
        recs = allRecognizers(self.Query)
        return And([Implies(l[0](q1), Or([rec(q2) for rec in l])) for l in
                    # all of the tails of recs (whole list is a trivial case)
                    [recs[i:] for i in range(1, len(recs))]])

    def leftPlan(self, p):
        Plan = self.Plan
        return getArgNum(value=p, Type=Plan, argIdx=0,
                         ArgType=Plan, default=Plan.All)
    def rightPlan(self, p):
        Plan = self.Plan
        return getArgNum(value=p, Type=Plan, argIdx=1,
                         ArgType=Plan, default=Plan.All)

    def leftQuery(self, q):
        Query = self.Query
        return getArgNum(value=q, Type=Query, argIdx=0,
                         ArgType=Query, default=Query.TrueQuery)
    def rightQuery(self, q):
        Query = self.Query
        return getArgNum(value=q, Type=Query, argIdx=1,
                         ArgType=Query, default=Query.TrueQuery)

    def isTrivialQuery(self, q):
        Query = self.Query
        return Or(q == Query.TrueQuery, q == Query.FalseQuery)

    def queryWf(self, q, depth=MAX_QUERY_DEPTH):
        Query = self.Query

        baseCase = Or(self.isTrivialQuery(q), Query.is_Cmp(q))
        if depth == 0:
            return baseCase
        else:
            rdepth = depth - 1
            return Or(
                baseCase,
                And(
                    self.queryWf(self.leftQuery(q), depth=rdepth),
                    self.queryWf(self.rightQuery(q), depth=rdepth),
                    Implies(Query.is_And(q), And(
                        Not(self.isTrivialQuery(Query.andLeft(q))),
                        Not(self.isTrivialQuery(Query.andRight(q))),
                        self.queryLe(Query.andLeft(q), Query.andRight(q)))),
                    Implies(Query.is_Or(q), And(
                        Not(self.isTrivialQuery(Query.orLeft(q))),
                        Not(self.isTrivialQuery(Query.orRight(q))),
                        self.queryLe(Query.orLeft(q), Query.orRight(q)))),
                    Implies(Query.is_Not(q),
                        Not(self.isTrivialQuery(Query.notQ(q))))))

    def isTrivialPlan(self, p):
        Plan = self.Plan

        return Or(p == Plan.All, p == Plan.None)

    def planWf(self, p, depth=MAX_PLAN_DEPTH):
        Plan = self.Plan

        if depth == 0:
            return self.isTrivialPlan(p)
        else:
            rdepth = depth-1
            return Or(self.isTrivialPlan(p), And(
                self.planWf(self.leftPlan(p), depth=rdepth),
                self.planWf(self.rightPlan(p), depth=rdepth),
                Implies(Plan.is_HashLookup(p),
                    Or(Plan.is_All(Plan.hashPlan(p)),
                       Plan.is_HashLookup(Plan.hashPlan(p)))),
                Implies(Plan.is_BinarySearch(p),
                    self.isSortedBy(Plan.bsPlan(p), Plan.bsField(p))),
                Implies(Plan.is_Filter(p), And(
                    self.queryWf(Plan.filterQuery(p), depth=rdepth),
                    Not(Plan.is_Filter(Plan.filterPlan(p))))),
                Implies(Plan.is_Intersect(p), And(
                    Not(self.isTrivialPlan(Plan.isectFirstPlan(p))),
                    Not(self.isTrivialPlan(Plan.isectSecondPlan(p))),
                    self.planLe(Plan.isectFirstPlan(p),
                                Plan.isectSecondPlan(p))
                    )),
                Implies(Plan.is_Union(p), And(
                    Not(self.isTrivialPlan(Plan.uFirstPlan(p))),
                    Not(self.isTrivialPlan(Plan.uSecondPlan(p))),
                    self.planLe(Plan.uFirstPlan(p), Plan.uSecondPlan(p))
                    )),
                ))

    def val_gt(self, a, b):
        Val = self.Val

        return And(
                Implies(a == Val.hi, Not(b == Val.hi)),
                Implies(a == Val.mid, b == Val.lo),
                Implies(a == Val.lo, False),
                )
    def cmpDenote(self, comp, a, b):
        Comparison = self.Comparison

        return And(
                Implies(comp == Comparison.Eq, a == b),
                Implies(comp == Comparison.Gt, self.val_gt(a, b)),
                Implies(comp == Comparison.Ge, Not(self.val_gt(b, a))),
                Implies(comp == Comparison.Lt, self.val_gt(b, a)),
                Implies(comp == Comparison.Le, Not(self.val_gt(a, b))),
                )

    def getField(self, f, vals):
        return doSymbolTableLookup(self.Field, f, vals)
    def getQueryVar(self, qv, vals):
        return doSymbolTableLookup(self.QueryVar, qv, vals)

    def queryDenote(self, q, fieldVals, queryVals, depth=MAX_QUERY_DEPTH):
        Query = self.Query

        default = False
        baseCase = iteCases(default,
                    (Query.is_TrueQuery(q), True),
                    (Query.is_FalseQuery(q), False),
                    (Query.is_Cmp(q),
                        self.cmpDenote(Query.cmpOp(q),
                                       self.getField(Query.cmpField(q),
                                                     fieldVals),
                                       self.getQueryVar(Query.cmpVar(q),
                                                        queryVals))),
                    )
        if depth == 0:
            return baseCase
        else:
            def recurseDenote(subQuery):
                return self.queryDenote(subQuery, fieldVals, queryVals,
                                        depth-1)
            leftDenote = recurseDenote(self.leftQuery(q))
            rightDenote = recurseDenote(self.rightQuery(q))
            return iteCases(baseCase,
                    (Query.is_And(q), And(leftDenote, rightDenote)),
                    (Query.is_Or(q), Or(leftDenote, rightDenote)),
                    (Query.is_Not(q), Not(leftDenote)),
                    )

    def planIncludes(self, p, fieldVals, queryVals, depth=MAX_PLAN_DEPTH):
        Plan = self.Plan

        baseCase = p == Plan.All
        if depth == 0:
            return baseCase
        else:
            def recurseIncludes(subPlan):
                return self.planIncludes(subPlan, fieldVals, queryVals,
                                         depth-1)
            def recurseDenote(subQuery):
                return self.queryDenote(subQuery, fieldVals, queryVals,
                                        depth-1)
            def getFieldVal(f):
                return self.getField(f, fieldVals)
            def getQueryVarVal(qv):
                return self.getQueryVar(qv, queryVals)
            leftIncludes = recurseIncludes(self.leftPlan(p))
            rightIncludes = recurseIncludes(self.rightPlan(p))
            return And(
                    Implies(Plan.is_None(p), False),
                    Implies(Plan.is_HashLookup(p),
                        And(leftIncludes,
                            getFieldVal(Plan.hashField(p))
                                == getQueryVarVal(Plan.hashVar(p))
                            )),
                    Implies(Plan.is_BinarySearch(p),
                        And(leftIncludes,
                            self.cmpDenote(Plan.bsOp(p),
                                getFieldVal(Plan.bsField(p)),
                                getQueryVarVal(Plan.bsVar(p)))
                            )),
                    Implies(Plan.is_Filter(p),
                        And(leftIncludes,
                            recurseDenote(Plan.filterQuery(p))
                            )),
                    Implies(Plan.is_Intersect(p),
                        And(leftIncludes, rightIncludes)),
                    Implies(Plan.is_Union(p),
                        Or(leftIncludes, rightIncludes))
                    )

    def implements(self, p, q):
        Val = self.Val

        fieldVals = Consts(self.fieldNames, Val)
        queryVarVals = Consts(self.varNames, Val)
        return ForAll(fieldVals + queryVarVals,
                self.queryDenote(q, fieldVals, queryVarVals)
                ==
                self.planIncludes(p, fieldVals, queryVarVals))

    def trees(self, p):
        """Generates all AST nodes in the given plan"""
        yield p
        if str(p.decl()) in ["HashLookup", "BinarySearch", "Filter"]:
            for n in self.trees(p.arg(0)): yield n
        elif str(p.decl()) in ["Intersect", "Union"]:
            for n in self.trees(p.arg(0)): yield n
            for n in self.trees(p.arg(1)): yield n

    def size(self, p):
        """Count how many AST nodes are in the given plan"""
        return len(list(self.trees(p)))

    def computeCost(self, p, n=COST_ITEM_COUNT):
        """Returns (cost,size) tuples"""
        if str(p.decl()) == "All":
            return 1, n
        elif str(p.decl()) == "None":
            return 1, 0
        elif str(p.decl()) == "HashLookup":
            cost1, size1 = self.computeCost(p.arg(0))
            return cost1 + 1, size1 / 2
        elif str(p.decl()) == "BinarySearch":
            cost1, size1 = self.computeCost(p.arg(0))
            return cost1 + (math.log(size1) if size1 >= 1 else 1), size1 / 2
        elif str(p.decl()) == "Filter":
            cost1, size1 = self.computeCost(p.arg(0))
            return cost1 + size1, size1 / 2
        elif str(p.decl()) == "Intersect":
            cost1, size1 = self.computeCost(p.arg(0))
            cost2, size2 = self.computeCost(p.arg(1))
            return cost1 + cost2 + size1 + size2, min(size1, size2) / 2
        elif str(p.decl()) == "Union":
            cost1, size1 = self.computeCost(p.arg(0))
            cost2, size2 = self.computeCost(p.arg(1))
            return cost1 + cost2 + size1 + size2, size1 + size2
        else:
            raise Exception("Couldn't parse plan: {}".format(p))

    def z3Cost_(self, p, N, depth):
        Plan = self.Plan
        CostResult = self.CostResult

        baseCase = iteCases(CostResult.CostRes(0, 0),
               (Plan.is_All(p), CostResult.CostRes(1, N)),
               (Plan.is_None(p), CostResult.CostRes(1, 0)))

        if depth == 0:
            return baseCase
        else:
            def costRecurse(p):
                return self.z3Cost_(p, N, depth-1)

            leftRes = costRecurse(self.leftPlan(p))
            rightRes = costRecurse(self.rightPlan(p))

            cases = []

            # hash lookup is O(1)
            cases.append((Plan.is_HashLookup(p),
                          CostResult.CostRes(1 + CostResult.cost(leftRes),
                                             CostResult.costN(leftRes)/2)))

            # TODO Estimate log(N), currently estimating (very poorly)
            #      with sqrt(N)
            cases.append((Plan.is_BinarySearch(p),
                          CostResult.CostRes((z3Log(CostResult.costN(leftRes)))
                                              + CostResult.cost(leftRes),
                                             CostResult.costN(leftRes)/2)))

            # filter is O(N)
            cases.append((Plan.is_Filter(p),
                          CostResult.CostRes(CostResult.costN(leftRes)
                                              + CostResult.cost(leftRes),
                                             CostResult.costN(leftRes)/2)))

            isectTime = (CostResult.costN(leftRes) + CostResult.cost(leftRes)
                    + CostResult.costN(rightRes) + CostResult.cost(rightRes))
            isectN = Min(CostResult.costN(leftRes),
                         CostResult.costN(rightRes)) / 2
            cases.append((Plan.is_Intersect(p),
                          CostResult.CostRes(isectTime, isectN)))

            uTime = (CostResult.costN(leftRes) + CostResult.cost(leftRes)
                    + CostResult.costN(rightRes) + CostResult.cost(rightRes))
            uN = CostResult.costN(leftRes) + CostResult.costN(rightRes)
            cases.append((Plan.is_Union(p),
                          CostResult.CostRes(uTime, uN)))

            return iteCases(baseCase, *cases)

    def z3Cost(self, p, N=COST_ITEM_COUNT, depth=MAX_PLAN_DEPTH):
        res = self.CostResult.cost(self.z3Cost_(p, N, depth))
        return res

    def smallestBadSubtree(self, p, maxCost):
        """
        Returns the smallest subtree of the given plan whose cost is
        at least maxCost, or None if no such element exists.
        """
        candidates = sorted(
            [t for t in self.trees(p) if self.computeCost(t)[0] >= maxCost],
            key=lambda c: self.size(c))
        if candidates:
            return candidates[0]

    def treeMatch(self, p, pattern):
        """
        Determines if the node types of p match the node types of the pattern.
        """
        Plan = self.Plan
        if str(pattern.decl()) == "All":
            return Plan.is_All(p)
        elif str(pattern.decl()) == "None":
            return Plan.is_None(p)
        elif str(pattern.decl()) == "HashLookup":
            return And(
                Plan.is_HashLookup(p),
                self.treeMatch(Plan.hashPlan(p), pattern.arg(0)))
        elif str(pattern.decl()) == "BinarySearch":
            return And(
                Plan.is_BinarySearch(p),
                self.treeMatch(Plan.bsPlan(p), pattern.arg(0)))
        elif str(pattern.decl()) == "Filter":
            return And(
                Plan.is_Filter(p),
                self.treeMatch(Plan.filterPlan(p), pattern.arg(0)))
        elif str(pattern.decl()) == "Intersect":
            return And(
                Plan.is_Intersect(p),
                self.treeMatch(Plan.isectFirstPlan(p), pattern.arg(0)),
                self.treeMatch(Plan.isectSecondPlan(p), pattern.arg(1)))
        elif str(pattern.decl()) == "Union":
            return And(
                Plan.is_Union(p),
                self.treeMatch(Plan.uFirstPlan(p), pattern.arg(0)),
                self.treeMatch(Plan.uSecondPlan(p), pattern.arg(1)))
        else:
            raise Exception("Couldn't parse plan pattern: {}".format(p))

    def forallNodes(self, p, predicate, depth=MAX_PLAN_DEPTH):
        Plan = self.Plan
        if depth == 0:
            return predicate(p)
        else:
            rdepth = depth - 1
            leftBranch = self.forallNodes(self.leftPlan(p), predicate, rdepth)
            rightBranch = self.forallNodes(self.rightPlan(p), predicate, rdepth)
            return And(
                predicate(p),
                Implies(Plan.is_HashLookup(p),   leftBranch),
                Implies(Plan.is_BinarySearch(p), leftBranch),
                Implies(Plan.is_Filter(p),       leftBranch),
                Implies(Plan.is_Intersect(p),    And(leftBranch, rightBranch)),
                Implies(Plan.is_Union(p),        And(leftBranch, rightBranch)))

    def synthesizePlans(self, query):
        Plan = self.Plan
        Query = self.Query
        Val = self.Val
        Field = self.Field

        s = SolverFor("UF")

        plan = Const('plan', Plan)
        s.add(self.planWf(plan))
        s.add(self.implements(plan, query))
        res = []
        bestCost = None
        bestPlan = None

        def eliminate_pattern(pat):
            print "Eliminating: ", pat
            s.add(self.forallNodes(plan, lambda n: Not(self.treeMatch(n, pat))))

        while(str(s.check()) == 'sat'):
            model = s.model()
            modelPlan = model[plan]
            res.append(modelPlan)
            print modelPlan

            cost = self.computeCost(modelPlan)[0]
            print "Cost: ", cost
            z3Cost = model.evaluate(self.z3Cost(modelPlan))
            print "z3 Cost: ", z3Cost
            if bestCost is None or cost < bestCost:
                bestCost = cost
                bestPlan = modelPlan

            s.add(self.z3Cost(plan) < z3Cost)

            elim = self.smallestBadSubtree(modelPlan, bestCost)
            eliminate_pattern(elim)
            print "="*60

        print "Best plan found: {}; cost={}".format(bestPlan, bestCost)
        return res

    def synthesizePlansByEnumeration(self, query, maxSize=1000):
        examples = []
        while True:
            print "starting synthesis using", len(examples), "examples"
            for responseType, response in self._synthesizePlansByEnumeration(query, maxSize, examples):
                if responseType == "counterexample":
                    print "found counterexample", response
                    if response in examples:
                        raise Exception("error: already saw counterexample!")
                    examples.append(response)
                    break
                elif responseType == "validPlan":
                    yield response

    def _synthesizePlansByEnumeration(self, query, maxSize, examples):
        Plan = self.Plan
        Query = self.Query
        Val = self.Val
        Field = self.Field
        QueryVar = self.QueryVar
        Comparison = self.Comparison

        def constructors(datatype):
            l = (datatype.constructor(i) for i in xrange(datatype.num_constructors()))
            return [(x if x.arity() > 0 else x()) for x in l]

        def outputvector(p):
            return tuple([planEval(p, *e) for e in examples])

        def comparisons(q):
            """returns (field,queryvar) tuples for a query"""
            m = defaultdict(list)
            if str(q.decl()) == "TrueQuery":
                return set()
            if str(q.decl()) == "FalseQuery":
                return set()
            if str(q.decl()) == "Cmp":
                return set([(str(q.arg(0).decl()), str(q.arg(2).decl()))])
            if str(q.decl()) == "And":
                return comparisons(q.arg(0)) | comparisons(q.arg(1))
            if str(q.decl()) == "Or":
                return comparisons(q.arg(0)) | comparisons(q.arg(1))
            if str(q.decl()) == "Not":
                return comparisons(q.arg(0))
            else:
                raise Exception("Couldn't parse query: {}".format(q))

        def markIllegal(pattern):
            illegal.append(pattern)
            for k, p in list(cache.items()):
                if match(p, pattern):
                    del cache[k]

        def match(plan, pattern):
            if str(plan.decl()) == str(pattern.decl()):
                if str(plan.decl()) in ["HashLookup", "BinarySearch", "Filter"]:
                    return match(plan.arg(0), pattern.arg(0))
                elif str(plan.decl()) in ["Intersect", "Union"]:
                    return (
                        match(plan.arg(0), pattern.arg(0)) and
                        match(plan.arg(1), pattern.arg(1)))
                else:
                    return True
            else:
                return False

        def cmpDenote(comp, a, b):
            return And(
                Implies(comp == Comparison.Eq, a == b),
                Implies(comp == Comparison.Gt, a > b),
                Implies(comp == Comparison.Ge, a >= b),
                Implies(comp == Comparison.Lt, a < b),
                Implies(comp == Comparison.Le, a <= b))

        def planDenote(p, fieldVals, queryVals):
            if str(p.decl()) == "All":
                return True
            elif str(p.decl()) == "None":
                return False
            elif str(p.decl()) == "HashLookup":
                return And(
                    planDenote(p.arg(0), fieldVals, queryVals),
                    self.getField(Plan.hashField(p), fieldVals) == self.getQueryVar(Plan.hashVar(p), queryVals))
            elif str(p.decl()) == "BinarySearch":
                return And(
                    planDenote(p.arg(0), fieldVals, queryVals),
                    cmpDenote(Plan.bsOp(p), self.getField(Plan.bsField(p), fieldVals), self.getQueryVar(Plan.bsVar(p), queryVals)))
            elif str(p.decl()) == "Filter":
                return And(
                    planDenote(p.arg(0), fieldVals, queryVals),
                    queryDenote(p.arg(1), fieldVals, queryVals))
            elif str(p.decl()) == "Intersect":
                return And(
                    planDenote(p.arg(0), fieldVals, queryVals),
                    planDenote(p.arg(1), fieldVals, queryVals))
            elif str(p.decl()) == "Union":
                return Or(
                    planDenote(p.arg(0), fieldVals, queryVals),
                    planDenote(p.arg(1), fieldVals, queryVals))
            else:
                raise Exception("Couldn't parse plan: {}".format(p))

        def cmpEval(op, f, v, fieldVals, queryVals):
            if   op == "Eq": return fieldVals[self.fieldNames.index(f)] == queryVals[self.varNames.index(v)]
            elif op == "Gt": return fieldVals[self.fieldNames.index(f)] >  queryVals[self.varNames.index(v)]
            elif op == "Ge": return fieldVals[self.fieldNames.index(f)] >= queryVals[self.varNames.index(v)]
            elif op == "Lt": return fieldVals[self.fieldNames.index(f)] <  queryVals[self.varNames.index(v)]
            elif op == "Le": return fieldVals[self.fieldNames.index(f)] <= queryVals[self.varNames.index(v)]
            else: raise Exception("unknown comparison {}".format(op))

        def queryEval(q, fieldVals, queryVals):
            if str(q.decl()) == "TrueQuery":
                return True
            if str(q.decl()) == "FalseQuery":
                return False
            if str(q.decl()) == "Cmp":
                return cmpEval(str(q.arg(1)), str(q.arg(0)), str(q.arg(2)), fieldVals, queryVals)
            if str(q.decl()) == "And":
                return queryEval(q.arg(0), fieldVals, queryVals) and queryEval(q.arg(1), fieldVals, queryVals)
            if str(q.decl()) == "Or":
                return queryEval(q.arg(0), fieldVals, queryVals) or queryEval(q.arg(1), fieldVals, queryVals)
            if str(q.decl()) == "Not":
                return not queryEval(q.arg(0), fieldVals, queryVals)
            else:
                raise Exception("Couldn't parse query: {}".format(q))

        def planEval(p, fieldVals, queryVals):
            if str(p.decl()) == "All":
                return True
            elif str(p.decl()) == "None":
                return False
            elif str(p.decl()) == "HashLookup":
                return (
                    cmpEval("Eq", str(p.arg(1)), str(p.arg(2)), fieldVals, queryVals) and
                    planEval(p.arg(0), fieldVals, queryVals))
            elif str(p.decl()) == "BinarySearch":
                return (
                    cmpEval(str(p.arg(2)), str(p.arg(1)), str(p.arg(3)), fieldVals, queryVals) and
                    planEval(p.arg(0), fieldVals, queryVals))
            elif str(p.decl()) == "Filter":
                return (
                    queryEval(p.arg(1), fieldVals, queryVals) and
                    planEval(p.arg(0), fieldVals, queryVals))
            elif str(p.decl()) == "Intersect":
                return (
                    planEval(p.arg(0), fieldVals, queryVals) and
                    planEval(p.arg(1), fieldVals, queryVals))
            elif str(p.decl()) == "Union":
                return (
                    planEval(p.arg(0), fieldVals, queryVals) or
                    planEval(p.arg(1), fieldVals, queryVals))
            else:
                raise Exception("Couldn't parse plan: {}".format(p))

        def queryDenote(q, fieldVals, queryVals):
            if str(q.decl()) == "TrueQuery":
                return True
            if str(q.decl()) == "FalseQuery":
                return False
            if str(q.decl()) == "Cmp":
                return cmpDenote(Query.cmpOp(q), self.getField(Query.cmpField(q), fieldVals), self.getQueryVar(Query.cmpVar(q), queryVals))
            if str(q.decl()) == "And":
                return And(queryDenote(q.arg(0), fieldVals, queryVals), queryDenote(q.arg(1), fieldVals, queryVals))
            if str(q.decl()) == "Or":
                return Or(queryDenote(q.arg(0), fieldVals, queryVals), queryDenote(q.arg(1), fieldVals, queryVals))
            if str(q.decl()) == "Not":
                return Not(queryDenote(q.arg(0), fieldVals, queryVals))
            else:
                raise Exception("Couldn't parse query: {}".format(q))

        def isValid(plan):
            """returns True, False, or a new counterexample"""
            if outputvector(plan) != queryVector:
                return False

            result = False
            s.push()
            fieldVals = Consts(self.fieldNames, IntSort())
            queryVals = Consts(self.varNames, IntSort())
            s.add(planDenote(plan, fieldVals, queryVals) != queryDenote(query, fieldVals, queryVals))
            if str(s.check()) == 'unsat':
                result = True
            else:
                m = s.model()
                result = (
                    [int(str(m[f])) for f in fieldVals],
                    [int(str(m[v])) for v in queryVals])
            s.pop()
            return result

        def isSortedBy(p, f):
            if str(p.decl()) == "All" or str(p.decl()) == "HashLookup":
                return True
            if str(p.decl()) == "BinarySearch":
                return str(p.arg(1)) == str(f)
            return False

        def planCmp(p1, p2):
            if str(p1.decl()) < str(p2.decl()):
                return -1
            if str(p1.decl()) > str(p2.decl()):
                return 1
            if str(p1.decl()) not in ["All", "None"]:
                x = planCmp(p1.arg(0), p2.arg(0))
                if x != 0:
                    return x
            if str(p1.decl()) in ["Intersect", "Union"]:
                x = planCmp(p1.arg(1), p2.arg(1))
                if x != 0:
                    return x
            return 0

        def wf(p):
            if str(p.decl()) in ["All", "None"]:
                return True
            elif str(p.decl()) == "HashLookup":
                return (str(p.arg(1).decl()), str(p.arg(2).decl())) in comps and wf(p.arg(0)) and (
                    str(p.arg(0).decl()) == "HashLookup" or
                    str(p.arg(0).decl()) == "All")
            elif str(p.decl()) == "BinarySearch":
                return (str(p.arg(1).decl()), str(p.arg(3).decl())) in comps and wf(p.arg(0)) and isSortedBy(p.arg(0), p.arg(1))
            elif str(p.decl()) == "Filter":
                return wf(p.arg(0))
            elif str(p.decl()) in ["Intersect", "Union"]:
                return (planCmp(p.arg(0), p.arg(1)) < 0) and all(wf(p.arg(i)) and (str(p.arg(i).decl()) != "All") and (str(p.arg(i).decl()) != "None") for i in [0, 1])
            else:
                raise Exception("Couldn't parse plan: {}".format(p))

        def consider(plan, size):
            if not wf(plan):
                return None, None
            if any(match(plan, p) for p in illegal):
                return None, None
            cost = self.computeCost(plan)[0]
            vec = outputvector(plan)
            x = isValid(plan)
            if x is True:
                if bestCost[0] is None or cost < bestCost[0]:
                    bestPlan[0] = plan
                    bestCost[0] = cost
                    result = True
                subtree = self.smallestBadSubtree(plan, bestCost[0])
                if subtree:
                    markIllegal(subtree)
                return "validPlan", plan
            elif x is False:
                if vec not in cache or self.computeCost(cache[vec]) < cost:
                    cache[vec] = plan
                return None, None
            else:
                # x is new example!
                return "counterexample", x

        s = SolverFor("QF_LIA")

        queryVector = tuple([queryEval(query, *e) for e in examples])

        # cache maps output vectors to the best known plan implementing them
        cache = {}
        illegal = [] # contains all plan patterns forbidden thus far

        # these are lists so that the closures below can modify their values
        bestPlan = [None] # best plan found so far
        bestCost = [None] # cost of bestPlan

        comps = comparisons(query)

        print "round 1"
        for plan in [Plan.All, Plan.None]:
            yield consider(plan, 1)

        for size in xrange(2, maxSize + 1):
            print "round", size
            smallerPlans = list(cache.values())
            for plan in (Plan.HashLookup(p, f, v) for p in smallerPlans for f in constructors(Field) for v in constructors(QueryVar)):
                yield consider(plan, size)
            for plan in (Plan.BinarySearch(p, f, op, v) for p in smallerPlans for f in constructors(Field) for v in constructors(QueryVar) for op in constructors(Comparison)):
                yield consider(plan, size)
            # TODO: more elaborate filters
            for plan in (Plan.Filter(p, Query.Cmp(f, op, v)) for p in smallerPlans for f in constructors(Field) for v in constructors(QueryVar) for op in constructors(Comparison)):
                yield consider(plan, size)
            for plan in (ty(p1, p2) for ty in [Plan.Intersect, Plan.Union] for p1 in smallerPlans for p2 in smallerPlans):
                yield consider(plan, size)

if __name__ == "__main__":

    sc = SolverContext(varNames = ['x', 'y'], fieldNames = ['Age', 'Name'])
    q = sc.Query.And(
        sc.Query.Cmp(sc.Field.Age, sc.Comparison.Gt, sc.QueryVar.x),
        sc.Query.Cmp(sc.Field.Name, sc.Comparison.Eq, sc.QueryVar.y)
        )

    #### This line asks Z3 to straight-up find us an answer
    # sc.synthesizePlans(q)

    #### This uses enumeration
    for p in sc.synthesizePlansByEnumeration(q, 1000000):
        print p
        print "Cost =", sc.computeCost(p)
        print "="*60
