#!/usr/bin/env python2

import math
from z3 import *

MAX_PLAN_DEPTH = 2
MAX_QUERY_DEPTH = 2

# TODO Is it possible (easy) to make an @z3Typed(Int, Int, Bool) annotation
#       that will convert a Python function to z3? Recursion would be tricky
#       ... maybe be slightly ugly... or use a type overriding callable?

def iteCases(default, *caseList):
    res = default
    for (test, val) in caseList:
        res = If(test, val, res)
    return res
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

def Min(a, b):
    return If(a < b, a, b)

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
            ('CostRes', [('cost', IntSort()),
                         ('costN', IntSort())])
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

    def computeCost(self, p, n=100000.0):
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
            if bestCost is None or cost < bestCost:
                bestCost = cost
                bestPlan = modelPlan

            elim = self.smallestBadSubtree(modelPlan, bestCost)
            eliminate_pattern(elim)
            print "="*60

        print "Best plan found: {}; cost={}".format(bestPlan, bestCost)
        return res

sc = SolverContext(varNames = ['x', 'y'], fieldNames = ['Age', 'Name'])
sc.synthesizePlans(sc.Query.And(
    sc.Query.Cmp(sc.Field.Age, sc.Comparison.Gt, sc.QueryVar.x),
    sc.Query.Cmp(sc.Field.Name, sc.Comparison.Eq, sc.QueryVar.y)
    ))
