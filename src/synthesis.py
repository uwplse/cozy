#!/usr/bin/env python2

import datetime
import math
import random
import sys
from collections import defaultdict
from z3 import *

COST_ITEM_COUNT = 1000

def doSymbolTableLookup(Type, variable, vals):
    res = vals[0]
    for idx in range(1, Type.num_constructors()):
        res = If(Type.recognizer(idx)(variable), vals[idx], res)
    return res

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

        self.comparisonOperators = ['Eq', 'Gt', 'Ge', 'Lt', 'Le']
        self.Comparison = self.declareSimpleDatatype('Comparison',
                                                     self.comparisonOperators)
        Comparison = self.Comparison

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

    def getField(self, f, vals):
        return doSymbolTableLookup(self.Field, f, vals)
    def getQueryVar(self, qv, vals):
        return doSymbolTableLookup(self.QueryVar, qv, vals)

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

    def synthesizePlansByEnumeration(self, query, maxSize=1000):
        examples = []
        while True:
            #print "starting synthesis using", len(examples), "examples"
            for responseType, response in self._synthesizePlansByEnumeration(query, maxSize, examples):
                if responseType == "counterexample":
                    #print "found counterexample", response
                    if response in examples:
                        raise Exception("error: already saw counterexample!")
                    examples.append(response)
                    break
                elif responseType == "validPlan":
                    yield response
                elif responseType == "stop":
                    return

    def _synthesizePlansByEnumeration(self, query, maxSize, examples):
        Plan = self.Plan
        Query = self.Query
        Field = self.Field
        QueryVar = self.QueryVar
        Comparison = self.Comparison

        def constructors(datatype):
            l = (datatype.constructor(i) for i in xrange(datatype.num_constructors()))
            return [(x if x.arity() > 0 else x()) for x in l]

        def outputvector(p):
            return tuple([planEval(p, *e) for e in examples])

        def toNNF(q):
            """Converts a query q to negation normal form
                (i.e. no use of "not"). If negate is true, then act like
                there is a Not() wrapped around the query."""
            if str(q.decl()) == "Not":
                if str(q.decl()) == "TrueQuery":
                    return Query.FalseQuery()
                if str(q.decl()) == "FalseQuery":
                    return Query.TrueQuery()
                if str(q.decl()) == "Cmp":
                    if str(q.arg(1)) == 'Eq':
                        return q
                    else:
                        reverses = { 'Gt': Comparison.Le(),
                                     'Le': Comparison.Gt(),
                                     'Lt': Comparison.Ge(),
                                     'Ge': Comparison.Lt() }
                        opposite = reverses[str(q.arg(1))]
                        return Query.Cmp(q.arg(0), opposite, q.arg(2))
                if str(q.decl()) == "And":
                    return Query.Or(toNNF(Query.Not(q.arg(0))),
                                    toNNF(Query.Not(q.arg(1))))
                if str(q.decl()) == "Or":
                    return Query.And(toNNF(Query.Not(q.arg(0))),
                                     toNNF(Query.Not(q.arg(1))))
                if str(q.decl()) == "Not":
                    return q.arg(0)
                else:
                    raise Exception("Couldn't parse query: {}".format(q))
            elif str(q.decl()) == "And":
                return Query.And(toNNF(Query.Not(q.arg(0))),
                                 toNNF(Query.Not(q.arg(1))))
            elif str(q.decl()) == "Or":
                return Query.Or(toNNF(Query.Not(q.arg(0))),
                                toNNF(Query.Not(q.arg(1))))
            elif str(q.decl()) == "TrueQuery":
                return q
            elif str(q.decl()) == "FalseQuery":
                return q
            elif str(q.decl()) == "Cmp":
                return q
            else:
                raise Exception("Couldn't parse query: {}".format(q))

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

        def comparisonsNNF(q):
            """returns (field,cmp,queryvar) tuples for a query"""
            m = defaultdict(list)
            if str(q.decl()) == "TrueQuery":
                return set()
            if str(q.decl()) == "FalseQuery":
                return set()
            if str(q.decl()) == "Cmp":
                return set([(str(q.arg(0).decl()), str(q.arg(1)),
                             str(q.arg(2).decl()))])
            if str(q.decl()) == "And":
                return comparisonsNNF(q.arg(0)) | comparisonsNNF(q.arg(1))
            if str(q.decl()) == "Or":
                return comparisonsNNF(q.arg(0)) | comparisonsNNF(q.arg(1))
            if str(q.decl()) == "Not":
                # The only way to have Not is for !=, in which case, give up
                #   and allow all operators.
                if str(q.arg(0).decl()) == "Cmp" and\
                   str(q.arg(0).arg(1)) == 'Eq':
                    return set([(str(q.arg(0).arg(0).decl()),
                                 c,
                                 str(q.arg(0).arg(2).decl()))
                                for c in self.comparisonOperators])
                else:
                    raise Exception("Query not in NNF: {}".format(q))
            else:
                raise Exception("Couldn't parse query: {}".format(q))

        def match_one(plan, pattern):
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

        def match(plan, pattern):
            if match_one(plan, pattern):
                return True
            elif str(plan.decl()) in ["HashLookup", "BinarySearch", "Filter"]:
                return match(plan.arg(0), pattern)
            elif str(plan.decl()) in ["Intersect", "Union"]:
                return match(plan.arg(0), pattern) or match(plan.arg(1), pattern)
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
                    [int(str(m[f] or 0)) for f in fieldVals],
                    [int(str(m[v] or 0)) for v in queryVals])
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
                return (str(p.arg(1).decl()), 'Eq', str(p.arg(2).decl())) in comps and wf(p.arg(0)) and (
                    str(p.arg(0).decl()) == "HashLookup" or
                    str(p.arg(0).decl()) == "All")
            elif str(p.decl()) == "BinarySearch":
                return (str(p.arg(1).decl()), str(p.arg(2).decl()), str(p.arg(3).decl())) in comps and wf(p.arg(0)) and isSortedBy(p.arg(0), p.arg(1))
            elif str(p.decl()) == "Filter":
                return wf(p.arg(0))
            elif str(p.decl()) in ["Intersect", "Union"]:
                return (planCmp(p.arg(0), p.arg(1)) <= 0) and all(wf(p.arg(i)) and (str(p.arg(i).decl()) != "All") and (str(p.arg(i).decl()) != "None") for i in [0, 1])
            else:
                raise Exception("Couldn't parse plan: {}".format(p))

        def consider(plan, size):
            if not wf(plan):
                return None, None
            cost = self.computeCost(plan)[0]
            if bestCost[0] is not None and cost >= bestCost[0]:
                # oops! this can't possibly be part of a better plan
                return None, None
            vec = outputvector(plan)
            x = isValid(plan)
            if x is True:
                if bestCost[0] is None or cost < bestCost[0]:
                    productive[0] = True
                    bestPlan[0] = plan
                    bestCost[0] = cost
                    result = True
                return "validPlan", plan
            elif x is False:
                if vec not in cache or self.computeCost(cache[vec]) < cost:
                    productive[0] = True
                    cache[vec] = plan
                return None, None
            else:
                # x is new example!
                productive[0] = True
                return "counterexample", x

        query = toNNF(query)

        s = SolverFor("QF_LIA")

        queryVector = tuple([queryEval(query, *e) for e in examples])

        # cache maps output vectors to the best known plan implementing them
        cache = {}

        # the stupidest possible plan: linear search
        dumbestPlan = Plan.Filter(Plan.All, query)

        # these are lists so that the closures can modify their values
        # (grumble grumble "nonlocal" keyword missing grumble)
        bestPlan = [dumbestPlan] # best plan found so far
        bestCost = [self.computeCost(dumbestPlan)[0]] # cost of bestPlan
        yield "validPlan", dumbestPlan
        productive = [False]

        comps = comparisonsNNF(query)
        z3comps = [(getattr(Field, f),
                    getattr(Comparison, op),
                    getattr(QueryVar, v))
                   for (f, op, v) in comps]

        #print "round 1"
        for plan in [Plan.All, Plan.None]:
            yield consider(plan, 1)

        for size in xrange(2, maxSize + 1):
            productive[0] = False
            #print "round", size
            smallerPlans = list(cache.values())
            for plan in (Plan.HashLookup(p, f, v) for p in smallerPlans for f in constructors(Field) for v in constructors(QueryVar)):
                yield consider(plan, size)
            for plan in (Plan.BinarySearch(p, f, op, v) for p in smallerPlans for (f, op, v) in z3comps):
                yield consider(plan, size)
            # TODO: more elaborate filters
            for plan in (Plan.Filter(p, Query.Cmp(f, op, v)) for p in smallerPlans for (f, op, v) in z3comps):
                yield consider(plan, size)
            for plan in (ty(p1, p2) for ty in [Plan.Intersect, Plan.Union] for p1 in smallerPlans for p2 in smallerPlans):
                yield consider(plan, size)
            if not productive[0]:
                print "last round was not productive; stopping"
                yield "stop", None


    def generateJava(self, p, queryVarTypes, public=True, queryType=None,
                     recordType="Record", className="DataStructure"):
        # constructEmpty() is separate because it might need a custom
        #   comparator.
        skeleton = """%(public)sclass %(className)s {
%(fields)s

    public %(lookupType)s lookup(%(lookupParams)s) {
        %(lookupType)s res = lookup_(%(lookupArgs)s);
        if(res == null) {
            return constructEmpty();
        } else {
            return res;
        }
    }

    public %(lookupType)s getDataStructure(%(recordType)s el, boolean add) {
%(getDSBody)s
    }

    private %(lookupType)s lookup_(%(lookupParams)s) {
%(lookupBody)s
    }
%(combine)s
    private %(lookupType)s constructEmpty() {
        return new %(lookupType)s();
    }
%(addremove)s%(otherClasses)s}
"""
        if queryType is None:
            queryType = "TreeSet<Record>"
        formatStrs = {'recordType': recordType, 'className': className,
                      'lookupType': queryType,
                      'lookupArgs': ', '.join(self.varNames),
                      'lookupParams': ', '.join(["%s %s" % (t, name)
                                                 for (t, name)
                                                 in zip(queryVarTypes,
                                                        self.varNames)]),
                      'public': """import java.util.*;

public """ if public else '',
                      'addremove': '',
                      'otherClasses': '',
                      'cmp': '',
                      'combine': '',
                      }
        queryVarTypeDict = dict(zip(self.varNames, queryVarTypes))
        if str(p.decl()) == "Intersect" or str(p.decl()) == "Union":
            formatStrs['addremove'] = """
    public boolean add(%(recordType)s el) {
        return left.add(el) | right.add(el);
    }

    public boolean remove(%(recordType)s el) {
        return left.remove(el) | right.remove(el);
    }
""" % { 'recordType': formatStrs['recordType'], }
        elif queryType == "TreeSet<Record>":
            formatStrs['addremove'] = """
    public boolean add(%(recordType)s el) {
%(addBody)s
    }

    public boolean remove(%(recordType)s el) {
%(removeBody)s
    }
""" % {
                    'addBody': """\t\treturn getDataStructure(el, true).add(el);""",
                    'removeBody': """\t\t%s ds = getDataStructure(el, false);
\t\tif(ds == null) {
\t\t\treturn false;
\t\t}
\t\treturn ds.remove(el);""" % queryType,
                    'recordType': formatStrs['recordType'],
                }
            formatStrs['combine'] = """    private %(lookupType)s combine(Collection<%(lookupType)s> collections) {
        %(lookupType)s res = constructEmpty();
        for(%(lookupType)s c : collections) {
            res.addAll(c);
        }
        return res;
    }""" % formatStrs

        if str(p.decl()) == "All":
            formatStrs['fields'] = "\tprivate %(dataName)s data = new %(dataName)s();" % {'dataName': queryType}
            formatStrs['lookupBody'] = "\t\treturn data;"
            formatStrs['getDSBody'] = "\t\treturn data;"
            #return True
        elif str(p.decl()) == "None":
            # Uh, what does this mean? Shouldn't get here.
            formatStrs['fields'] = "\tprivate %(dataName)s data = new %(dataName)s();" % {'dataName': queryType}
            formatStrs['lookupBody'] = "\t\treturn data;"
            formatStrs['getDSBody'] = "\t\treturn data;"
            #return False
        elif str(p.decl()) == "HashLookup":
            subplan = p.arg(0)
            keyType = queryVarTypeDict[str(p.arg(2))]
            subQueryType = "HashMap<%(key)s, %(value)s>" \
                    % {'key': keyType, 'value': queryType}
            subplanClassName = '%s_%s' % (className, 'hash')
            subplanCode = self.generateJava(subplan, queryVarTypes,
                                            public=False,
                                            queryType=subQueryType,
                                            recordType=recordType,
                                            className=subplanClassName)
            formatStrs['otherClasses'] = '\n\n' + subplanCode
            formatStrs['fields'] = "\tprivate %(spName)s data = new %(spName)s();" % {'spName': subplanClassName}
            formatStrs['lookupBody'] = """\t\treturn data.lookup(%(queryVars)s).get(%(queryVar)s);""" % {'queryVars': ', '.join(self.varNames), 'queryVar': str(p.arg(2))}
            formatStrs['getDSBody'] = """\t\t%(subQueryType)s subres = data.getDataStructure(el, add);
\t\tif(subres == null) {
\t\t\treturn null;
\t\t}
\t\t%(lookupType)s res = subres.get(el.get%(fieldName)s());
\t\tif(res == null && add) {
\t\t\tres = constructEmpty();
\t\t\tsubres.put(el.get%(fieldName)s(), res);
\t\t}
\t\treturn res;""" % {'queryVars': ', '.join(self.varNames),
                      'fieldName': str(p.arg(1)),
                      'subQueryType': subQueryType,
                      'lookupType': formatStrs['lookupType']}
        elif str(p.decl()) == "BinarySearch":
            subplan = p.arg(0)
            keyType = queryVarTypeDict[str(p.arg(3))]
            subQueryType = "TreeMap<%(key)s, %(value)s>" \
                    % {'key': keyType, 'value': queryType}
            subplanClassName = '%s_%s' % (className, 'bs')
            subplanCode = self.generateJava(subplan, queryVarTypes,
                                            public=False,
                                            queryType=subQueryType,
                                            recordType=recordType,
                                            className=subplanClassName)
            formatStrs['otherClasses'] = '\n\n' + subplanCode
            formatStrs['fields'] = "\tprivate %(spName)s data = new %(spName)s();" % {'spName': subplanClassName}
            if str(p.arg(2)) == 'Eq':
                formatStrs['lookupBody'] = """\t\treturn data.lookup(%(queryVars)s).get(%(queryVar)s);""" % {'queryVars': ', '.join(self.varNames), 'queryVar': str(p.arg(3))}
            elif str(p.arg(2)) == 'Lt' or str(p.arg(2)) == 'Le':
                formatStrs['lookupBody'] = """\t\treturn combine(data.lookup(%(queryVars)s).headMap(%(queryVar)s, %(inclusive)s).values());""" % {'queryVars': ', '.join(self.varNames), 'queryVar': str(p.arg(3)), 'inclusive': 'true' if str(p.arg(2)) == 'Le' else 'false'}
            elif str(p.arg(2)) == 'Gt' or str(p.arg(2)) == 'Ge':
                formatStrs['lookupBody'] = """\t\treturn combine(data.lookup(%(queryVars)s).tailMap(%(queryVar)s, %(inclusive)s).values());""" % {'queryVars': ', '.join(self.varNames), 'queryVar': str(p.arg(3)), 'inclusive': 'true' if str(p.arg(2)) == 'Ge' else 'false'}
            formatStrs['getDSBody'] = """\t\t%(subQueryType)s subres = data.getDataStructure(el, add);
\t\tif(subres == null) {
\t\t\treturn null;
\t\t}
\t\t%(lookupType)s res = subres.get(el.get%(fieldName)s());
\t\tif(res == null && add) {
\t\t\tres = constructEmpty();
\t\t\tsubres.put(el.get%(fieldName)s(), res);
\t\t}
\t\treturn res;""" % {'queryVars': ', '.join(self.varNames),
                      'fieldName': str(p.arg(1)),
                      'subQueryType': subQueryType,
                      'lookupType': formatStrs['lookupType']}
        elif str(p.decl()) == "Filter":
            subplan = p.arg(0)
            # TODO query type better be TreeSet<recordType>...
            subQueryType = "TreeSet<%(recordType)s>" \
                    % {'recordType': recordType}
            subplanClassName = '%s_%s' % (className, 'filter')
            subplanCode = self.generateJava(subplan, queryVarTypes,
                                            public=False,
                                            queryType=subQueryType,
                                            recordType=recordType,
                                            className=subplanClassName)
            formatStrs['otherClasses'] = '\n\n' + subplanCode
            formatStrs['fields'] = "\tprivate %(spName)s data = new %(spName)s();" % {'spName': subplanClassName}
            formatStrs['getDSBody'] = """\t\treturn data.getDataStructure(el, add);"""
            def queryToJava(q):
                if str(q.decl()) == "TrueQuery":
                    return 'true'
                elif str(q.decl()) == "FalseQuery":
                    return 'false'
                elif str(q.decl()) == "Cmp":
                    opLookup = { 'Eq': '==', 'Gt': '>', 'Ge': '>=',
                                 'Lt': '<', 'Le': '<=' }
                    op = opLookup[str(q.arg(1))]
                    if queryVarTypeDict[str(q.arg(2))] == 'Integer':
                        return 'el.get%s() %s %s' % (q.arg(0), op, q.arg(2))
                    else:
                        return 'el.get%s().compareTo(%s) %s 0' % (q.arg(0), q.arg(2), op)
                elif str(q.decl()) == "And":
                    return '(%s && %s)' % (queryToJava(q.arg(0)),
                                           queryToJava(q.arg(1)))
                elif str(q.decl()) == "Or":
                    return '(%s || %s)' % (queryToJava(q.arg(0)),
                                           queryToJava(q.arg(1)))
                elif str(q.decl()) == "Not":
                    return '!%s' % queryToJava(q.arg(0))
                else:
                    raise Exception("Couldn't parse query: {}".format(q))
            formatStrs['lookupBody'] = """\t\t%(lookupType)s res = constructEmpty();
        for(%(recordType)s el : data.lookup(%(queryVars)s)) {
            if(%(query)s) {
                res.add(el);
            }
        }
        return res;""" % {
                'lookupType': formatStrs['lookupType'],
                'recordType': recordType,
                'queryVars': ', '.join(self.varNames),
                'query': queryToJava(p.arg(1))
                }
        elif str(p.decl()) == "Intersect" or str(p.decl()) == "Union":
            left = p.arg(0)
            right = p.arg(1)
            # TODO query type better be TreeSet<recordType>...
            subQueryType = "TreeSet<%(recordType)s>" \
                    % {'recordType': recordType}
            leftClassName = '%s_%s' % (className, 'left')
            rightClassName = '%s_%s' % (className, 'right')
            leftCode = self.generateJava(left, queryVarTypes,
                                         public=False,
                                         queryType=subQueryType,
                                         recordType=recordType,
                                         className=leftClassName)
            rightCode = self.generateJava(right, queryVarTypes,
                                          public=False,
                                          queryType=subQueryType,
                                          recordType=recordType,
                                          className=rightClassName)
            formatStrs['otherClasses'] = '\n\n' + leftCode + '\n\n' + rightCode
            formatStrs['fields'] = """\tprivate %(leftName)s left = new %(leftName)s();
    private %(rightName)s right = new %(rightName)s();"""\
                % {'leftName': leftClassName, 'rightName': rightClassName}
            formatStrs['getDSBody'] = '\t\tthrow new UnsupportedOperationException();'
            formatStrs['lookupBody'] = """\t\t%(subQueryType)s leftRes = left.lookup(%(queryVars)s);
        %(subQueryType)s rightRes = right.lookup(%(queryVars)s);
        %(lookupType)s res = constructEmpty();
        res.addAll(leftRes);
        res.%(op)s(rightRes);
        return res;
        """ % { 'subQueryType': subQueryType,
                'lookupType': formatStrs['lookupType'],
                'op': 'addAll' if str(p.decl()) == "Union" else 'retainAll',
                'queryVars': ', '.join(self.varNames),
                }
        else:
            raise Exception("Couldn't parse plan: {}".format(p))

        #if public:
            #formatStrs['otherClasses'] += """class %(className)s_cmp {
#%(comparators)s
#}""" % {'className': className, 'comparators': '\n\n'.join(["""\tpublic Comparator<%(r)s> Comparator_%(f)s = new Comparator<%(r)s>() {
        #public int compare(%(r)s a, %(r)s b) {
            #return ((%(t)s)a.get%(f)s()).compareTo(b.get%(f)s());
        #}
    #};""" % {'r': recordType, 'f': f, 't': 'Comparable'} for f in self.fieldNames])}

        if len(formatStrs['otherClasses']) > 0:
            formatStrs['otherClasses'] = '\t' + formatStrs['otherClasses']\
                                               .replace('\n', '\n\t') + "\n"

        return (skeleton % formatStrs).replace('\t', '    ')

if __name__ == "__main__":

    sc = SolverContext(varNames = ['x', 'y'], fieldNames = ['Age', 'Name'])
    q = sc.Query.And(
        sc.Query.Cmp(sc.Field.Age, sc.Comparison.Gt, sc.QueryVar.x),
        sc.Query.Cmp(sc.Field.Name, sc.Comparison.Eq, sc.QueryVar.y)
        )

    for p in sc.synthesizePlansByEnumeration(q, 1000000):
        print p
        print "Cost =", sc.computeCost(p)
        code = sc.generateJava(p, queryVarTypes=['Integer', 'String'])
        with open("DataStructure.java", "w") as f:
            f.write(code)
        print "="*60
