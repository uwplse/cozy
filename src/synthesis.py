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

COST_ITEM_COUNT = float(1000)

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
            for plan in (plans.BinarySearch(p, f, op, v) for p in plansOfSize[size-1] for f in self.fieldNames for v in self.varNames if (f, v) in comps for op in predicates.operators):
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
