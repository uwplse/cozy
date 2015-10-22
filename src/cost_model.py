from __future__ import print_function
import math
import tempfile
import os
import subprocess
import sys

import plans
from codegen_java import JavaCodeGenerator
from codegen_cpp import CppCodeGenerator

def _cost(plan, n=float(1000)):
    """Returns (cost,size) tuples"""
    if isinstance(plan, plans.AllWhere): return 1, n
    if isinstance(plan, plans.HashLookup):
        cost1, size1 = _cost(plan.plan)
        return cost1 + 1, size1 / 3
    if isinstance(plan, plans.BinarySearch):
        cost1, size1 = _cost(plan.plan)
        return cost1 + (math.log(size1) if size1 >= 1 else 1), size1 / 2
    if isinstance(plan, plans.Filter):
        cost1, size1 = _cost(plan.plan)
        return cost1 + size1, size1 / 2
    if isinstance(plan, plans.Intersect):
        cost1, size1 = _cost(plan.plan1)
        cost2, size2 = _cost(plan.plan2)
        return cost1 + cost2 + size1 + size2, min(size1, size2) / 2
    if isinstance(plan, plans.Union):
        cost1, size1 = _cost(plan.plan1)
        cost2, size2 = _cost(plan.plan2)
        return cost1 + cost2 + size1 + size2, size1 + size2
    if isinstance(plan, plans.Concat):
        cost1, size1 = _cost(plan.plan1)
        cost2, size2 = _cost(plan.plan2)
        return 1 + cost1 + cost2, size1 + size2
    raise Exception("Couldn't parse plan: {}".format(plan))

def cost(fields, qvars, plan):
    return _cost(plan)[0]

def dynamic_cost(fields, queries, impls, cost_model_file):
    for q, i in zip(queries, impls):
        q.impl = i

    tmp = tempfile.mkdtemp()
    print("benchmarking {} in {}... ".format([q.name for q in queries], tmp), end="")
    sys.stdout.flush()

    if cost_model_file.endswith(".java"):

        with open(os.path.join(tmp, "DataStructure.java"), "w") as f:
            JavaCodeGenerator(f.write, class_name="DataStructure").write(fields, queries)

        with open(os.path.join(tmp, "Main.java"), "w") as f:
            f.write("import java.util.*;")
            f.write("\npublic class Main {\n")
            f.write("public static void main(String[] args) { new Main().run(); }\n")
            with open(cost_model_file, "r") as b:
                f.write(b.read())
            f.write("\n}\n")

        orig = os.getcwd()
        os.chdir(tmp)
        ret = subprocess.call(["javac", "Main.java"])
        assert ret == 0

        java = subprocess.Popen(["java", "Main"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        stdout, stdin = java.communicate()
        assert java.returncode == 0

    elif cost_model_file.endswith(".cpp") or cost_model_file.endswith(".cxx"):

        raise Exception("cpp dynamic cost not implemented")

    else:

        raise Exception("no code generator available for file {}".format(cost_model_file))

    score = long(stdout.strip())

    os.chdir(orig)

    print("cost = {}".format(score))

    return score
