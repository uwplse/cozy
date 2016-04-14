"""
Cozy fuzzer. Generates random specifications, runs the tool on them, and checks
that each candidate implementation adheres to its spec.
"""

# Builtin
from __future__ import print_function
import random
import argparse
import time
import tempfile
import subprocess
import os.path
import sys
import traceback
import subprocess

# Cozy libraries
import queries
import predicates

DEFAULT_TIMEOUT = None
DEFAULT_MAX_FIELDS = 5
DEFAULT_MAX_EXPR_SIZE = 5
DEFAULT_MAX_NQUERIES = 3
DEFAULT_MAX_VARS = DEFAULT_MAX_FIELDS
ALL_TYPES = ["byte", "char", "short", "int", "long", "float", "double", "boolean", "Integer", "String"]

def random_fields(n, prefix="f", types=ALL_TYPES):
    nfields = random.randint(1, n)
    return [("{}{}".format(prefix, n), random.choice(types)) for n in range(nfields)]

def get_seed():
    return int(time.time() * 1000)

def _random_predicate(fields, vars, max_size):
    choice = random.choice([predicates.Compare, predicates.And, predicates.Or, predicates.Not])
    if max_size <= 1 or choice is predicates.Compare:
        f, t = random.choice([(f, t) for f, t in fields if any(vt == t for v, vt in vars)])
        v = random.choice([v for v, vt in vars if vt == t])
        op = random.choice(predicates.operators)
        return (predicates.Compare(predicates.Var(f), op, predicates.Var(v)), 1)
    elif choice in [predicates.And, predicates.Or]:
        p1, sz1 = _random_predicate(fields, vars, max_size - 2)
        p2, sz2 = _random_predicate(fields, vars, max_size - sz1 - 1)
        return (choice(p1, p2), sz1 + sz2 + 1)
    elif choice is predicates.Not:
        p, sz = _random_predicate(fields, vars, max_size - 1)
        return (predicates.Not(p), sz + 1)

def random_predicate(*args, **kwargs):
    return _random_predicate(*args, **kwargs)[0]

def random_query(name, fields, max_vars_per_query, max_expr_size):
    vars = random_fields(max_vars_per_query, prefix="v", types=[t for (f, t) in fields])
    pred = random_predicate(fields, vars, max_expr_size)
    sort = random.choice([f for f, t in fields]) if random.random() < 0.1 else None
    return queries.Query(name, vars, pred, sort_field=sort)

def random_spec(max_fields, max_queries, max_vars_per_query, max_expr_size):
    fields = random_fields(max_fields)
    nqueries = random.randint(1, max_queries)
    return (fields, [
        random_query("q{}".format(n), fields, max_vars_per_query, max_expr_size)
        for n in range(nqueries)])

def format_pred(p):
    if type(p) is predicates.Compare:
        return "({} {} {})".format(p.lhs.name, predicates.opToStr(p.op), p.rhs.name)
    elif type(p) is predicates.And:
        return "({} and {})".format(format_pred(p.lhs), format_pred(p.rhs))
    elif type(p) is predicates.Or:
        return "({} or {})".format(format_pred(p.lhs), format_pred(p.rhs))
    elif type(p) is predicates.Not:
        return "(not {})".format(format_pred(p.p))
    else:
        raise Exception("wtf: {}".format(p))

def format_spec(spec, benchmark_file):
    fields, queries = spec

    s = "fields {}\n".format(", ".join("{} : {}".format(f, t) for f, t in fields))
    for q in queries:
        s += "query {}({}) {}\n".format(q.name, ", ".join("{} : {}".format(v, t) for v, t in q.vars), format_pred(q.pred))
    s += "costmodel {}\n".format(benchmark_file)
    return s

def make_benchmark(spec):
    fields, queries = spec
    return ("""
    Random rand = new Random(10);

    void check(boolean cond) {
        if (!cond) System.exit(1);
    }

    byte random_byte() { return (byte)rand.nextInt(); }
    char random_char() { return (char)((short)rand.nextInt()); }
    short random_short() { return (short)rand.nextInt(); }
    int random_int() { return rand.nextInt(); }
    long random_long() { return (long)rand.nextInt() << 32 | rand.nextInt(); }
    float random_float() { return rand.nextFloat(); }
    double random_double() { return rand.nextDouble(); }
    boolean random_boolean() { return rand.nextBoolean(); }
    Integer random_Integer() { return Integer.valueOf(rand.nextInt()); }
    String random_String() { return rand.nextBoolean() ? "" : new String(new char[] { random_char(), random_char() }); }
    DataStructure.Record random_Record() { return new DataStructure.Record(""" + ",".join("random_{}()".format(t) for f, t in fields) + """); }

    Collection<DataStructure.Record> mirror = new ArrayList<>();
    void run() {
        long start = System.currentTimeMillis();
        final int N = 1000;
        DataStructure ds = new DataStructure();
        for (int i = 0; i < N; ++i) {
            ds.add(random_Record());
        }
        check(ds.size() == N);
        for (int i = 0; i < 10000; ++i) {
            Iterator<DataStructure.Record> it;
            switch (Math.abs(rand.nextInt()) % """ + str(len(queries)) + """) {
                """ +

                "".join("case {}: it = ds.{}({}); break;\n".format(i, queries[i].name,
                    ", ".join("random_{}()".format(t) for v, t in queries[i].vars)) for i in range(len(queries)))

                + """
                default: continue; // impossible
            }
            while (it.hasNext()) {
                DataStructure.Record r = it.next();
                check(r != null);
            }
        }
        System.out.println(System.currentTimeMillis() - start);
    }
    """)

def cozy(input_file):
    proc = subprocess.Popen(["python", "src/main.py", "-d", "-t", "60", "--enable-arrays", "--java", "-", input_file],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE)
    stdout, stderr = proc.communicate()
    assert proc.returncode == 0, "cozy died (stderr={})".format(stderr)

def run(args):
    timeout = float(args.timeout) if args.timeout is not None else None
    seed = int(args.seed) if args.seed is not None else get_seed()
    max_fields = DEFAULT_MAX_FIELDS
    max_queries = DEFAULT_MAX_NQUERIES
    max_vars_per_query = DEFAULT_MAX_VARS
    max_expr_size = DEFAULT_MAX_EXPR_SIZE

    print("Starting fuzzing...")
    print("timeout = {}".format(timeout))
    print("seed = {}".format(seed))

    random.seed(seed)

    end_time = time.time() + timeout if timeout is not None else None
    iteration = 1
    fail = False
    while end_time is None or time.time() < end_time:

        print("iteration {}".format(iteration))
        iteration += 1

        spec = random_spec(max_fields, max_queries, max_vars_per_query, max_expr_size)

        with tempfile.NamedTemporaryFile() as spec_file:
            with tempfile.NamedTemporaryFile(suffix=".java") as benchmark_file:
                spec_file.write(format_spec(spec, benchmark_file.name))
                spec_file.flush()
                benchmark = make_benchmark(spec)
                benchmark_file.write(benchmark)
                benchmark_file.flush()
                try:
                    cozy(spec_file.name)
                except KeyboardInterrupt:
                    print("Stopping due to keyboard interrupt")
                    break
                except:
                    faildir = os.path.dirname(__file__)
                    failspec = os.path.join(faildir, "fuzz_fail_spec")
                    failbench = os.path.join(faildir, "fuzz_fail_bench.java")
                    with open(failspec, "w") as f: f.write(format_spec(spec, os.path.basename(failbench)))
                    with open(failbench, "w") as f: f.write(benchmark)
                    traceback.print_exc()
                    print("Failing input was written to: {}".format(failspec), file=sys.stderr)
                    fail = True
                    break

    sys.exit(1 if fail else 0)

def get_cmdline_args():
    parser = argparse.ArgumentParser(description="Cozy fuzzer.")
    parser.add_argument("-t", "--timeout", metavar="N", default=DEFAULT_TIMEOUT, help="How long to run (in seconds); default={}".format(DEFAULT_TIMEOUT))
    parser.add_argument("-s", "--seed", metavar="N", default=None, help="Random seed (default=time-based)")
    return parser.parse_args()

if __name__ == "__main__":
    run(get_cmdline_args())
