
import predicates
import plans
from codegen import HashMap, SortedSet, UnsortedSet, fresh_name

def ty_to_java(ty, record_type):
    if type(ty) is HashMap:
        return "java.util.Map<{},{}>".format(_box(ty.fieldTy), ty_to_java(ty.ty, record_type))
    elif type(ty) is SortedSet or type(ty) is UnsortedSet:
        return "java.util.List<{}>".format(record_type)
    else:
        raise Exception("unknown type {}".format(ty))

def write_java(fields, queries, writer, package=None):
    """
    Writes a Java data structure implementation to the given writer.
    Arguments:
     - fields  - a list of (field_name, type)
     - queries - a dict of query objects with .bestPlan set
     - writer  - a function that consumes strings
     - package - what Java package to put the generated class in
    """

    record_type_name = "Record"
    structure_name = "DataStructure"

    members = [] # will be filled with (name,ty) tuples

    def onMember(ty):
        name = fresh_name()
        members.append((name, ty))
        return name

    qfuncs = []
    field_dict = dict(fields)
    for q in queries:
        ty = UnsortedSet() if q.sort_field is None else SortedSet(field_dict[q.sort_field], q.sort_field)
        proc, result = _traverse(fields, q.vars, q.bestPlan, record_type_name, ty, onMember)
        qfuncs.append((q.name, q.vars, proc, result))

    if package is not None:
        writer("package {};\n\n".format(package))
    writer("public class {} implements java.io.Serializable {{\n".format(structure_name))

    writer("    private static final long serialVersionUID = 1L;\n")

    writer("""
    private static <T> void insert_sorted(java.util.List<T> l, T x, java.util.Comparator<T> cmp) {
        int idx = java.util.Collections.binarySearch(l, x, cmp);
        if (idx < 0) { idx = -(idx + 1); }
        l.add(idx, x);
    }
    private static abstract class FilteredIterable<T> implements Iterable<T> {
        private final Iterable<T> wrapped;
        public FilteredIterable(Iterable<T> wrapped) {
            this.wrapped = wrapped;
        }

        protected abstract boolean test(T x);

        @Override
        public java.util.Iterator<T> iterator() {
            final java.util.Iterator<T> it = wrapped.iterator();
            return new java.util.Iterator<T>() {
                boolean hasNext = false;
                T next = null;
                {
                    advance();
                }
                private void advance() {
                    hasNext = it.hasNext();
                    while (hasNext) {
                        next = it.next();
                        if (test(next)) {
                            break;
                        }
                        hasNext = it.hasNext();
                    }
                }
                @Override
                public boolean hasNext() {
                    return hasNext;
                }
                @Override
                public T next() {
                    T result = next;
                    advance();
                    return result;
                }
                @Override
                public void remove() {
                    throw new UnsupportedOperationException();
                }
            };
        }
    }
    private static <T> java.util.Set<T> mkset(Iterable<T> it) {
        java.util.Set<T> s = new java.util.HashSet<T>();
        for (T x : it) {
            s.add(x);
        }
        return s;
    }
    private static <T> Iterable<T> intersect(Iterable<T> left, Iterable<T> right) {
        final java.util.Set<T> s = mkset(left);
        return new FilteredIterable<T>(right) {
            @Override
            public boolean test(T x) {
                return s.contains(x);
            }
        };
    }
    private static <T> Iterable<T> union(Iterable<T> left, Iterable<T> right) {
        java.util.Set<T> s = mkset(left);
        for (T x : right) {
            s.add(x);
        }
        return s;
    }\n""")

    _gen_record_type(record_type_name, fields, writer)

    # generate comparators
    for f, ty in fields:
        writer("    public static final java.util.Comparator<{record_type}> COMPARE_{field} = new java.util.Comparator<{record_type}>() {{ public int compare({record_type} a, {record_type} b) {{ return {pred}; }} }};\n".format(
            record_type=record_type_name,
            field=f,
            pred=_compare("a.{}".format(f), "b.{}".format(f), ty)))

    for name, ty in members:
        writer("    private {} {} = {};\n".format(ty_to_java(ty, record_type_name), name, new(ty, record_type_name)))

    for name, qvars, proc, result in qfuncs:
        writer("    public Iterable<{}> {}({}) {{\n".format(record_type_name, name, ", ".join("final {} {}".format(ty, v) for v,ty in qvars)))
        writer(proc)
        writer("        return {};\n".format(result))
        writer("    }\n")

    writer("    public void add({record_type} x) {{\n".format(record_type=record_type_name))
    for name, ty in members:
        _gen_insert(name, ty, "x", record_type_name, writer)
    writer("    }\n")

    writer("    public void remove({record_type} x) {{\n".format(record_type=record_type_name))
    writer("        throw new UnsupportedOperationException();\n")
    writer("    }\n")

    writer("}\n")

def _gen_insert(e, ty, x, record_type_name, writer):
    if type(ty) is HashMap:
        k = "{}.{}".format(x, ty.fieldName)
        tmp = fresh_name()
        writer("        {} {} = {}.get({});\n".format(ty_to_java(ty.ty, record_type_name), tmp, e, k))
        writer("        if ({} == null) {{\n".format(tmp))
        writer("            {} = {};\n".format(tmp, new(ty.ty, record_type_name)))
        writer("            {}.put({}, {});\n".format(e, k, tmp))
        writer("        }\n")
        _gen_insert(tmp, ty.ty, x, record_type_name, writer)
    elif type(ty) is SortedSet:
        writer("        insert_sorted({}, {}, COMPARE_{});\n".format(e, x, ty.fieldName))
    elif type(ty) is UnsortedSet:
        writer("        {}.add({});\n".format(e, x))

def _compare(x, y, ty):
    if _is_primitive(ty):
        return "{}.compare({}, {})".format(_box(ty), x, y)
    return "({}).compareTo({})".format(x, y)

def new(ty, record_type_name):
    if type(ty) is HashMap:
        return "new java.util.HashMap<{}, {}>()".format(_box(ty.fieldTy), ty_to_java(ty.ty, record_type_name))
    elif type(ty) is SortedSet or type(ty) is UnsortedSet:
        return "new java.util.ArrayList<{}>()".format(record_type_name)

def _gen_record_type(name, fields, writer):
    writer("    public static class {} implements java.io.Serializable {{\n".format(name))
    writer("        private static final long serialVersionUID = 1L;\n")
    for f,ty in fields:
        writer("        public final {} {};\n".format(ty, f))
    writer("        public {}({}) {{\n".format(name, ", ".join("{} {}".format(ty, f) for f,ty in fields)))
    for f,ty in fields:
        writer("            this.{f} = {f};\n".format(f=f))
    writer("        }\n")
    writer("        @Override\n");
    writer("        public String toString() {\n")
    writer('            return new StringBuilder().append("{}(")'.format(name))
    first = True
    for f,ty in fields:
        if not first:
            writer(".append(',')")
        writer('.append("{}=")'.format(f))
        writer(".append({})".format(f))
        first = False
    writer(".append(')').toString();\n")
    writer("        }\n")
    writer("    }\n")

def _box(ty):
    if ty == "int":
        return "Integer"
    if ty == "char":
        return "Character"
    return ty[0].upper() + ty[1:]

def _is_primitive(ty):
    return ty[0] != ty[0].upper()

def _predicate_to_exp(fields, qvars, pred, target):
    if type(pred) is predicates.Var:
        return pred.name if pred.name in {v for v,ty in qvars} else "{}.{}".format(target, pred.name)
    elif type(pred) is predicates.Bool:
        return "true" if pred.val else "false"
    elif type(pred) is predicates.Compare:
        if _is_primitive(dict(fields + qvars)[pred.lhs.name]):
            return "({}) {} ({})".format(
                _predicate_to_exp(fields, qvars, pred.lhs, target),
                predicates.opToStr(pred.op),
                _predicate_to_exp(fields, qvars, pred.rhs, target))
        else:
            return "({}).compareTo({}) {} 0".format(
                _predicate_to_exp(fields, qvars, pred.lhs, target),
                _predicate_to_exp(fields, qvars, pred.rhs, target),
                predicates.opToStr(pred.op))
    elif type(pred) is predicates.And:
        return "({}) && ({})".format(
            _predicate_to_exp(fields, qvars, pred.lhs, target),
            _predicate_to_exp(fields, qvars, pred.rhs, target))
    elif type(pred) is predicates.Or:
        return "({}) || ({})".format(
            _predicate_to_exp(fields, qvars, pred.lhs, target),
            _predicate_to_exp(fields, qvars, pred.rhs, target))
    elif type(pred) is predicates.Not:
        return "!({})".format(_predicate_to_exp(fields, qvars, pred.p, target))

def empty(ty, record_type_name):
    if type(ty) is HashMap:
        return "java.util.Collections.<{}, {}>emptyMap()".format(_box(ty.fieldTy), ty_to_java(ty.ty, record_type_name))
    return "java.util.Collections.<{}>emptyList()".format(record_type_name)

def _traverse(fields, qvars, plan, record_type_name, resultTy, onMember):
    if type(plan) is plans.All:
        name = onMember(resultTy)
        return ("", name)
    elif type(plan) is plans.Empty:
        return ("", empty(resultTy, record_type_name))
    elif type(plan) is plans.HashLookup:
        p, r = _traverse(fields, qvars, plan.plan, record_type_name, HashMap(dict(fields)[plan.fieldName], plan.fieldName, resultTy), onMember)
        n = fresh_name()
        proc  = "        {} {} = {}.get({});\n".format(ty_to_java(resultTy, record_type_name), n, r, plan.varName)
        proc += "        if ({n} == null) {{ {n} = {empty}; }}\n".format(n=n, empty=empty(resultTy, record_type_name))
        return (p + proc, n)
    elif type(plan) is plans.BinarySearch:
        resultTy = resultTy.unify(SortedSet(dict(fields)[plan.fieldName], plan.fieldName))
        p, r = _traverse(fields, qvars, plan.plan, record_type_name, resultTy, onMember)
        start = fresh_name()
        end = fresh_name()
        proc = "        int {}, {};\n".format(start, end)

        def bisect(op, dst, start=None, end=None):
            """Generates code to set `dst` such that tmp[0:dst] `op` varName and not (tmp[dst:] `op` varName)."""
            if start is None: start = "0"
            if end is None: end = "{}.size()".format(r)
            return """
        int {lo} = {start};
        int {hi} = {end};
        while ({lo} < {hi}) {{
            int {mid} = ({lo} >> 1) + ({hi} >> 1) + ({lo} & {hi} & 1); // overflow-free average
            if ({tmp}.get({mid}).{fieldName} {op} {varName}) {{
                {lo} = {mid} + 1;
            }} else {{
                {hi} = {mid};
            }}
        }}
        {dst} = {lo};\n""".format(
                lo=fresh_name(),
                hi=fresh_name(),
                mid=fresh_name(),
                dst=dst,
                op=op,
                tmp=r,
                fieldName=plan.fieldName,
                varName=plan.varName,
                start=start,
                end=end)

        if plan.op is plans.Eq:
            proc += bisect("<", start)
            proc += bisect("<=", end, start=start)
        elif plan.op is plans.Lt:
            proc += "        {} = 0;\n".format(start)
            proc += bisect("<", end)
        elif plan.op is plans.Le:
            proc += "        {} = 0;\n".format(start)
            proc += bisect("<=", end)
        elif plan.op is plans.Gt:
            proc += bisect("<=", start)
            proc += "        {} = {}.size();\n".format(end, r)
        elif plan.op is plans.Ge:
            proc += bisect("<", start)
            proc += "        {} = {}.size();\n".format(end, r)
        return (p + proc, "{}.subList({}, {})".format(r, start, end))
    elif type(plan) is plans.Filter:
        p, r = _traverse(fields, qvars, plan.plan, record_type_name, resultTy, onMember)
        n = fresh_name()
        proc = """
        Iterable<{ty}> {n} = new FilteredIterable<{ty}>({r}) {{
            @Override
            public boolean test({ty} x) {{
                return {pred};
            }}
        }};\n""".format(r=r, n=n, pred=_predicate_to_exp(fields, qvars, plan.predicate, "x"), ty=record_type_name)
        return (p + proc, n)
    elif type(plan) is plans.Intersect:
        p1, r1 = _traverse(fields, qvars, plan.plan1, record_type_name, resultTy, onMember)
        p2, r2 = _traverse(fields, qvars, plan.plan2, record_type_name, resultTy, onMember)
        return (p1 + p2, "intersect({}, {})".format(r1, r2))
    elif type(plan) is plans.Union:
        p1, r1 = _traverse(fields, qvars, plan.plan1, record_type_name, resultTy, onMember)
        p2, r2 = _traverse(fields, qvars, plan.plan2, record_type_name, resultTy, onMember)
        return (p1 + p2, "union({}, {})".format(r1, r2))
