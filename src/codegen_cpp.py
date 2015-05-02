
import predicates
import plans
from codegen import HashMap, SortedSet, UnsortedSet, fresh_name

def ty_to_cpp(ty, record_type):
    if type(ty) is HashMap:
        return "std::map< {}, {} >".format(ty.fieldTy, ty_to_cpp(ty.ty, record_type))
    elif type(ty) is SortedSet or type(ty) is UnsortedSet:
        return "std::vector< {} >".format(record_type)
    else:
        raise Exception("unknown type {}".format(ty))

def write_cpp(fields, qvars, plan, writer, header_writer, namespace=None):
    """
    Writes a C++ data structure implementation to the given writers.
    Arguments:
     - fields  - a list of (field_name, type)
     - qvars   - a list of (query_var, type)
     - plan    - an execution plan
     - writer  - a function that consumes strings
     - header_writer  - a function that consumes strings
     - namespace - what C++ namespace to put the generated classes in
    """

    record_type_name = "Record"
    structure_name = "DataStructure"
    namespace = namespace or ""

    members = [] # will be filled with (name,ty) tuples

    def onMember(ty):
        name = fresh_name()
        members.append((name, ty))
        return name

    proc, result, pred = _traverse(fields, qvars, plan, record_type_name, UnsortedSet(), onMember)

    header_writer("#include <vector>\n");
    header_writer("#include <map>\n");

    if namespace:
        header_writer("namespace {} {{".format(namespace))

    header_writer("struct {} {{\n".format(record_type_name))
    for f, ty in fields:
        header_writer("    {} {};\n".format(ty, f))
    header_writer("    inline {}({}) : {} {{ }};\n".format(
        record_type_name,
        ", ".join("{} _{}".format(ty, f) for f, ty in fields),
        ", ".join("{f}(_{f})".format(f=f) for f, ty in fields)))
    header_writer("};\n")

    header_writer("class {} {{\n".format(structure_name))
    header_writer("public:\n")
    header_writer("    class Iterator {\n")
    header_writer("    friend class {};\n".format(structure_name))
    header_writer("    public:\n")
    header_writer("        inline const {}& next() {{ const Record& r = *cursor; advance(); return r; }};\n".format(record_type_name))
    header_writer("        inline bool hasNext() { return cursor != end; };\n")
    header_writer("    private:\n")
    header_writer("        Iterator(std::vector< {ty} >::const_iterator _cursor, std::vector< {ty} >::const_iterator _end, {var_args}) : cursor(_cursor), end(_end), {var_inits} {{ }}\n".format(
        ty=record_type_name,
        var_args=", ".join("{} _{}".format(ty, v) for v, ty in qvars),
        var_inits=", ".join("{v}(_{v})".format(v=v) for v, ty in qvars)))
    header_writer("        void advance();\n")
    header_writer("        std::vector< {} >::const_iterator cursor;\n".format(record_type_name))
    header_writer("        std::vector< {} >::const_iterator end;\n".format(record_type_name))
    for v, ty in qvars:
        header_writer("        {} {};\n".format(ty, v))
    header_writer("    };\n")
    header_writer("    void add({});\n".format(", ".join("{} {}".format(ty, f) for f,ty in fields)))
    header_writer("    Iterator query({}) const;\n".format(", ".join("{} {}".format(ty, v) for v,ty in qvars)))
    header_writer("private:\n")

    for name, ty in members:
        header_writer("    {} {};\n".format(ty_to_cpp(ty, record_type_name), name))

    header_writer("};\n")

    if namespace:
        header_writer("}")

    writer('#include "{}.hpp"\n'.format(structure_name))
    writer("#include <algorithm>\n")

    writer("static const std::vector< {} > EMPTY_VECTOR;\n".format(record_type_name))
    writer("template<class T>\nstruct Range {\n")
    writer("    T& begin() { return _begin; }\n")
    writer("    T& end() { return _end; }\n")
    writer("    T _begin;\n")
    writer("    T _end;\n")
    writer("};\n")

    for f, ty in fields:
        comp = "lt_{}".format(f)
        writer("struct {name} {{\n".format(name=comp))
        writer("    bool operator()(const {rty}& r, {fty} f) {{ return r.{f} < f; }}\n".format(rty=record_type_name, f=f, fty=ty))
        writer("    bool operator()({fty} f, const {rty}& r) {{ return f < r.{f}; }}\n".format(rty=record_type_name, f=f, fty=ty))
        writer("};\n")

    writer("void {ns}{sn}::add({}) {{\n".format(
        ", ".join("{} {}".format(ty, f) for f,ty in fields),
        ns="{}::".format(namespace) if namespace else "",
        sn=structure_name))
    writer("    {} x({});\n".format(record_type_name, ", ".join(f for f, ty in fields)))
    for name, ty in members:
        _gen_insert(name, ty, "x", record_type_name, writer)
    writer("\n}\n")

    writer("{sn}::Iterator {ns}{sn}::query({}) const {{\n".format(
        ", ".join("{} {}".format(ty, v) for v,ty in qvars),
        ns="{}::".format(namespace) if namespace else "",
        sn=structure_name))
    writer(proc)
    writer("    return ({v} == NULL) ? Iterator(EMPTY_VECTOR.end(), EMPTY_VECTOR.end(), {vars}) : Iterator(({v})->begin(), ({v})->end(), {vars});\n".format(
        v=result,
        vars=", ".join(v for v, ty in qvars)))
    writer("}\n")

    writer("void {ns}{sn}::Iterator::advance() {{\n".format(ns="{}::".format(namespace) if namespace else "", sn=structure_name))
    writer("    do {{ ++cursor; }} while (hasNext() && !({}));\n".format(pred("*cursor")))
    writer("}\n")

def _gen_insert(e, ty, x, record_type_name, writer):
    if type(ty) is HashMap:
        _gen_insert("{e}[{}]".format(ty.fieldName, e=e), ty.ty, x, record_type_name, writer)
    elif type(ty) is SortedSet:
        # TODO: use std::binary_search
        v = fresh_name()
        writer("    {}& {} = {};\n".format(ty_to_cpp(ty, record_type_name), v, e))
        writer("    {v}.insert(std::upper_bound({v}.begin(), {v}.end(), {field}, {comp}()), {x});".format(
            x=x,
            v=v,
            field=ty.fieldName,
            comp="lt_{}".format(ty.fieldName)))
    elif type(ty) is UnsortedSet:
        writer("    {}.push_back({});".format(e, x))

def new(ty, record_type_name):
    if type(ty) is HashMap:
        return "std::map< {}, {} >()".format(ty.fieldTy, ty_to_cpp(ty.ty, record_type_name))
    elif type(ty) is SortedSet or type(ty) is UnsortedSet:
        return "std::vector< {} >()".format(record_type_name)

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

def _predicate_to_exp(fields, qvars, pred, target):
    if type(pred) is predicates.Var:
        return pred.name if pred.name in {v for v,ty in qvars} else "({}).{}".format(target, pred.name)
    elif type(pred) is predicates.Bool:
        return "true" if pred.val else "false"
    elif type(pred) is predicates.Compare:
        return "({}) {} ({})".format(
            _predicate_to_exp(fields, qvars, pred.lhs, target),
            predicates.opToStr(pred.op),
            _predicate_to_exp(fields, qvars, pred.rhs, target))
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

def _traverse(fields, qvars, plan, record_type_name, resultTy, onMember):
    """returns proc, result_ptr, predicate"""
    if type(plan) is plans.All:
        name = onMember(resultTy)
        return ("", "&{}".format(name), lambda x: "true")
    elif type(plan) is plans.Empty:
        return ("", "NULL", lambda x: "false")
    elif type(plan) is plans.HashLookup:
        t = HashMap(dict(fields)[plan.fieldName], plan.fieldName, resultTy)
        p, r, pred = _traverse(fields, qvars, plan.plan, record_type_name, t, onMember)
        rn = fresh_name()
        p += "    const {ty}* {rn};\n".format(ty=ty_to_cpp(resultTy, record_type_name), rn=rn)

        p += "    if (({}) != NULL) {{\n".format(r)
        n1 = fresh_name()
        p += "        {}::const_iterator {} = ({})->find({});\n".format(ty_to_cpp(t, record_type_name), n1, r, plan.varName)
        p += "        {rn} = ({n1} == ({map})->end()) ? NULL : (&(({n1})->second));\n".format(ty=ty_to_cpp(resultTy, record_type_name), n1=n1, rn=rn, map=r)
        p += "    } else {\n"
        p += "        {rn} = NULL;\n".format(rn=rn)
        p += "    }\n"

        return (p, rn, pred)
    elif type(plan) is plans.BinarySearch:
        resultTy = resultTy.unify(SortedSet(dict(fields)[plan.fieldName], plan.fieldName))
        p, r, pred = _traverse(fields, qvars, plan.plan, record_type_name, resultTy, onMember)

        rn = fresh_name()
        rng = fresh_name()
        ty = ty_to_cpp(resultTy, record_type_name)
        p += "    Range<{ty}::const_iterator>* {rn};\n".format(ty=ty, rn=rn)
        p += "    Range<{ty}::const_iterator> {rng};\n".format(ty=ty, rng=rng)
        p += "    if (({r}) != NULL) {{\n".format(r=r)

        if plan.op is plans.Eq:
            p += "        {rng}._begin = std::lower_bound(({r})->begin(), ({r})->end(), {var}, lt_{field}());\n".format(ty=ty, rng=rng, r=r, var=plan.varName, field=plan.fieldName)
            p += "        {rng}._end   = std::upper_bound(({rng})->begin(), ({r})->end(), {var}, lt_{field}());\n".format(ty=ty, rng=rng, r=r, var=plan.varName, field=plan.fieldName)
        elif plan.op is plans.Lt:
            p += "        {rng}._begin = ({r})->begin();\n".format(ty=ty, rng=rng, r=r)
            p += "        {rng}._end   = std::lower_bound(({r})->begin(), ({r})->end(), {var}, lt_{field}());\n".format(ty=ty, rng=rng, r=r, var=plan.varName, field=plan.fieldName)
        elif plan.op is plans.Le:
            p += "        {rng}._begin = ({r})->begin();\n".format(ty=ty, rng=rng, r=r)
            p += "        {rng}._end   = std::upper_bound(({r})->begin(), ({r})->end(), {var}, lt_{field}());\n".format(ty=ty, rng=rng, r=r, var=plan.varName, field=plan.fieldName)
        elif plan.op is plans.Gt:
            p += "        {rng}._begin = std::upper_bound(({r})->begin(), ({r})->end(), {var}, lt_{field}());\n".format(ty=ty, rng=rng, r=r, var=plan.varName, field=plan.fieldName)
            p += "        {rng}._end   = ({r})->end();\n".format(ty=ty, rng=rng, r=r)
        elif plan.op is plans.Ge:
            p += "        {rng}._begin = std::lower_bound(({r})->begin(), ({r})->end(), {var}, lt_{field}());\n".format(ty=ty, rng=rng, r=r, var=plan.varName, field=plan.fieldName)
            p += "        {rng}._end   = ({r})->end();\n".format(ty=ty, rng=rng, r=r)

        p += "        {rn} = &{rng};\n".format(rn=rn, rng=rng)
        p += "    } else {\n"
        p += "        {rn} = NULL;\n".format(rn=rn)
        p += "    }\n"
        return (p, rn, pred)
    elif type(plan) is plans.Filter:
        p, r, pred = _traverse(fields, qvars, plan.plan, record_type_name, resultTy, onMember)
        return (p, r, lambda x: "({}) && ({})".format(pred(x), _predicate_to_exp(fields, qvars, plan.predicate, x)))
    elif type(plan) is plans.Intersect:
        raise Exception("intersect codegen not implemented")
    elif type(plan) is plans.Union:
        raise Exception("union codegen not implemented")
