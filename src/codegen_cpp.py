
import predicates
import plans
from codegen import HashMap, SortedSet, UnsortedSet, fresh_name

def ty_to_cpp(ty, record_type):
    if type(ty) is HashMap:
        return "std::map< {}, {} >".format(ty.fieldTy, ty_to_cpp(ty.ty, record_type))
    elif type(ty) is SortedSet or type(ty) is UnsortedSet:
        return "std::vector< {}* >".format(record_type)
    else:
        raise Exception("unknown type {}".format(ty))

class Iterator(object):
    def __init__(self):
        self.init = ""            # run before iterator construction
        self.fields = []          # (name, cpp_type) members the iterator needs

        self.advance = ""         # routine for advancing the iterator
        self.advanceResults = []  # dependent on the plan type

        self.hasNext = ""         # cpp expression indicating whether exhausted
        self.destruct = ""        # destructor code

    def write_impl(self, namespace, name, args, argTypes, record_type_name, writer):
        writer("{}::{name}::{name}({args}) {{\n".format(namespace, name=name, args=", ".join("{} {}".format(ty_to_cpp(argTypes[a], record_type_name) if a in self.memberVars else argTypes[a], a) for a in args)))
        writer(self.init)
        for ty, r in self.initResults:
            writer("    this->{x} = {x};\n".format(x=r))
        writer("}\n")

    @staticmethod
    def ofIterablePtr(init, ptr, ptr_ty):
        it = Iterator()
        it.init = init

        it_ty = "{}::iterator".format(ptr_ty)
        begin = fresh_name()
        end = fresh_name()

        it.init += "    {} {}({}->begin());\n".format(it_ty, begin, ptr)
        it.init += "    {} {}({}->end());\n".format(it_ty, end, ptr)

        it.advanceResults = "*({}++)".format(begin)
        it.hasNext = "{} != {}".format(begin, end)

        it.fields = [
            (begin, it_ty),
            (end, it_ty)]

        return it

def capitalize(s):
    return s[0].upper() + s[1:]

def write_cpp(fields, queries, writer, header_writer, extra="", namespace=None):
    """
    Writes a C++ data structure implementation to the given writers.
    Arguments:
     - fields  - a list of (field_name, type)
     - queries - a dict of query objects with .bestPlan set
     - writer  - a function that consumes strings
     - header_writer  - a function that consumes strings
     - namespace - what C++ namespace to put the generated classes in
    """

    record_type_name = "Record"
    structure_name = "DataStructure"
    namespace = namespace or ""

    members = [] # will be filled with (name,ty) tuples

    def onMember(ty):
        for name, ty2 in members:
            u = ty.unify(ty2)
            if u is not None:
                members.remove((name, ty2))
                members.append((name, u))
                return name
        name = fresh_name()
        members.append((name, ty))
        return name

    its = [] # iterators
    field_dict = dict(fields)
    for q in queries:
        ty = UnsortedSet() if q.sort_field is None else SortedSet(field_dict[q.sort_field], q.sort_field)
        it = _traverse(fields, q.vars, q.bestPlan, record_type_name, ty, onMember)
        its.append((q, it))

    header_writer("#ifndef {}_H\n".format(structure_name))
    header_writer("#define {}_H 1\n".format(structure_name))
    header_writer("#include <vector>\n")
    header_writer("#include <map>\n")
    header_writer("#include <set>\n")
    header_writer(extra)
    header_writer("\n")

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
    header_writer("    void add({} *);\n".format(record_type_name))
    header_writer("    void remove({} *);\n".format(record_type_name))

    for f, ty in fields:
        header_writer("    void update{}({} *, {});\n".format(capitalize(f), record_type_name, ty))

    header_writer("\n")
    for q, it in its:
        # TODO
        vars_dict = dict(q.vars)
        it_name = "{}_iterator".format(q.name)
        header_writer("    class {} {{\n".format(it_name))
        header_writer("    friend class {};\n".format(structure_name))
        header_writer("    public:\n")
        header_writer("        ~{}();\n".format(it_name))
        header_writer("        Record* next();\n")
        header_writer("        bool hasNext();\n")
        header_writer("    private:\n")
        header_writer("        {it_name}({args});\n".format(it_name=it_name,
            args=", ".join("{} _{}".format(ty, f) for f, ty in it.fields)))
        for f, ty in it.fields:
            header_writer("        {} {};\n".format(ty, f))
        header_writer("    };\n")
        header_writer("    {name}_iterator {name}({args});\n\n".format(
            name=q.name,
            args=", ".join("{} {}".format(ty, v) for v,ty in q.vars)))
    header_writer("private:\n")

    for name, ty in members:
        header_writer("    {} {};\n".format(ty_to_cpp(ty, record_type_name), name))

    header_writer("};\n")

    if namespace:
        header_writer("}\n")

    header_writer("#endif\n")

    writer('#include "{}.hpp"\n'.format(structure_name))
    writer("#include <algorithm>\n")

    for f, ty in fields:
        comp = "lt_{}".format(f)
        writer("struct {name} {{\n".format(name=comp))
        writer("    bool operator()(const {rty}* r, {fty} f) {{ return r->{f} < f; }}\n".format(rty=record_type_name, f=f, fty=ty))
        writer("    bool operator()({fty} f, const {rty}* r) {{ return f < r->{f}; }}\n".format(rty=record_type_name, f=f, fty=ty))
        writer("};\n")

    namespace = "{}::".format(namespace) if namespace else ""

    writer("void {ns}{sn}::add({ty} * x) {{\n".format(
        ty=record_type_name,
        ns=namespace,
        sn=structure_name))
    for name, ty in members:
        _gen_insert(name, ty, "x", record_type_name, writer)
    writer("\n}\n")

    writer("void {ns}{sn}::remove({ty} * x) {{\n".format(
        ty=record_type_name,
        ns=namespace,
        sn=structure_name))
    for name, ty in members:
        _gen_remove(name, ty, "x", record_type_name, writer)
    writer("\n}\n")

    ns = "{}{}".format(namespace, structure_name)
    for q, it in its:
        it_name = "{}_iterator".format(q.name)

        writer("\n")

        writer("{ns}::{it_name}::{it_name}({args}) : {inits} {{ }}\n".format(
            ns=ns, it_name=it_name,
            args=", ".join("{} _{}".format(ty, f) for f, ty in it.fields),
            inits=", ".join("{f}(_{f})".format(f=f) for f, ty in it.fields)))

        writer("{ns}::{it_name}::~{it_name}() {{\n{destruct}}}\n".format(
            ns=ns, it_name=it_name, destruct=it.destruct))

        writer("{rn}* {ns}::{it_name}::next() {{\n{advance}    return {val};\n}}\n".format(
            rn=record_type_name, ns=ns, it_name=it_name,
            advance=it.advance, val=it.advanceResults))

        writer("bool {ns}::{it_name}::hasNext() {{\n    return {val};\n}}\n".format(
            ns=ns, it_name=it_name,
            val=it.hasNext))

        writer("{ns}::{it_name} {ns}::{query_name}({args}) {{\n{proc}    return {it_name}({it_args});\n}}\n".format(
            query_name=q.name,
            ns=ns, it_name=it_name,
            proc=it.init,
            args=", ".join("{} {}".format(ty, v) for v, ty in q.vars),
            it_args=", ".join(f for f, ty in it.fields)))

    for f, ty in fields:
        # TODO: these update routines could be way better...
        writer("void {ns}::update{F}(Record* r, {ty} val) {{\n".format(ns=ns, F=capitalize(f), f=f, ty=ty))
        writer("    remove(r);\n")
        writer("    r->{f} = val;\n".format(f=f))
        writer("    add(r);\n")
        writer("}\n")

def _gen_insert(e, ty, x, record_type_name, writer):
    if type(ty) is HashMap:
        _gen_insert("{e}[{x}->{f}]".format(f=ty.fieldName, e=e, x=x), ty.ty, x, record_type_name, writer)
    elif type(ty) is SortedSet:
        v = fresh_name()
        writer("    {}& {} = {};\n".format(ty_to_cpp(ty, record_type_name), v, e))
        writer("    {v}.insert(std::upper_bound({v}.begin(), {v}.end(), {x}->{field}, {comp}()), {x});\n".format(
            x=x,
            v=v,
            field=ty.fieldName,
            comp="lt_{}".format(ty.fieldName)))
    elif type(ty) is UnsortedSet:
        writer("    {}.push_back({});\n".format(e, x))

def _gen_remove(e, ty, x, record_type_name, writer):
    if type(ty) is HashMap:
        _gen_remove("{e}[{x}->{f}]".format(f=ty.fieldName, e=e, x=x), ty.ty, x, record_type_name, writer)
    else:
        v = fresh_name()
        writer("    {ty}& {v} = {e};\n".format(ty=ty_to_cpp(ty, record_type_name), v=v, e=e))
        e = v
        # TODO: we can use binary search when the set is sorted
        pos = fresh_name()
        end = fresh_name()
        it_ty = "{}::iterator".format(ty_to_cpp(ty, record_type_name))
        writer("    {ty} {end} = {e}.end();\n".format(ty=it_ty, end=end, e=e))
        writer("    {ty} {pos} = std::find({e}.begin(), {end}, {x});\n".format(ty=it_ty, pos=pos, e=e, end=end, x=x))
        writer("    if ({pos} != {end}) {{\n".format(pos=pos, end=end))
        writer("        {e}.erase({pos});\n".format(e=e, pos=pos))
        writer("    }\n")

def new(ty, record_type_name):
    if type(ty) is HashMap:
        return "std::map< {}, {} >()".format(ty.fieldTy, ty_to_cpp(ty.ty, record_type_name))
    elif type(ty) is SortedSet or type(ty) is UnsortedSet:
        return "std::vector< {} >()".format(record_type_name)

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
    """returns an Iterator"""
    if type(plan) is plans.All:
        name = onMember(resultTy)
        if type(resultTy) is HashMap:
            return ("", "&{}".format(name))
        else:
            it = Iterator()

            begin_name = fresh_name()
            end_name   = fresh_name()

            it_ty = "{}::iterator".format(ty_to_cpp(resultTy, record_type_name))

            it.init += "    {} {}({}.begin());".format(it_ty, begin_name, name)
            it.init += "    {} {}({}.end());".format(it_ty, begin_name, name)

            it.fields = [(begin_name, it_ty), (end_name, it_ty)]

            it.advanceResults = "*({}++)".format(begin_name)
            it.hasNext = "{} == {}".format(begin_name, end_name)
            return it
    elif type(plan) is plans.Empty:
        if type(resultTy) is HashMap:
            return ("", "NULL")
        else:
            raise Exception("implement empty iterator")
    elif type(plan) is plans.HashLookup:
        t = HashMap(dict(fields)[plan.fieldName], plan.fieldName, resultTy)
        proc, r = _traverse(fields, qvars, plan.plan, record_type_name, t, onMember)

        rn = fresh_name()
        it_name = fresh_name()
        proc += "    {ty}* {rn};\n".format(ty=ty_to_cpp(resultTy, record_type_name), rn=rn)
        proc += "    if (({}) != NULL) {{\n".format(r)
        proc += "        {}::iterator {it_name} = ({})->find({});\n".format(ty_to_cpp(t, record_type_name), r, plan.varName, it_name=it_name)
        proc += "        {rn} = ({it_name} == ({map})->end()) ? NULL : (&(({it_name})->second));\n".format(ty=ty_to_cpp(resultTy, record_type_name), it_name=it_name, rn=rn, map=r)
        proc += "    } else {\n"
        proc += "        {rn} = NULL;\n".format(rn=rn)
        proc += "    }\n"

        if type(resultTy) is HashMap:
            return (proc, rn)
        else:
            return Iterator.ofIterablePtr(proc, rn, ty_to_cpp(resultTy, record_type_name))

    # elif type(plan) is plans.BinarySearch:
    #     resultTy = resultTy.unify(SortedSet(dict(fields)[plan.fieldName], plan.fieldName))
    #     p, r, pred = _traverse(fields, qvars, plan.plan, record_type_name, resultTy, onMember)

    #     rn = fresh_name()
    #     rng = fresh_name()
    #     ty = ty_to_cpp(resultTy, record_type_name)
    #     p += "    Range<{ty}::iterator>* {rn};\n".format(ty=ty, rn=rn)
    #     p += "    Range<{ty}::iterator> {rng};\n".format(ty=ty, rng=rng)
    #     p += "    if (({r}) != NULL) {{\n".format(r=r)

    #     if plan.op is plans.Eq:
    #         p += "        {rng}._begin = std::lower_bound(({r})->begin(), ({r})->end(), {var}, lt_{field}());\n".format(ty=ty, rng=rng, r=r, var=plan.varName, field=plan.fieldName)
    #         p += "        {rng}._end   = std::upper_bound(({rng})->begin(), ({r})->end(), {var}, lt_{field}());\n".format(ty=ty, rng=rng, r=r, var=plan.varName, field=plan.fieldName)
    #     elif plan.op is plans.Lt:
    #         p += "        {rng}._begin = ({r})->begin();\n".format(ty=ty, rng=rng, r=r)
    #         p += "        {rng}._end   = std::lower_bound(({r})->begin(), ({r})->end(), {var}, lt_{field}());\n".format(ty=ty, rng=rng, r=r, var=plan.varName, field=plan.fieldName)
    #     elif plan.op is plans.Le:
    #         p += "        {rng}._begin = ({r})->begin();\n".format(ty=ty, rng=rng, r=r)
    #         p += "        {rng}._end   = std::upper_bound(({r})->begin(), ({r})->end(), {var}, lt_{field}());\n".format(ty=ty, rng=rng, r=r, var=plan.varName, field=plan.fieldName)
    #     elif plan.op is plans.Gt:
    #         p += "        {rng}._begin = std::upper_bound(({r})->begin(), ({r})->end(), {var}, lt_{field}());\n".format(ty=ty, rng=rng, r=r, var=plan.varName, field=plan.fieldName)
    #         p += "        {rng}._end   = ({r})->end();\n".format(ty=ty, rng=rng, r=r)
    #     elif plan.op is plans.Ge:
    #         p += "        {rng}._begin = std::lower_bound(({r})->begin(), ({r})->end(), {var}, lt_{field}());\n".format(ty=ty, rng=rng, r=r, var=plan.varName, field=plan.fieldName)
    #         p += "        {rng}._end   = ({r})->end();\n".format(ty=ty, rng=rng, r=r)

    #     p += "        {rn} = &{rng};\n".format(rn=rn, rng=rng)
    #     p += "    } else {\n"
    #     p += "        {rn} = NULL;\n".format(rn=rn)
    #     p += "    }\n"
    #     return (p, rn, pred)
    # elif type(plan) is plans.Filter:
    #     p, r, pred = _traverse(fields, qvars, plan.plan, record_type_name, resultTy, onMember)
    #     return (p, r, lambda x: "({}) && ({})".format(pred(x), _predicate_to_exp(fields, qvars, plan.predicate, x)))
    # elif type(plan) is plans.Intersect:
    #     raise Exception("intersect codegen not implemented")
    elif type(plan) is plans.Union:
        it1 = _traverse(fields, qvars, plan.plan1, record_type_name, resultTy, onMember)
        it2 = _traverse(fields, qvars, plan.plan2, record_type_name, resultTy, onMember)

        s_ty = "std::set< {}* >".format(record_type_name)
        s_name = fresh_name()
        proc = it1.init
        proc += "    {ty}* {s} = new {ty}();\n".format(ty=s_ty, s=s_name)
        proc += "    while ({}) {{\n".format(it1.hasNext)
        proc += it1.advance
        proc += "        {}->insert({});\n".format(s_name, it1.advanceResults)
        proc += "    }\n"
        proc += it1.destruct
        proc += it2.init

        it = Iterator.ofIterablePtr(proc, s_name, s_ty);
        it.fields += it2.fields
        it.fields.append((s_name, "{}*".format(s_ty)))

        old_advance = it.advance
        old_advance_result = it.advanceResults
        old_has_next = it.hasNext

        adv_name = fresh_name()
        it.advance  = "    {}* {} = NULL;\n".format(record_type_name, adv_name)
        it.advance += "    if ({}) {{\n".format(old_has_next)
        it.advance += old_advance
        it.advance += "        {} = {};\n".format(adv_name, old_advance_result)
        it.advance += "    } else {\n"
        it.advance += it2.advance
        it.advance += "        {} = {};\n".format(adv_name, it2.advanceResults)
        it.advance += "    }\n"
        it.advanceResults = adv_name

        it.hasNext = "({}) || ({})".format(old_has_next, it2.hasNext)

        it.destruct = it2.destruct + "    delete {};\n".format(s_name)

        return it
    else:
        raise Exception("codegen not implemented for {}".format(type(plan)))
