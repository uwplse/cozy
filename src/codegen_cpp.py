import re

import codegen
import predicates
import plans
from common import capitalize, fresh_name, indent

RECORD_NAME = "Record"

class CppCodeGenerator(object):
    def __init__(self, header_writer, code_writer, class_name="DataStructure", namespace=None, header_extra=None):
        self.header_writer = header_writer
        self.writer = code_writer
        self.class_name = class_name
        self.namespace = namespace
        self.header_extra = header_extra

    def map_type(self, kt, vt):
        return "std::unordered_map < {}, {} >".format(kt.gen_type(self), vt.gen_type(self))

    def map_handle_type(self, kt, vt):
        return "{}::iterator".format(self.map_type(kt, vt))

    def bool_type(self):
        return "bool";

    def int_type(self):
        return "int";

    def ref_type(self, ty):
        return "{}&".format(ty.gen_type(self));

    def vector_type(self, ty, n):
        return "{}*".format(ty.gen_type(self));

    def new_map(self, kt, vt):
        return "std::unordered_map < {}, {} > ()".format(kt.gen_type(self), vt.gen_type(self))

    def map_find_handle(self, m, k, dst):
        return "{} = {}.find({});\n".format(dst, m, k)

    def map_handle_exists(self, m, handle):
        return "{} != {}.end()".format(handle, m)

    def map_read_handle(self, handle):
        return "{}->second".format(handle)

    def map_write_handle(self, m, handle, k, v):
        return "{}->second = {};\n".format(handle, v)

    def map_put(self, m, k, v):
        return "{}[{}] = {};\n".format(m, k, v)

    def new_vector(self, ty, n):
        return "new {}[{}]".format(ty.gen_type(self), n)

    def vector_get(self, v, i):
        return "{}[{}]".format(v, i)

    def vector_set(self, v, i, x):
        return "{}[{}] = {};\n".format(v, i, x)

    def native_type(self, t):
        return t

    def record_type(self):
        return "{}*".format(RECORD_NAME)

    def predicate(self, fields, qvars, pred, target):
        return _predicate_to_exp(fields, qvars, pred, target)

    def not_true(self, e):
        return "!({})".format(e)

    def is_null(self, e):
        return "!({})".format(e)

    def ternary(self, cond, v1, v2):
        return "({}) ? ({}) : ({})".format(cond, v1, v2)

    def same(self, e1, e2):
        return "({}) == ({})".format(e1, e2)

    def lt(self, ty, e1, e2):
        return "({}) < ({})".format(e1, e2)

    def le(self, ty, e1, e2):
        return "({}) <= ({})".format(e1, e2)

    def gt(self, ty, e1, e2):
        return "({}) > ({})".format(e1, e2)

    def ge(self, ty, e1, e2):
        return "({}) >= ({})".format(e1, e2)

    def add(self, e1, e2):
        return "({}) + ({})".format(e1, e2)

    def mul(self, e1, e2):
        return "({}) * ({})".format(e1, e2)

    def init_new(self, target, ty):
        return self.set(target, "{}()".format(ty.gen_type(self)))

    def null_value(self):
        return "NULL"

    def true_value(self):
        return "true";

    def false_value(self):
        return "false";

    def get_field(self, e, m):
        if e is None:
            return m
        return "({})->{}".format(e, m)

    def both(self, e1, e2):
        return "({}) && ({})".format(e1, e2)

    def either(self, e1, e2):
        return "({}) || ({})".format(e1, e2)

    def decl(self, v, ty, e=None):
        if e is not None:
            return "{} {} = {};\n".format(ty.gen_type(self), v, e)
        return "{} {};\n".format(ty.gen_type(self), v)

    def set(self, lval, e):
        return "{} = {};\n".format(lval, e)

    def if_true(self, e):
        return "if ({}) {{\n".format(e)

    def else_if(self, e):
        return "}} else if ({}) {{\n".format(e)

    def else_true(self):
        return "} else {\n"

    def endif(self):
        return "}\n"

    def while_true(self, e):
        return "while ({}) {{\n".format(e)

    def endwhile(self):
        return "}\n"

    def do_while(self):
        return "do {\n"

    def end_do_while(self, e):
        return "}} while ({});\n".format(e)

    def break_loop(self):
        return "break;\n"

    def comment(self, text):
        return " /* {} */ ".format(text)

    def write(self, fields, queries):

        # ---------------------------------------------------------------------
        # HEADER

        guard = "HEADER_{}".format(fresh_name())
        self.header_writer("#ifndef {}\n".format(guard))
        self.header_writer("#define {} 1\n".format(guard))
        self.header_writer("\n")

        if self.header_extra:
            self.header_writer("{}\n".format(self.header_extra))

        self.header_writer("#include <unordered_map>\n")
        self.header_writer("\n")
        if self.namespace is not None:
            self.header_writer("namespace {} {{\n".format(self.namespace))

        # forward decls
        self.header_writer("class Record;\n")
        self.header_writer("class {};\n".format(self.class_name))
        self.header_writer("\n")

        # auxiliary type definitions
        seen = set()
        for q in queries:
            for t in q.impl.auxtypes():
                _gen_aux_type_header(t, self, self.header_writer, seen)

        # record type
        private_members = []
        for q in queries:
            private_members += list((f, ty.gen_type(self), init) for f, ty, init in q.impl.private_members(self))
        _gen_record_type(RECORD_NAME, list(fields.items()), private_members, self.header_writer)
        self.header_writer("\n")

        self.header_writer("class {} {{\n".format(self.class_name))
        self.header_writer("public:\n")

        # constructor
        self.header_writer("    {}();\n".format(self.class_name))

        # add routine
        self.header_writer("    void add({} x);\n".format(self.record_type()))

        # remove routine
        self.header_writer("    void remove({} x);\n".format(self.record_type()))

        # update routines
        for f, ty in fields.items():
            self.header_writer("    void update{}({} x, {} val);".format(capitalize(f), self.record_type(), ty))

        # query routines
        for q in queries:
            it_name = "{}_iterator".format(q.name)
            vars_needed = [(v, ty) for v, ty in q.vars if q.impl.needs_var(v)]

            # iterator class
            self.header_writer("    class {} {{\n".format(it_name, RECORD_NAME))
            self.header_writer("    friend class DataStructure;\n")
            self.header_writer("    public:\n")
            self.header_writer("        bool hasNext();\n")
            self.header_writer("        Record* next();\n")
            self.header_writer("        void remove();\n")
            self.header_writer("    private:\n")
            state = q.impl.state()
            self.header_writer("        {}* parent;\n".format(self.class_name))
            vars_needed = [(v, ty) for v, ty in q.vars if q.impl.needs_var(v)]
            for v, ty in vars_needed:
                self.header_writer("        {} {};\n".format(ty, v))
            for f, ty in state:
                self.header_writer("        {} {};\n".format(ty.gen_type(self), f))
            self.header_writer("        {}({}* parent{}{});\n".format(it_name, self.class_name, "".join(", {} {}".format(ty, v) for v, ty in vars_needed), "".join(", {} {}".format(ty.gen_type(self), f) for f, ty in state)))
            self.header_writer("    };\n")

            # query method
            self.header_writer("    {} {}({});\n".format(it_name, q.name, ", ".join("{} {}".format(ty, v) for v,ty in q.vars)))

        # private members
        self.header_writer("private:\n")
        for q in queries:
            for f, ty in q.impl.fields():
                self.header_writer("    {} {};\n".format(ty.gen_type(self), f))

        self.header_writer("};\n")

        if self.namespace is not None:
            self.header_writer("}\n")

        self.header_writer("\n")
        self.header_writer("#endif\n")

        # ---------------------------------------------------------------------
        # CODE

        name = self.class_name if self.namespace is None else "{}::{}".format(self.namespace, self.class_name)

        self.writer("#include \"DataStructure.hpp\"\n")

        self.writer("template <class K, class V>\n")
        self.writer("inline V* mapget(const std::unordered_map<K, V*>& m, const K& k) {\n")
        self.writer("    typename std::unordered_map<K, V*>::const_iterator it(m.find(k));\n")
        self.writer("    return it == m.end() ? NULL : it->second;\n")
        self.writer("}\n")

        # constructor
        self.writer("{}::{}() {{\n".format(name, self.class_name))
        for q in queries:
            self.writer(indent("    ", q.impl.construct(self)))
        self.writer("}\n")

        # add routine
        self.writer("void {}::add({} x) {{\n".format(name, self.record_type()))
        for q in queries:
            self.writer(indent("    ", q.impl.gen_insert(self, "x")))
        self.writer("}\n")

        # remove routine
        self.writer("void {}::remove({} x) {{\n".format(name, self.record_type()))
        for q in queries:
            self.writer(indent("    ", q.impl.gen_remove(self, "x")))
        self.writer("}\n")

        # update routines
        # TODO: make this implementation efficient
        for f, ty in fields.items():
            self.writer("void {}::update{}({} x, {} val) {{\n".format(name, capitalize(f), self.record_type(), ty))
            self.writer("    if (x->{} != val) {{\n".format(f))
            for q in queries:
                self.writer(indent("        ", q.impl.gen_update(self, fields, f, "x", "val")))
            self.writer("        x->{} = val;\n".format(f))
            self.writer("    }")
            self.writer("}\n")

        # query routines
        for q in queries:
            vars_needed = [(v, ty) for v, ty in q.vars if q.impl.needs_var(v)]
            state = q.impl.state()

            # query call
            self.writer("{prefix}::{q}_iterator {prefix}::{q}({}) {{\n".format(", ".join("{} {}".format(ty, v) for v,ty in q.vars), prefix=name, q=q.name))
            proc, stateExps = q.impl.gen_query(self, q.vars)
            self.writer(indent("    ", proc))
            self.writer("    return {}_iterator(this{}{});".format(q.name, "".join(", {}".format(v) for v, ty in vars_needed), "".join(", {}".format(e) for e in stateExps)))
            self.writer("  }\n")

            # iterator constructor
            self.writer("{prefix}::{q}_iterator::{q}_iterator({}* _parent{}{}) :\n".format(self.class_name, "".join(", {} {}".format(ty, v) for v, ty in vars_needed), "".join(", {} _{}".format(ty.gen_type(self), f) for f, ty in state), prefix=name, q=q.name))
            self.writer("  parent(_parent){}{}\n".format("".join(", {f}(_{f})".format(f=v) for v, ty in vars_needed), "".join(", {f}(_{f})".format(f=v) for v, ty in state)))
            self.writer("{ }\n")

            # hasNext
            self.writer("bool {prefix}::{q}_iterator::hasNext() {{\n".format(self.class_name, "".join(", {} {}".format(ty, v) for v, ty in vars_needed), "".join(", {} _{}".format(ty.gen_type(self), f) for f, ty in state), prefix=name, q=q.name))
            proc, ret = q.impl.gen_has_next(self)
            self.writer(indent("    ", proc))
            self.writer("    return {};\n".format(ret))
            self.writer("}\n")

            # next
            self.writer("{} {prefix}::{q}_iterator::next() {{\n".format(self.record_type(), self.class_name, "".join(", {} {}".format(ty, v) for v, ty in vars_needed), "".join(", {} _{}".format(ty.gen_type(self), f) for f, ty in state), prefix=name, q=q.name))
            proc, ret = q.impl.gen_next(self)
            self.writer(indent("    ", proc))
            self.writer("    return {};\n".format(ret))
            self.writer("}\n")

def _gen_aux_type_header(ty, gen, writer, seen):
    if ty in seen:
        return
    seen.add(ty)
    if type(ty) is codegen.TupleTy:
        for _, t in ty.fields.items():
            _gen_aux_type_header(t, gen, writer, seen)
        writer("class {} {{\n".format(ty.name))
        writer("friend class {};\n".format(gen.class_name))
        for f, t in ty.fields.items():
            writer("    {} {};\n".format(t.gen_type(gen), f))
        writer("    inline {}* operator->() {{ return this; }}\n".format(ty.name))
        writer("public:\n")
        writer("    bool operator<(const {t}& y) const {{\n".format(t=ty.name))
        for f, t in ty.fields.items():
            writer("        if ({f} <  y.{f}) return true;\n".format(f=f))
            writer("        if ({f} != y.{f}) return false;\n".format(f=f))
        writer("        return false;\n")
        writer("    }\n")
        writer("};\n")

def _gen_record_type(name, fields, private_fields, writer):
    all_fields = [(f, ty, "_{}".format(f)) for f, ty in fields] + list(private_fields)
    writer("class {} {{\n".format(name))
    writer("friend class DataStructure;\n")
    writer("public:\n")
    for f,ty in fields:
        writer("    {} {};\n".format(ty, f))
    writer("private:\n")
    for f,ty,_ in private_fields:
        writer("    {} {};\n".format(ty, f))
    writer("public:\n")
    writer("    {name}({args}) : {init} {{ }}\n".format(
        name=name,
        args=", ".join("{ty} _{f}".format(f=f, ty=ty) for f, ty in fields),
        init=", ".join("{f}({init})".format(f=f, init=init) for f, _, init in all_fields)))
    writer("};\n")

def _predicate_to_exp(fields, qvars, pred, target):
    if type(pred) is predicates.Var:
        return pred.name if pred.name in {v for v,ty in qvars} else "{}->{}".format(target, pred.name)
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
