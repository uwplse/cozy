import re
import subprocess

import codegen
import predicates
import plans
from common import capitalize, fresh_name, indent, open_maybe_stdout

class CppCodeGenerator(object):
    def __init__(self, maptype="hash"):
        self.maptype = maptype

    def map_type(self, kt, vt):
        if self.maptype == "hash":
            return "std::unordered_map < {}, {} >".format(kt.gen_type(self), vt.gen_type(self))
        if self.maptype == "tree":
            return "std::map < {}, {} >".format(kt.gen_type(self), vt.gen_type(self))
        if self.maptype == "qhash":
            return "QHash < {}, {} >".format(kt.gen_type(self), vt.gen_type(self))

    def map_handle_type(self, kt, vt):
        return "{}::iterator".format(self.map_type(kt, vt))

    def bool_type(self):
        return "bool";

    def int_type(self):
        return "int";

    def ref_type(self, ty):
        return ty.gen_type(self) if type(ty) is codegen.RecordType else "{}&".format(ty.gen_type(self));

    def vector_type(self, ty, n):
        return "{}*".format(ty.gen_type(self));

    def new_map(self, kt, vt):
        return "{}()".format(self.map_type(kt, vt))

    def map_find_handle(self, m, k, dst):
        return "{} = {}.find({});\n".format(dst, m, k)

    def map_handle_exists(self, m, handle):
        return "{} != {}.end()".format(handle, m)

    def map_read_handle(self, handle):
        if self.maptype == "hash":
            return "{}->second".format(handle)
        if self.maptype == "tree":
            return "{}->second".format(handle)
        if self.maptype == "qhash":
            return "{}.value()".format(handle)

    def map_write_handle(self, m, handle, k, v):
        if self.maptype == "hash":
            return "{}->second = {};".format(handle, v)
        if self.maptype == "tree":
            return "{}->second = {};".format(handle, v)
        if self.maptype == "qhash":
            return "{}.value() = {};".format(handle, v)

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
        return "{}*".format(self.cpp_record_class)

    def predicate(self, fields, qvars, pred, target):
        return _predicate_to_exp(fields, qvars, pred, target)

    def not_true(self, e):
        return "!({})".format(e)

    def is_null(self, e):
        return "({}) == NULL".format(e)

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
        if self.cpp_abstract_record and (m in self.fields or any(name == m for name, _, _ in self.private_members)):
            return "read_{}({})".format(m, e)
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

    def write(self, fields, queries, cpp=None, cpp_header=None, cpp_class="DataStructure", cpp_record_class="Record", cpp_abstract_record=False, cpp_extra=None, cpp_namespace=None, **kwargs):
        self.cpp_record_class = cpp_record_class
        self.cpp_abstract_record = cpp_abstract_record
        self.fields = fields

        with open_maybe_stdout(cpp) as outfile:
            with open_maybe_stdout(cpp_header) as header_outfile:
                writer = outfile.write
                header_writer = header_outfile.write

                # ---------------------------------------------------------------------
                # HEADER

                guard = "HEADER_{}".format(fresh_name())
                header_writer("#ifndef {}\n".format(guard))
                header_writer("#define {} 1\n".format(guard))
                header_writer("\n")

                if cpp_extra:
                    header_writer("{}\n".format(cpp_extra))

                if self.maptype == "hash":
                    header_writer("#include <unordered_map>\n")
                if self.maptype == "tree":
                    header_writer("#include <map>\n")
                if self.maptype == "qhash":
                    header_writer("#include <QHash>\n")

                header_writer("\n")
                if cpp_namespace is not None:
                    header_writer("namespace {} {{\n".format(cpp_namespace))

                # forward decls
                header_writer("class {};\n".format(cpp_record_class))
                header_writer("class {};\n".format(cpp_class))
                header_writer("\n")

                # auxiliary type definitions
                seen = set()
                for q in queries:
                    for t in q.impl.auxtypes():
                        _gen_aux_type_header(t, self, header_writer, cpp_class, seen)

                # record type
                private_members = []
                for q in queries:
                    private_members += list((f, ty.gen_type(self), init) for f, ty, init in q.impl.private_members(self, parent_structure=(codegen.TupleInstance("x") if cpp_abstract_record else codegen.This())))
                self.private_members = private_members
                if cpp_abstract_record:
                    for name, ty in list(fields.items()) + [(name, ty) for name, ty, _ in private_members]:
                        header_writer("inline {}& read_{}({}); /* MUST BE IMPLEMENTED BY CLIENT */\n".format(ty, name, self.record_type()))
                    for name, ty, init in private_members:
                        header_writer("inline {} init_{}({} x) {{ return {}; }}\n".format(ty, name, self.record_type(), init))
                else:
                    _gen_record_type(cpp_record_class, list(fields.items()), private_members, header_writer)
                header_writer("\n")

                header_writer("class {} {{\n".format(cpp_class))
                header_writer("public:\n")

                # constructor
                header_writer("    inline {}();\n".format(cpp_class))

                # get current size
                header_writer("    inline size_t size() const;\n")

                # add routine
                header_writer("    inline void add({} x);\n".format(self.record_type()))

                # remove routine
                header_writer("    inline void remove({} x);\n".format(self.record_type()))

                # update routines
                for f, ty in fields.items():
                    header_writer("    inline void update{}({} x, {} val);\n".format(capitalize(f), self.record_type(), ty))

                # query routines
                for q in queries:
                    it_name = "{}_iterator".format(q.name)
                    vars_needed = [(v, ty) for v, ty in q.vars if q.impl.needs_var(v)]

                    # iterator class
                    header_writer("    class {} {{\n".format(it_name))
                    header_writer("    friend class {};\n".format(cpp_class))
                    header_writer("    public:\n")
                    header_writer("        inline bool hasNext();\n")
                    header_writer("        inline {}* next();\n".format(cpp_record_class))
                    header_writer("        inline void remove();\n")
                    header_writer("    private:\n")
                    state = q.impl.state()
                    header_writer("        {}* parent;\n".format(cpp_class))
                    vars_needed = [(v, ty) for v, ty in q.vars if q.impl.needs_var(v)]
                    for v, ty in vars_needed:
                        header_writer("        {} {};\n".format(ty, v))
                    for f, ty in state:
                        header_writer("        {} {};\n".format(ty.gen_type(self), f))
                    header_writer("        inline {}({}* parent{}{});\n".format(it_name, cpp_class, "".join(", {} {}".format(ty, v) for v, ty in vars_needed), "".join(", {} {}".format(ty.gen_type(self), f) for f, ty in state)))
                    header_writer("    };\n")

                    # query method
                    header_writer("    inline {} {}({});\n".format(it_name, q.name, ", ".join("{} {}".format(ty, v) for v,ty in q.vars)))

                # private members
                header_writer("private:\n")
                header_writer("    size_t my_size;\n")
                for q in queries:
                    for f, ty in q.impl.fields():
                        header_writer("    {} {};\n".format(ty.gen_type(self), f))

                header_writer("};\n")

                if cpp_namespace is not None:
                    header_writer("}\n")

                header_writer("\n")

                # ---------------------------------------------------------------------
                # CODE

                name = cpp_class if cpp_namespace is None else "{}::{}".format(cpp_namespace, cpp_class)

                # writer("#include \"DataStructure.hpp\"\n")
                writer = header_writer

                # constructor
                writer("{}::{}() {{\n".format(name, cpp_class))
                for q in queries:
                    writer(indent("    ", q.impl.construct(self)))
                writer("}\n")

                # size
                writer("size_t {}::size() const {{ return my_size; }}\n".format(name, cpp_class))

                # add routine
                writer("void {}::add({} x) {{\n".format(name, self.record_type()))
                writer("    ++my_size;")
                for q in queries:
                    writer(indent("    ", q.impl.gen_insert(self, "x")))
                writer("}\n")

                # remove routine
                writer("void {}::remove({} x) {{\n".format(name, self.record_type()))
                writer("    --my_size;")
                for q in queries:
                    writer(indent("    ", q.impl.gen_remove(self, "x")))
                writer("}\n")

                # update routines
                for f, ty in fields.items():
                    writer("void {}::update{}({} x, {} val) {{\n".format(name, capitalize(f), self.record_type(), ty))
                    writer("    if ({} != val) {{\n".format(self.get_field("x", f)))
                    for q in queries:
                        writer(indent("        ", q.impl.gen_update(self, fields, f, "x", "val")))
                    writer("        {} = val;\n".format(self.get_field("x", f)))
                    writer("    }")
                    writer("}\n")

                # query routines
                for q in queries:
                    vars_needed = [(v, ty) for v, ty in q.vars if q.impl.needs_var(v)]
                    state = q.impl.state()

                    # query call
                    writer("{prefix}::{q}_iterator {prefix}::{q}({}) {{\n".format(", ".join("{} {}".format(ty, v) for v,ty in q.vars), prefix=name, q=q.name))
                    proc, stateExps = q.impl.gen_query(self, q.vars)
                    writer(indent("    ", proc))
                    writer("    return {}_iterator(this{}{});".format(q.name, "".join(", {}".format(v) for v, ty in vars_needed), "".join(", {}".format(e) for e in stateExps)))
                    writer("  }\n")

                    # iterator constructor
                    writer("{prefix}::{q}_iterator::{q}_iterator({}* _parent{}{}) :\n".format(cpp_class, "".join(", {} _{}".format(ty, v) for v, ty in vars_needed), "".join(", {} _{}".format(ty.gen_type(self), f) for f, ty in state), prefix=name, q=q.name))
                    writer("  parent(_parent){}{}\n".format("".join(", {f}(_{f})".format(f=v) for v, ty in vars_needed), "".join(", {f}(_{f})".format(f=v) for v, ty in state)))
                    writer("{ }\n")

                    # hasNext
                    writer("bool {prefix}::{q}_iterator::hasNext() {{\n".format(cpp_class, "".join(", {} {}".format(ty, v) for v, ty in vars_needed), "".join(", {} _{}".format(ty.gen_type(self), f) for f, ty in state), prefix=name, q=q.name))
                    proc, ret = q.impl.gen_has_next(self)
                    writer(indent("    ", proc))
                    writer("    return {};\n".format(ret))
                    writer("}\n")

                    # next
                    writer("{} {prefix}::{q}_iterator::next() {{\n".format(self.record_type(), cpp_class, "".join(", {} {}".format(ty, v) for v, ty in vars_needed), "".join(", {} _{}".format(ty.gen_type(self), f) for f, ty in state), prefix=name, q=q.name))
                    proc, ret = q.impl.gen_next(self)
                    writer(indent("    ", proc))
                    writer("    return {};\n".format(ret))
                    writer("}\n")

                    # remove
                    writer("void {prefix}::{q}_iterator::remove() {{\n".format(cpp_class, "".join(", {} {}".format(ty, v) for v, ty in vars_needed), "".join(", {} _{}".format(ty.gen_type(self), f) for f, ty in state), prefix=name, q=q.name))
                    writer("    --(parent->my_size);\n")
                    proc, removed = q.impl.gen_remove_in_place(self, codegen.TupleInstance("parent"))
                    writer(indent("    ", proc))
                    for q2 in queries:
                        if q2 != q:
                            writer(indent("    ", q2.impl.gen_remove(self, removed, parent_structure=codegen.TupleInstance("parent"))))
                    writer("}\n")

                header_writer("#endif\n")

    def supports_cost_model_file(self, f):
        return f.endswith(".cpp") or f.endswith(".cxx")

    def dynamic_cost(self, fields, queries, impls, cost_model_file):
        for q, i in zip(queries, impls):
            q.impl = i

        self.write(fields, queries,
            cpp_class="DataStructure",
            cpp="/tmp/DataStructure.cpp",
            cpp_header="/tmp/DataStructure.hpp")

        flags = ["-DQT_SHARED", "-I/usr/local/Cellar/qt/4.8.7_1/include", "-I/usr/local/Cellar/qt/4.8.7_1/include/QtGui", "-I/usr/local/Cellar/qt/4.8.7_1/include", "-I/usr/local/Cellar/qt/4.8.7_1/include/QtCore", "-F/usr/local/Cellar/qt/4.8.7_1/lib", "-framework", "QtGui", "-F/usr/local/Cellar/qt/4.8.7_1/lib", "-framework", "QtCore"]
        ret = subprocess.call(["c++", "-O2", "-I/tmp", "/tmp/DataStructure.cpp", cost_model_file, "-o", "/tmp/a.out"] + flags)
        assert ret == 0

        proc = subprocess.Popen(["/tmp/a.out"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        stdout, stdin = proc.communicate()
        assert proc.returncode == 0

        score = long(stdout.strip())
        return score


def _gen_aux_type_header(ty, gen, writer, class_name, seen):
    if ty in seen:
        return
    seen.add(ty)
    if type(ty) is codegen.TupleTy:
        for _, t in ty.fields.items():
            _gen_aux_type_header(t, gen, writer, class_name, seen)
        writer("class {} {{\n".format(ty.name))
        writer("friend class {};\n".format(class_name))
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
