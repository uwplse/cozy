import re
import subprocess

import codegen
import abstract_types
import predicates
import plans
import structures
from structures.interface import This, TupleInstance, TupleTy, RecordType, MapTy, NativeTy
from common import capitalize, fresh_name, indent, open_maybe_stdout

USE_QT = False # TODO: make this an option

class STLMapTy(MapTy):
    def gen_type(self, gen):
        return "std::map < {}, {} >".format(self.keyTy.gen_type(gen), self.valTy.gen_type(gen))

class QHashMapTy(MapTy):
    def gen_type(self, gen):
        return "QHash < {}, {} >".format(self.keyTy.gen_type(gen), self.valTy.gen_type(gen))

class STLMap(structures.HashMap):
    def fields(self):
        return ((self.name, STLMapTy(self.keyTy, self.valueTy)),)
    def construct(self, gen, parent_structure):
        return "" # default initialization is fine
    def handle_type(self, gen):
        return NativeTy("std::map < {}, {} >::iterator".format(self.keyTy.gen_type(gen), self.valueTy.gen_type(gen)))

class QHashMap(structures.HashMap):
    def fields(self):
        return ((self.name, QHashMapTy(self.keyTy, self.valueTy)),)
    def construct(self, gen, parent_structure):
        return "" # default initialization is fine
    def handle_type(self, gen):
        return NativeTy("QHash < {}, {} >::iterator".format(self.keyTy.gen_type(gen), self.valueTy.gen_type(gen)))
    def read_handle(self, gen, m, handle):
        return "{}.value()".format(handle)
    def write_handle(self, gen, m, handle, k, v):
        return "{}.value() = {};\n".format(handle, v)

class CppCodeGenerator(object):
    def __str__(self):
        return "CppCodeGenerator"

    def map_type(self, kt, vt):
        return "std::unordered_map < {}, {} >".format(kt.gen_type(self), vt.gen_type(self))

    def map_handle_type(self, kt, vt):
        return "{}::iterator".format(self.map_type(kt, vt))

    def bool_type(self):
        return "bool";

    def int_type(self):
        return "int";

    def ref_type(self, ty):
        return ty.gen_type(self) if type(ty) is RecordType else "{}&".format(ty.gen_type(self));

    def ptr_type(self, ty):
        return ty.gen_type(self) if type(ty) is RecordType else "{}*".format(ty.gen_type(self));

    def stack_type(self, ty):
        return "mystk < {} >".format(ty.gen_type(self))

    def vector_type(self, ty, n):
        return "{}*".format(ty.gen_type(self))

    def alloc(self, t, args):
        return "new {}({})".format(t.gen_type(self), ", ".join(args))

    def free(self, x):
        return "delete {};\n".format(x)

    def new_map(self, kt, vt):
        return "{}()".format(self.map_type(kt, vt))

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

    def new_stack(self, t):
        return "{}()".format(self.stack_type(t))

    def stack_push(self, stk, x):
        return "{}.push_back({});\n".format(stk, x)

    def stack_peek(self, stk):
        return "{}.back()".format(stk)

    def stack_size_hint(self, stk, n):
        return "{}.reserve({});\n".format(stk, n)

    def stack_pop(self, stk):
        return "{}.pop_back();\n".format(stk)

    def stack_is_empty(self, stk):
        return "{}.empty()".format(stk)

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
        return _predicate_to_exp(self, fields, qvars, pred, target)

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

    def sub(self, e1, e2):
        return "({}) - ({})".format(e1, e2)

    def mul(self, e1, e2):
        return "({}) * ({})".format(e1, e2)

    def abs(self, e):
        return "std::abs({})".format(e)

    def min(self, t, e1, e2):
        return "std::min({}, {})".format(e1, e2)

    def max(self, t, e1, e2):
        return "std::max({}, {})".format(e1, e2)

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
        if self.cpp_abstract_record and m in self.fields:
            return "read_{}({})".format(m, e)
        if self.cpp_abstract_record and any(name == m for name, _ in self.private_members):
            return "read_private_data({}).{}".format(e, m)
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

    def assert_true(self, e):
        return "assert({});\n".format(e)

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

                header_writer("#include <cassert>\n")
                header_writer("#include <ctgmath>\n")
                # header_writer("#include <vector>\n")
                header_writer("#include <unordered_map>\n")
                header_writer("#include <map>\n")

                if USE_QT:
                    header_writer("#include <QHash>\n")

                header_writer("""

                    #include <cstdint>

                    template <class T>
                    class mystk {
                        int32_t _end;
                        static int32_t _cap;
                        static T* _data;
                    public:
                        mystk() : _end(-1) { }
                        void reserve(size_t n) { }
                        bool empty() { return _end < 0; }
                        T& back() { return _data[_end]; }
                        void push_back(const T& x) {
                            ++_end;
                            if (_end >= _cap) {
                                _cap *= 2;
                                T* newdata = new T[_cap];
                                std::copy(_data, _data + _end, newdata);
                                delete[] _data;
                                _data = newdata;
                            }
                            // printf("inserting %p @ %d\\n", x, (int)_end);
                            _data[_end] = x;
                        }
                        void pop_back() { --_end; }
                    };

                    template<class T> int32_t mystk<T>::_cap = 10;
                    template<class T> T*      mystk<T>::_data = new T[10];

                """)

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
                        _gen_aux_type_fwd_decl(t, self, header_writer, seen)
                seen = set()
                for q in queries:
                    for t in q.impl.auxtypes():
                        _gen_aux_type_header(t, self, header_writer, cpp_class, seen)

                # record type
                private_members = []
                for q in queries:
                    private_members += list((f, ty.gen_type(self)) for f, ty in q.impl.private_members())
                self.private_members = private_members
                if cpp_abstract_record:
                    header_writer("struct PrivateData {\n")
                    for name, ty in private_members:
                        header_writer("    {} {};\n".format(ty, name))
                    header_writer("};\n")
                    for name, ty in list(fields.items()):
                        header_writer("inline {}& read_{}({}); /* MUST BE IMPLEMENTED BY CLIENT */\n".format(ty, name, self.record_type()))
                    header_writer("inline PrivateData& read_private_data({}); /* MUST BE IMPLEMENTED BY CLIENT */\n".format(self.record_type()))
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
                header_writer("    inline void update({} x, {});\n".format(self.record_type(), ", ".join("{} {}".format(ty, f) for f, ty in fields.items())))

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

                # debugging
                header_writer("    inline void checkRep();\n")

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
                writer("{}::{}() : my_size(0) {{\n".format(name, cpp_class))
                for q in queries:
                    writer(indent("    ", q.impl.construct(self, This())))
                writer("}\n")

                # size
                writer("size_t {}::size() const {{ return my_size; }}\n".format(name, cpp_class))

                # add routine
                writer("void {}::add({} x) {{\n".format(name, self.record_type()))
                writer("    ++my_size;\n")
                for q in queries:
                    writer(indent("    ", q.impl.gen_insert(self, "x", This())))
                writer("}\n")

                # remove routine
                writer("void {}::remove({} x) {{\n".format(name, self.record_type()))
                writer("    --my_size;\n")
                for q in queries:
                    writer(indent("    ", q.impl.gen_remove(self, "x", This())))
                writer("}\n")

                # update routines
                for f, ty in fields.items():
                    writer("void {}::update{}({} x, {} val) {{\n".format(name, capitalize(f), self.record_type(), ty))
                    writer("    if ({} != val) {{\n".format(self.get_field("x", f)))
                    for q in queries:
                        writer(indent("        ", q.impl.gen_update(self, fields, "x", {f: "val"}, This())))
                    writer("        {} = val;\n".format(self.get_field("x", f)))
                    writer("    }")
                    writer("}\n")
                writer("void {}::update({} x, {}) {{\n".format(name, self.record_type(), ", ".join("{} {}".format(ty, f) for f, ty in fields.items())))
                for q in queries:
                    writer(indent("        ", q.impl.gen_update(self, fields, "x", {f:f for f in fields}, This())))
                for f, ty in fields.items():
                    writer("        {} = {};\n".format(self.get_field("x", f), f))
                writer("}\n")


                # query routines
                for q in queries:
                    vars_needed = [(v, ty) for v, ty in q.vars if q.impl.needs_var(v)]
                    state = q.impl.state()

                    # query call
                    writer("{prefix}::{q}_iterator {prefix}::{q}({}) {{\n".format(", ".join("{} {}".format(ty, v) for v,ty in q.vars), prefix=name, q=q.name))
                    proc, stateExps = q.impl.gen_query(self, q.vars, This())
                    writer(indent("    ", proc))
                    writer("    return {}_iterator(this{}{});\n".format(q.name, "".join(", {}".format(v) for v, ty in vars_needed), "".join(", {}".format(e) for e in stateExps)))
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
                    proc, removed = q.impl.gen_remove_in_place(self, TupleInstance("parent"))
                    writer(indent("    ", proc))
                    for q2 in queries:
                        if q2 != q:
                            writer(indent("    ", q2.impl.gen_remove(self, removed, parent_structure=TupleInstance("parent"))))
                    writer("}\n")

                writer("void {}::checkRep() {{\n".format(name))
                for q in queries:
                    writer(indent("    ", q.impl.check_rep(self, This())))
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

        if USE_QT:
            flags = "-DQT_SHARED -I/usr/local/Cellar/qt/4.8.7_2/include -I/usr/local/Cellar/qt/4.8.7_2/include/QtGui -I/usr/local/Cellar/qt/4.8.7_2/include -I/usr/local/Cellar/qt/4.8.7_2/include/QtCore -F/usr/local/Cellar/qt/4.8.7_2/lib -framework QtGui -F/usr/local/Cellar/qt/4.8.7_2/lib -framework QtCore".split()
        else:
            flags = []
        ret = subprocess.call(["c++", "-O2", "-I/tmp", "/tmp/DataStructure.cpp", cost_model_file, "-o", "/tmp/a.out"] + flags)
        assert ret == 0

        proc = subprocess.Popen(["/tmp/a.out"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        stdout, stdin = proc.communicate()
        assert proc.returncode == 0

        score = long(stdout.strip())
        return score

    def extensions(self, old):
        map_types = [STLMap]
        if USE_QT:
            map_types.append(QHashMap)
        def f(aimpl):
            for x in old(aimpl):
                yield x
            if type(aimpl) is abstract_types.Bucketed:
                for maptype in map_types:
                    for impl in old(aimpl.value_impl):
                        if aimpl.enum_p and aimpl.rest_p:
                            m = maptype(aimpl.fields, predicates.conjunction(aimpl.rest_p), impl)
                            yield structures.VectorMap(aimpl.fields, predicates.conjunction(aimpl.enum_p), m)
                        elif aimpl.rest_p: # aimpl.rest_p
                            yield maptype(aimpl.fields, predicates.conjunction(aimpl.rest_p), impl)
        return f

def _gen_aux_type_fwd_decl(ty, gen, writer, seen):
    if ty in seen:
        return
    seen.add(ty)
    if type(ty) is TupleTy:
        writer("class {};\n".format(ty.name))

def _gen_aux_type_header(ty, gen, writer, class_name, seen):
    if ty in seen:
        return
    seen.add(ty)
    if type(ty) is TupleTy:
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
    all_fields = [(f, ty, "_{}".format(f)) for f, ty in fields] + [(f, ty, "") for f, ty in private_fields]
    writer("class {} {{\n".format(name))
    writer("friend class DataStructure;\n")
    writer("public:\n")
    for f,ty in fields:
        writer("    {} {};\n".format(ty, f))
    writer("private:\n")
    for f,ty in private_fields:
        writer("    {} {};\n".format(ty, f))
    writer("public:\n")
    writer("    {name}({args}) : {init} {{ }}\n".format(
        name=name,
        args=", ".join("{ty} _{f}".format(f=f, ty=ty) for f, ty in fields),
        init=", ".join("{f}({init})".format(f=f, init=init) for f, _, init in all_fields)))
    writer("};\n")

def _predicate_to_exp(gen, fields, qvars, pred, target):
    if type(pred) is predicates.Var:
        return pred.name if pred.name in {v for v,ty in qvars} else gen.get_field(target, pred.name)
    elif type(pred) is predicates.Bool:
        return "true" if pred.val else "false"
    elif type(pred) is predicates.Compare:
        return "({}) {} ({})".format(
            _predicate_to_exp(gen, fields, qvars, pred.lhs, target),
            predicates.opToStr(pred.op),
            _predicate_to_exp(gen, fields, qvars, pred.rhs, target))
    elif type(pred) is predicates.And:
        return "({}) && ({})".format(
            _predicate_to_exp(gen, fields, qvars, pred.lhs, target),
            _predicate_to_exp(gen, fields, qvars, pred.rhs, target))
    elif type(pred) is predicates.Or:
        return "({}) || ({})".format(
            _predicate_to_exp(gen, fields, qvars, pred.lhs, target),
            _predicate_to_exp(gen, fields, qvars, pred.rhs, target))
    elif type(pred) is predicates.Not:
        return "!({})".format(_predicate_to_exp(gen, fields, qvars, pred.p, target))
