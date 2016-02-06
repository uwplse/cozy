import re
import tempfile
import os
import subprocess

import codegen
import predicates
import plans
from structures.interface import TupleTy, This, TupleInstance, IntTy
from common import capitalize, fresh_name, indent, open_maybe_stdout

class JavaCodeGenerator(object):
    def __str__(self):
        return "JavaCodeGenerator"

    def map_type(self, kt, vt):
        return "java.util.Map<{}, {}>".format(_box(kt.gen_type(self)), vt.gen_type(self))

    def map_handle_type(self, kt, vt):
        return vt.gen_type(self)

    def stack_type(self, t):
        return "java.util.Deque<{}>".format(t.gen_type(self))

    def ref_type(self, ty):
        return ty.gen_type(self)

    def bool_type(self):
        return "boolean";

    def int_type(self):
        return "int";

    def ptr_type(self, t):
        return t.gen_type(self)

    def vector_type(self, ty, n):
        return self.array_type(ty)

    def array_type(self, ty):
        return "{}[]".format(ty.gen_type(self))

    def new_array(self, ty, count):
        return "new {}[{}]".format(ty.gen_type(self), count)

    def array_get(self, a, n):
        return "{}[{}]".format(a, n)

    def array_set(self, a, n, v):
        return "{}[{}] = {};\n".format(a, n, v)

    def array_size(self, a):
        return "{}.length".format(a)

    # def array_realloc(self, ty, a, new_size):
    #     a2 = fresh_name("a")
    #     proc = ""
    #     proc += self.decl(a2, self.array_type(ty), self.new_array(ty, new_size))
    #     proc += "System.arraycopy({}, 0, {}, 0, {});\n".format(a, a2, self.min(IntTy(), self.array_size(a), new_size))
    #     proc += self.set(a, a2)
    #     return proc

    def data_structure_size(self):
        return "my_size" # massive hack

    def alloc(self, ty, args):
        return "new {}({})".format(ty.gen_type(self), ", ".join(args))

    def free(self, x):
        return ""

    def min(self, ty, x, y):
        return "({x} < {y}) ? {x} : {y}".format(x=x, y=y) if _is_primitive(ty.gen_type(self)) else "({x}.compareTo({y}) < 0) ? {x} : {y}".format(x=x, y=y)

    def max(self, ty, x, y):
        return "({x} < {y}) ? {y} : {x}".format(x=x, y=y) if _is_primitive(ty.gen_type(self)) else "({x}.compareTo({y}) < 0) ? {y} : {x}".format(x=x, y=y)

    def new_map(self, kt, vt):
        return "new java.util.HashMap<{}, {}>()".format(_box(kt.gen_type(self)), vt.gen_type(self))

    def map_find_handle(self, m, k, dst):
        return "{} = {}.get({});\n".format(dst, m, k)

    def map_handle_exists(self, m, handle):
        return "{} != null".format(handle)

    def map_read_handle(self, handle):
        return handle

    def map_write_handle(self, m, handle, k, v):
        return self.map_put(m, k, v)

    def map_put(self, m, k, v):
        return "{}.put({}, {});\n".format(m, k, v)

    def new_stack(self, t):
        return "new java.util.ArrayDeque<{}>()".format(t.gen_type(self))

    def stack_size_hint(self, stk, n):
        return ""

    def stack_is_empty(self, stk):
        return "{}.isEmpty()".format(stk)

    def stack_push(self, stk, x):
        return "{}.push({});\n".format(stk, x)

    def stack_pop(self, stk):
        return "{}.pop();\n".format(stk)

    def stack_peek(self, stk):
        return "{}.peek()".format(stk)

    def new_vector(self, ty, n):
        return "({}[])(new Object[{}])".format(ty.gen_type(self), n)

    def vector_get(self, v, i):
        return "{}[{}]".format(v, i)

    def vector_set(self, v, i, x):
        return "{}[{}] = {};\n".format(v, i, x)

    def native_type(self, t):
        return t

    def record_type(self):
        return "Record"

    def predicate(self, fields, qvars, pred, target):
        return _predicate_to_exp(fields, qvars, pred, target)

    def not_true(self, e):
        return "!({})".format(e)

    def is_null(self, e):
        return "({}) == null".format(e)

    def ternary(self, cond, v1, v2):
        return "({}) ? ({}) : ({})".format(cond, v1, v2)

    def same(self, e1, e2):
        return "({}) == ({})".format(e1, e2)

    def lt(self, ty, e1, e2):
        return ("({}) < ({})" if _is_primitive(ty.gen_type(self)) else "({}).compareTo({}) < 0").format(e1, e2)

    def le(self, ty, e1, e2):
        return ("({}) <= ({})" if _is_primitive(ty.gen_type(self)) else "({}).compareTo({}) <= 0").format(e1, e2)

    def gt(self, ty, e1, e2):
        return ("({}) > ({})" if _is_primitive(ty.gen_type(self)) else "({}).compareTo({}) > 0").format(e1, e2)

    def ge(self, ty, e1, e2):
        return ("({}) >= ({})" if _is_primitive(ty.gen_type(self)) else "({}).compareTo({}) >= 0").format(e1, e2)

    def to_float(self, ty, e):
        return "(float)({})".format(e)

    def add(self, e1, e2):
        return "({}) + ({})".format(e1, e2)

    def sub(self, e1, e2):
        return "({}) - ({})".format(e1, e2)

    def mul(self, e1, e2):
        return "({}) * ({})".format(e1, e2)

    def div(self, e1, e2):
        return "({}) / ({})".format(e1, e2)

    def mod(self, e1, e2):
        return "({}) % ({})".format(e1, e2)

    def abs(self, e):
        return "Math.abs({})".format(e)

    def init_new(self, target, ty):
        return self.set(target, "new {}()".format(ty.gen_type(self)))

    def null_value(self):
        return "null"

    def true_value(self):
        return "true";

    def false_value(self):
        return "false";

    def get_field(self, e, m):
        if e is None:
            return m
        return "({}).{}".format(e, m)

    def hash(self, values):
        """values is [(type, val)]; returns proc, result"""
        h = fresh_name("hash")
        return (self.decl(h, IntTy(), "0") + self._hash_into(values, h), h)

    def _hash_into(self, values, out):
        proc = ""
        first = True
        for t, v in values:
            if first:
                proc += self.set(out, _hash_code(t, v))
                first = False
            else:
                proc += self.set(out, self.add(self.mul(out, "31"), _hash_code(t, v)))
        return proc

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

    def write(self, fields, queries, java_package=None, java_class="DataStructure", java="-", **kwargs):
        with open_maybe_stdout(java) as f:
            writer = f.write

            if java_package:
                writer("package {};\n\n".format(java_package))

            writer("public class {} implements java.io.Serializable {{\n".format(java_class))

            # record type
            private_members = []
            RECORD_NAME = self.record_type()
            for q in queries:
                private_members += list((f, ty.gen_type(self)) for f, ty in q.impl.private_members())
            _gen_record_type(RECORD_NAME, list(fields.items()), private_members, writer)

            # auxiliary type definitions
            seen = set()
            for q in queries:
                for t in q.impl.auxtypes():
                    _gen_aux_type(t, self, writer, seen)

            # constructor
            writer("  public {}() {{\n".format(java_class))
            for q in queries:
                writer(indent("    ", q.impl.construct(self, This())))
            writer("  }\n")

            # get current size
            writer("  int my_size = 0;\n")
            writer("  int size() { return my_size; }\n")

            # add routine
            writer("  public void add({} x) {{\n".format(RECORD_NAME))
            writer("    ++my_size;\n")
            for q in queries:
                writer(indent("    ", q.impl.gen_insert(self, "x", This())))
            writer("  }\n")

            # remove routine
            writer("  public void remove({} x) {{\n".format(RECORD_NAME))
            writer("    --my_size;\n")
            for q in queries:
                writer(indent("    ", q.impl.gen_remove(self, "x", This())))
            writer("  }\n")

            # update routines
            for f, ty in fields.items():
                writer("  void update{}({} x, {} val) {{\n".format(capitalize(f), self.record_type(), ty))
                writer("    if ({} != val) {{\n".format(self.get_field("x", f)))
                for q in queries:
                    writer(indent("        ", q.impl.gen_update(self, fields, "x", {f: "val"}, This())))
                writer("      {} = val;\n".format(self.get_field("x", f)))
                writer("    }\n")
                writer("  }\n")
            writer("  void update({} x, {}) {{\n".format(self.record_type(), ", ".join("{} {}".format(ty, f) for f, ty in fields.items())))
            for q in queries:
                writer(indent("    ", q.impl.gen_update(self, fields, "x", {f:f for f in fields}, This())))
            for f, ty in fields.items():
                writer("    {} = {};\n".format(self.get_field("x", f), f))
            writer("  }\n")

            # query routines
            for q in queries:

                for f, ty in q.impl.fields():
                    writer("  /*private*/ {} {};\n".format(ty.gen_type(self), f))

                it_name = "{}_iterator".format(q.name)
                writer("  /*private*/ static final class {} implements java.util.Iterator<{}> {{\n".format(it_name, RECORD_NAME))
                state = q.impl.state()
                writer("    {} parent;\n".format(java_class))
                vars_needed = [(v, ty) for v, ty in q.vars if q.impl.needs_var(v)]
                for v, ty in vars_needed:
                    writer("    final {} {};\n".format(ty, v))
                for f, ty in state:
                    writer("    {} {};\n".format(ty.gen_type(self), f))
                writer("    {}({} parent{}{}) {{\n".format(it_name, java_class, "".join(", {} {}".format(ty, v) for v, ty in vars_needed), "".join(", {} {}".format(ty.gen_type(self), f) for f, ty in state)))
                writer("      this.parent = parent;\n")
                for v, ty in vars_needed:
                    writer("      this.{v} = {v};\n".format(v=v))
                for f, ty in state:
                    writer("      this.{f} = {f};\n".format(f=f))
                writer("    }\n")
                writer("    @Override public boolean hasNext() {\n")
                proc, ret = q.impl.gen_has_next(self)
                writer(indent("      ", proc))
                writer("      return {};\n".format(ret))
                writer("    }\n")
                writer("    @Override public {} next() {{\n".format(RECORD_NAME))
                proc, ret = q.impl.gen_next(self)
                writer(indent("      ", proc))
                writer("      return {};\n".format(ret))
                writer("    }\n")
                writer("    @Override public void remove() {\n")
                writer("      --parent.my_size;\n")
                proc, removed = q.impl.gen_remove_in_place(self, TupleInstance("parent"))
                writer(indent("      ", proc))
                for q2 in queries:
                    if q2 != q:
                        writer(indent("        ", q2.impl.gen_remove(self, removed, parent_structure=TupleInstance("parent"))))
                writer("    }\n")
                writer("  }\n")

                writer("  public java.util.Iterator<{}> {}({}) {{\n".format(RECORD_NAME, q.name, ", ".join("{} {}".format(ty, v) for v,ty in q.vars)))
                proc, stateExps = q.impl.gen_query(self, q.vars, This())
                writer(indent("    ", proc))
                writer("    return new {}(this{}{});\n".format(it_name, "".join(", {}".format(v) for v, ty in vars_needed), "".join(", {}".format(e) for e in stateExps)))
                writer("  }\n")

                writer("  public {} {}_1({}) {{\n".format(RECORD_NAME, q.name, ", ".join("{} {}".format(ty, v) for v,ty in q.vars)))
                proc, result = q.impl.gen_query_one(self, q.vars, This())
                writer(indent("    ", proc))
                writer("    return {};\n".format(result))
                writer("  }\n")

            writer("}\n")

    def supports_cost_model_file(self, f):
        return f.endswith(".java")

    def dynamic_cost(self, fields, queries, impls, cost_model_file, args):
        for q, i in zip(queries, impls):
            q.impl = i

        tmp = tempfile.mkdtemp()

        self.write(fields, queries, java_class="DataStructure", java=os.path.join(tmp, "DataStructure.java"))

        with open(os.path.join(tmp, "Main.java"), "w") as f:
            f.write("import java.util.*;")
            f.write("\npublic class Main {\n")
            f.write("public static void main(String[] args) { new Main().run(); }\n")
            with open(cost_model_file, "r") as b:
                f.write(b.read())
            f.write("\n}\n")

        orig = os.getcwd()
        os.chdir(tmp)
        inc = args.java_extra_classpath
        if inc:
            cmd = ["javac", "-d", ".", "-sourcepath", ".:{}".format(inc), "Main.java"]
        else:
            cmd = ["javac", "-d", ".", "Main.java"]
        ret = subprocess.call(cmd)
        assert ret == 0

        java = subprocess.Popen(["java", "Main"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        stdout, stdin = java.communicate()
        assert java.returncode == 0

        score = long(stdout.strip())

        os.chdir(orig)

        return score

    def extensions(self, old):
        return old # no extensions

def _hash_code(ty, exp):
    if _is_primitive(ty):
        if ty == "int":    return exp
        if ty == "long":   return "(int)({e}^({e}>>>32))".format(e=exp)
        if ty == "float":  return "Float.floatToIntBits({e})".format(e=exp)
        if ty == "double": return _hash_code("long", "Double.doubleToLongBits({e})".format(e=exp))
        raise Exception("I'm not sure how to take the hash code of {}".format(ty))
    else:
        return "{}.hashCode()".format(exp)

def _gen_aux_type(ty, gen, writer, seen):
    if ty in seen:
        return
    seen.add(ty)
    if type(ty) is TupleTy:
        for _, t in ty.fields.items():
            _gen_aux_type(t, gen, writer, seen)
        writer("    /*private*/ static class {} implements java.io.Serializable {{\n".format(ty.name))
        for f, t in ty.fields.items():
            writer("        {} {};\n".format(t.gen_type(gen), f))
        writer("        @Override\n")
        writer("        public int hashCode() {\n")
        writer("            int hc = 0;\n")
        for f, t in ty.fields.items():
            writer("            hc = 31 * hc + {};\n".format(_hash_code(t.gen_type(gen), f)))
        writer("            return hc;\n")
        writer("        }\n")
        writer("        @Override\n")
        writer("        public boolean equals(Object other) {\n")
        writer("            if (other == null) return false;\n")
        writer("            if (other.getClass() != getClass()) return false;\n")
        writer("            {t} x = ({t})other;\n".format(t=ty.name))
        for f in ty.fields:
            writer("            if (!({})) return false;\n".format(gen.same("x.{}".format(f), f)))
        writer("            return true;\n")
        writer("        }\n")
        writer("    }\n")

def _gen_record_type(name, fields, private_fields, writer):
    writer("    public static class {} implements java.io.Serializable {{\n".format(name))
    writer("        private static final long serialVersionUID = 1L;\n")
    for f,ty in fields:
        writer("        /*private*/ {} {};\n".format(ty, f))
        writer("        public {t} get{F}() {{ return {f}; }}\n".format(t=ty, f=f, F=capitalize(f)))
    for f,ty in private_fields:
        writer("        /*private*/ {} {};\n".format(ty, f))
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
    return capitalize(ty)

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
