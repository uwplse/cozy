import re

import codegen
import predicates
import plans
from common import capitalize, fresh_name

class JavaCodeGenerator(object):
    def __init__(self, writer, class_name, package_name=None):
        self.class_name = class_name
        self.package_name = package_name
        self.writer = writer
        self.types = dict()

    def begin(self):
        pass

    def end(self):
        pass

    def map_type(self, kt, vt):
        return "java.util.Map<{}, {}>".format(_box(kt.gen_type(self)), vt.gen_type(self))

    def bool_type(self):
        return "boolean";

    def new_map(self, kt, vt):
        return "new java.util.HashMap<{}, {}>()".format(_box(kt.gen_type(self)), vt.gen_type(self))

    def map_lookup(self, m, k):
        return "{}.get({})".format(m, k)

    def map_put(self, m, k, v):
        return "{}.put({}, {});\n".format(m, k, v)

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
        if self.package_name:
            self.writer("package {};\n\n".format(self.package_name))

        self.writer("public class {} implements java.io.Serializable {{\n".format(self.class_name))

        # record type
        private_members = []
        RECORD_NAME = self.record_type()
        for q in queries:
            private_members += list((f, ty.gen_type(self), init) for f, ty, init in q.impl.private_members(self))
        _gen_record_type(RECORD_NAME, list(fields.items()), private_members, self.writer)

        # auxiliary type definitions
        seen = set()
        for q in queries:
            for t in q.impl.auxtypes():
                _gen_aux_type(t, self, self.writer, seen)

        # constructor
        self.writer("  public {}() {{\n".format(self.class_name))
        for q in queries:
            self.writer(_indent("    ", q.impl.construct(self)))
        self.writer("  }\n")

        # add routine
        self.writer("  public void add({} x) {{\n".format(RECORD_NAME))
        for q in queries:
            self.writer(_indent("    ", q.impl.gen_insert(self, "x")))
        self.writer("  }\n")

        # remove routine
        self.writer("  public void remove({} x) {{\n".format(RECORD_NAME))
        for q in queries:
            self.writer(_indent("    ", q.impl.gen_remove(self, "x")))
        self.writer("  }\n")

        # query routines
        for q in queries:

            for f, ty in q.impl.fields():
                self.writer("  /*private*/ {} {};\n".format(ty.gen_type(self), f))

            it_name = "{}_iterator".format(q.name)
            self.writer("  /*private*/ static final class {} implements java.util.Iterator<{}> {{\n".format(it_name, RECORD_NAME))
            state = q.impl.state()
            self.writer("    {} parent;\n".format(self.class_name))
            vars_needed = [(v, ty) for v, ty in q.vars if q.impl.needs_var(v)]
            for v, ty in vars_needed:
                self.writer("    final {} {};\n".format(ty, v))
            for f, ty in state:
                self.writer("    {} {};\n".format(ty.gen_type(self), f))
            self.writer("    {}({} parent{}{}) {{\n".format(it_name, self.class_name, "".join(", {} {}".format(ty, v) for v, ty in vars_needed), "".join(", {} {}".format(ty.gen_type(self), f) for f, ty in state)))
            self.writer("      this.parent = parent;\n")
            for v, ty in vars_needed:
                self.writer("      this.{v} = {v};\n".format(v=v))
            for f, ty in state:
                self.writer("      this.{f} = {f};\n".format(f=f))
            self.writer("    }\n")
            self.writer("    @Override public boolean hasNext() {\n")
            proc, ret = q.impl.gen_has_next(self)
            self.writer(_indent("      ", proc))
            self.writer("      return {};\n".format(ret))
            self.writer("    }\n")
            self.writer("    @Override public {} next() {{\n".format(RECORD_NAME))
            proc, ret = q.impl.gen_next(self)
            self.writer(_indent("      ", proc))
            self.writer("      return {};\n".format(ret))
            self.writer("    }\n")
            self.writer("    @Override public void remove() {\n")
            proc = q.impl.gen_remove_in_place(self, codegen.TupleInstance("parent"))
            self.writer(_indent("      ", proc))
            self.writer("    }\n")
            self.writer("  }\n")

            self.writer("  public java.util.Iterator<{}> {}({}) {{\n".format(RECORD_NAME, q.name, ", ".join("{} {}".format(ty, v) for v,ty in q.vars)))
            proc, stateExps = q.impl.gen_query(self, q.vars)
            self.writer(_indent("    ", proc))
            self.writer("    return new {}(this{}{});".format(it_name, "".join(", {}".format(v) for v, ty in vars_needed), "".join(", {}".format(e) for e in stateExps)))
            self.writer("  }\n")

        self.writer("}\n")

def _gen_aux_type(ty, gen, writer, seen):
    if ty in seen:
        return
    seen.add(ty)
    if type(ty) is codegen.TupleTy:
        for _, t in ty.fields.items():
            _gen_aux_type(t, gen, writer, seen)
        writer("    /*private*/ static class {} implements java.io.Serializable {{\n".format(ty.name))
        for f, t in ty.fields.items():
            writer("        {} {};".format(t.gen_type(gen), f))
        writer("    }\n")

def _gen_record_type(name, fields, private_fields, writer):
    writer("    public static class {} implements java.io.Serializable {{\n".format(name))
    writer("        private static final long serialVersionUID = 1L;\n")
    for f,ty in fields:
        writer("        /*private*/ {} {};\n".format(ty, f))
        writer("        public {t} get{F}() {{ return {f}; }}\n".format(t=ty, f=f, F=capitalize(f)))
    for f,ty,init in private_fields:
        writer("        /*private*/ {} {};\n".format(ty, f))
    writer("        public {}({}) {{\n".format(name, ", ".join("{} {}".format(ty, f) for f,ty in fields)))
    for f,ty in fields:
        writer("            this.{f} = {f};\n".format(f=f))
    for f,ty,init in private_fields:
        writer("            this.{f} = {init};\n".format(f=f, init=init))
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

_START_OF_LINE = re.compile(r"^", re.MULTILINE)
def _indent(i, s):
    return _START_OF_LINE.sub(i, s)

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
