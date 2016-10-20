from __future__ import print_function

import re
import tempfile
import os
import subprocess
import sys
from functools import wraps

import codegen
import predicates
import plans
import structures
from structures.interface import TupleTy, This, TupleInstance, IntTy
from common import capitalize, fresh_name, indent, open_maybe_stdout

class JsCodeGenerator(codegen.CodeGenerator):
    def __init__(self):
        super(JsCodeGenerator, self).__init__()

    def map_type(self, *args):        return "var"
    def map_handle_type(self, *args): return "var"
    def stack_type(self, *args):      return "var"
    def ref_type(self, *args):        return "var"
    def bool_type(self, *args):       return "var"
    def int_type(self, *args):        return "var"
    def ptr_type(self, *args):        return "var"
    def vector_type(self, *args):     return "var"
    def array_type(self, *args):      return "var"
    def native_type(self, *args):     return "var"
    def record_type(self, *args):     return "var"

    def should_use_double_equals(self, ty):
        return _is_primitive(ty)

    def __str__(self):
        return "JsCodeGenerator"

    def new_array(self, ty, count):
        return "new Array({})".format(count)

    def array_get(self, a, n):
        return "{}[{}]".format(a, n)

    def array_set(self, a, n, v):
        return "{}[{}] = {};\n".format(a, n, v)

    def array_size(self, a):
        return "{}.length".format(a)

    def array_copy(self, ty, asrc, adst, src_start=0, dst_start=0, amt=None):
        raise NotImplementedError()

    def data_structure_size(self):
        return "this.my_size" # massive hack

    def alloc(self, ty, args):
        return "new {}({})".format(ty.gen_type(self), ", ".join(args))

    def initialize(self, ty, lval):
        if type(ty) is TupleTy and len(ty.fields) > 1:
            return "{lval} = {new};\n".format(lval=lval, new=self.alloc(ty, []))
        else:
            return ""

    def free(self, ty, x):
        return ""

    def min(self, ty, x, y):
        raise NotImplementedError()
        return "({x} < {y}) ? {x} : {y}".format(x=x, y=y) if _is_primitive(ty) else "({x}.compareTo({y}) < 0) ? {x} : {y}".format(x=x, y=y)

    def max(self, ty, x, y):
        raise NotImplementedError()
        return "({x} < {y}) ? {y} : {x}".format(x=x, y=y) if _is_primitive(ty) else "({x}.compareTo({y}) < 0) ? {y} : {x}".format(x=x, y=y)

    def new_stack(self, t):
        return self.new_array(t, 0)

    def stack_size_hint(self, stk, n):
        return ""

    def stack_is_empty(self, stk):
        return "{}.length == 0".format(stk)

    def stack_push(self, stk, x):
        return "{}.push({});\n".format(stk, x)

    def stack_pop(self, stk):
        return "{}.pop();\n".format(stk)

    def stack_peek(self, stk):
        return "{}[{}.length - 1]".format(stk, stk)

    def new_vector(self, ty, n):
        return self.new_array(ty, n)

    def vector_init_elem(self, v, ty, i):
        if isinstance(ty, TupleTy) and len(ty.fields) > 1: # a bit of a hack
            return self.vector_set(v, i, self.alloc(ty, []))
        return ""

    def vector_get(self, v, i):
        return self.array_get(v, i)

    def vector_set(self, v, i, x):
        return self.array_set(v, i, x)

#------------------------------------------------------------------

    def list_get(self, li, index):
        return "({})[{}]".format(li, index)

    def list_add(self, li, item):
        return "({}).push({});\n".format(li, item)

    def list_set(self, li, index, item):
        return "({})[{}] = {};\n".format(li, index, item)

    def list_size(self, li):
        return "({}).length".format(li)

    def new_list(self, ty):
        return self.new_array(ty, 0)

    def integer_bitcount(self, arg):
        return 52 # bits in significand of double - 1

    def plus_one(self, v):
        return "{}++;\n".format(v)

    def end_return(self):
        return "return;\n"

    def logical_and(self, lhs, rhs):
        return "({}) && ({})".format(lhs, rhs)

    def left_shift(self, lhs, rhs):
        return "(({}) << ({}))".format(lhs, rhs)

    def right_logic_shift(self, lhs, rhs):
        return "(({}) >>> ({}))".format(lhs, rhs)

    def bitwise_and(self, lhs, rhs):
        return "(({}) & ({}))".format(lhs, rhs)

    def bitwise_or(self, lhs, rhs):
        return "(({}) | ({}))".format(lhs, rhs)

    def record_name(self, r):
        return "({}).name".format(r)

    def get_node_values(self, node):
        return "{}.values".format(node)

    def get_node_is_leaf_value(self, node):
        return "{}.isLeaf".format(node)

    def get_node_signature(self, node):
        return "{}.signature".format(node)

    def get_node_next(self, node):
        return "{}.next".format(node)

    def not_eq(self, ty, lhs, rhs):
        return "(!{})".format(self.eq(ty, lhs, rhs))

    def not_same(self, e1, e2):
        return "(!({}))".format(self.same(e1, e2))

#------------------------------------------------------------------

    def same(self, e1, e2):
        return "({}) == ({})".format(e1, e2)

    def eq(self, ty, e1, e2):
        return ("({}) == ({})" if self.should_use_double_equals(ty) else "({}).equals({})").format(e1, e2)

    def lt(self, ty, e1, e2):
        if ty.gen_type(self) == "boolean": return "Boolean.compare({}, {}) < 0".format(e1, e2)
        return ("({}) < ({})" if _is_primitive(ty) else "({}).compareTo({}) < 0").format(e1, e2)

    def le(self, ty, e1, e2):
        if ty.gen_type(self) == "boolean": return "Boolean.compare({}, {}) <= 0".format(e1, e2)
        return ("({}) <= ({})" if _is_primitive(ty) else "({}).compareTo({}) <= 0").format(e1, e2)

    def gt(self, ty, e1, e2):
        if ty.gen_type(self) == "boolean": return "Boolean.compare({}, {}) > 0".format(e1, e2)
        return ("({}) > ({})" if _is_primitive(ty) else "({}).compareTo({}) > 0").format(e1, e2)

    def ge(self, ty, e1, e2):
        if ty.gen_type(self) == "boolean": return "Boolean.compare({}, {}) >= 0".format(e1, e2)
        return ("({}) >= ({})" if _is_primitive(ty) else "({}).compareTo({}) >= 0").format(e1, e2)

    def abs(self, e):
        return "Math.abs({})".format(e)

    def init_new(self, target, ty):
        return self.set(target, "new {}()".format(ty.gen_type(self)))

    def hash1(self, ty, value):
        return _hash_code(ty, value)

    def write(self, fields, queries, js="-", js_class="DataStructure", **kwargs):
        with open_maybe_stdout(js) as f:
            writer = f.write

            RECORD_NAME = js_class + "Entry"

            writer("/*\n * USAGE SUMMARY\n")
            writer(" *     initialization:\n *         ds = new {}();\n".format(js_class))
            writer(" *     get # of entries:\n *         ds.size();\n")
            writer(" *     add:\n *         ds.add(new {}({}));\n".format(RECORD_NAME, ", ".join(f for f in fields)))
            writer(" *     remove:\n *         ds.remove(elem);\n")
            writer(" *     update all fields:\n *         ds.update(elem, {});\n".format(", ".join("new_{}".format(f) for f in fields)))
            for f in fields:
                writer(" *     update {f}:\n *         ds.update{F}(elem, new_{f});\n".format(f=f, F=capitalize(f)))
            writer(" *     queries:\n")
            for q in queries:
                writer(" *         ds.{n}({args}, function(elem) {{ ... }});\n".format(n=q.name, args=", ".join(a for a,t in q.vars)))
            writer(" * NOTE: Be careful not to add the same {} object more than once.\n".format(RECORD_NAME))
            writer(" * NOTE: Be careful not to remove or update an entry that is not in the data structure.\n")
            writer(" * NOTE: You may not make changes (add/remove/update) in query callbacks.\n")
            writer(" * NOTE: Elements can be removed in-place during iteration: if your query callback returns a truthy value, then the element is removed.\n")
            writer(" */\n\n\n")

            # record type
            private_members = []
            for q in queries:
                private_members += list((f, ty.gen_type(self)) for f, ty in q.impl.private_members())
            _gen_record_type(RECORD_NAME, list(fields.items()), private_members, writer)

            # auxiliary type definitions
            seen = set()
            for q in queries:
                for t in q.impl.auxtypes():
                    _gen_aux_type(t, self, writer, seen)

            this = TupleInstance("this")

            # # constructor
            writer("function {}() {{\n".format(js_class))
            writer(indent("    ", "this.my_size = 0;\n"))
            for q in queries:
                writer(indent("    ", q.impl.construct(self, this)))
            writer("}\n")

            # get current size
            writer("{}.prototype.size = function() {{ return this.my_size; }};\n".format(js_class))

            # add routine
            writer("{}.prototype.add = function(x) {{\n".format(js_class))
            writer("    ++this.my_size;\n")
            for q in queries:
                writer(indent("    ", q.impl.gen_insert(self, "x", this)))
            writer("};\n")

            # remove routine
            writer("{}.prototype.remove = function(x) {{\n".format(js_class))
            writer("    --this.my_size;\n")
            for q in queries:
                writer(indent("    ", q.impl.gen_remove(self, "x", this)))
            writer("};\n")

            # update routines
            for f, ty in fields.items():
                writer("{}.prototype.update{} = function(__x, new_val) {{\n".format(js_class, capitalize(f)))
                writer("    if ({} != new_val) {{\n".format(self.get_field("__x", f)))
                for q in queries:
                    writer(indent("        ", q.impl.gen_update(self, fields, "__x", {f: "new_val"}, this)))
                writer("      {} = new_val;\n".format(self.get_field("__x", f)))
                writer("    }\n")
                writer("  }\n")
            writer("{}.prototype.update = function(__x, {}) {{\n".format(js_class, ", ".join(f for f, ty in fields.items())))
            for q in queries:
                writer(indent("    ", q.impl.gen_update(self, fields, "__x", {f:f for f in fields}, this)))
            for f, ty in fields.items():
                writer("    {} = {};\n".format(self.get_field("__x", f), f))
            writer("  }\n")

            # query routines
            for q in queries:
                writer("{}.prototype.{} = function({}, __callback) {{\n".format(js_class, q.name, ", ".join(v for v,ty in q.vars)))
                proc, stateExps = q.impl.gen_query(self, q.vars, this)
                writer(indent("    ", proc))
                state = q.impl.state()
                for (f, ty), e in zip(state, stateExps):
                    writer("    var {} = {};\n".format(f, e))

                writer("    for (;;) {\n")
                proc, has_next = q.impl.gen_has_next(self, parent_structure=this, iterator=This())
                writer(indent("        ", proc))
                writer("        if (!({})) break;\n".format(has_next))

                proc, next = q.impl.gen_next(self, parent_structure=this, iterator=This())
                writer(indent("        ", proc))
                writer("        if (__callback({})) {{\n".format(next))
                proc, next = q.impl.gen_remove_in_place(self, parent_structure=this, iterator=This())
                writer(indent("        ", proc))
                writer("        }\n")
                writer("    }\n")

                writer("  }\n")

    def extensions(self, old):
        @wraps(old)
        def f(*args, **kwargs):
            for res in old(*args, **kwargs):
                if not type(res) == structures.HashMap:
                    yield res
        return f

def _hash_code(ty, exp):
    if type(ty).__name__ in ["IntTy", "FloatTy"]:
        return "Math.round({})".format(exp)
    if type(ty).__name__ == "NativeTy":
        if ty.ty == "String":
            return '({}.split("").reduce(function(hc, c) {{ return hc * 31 + c.charCodeAt(0); }}, 0))'.format(exp)
    raise NotImplementedError(str(ty))

def _is_primitive(ty):
    return type(ty).__name__ in ["IntTy", "FloatTy", "NativeTy"]

def _gen_aux_type(ty, gen, writer, seen):
    if ty in seen:
        return
    seen.add(ty)
    if type(ty) is TupleTy:
        writer("function {}({}) {{\n".format(ty.name, ", ".join(ty.fields)))
        for f in ty.fields:
            writer("    this.{f} = {f};\n".format(f=f))
        writer("}\n")

def _gen_record_type(name, fields, private_fields, writer):
    writer("function {}({}) {{\n".format(name, ", ".join(f for f,ty in fields)))
    for f,ty in fields:
        writer("    this.{f} = {f};\n".format(f=f))
    for f,ty in private_fields:
        writer("    this.{f} = undefined;\n".format(f=f))
    writer("}\n")
