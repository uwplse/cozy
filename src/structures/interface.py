from common import fresh_name

class Ty(object):
    def gen_type(self, gen):
        raise Exception("not implemented for type: {}".format(type(self)))

class NativeTy(Ty):
    def __init__(self, ty):
        self.ty = ty
    def gen_type(self, gen):
        return gen.native_type(self.ty)

class IntTy(Ty):
    def gen_type(self, gen):
        return gen.int_type()

class FloatTy(Ty):
    def gen_type(self, gen):
        return "float" # TODO

class RefTy(Ty):
    def __init__(self, ty):
        self.ty = ty
    def gen_type(self, gen):
        return gen.ref_type(self.ty)

class PointerTy(Ty):
    def __init__(self, ty):
        self.ty = ty
    def gen_type(self, gen):
        return gen.ptr_type(self.ty)

class StackTy(Ty):
    def __init__(self, ty):
        self.ty = ty
    def gen_type(self, gen):
        return gen.stack_type(self.ty)

class BoolTy(Ty):
    def gen_type(self, gen):
        return gen.bool_type()

class VecTy(Ty):
    def __init__(self, ty, count):
        self.ty = ty
        self.count = count
    def gen_type(self, gen):
        return gen.vector_type(self.ty, self.count)

class ArrayTy(Ty):
    def __init__(self, ty):
        self.ty = ty
    def gen_type(self, gen):
        return gen.array_type(self.ty)

class MapTy(Ty):
    def __init__(self, k, v):
        self.keyTy = k
        self.valTy = v
    def gen_type(self, gen):
        return gen.map_type(self.keyTy, self.valTy)

class MapHandleType(Ty):
    def __init__(self, k, v):
        self.keyTy = k
        self.valTy = v
    def gen_type(self, gen):
        return gen.map_handle_type(self.keyTy, self.valTy)

class RecordType(Ty):
    def gen_type(self, gen):
        return gen.record_type()
    def instance(self, e):
        return This()

class TupleInstance(object):
    def __init__(self, this):
        self.this = this
    def field(self, gen, f):
        return gen.get_field(self.this, f)

class This(object):
    def field(self, gen, f):
        return f

class TupleTy(Ty):
    def __init__(self, fields):
        self.name = fresh_name("Tuple")
        self.fields = fields
    def __str__(self):
        return "Tuple({})".format(self.fields)
    def __repr__(self):
        return self.__str__()
    def gen_type(self, gen):
        if len(self.fields) == 1:
            ty, = self.fields.values()
            return ty.gen_type(gen)
        return gen.native_type(self.name)
    def instance(self, e):
        fields = self.fields
        class I(object):
            def field(self, gen, f):
                assert f in fields
                return e if len(fields) is 1 else gen.get_field(e, f)
        return I()

class ConcreteImpl(object):
    """
    Common interface for generated data structures
    """

    def fields(self):
        """data structure members; returns list of (name, ty)"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def construct(self, gen, parent_structure):
        """returns proc"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def needs_var(self, var):
        """iterator state; returns True or False"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def state(self):
        """iterator state; returns list of (name, ty)"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def private_members(self):
        """record state; returns list of (name, ty)"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def gen_query(self, gen, qvars, parent_structure):
        """returns (proc, stateExps)"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def gen_query_one(self, gen, qvars, parent_structure):
        """returns some single element, or null if no matches"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def gen_empty(self, gen, qvars):
        """returns stateExps"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def gen_find_any(self, gen, parent_structure):
        """returns proc, some single element"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def gen_current(self, gen):
        """returns (proc, result)"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def gen_advance(self, gen):
        """returns proc"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def gen_next(self, gen):
        """returns (proc, result)"""
        proc, cur = self.gen_current(gen)
        oldcursor = fresh_name()
        proc += gen.decl(oldcursor, RecordType(), cur)
        proc += self.gen_advance(gen)
        return proc, oldcursor
    def gen_has_next(self, gen):
        """returns (proc, result)"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def gen_insert(self, gen, x, parent_structure):
        """returns proc"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def gen_remove(self, gen, x, parent_structure):
        """returns proc"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def gen_remove_in_place(self, gen, parent_structure):
        """returns proc, removed element"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def gen_update(self, gen, fields, x, remap, parent_structure):
        """remap is {fieldname:newvalue} dict; returns proc"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def auxtypes(self):
        """generator of auxiliary types which need to be generated"""
        raise NotImplementedError("not implemented for type: {}".format(type(self)))
    def check_rep(self, gen, parent_structure):
        """procedure to check rep invariants for debugging"""
        return ""
