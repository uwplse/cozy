import itertools

import plans
import predicates

class Ty(object):
    def unify(self, other):
        raise Exception("not implemented for type: {}".format(type(self)))
    def gen_type(self, gen):
        raise Exception("not implemented for type: {}".format(type(self)))

class NativeTy(Ty):
    def __init__(self, ty):
        self.ty = ty
    # def unify(self, other):
    #     if type(other) is NativeTy and self.ty == other.ty:
    #         return self
    #     return None
    def gen_type(self, gen):
        return gen.native_type(self.ty)

class RecordType(Ty):
    # def unify(self, other):
    #     if type(other) is RecordType:
    #         return self
    #     return None
    def gen_type(self, gen):
        return gen.record_type()

class Tuple(Ty):
    def __init__(self, fields):
        self.type_name = fresh_name()
        self._fields = fields
    # def unify(self, other):
    #     raise Exception("Tuple.unify is not implemented")
    #     # if type(other) is Tuple:
    #     #     if len(self.fields) != len(other.fields):
    #     #         return None
    #     #     ts = { f : (t.unify(other.fields[f]) if f in other.fields else None) for (f, t) in self.fields.items() }
    #     #     if not any(t is None for t in ts.values()):
    #     #         return Tuple(ts)
    #     # return None
    def gen_type(self, gen):
        if len(self._fields) == 1:
            return list(self._fields.values())[0].gen_type(gen)
        return NativeTy(self.type_name).gen_type(gen)

class Map(Ty):
    def __init__(self, keyTy, valueTy):
        self.keyTy = keyTy
        self.valueTy = valueTy
    # def unify(self, other):
    #     raise Exception("Map.unify is not implemented")
    def gen_type(self, gen):
        return gen.map_type(self.keyTy, self.valueTy)

class Array(Ty):
    def __init__(self, ty):
        self.ty = ty
    # def unify(self, other):
    #     raise Exception("Array.unify is not implemented")
    def gen_type(self, gen):
        return gen.array_type(self.ty)

class BinaryTree(Ty):
    def __init__(self, ty):
        self.ty = ty
    # def unify(self, other):
    #     raise Exception("Array.unify is not implemented")
    def gen_type(self, gen):
        return gen.array_type(self.ty)

# class Impl(object):
#     def copy(self):
#         raise Exception("not implemented for type: {}".format(type(self)))
#     def is_sorted_by(self, field):
#         raise Exception("not implemented for type: {}".format(type(self)))
#     # def unify(self, other):
#     #     raise Exception("not implemented for type: {}".format(type(self)))
#     def fields(self):
#         """returns list of (name, ty)"""
#         raise Exception("not implemented for type: {}".format(type(self)))
#     def construct(self, gen):
#         """returns proc"""
#         raise Exception("not implemented for type: {}".format(type(self)))
#     def needs_var(self, var):
#         """returns True or False"""
#         raise Exception("not implemented for type: {}".format(type(self)))
#     def state(self):
#         """returns list of (name, ty)"""
#         raise Exception("not implemented for type: {}".format(type(self)))
#     def private_members(self, gen):
#         """returns list of (name, ty, init)"""
#         raise Exception("not implemented for type: {}".format(type(self)))
#     def gen_query(self, gen, qvars):
#         """returns (proc, stateExps)"""
#         raise Exception("not implemented for type: {}".format(type(self)))
#     def gen_current(self, gen):
#         """returns (proc, result)"""
#         raise Exception("not implemented for type: {}".format(type(self)))
#     def gen_advance(self, gen):
#         """returns proc"""
#         raise Exception("not implemented for type: {}".format(type(self)))
#     def gen_next(self, gen):
#         """returns (proc, result)"""
#         result = fresh_name()
#         proc, x = self.gen_current(gen)
#         proc += gen.decl(result, RecordType(), x)
#         proc += self.gen_advance(gen)
#         return proc, result
#     def gen_has_next(self, gen):
#         """returns (proc, result)"""
#         raise Exception("not implemented for type: {}".format(type(self)))
#     def gen_insert(self, gen, x):
#         """returns proc"""
#         raise Exception("not implemented for type: {}".format(type(self)))
#     def gen_remove(self, gen, x):
#         """returns proc"""
#         raise Exception("not implemented for type: {}".format(type(self)))
#     def gen_remove_in_place(self, gen, parent_structure):
#         """returns proc"""
#         raise Exception("not implemented for type: {}".format(type(self)))

class HashMap(Ty):
    def __init__(self, keyTy, keyArgs, valueImpl):
        self.name = fresh_name()
        self.keyTy = keyTy
        self.valueTy = self._make_value_type(valueImpl)
        self.keyArgs = keyArgs
        self.valueImpl = valueImpl
    def copy(self):
        return HashMap(self.keyTy, self.keyArgs, self.valueImpl.copy())
    # def unify(self, other):
    #     if type(other) is HashMap and other.keyTy == self.keyTy:
    #         unif = self.valueImpl.unify(other.valueImpl)
    #         if unif is not None:
    #             return HashMap(self.keyTy, unif)
    #     return None
    def _make_value_type(self, valueImpl):
        return Tuple(dict(valueImpl.fields()))
    def fields(self):
        return ((self.name, Map(self.keyTy, self.valueTy)),)
    def construct(self, gen):
        return gen.set(self.name, gen.new_map(self.keyTy, self.valueImpl))
    def needs_var(self, v):
        return self.valueImpl.needs_var(v)
    def state(self):
        return self.valueImpl.state()
    def private_members(self, gen):
        return self.valueImpl.private_members(gen)
    # def gen_type(self, gen):
    #     return gen.map_type(self.keyTy, self.valueImpl)
    def make_key(self, gen):
        if len(self.keyTy._fields) == 1:
            return self.keyArgs[list(self.keyTy._fields.keys())[0]]
        raise Exception("implement make_key")
    def make_key_of_record(self, gen, x):
        if len(self.keyTy._fields) == 1:
            return gen.get_field(x, list(self.keyTy._fields.keys())[0])
        raise Exception("implement make_key")
    def gen_query(self, gen, qvars):
        k = fresh_name()
        proc  = gen.decl(k, self.keyTy, self.make_key(gen))
        proc += gen.decl(self.valueImpl.name, self.valueImpl, gen.map_lookup(self.name, k))
        p, r = self.valueImpl.gen_query(gen, qvars)
        return (proc + p, r)
    def gen_current(self, gen):
        return self.valueImpl.gen_current(gen)
    def gen_next(self, gen):
        return self.valueImpl.gen_next(gen)
    def gen_has_next(self, gen):
        return self.valueImpl.gen_has_next(gen)
    def gen_insert(self, gen, x):
        k = fresh_name()
        proc  = gen.decl(k, self.keyTy, self.make_key_of_record(gen, x))
        proc += gen.decl(self.valueImpl.name, self.valueImpl, gen.map_lookup(self.name, k))
        return proc + self.valueImpl.gen_insert(gen, x) + gen.map_put(self.name, k, self.valueImpl.name)
    def gen_remove(self, gen, x):
        k = fresh_name()
        proc  = gen.decl(k, self.keyTy, self.make_key_of_record(gen, x))
        proc += gen.decl(self.valueImpl.name, self.valueImpl, gen.map_lookup(self.name, k))
        return proc + self.valueImpl.gen_remove(gen, x) + gen.map_put(self.name, k, self.valueImpl.name)
    def gen_remove_in_place(self, gen, parent_structure):
        k = fresh_name()
        px, x = self.valueImpl.gen_current(gen)
        proc  = gen.decl(k, self.keyTy, self.make_key_of_record(gen, x))
        proc += gen.decl(self.valueImpl.name, self.valueImpl, gen.map_lookup(gen.get_field(parent_structure, self.name), k))
        return px + proc + self.valueImpl.gen_remove_in_place(gen, None) + gen.map_put(gen.get_field(parent_structure, self.name), k, self.valueImpl.name)

AUG_MIN = "min"
AUG_MAX = "max"

def _break_conj(p):
    if type(p) is predicates.And:
        return itertools.chain(_break_conj(p.lhs), _break_conj(p.rhs))
    else:
        return (p,)

def _make_augdata(field_name, predicate, fields):
    """returns a generator of (field_name, var_name, min/max, inclusive)"""
    comparisons = list(_break_conj(predicate))
    for c in comparisons:
        if c.rhs.name in fields:
            c = c.flip()
        f = c.lhs.name
        v = c.rhs.name
        if f == field_name:
            continue
        if c.op == predicates.Lt:   yield (f, v, AUG_MAX, False)
        if c.op == predicates.Le:   yield (f, v, AUG_MAX, True)
        if c.op == predicates.Gt:   yield (f, v, AUG_MIN, False)
        if c.op == predicates.Ge:   yield (f, v, AUG_MIN, True)

INCLUSIVE = "inclusive"
EXCLUSIVE = "exclusive"

class AugTree(Ty):
    def __init__(self, fieldTy, fieldName, predicate, fields):
        self.name = fresh_name()
        self.fieldTy = fieldTy
        self.fieldName = fieldName
        self.ty = RecordType()
        self.predicate = predicate
        self._fields = fields
        clauses = list(_break_conj(predicate))

        # put field names on LHS of clauses
        for i in xrange(len(clauses)):
            if clauses[i].rhs.name in fields:
                clauses[i] = clauses[i].flip()

        self.mins = []
        self.maxes = []
        for c in clauses:
            if c.lhs.name == fieldName:
                if   c.op == predicates.Gt: self.mins.append((EXCLUSIVE, c.rhs))
                elif c.op == predicates.Ge: self.mins.append((INCLUSIVE, c.rhs))
                elif c.op == predicates.Lt: self.maxes.append((EXCLUSIVE, c.rhs))
                elif c.op == predicates.Le: self.maxes.append((INCLUSIVE, c.rhs))

        self.augData = list(_make_augdata(fieldName, predicate, fields)) if predicate else ()
        if self.augData:
            raise Exception("cannot handle augdata yet")

        self.cursor_name = fresh_name("cursor")
        self.left_ptr = fresh_name("left")
        self.right_ptr = fresh_name("right")
        self.parent_ptr = fresh_name("parent")
    def copy(self):
        return AugTree(self.fieldTy, self.fieldName, self.predicate, self._fields)
    def unify(self, other):
        raise Exception("not implemented")

    def fields(self):
        return [(self.name, self.ty)]
    def construct(self, gen):
        return gen.set(self.name, gen.null_value())
    def needs_var(self, v):
        return v in (x.name for x in self.predicate.vars())
    def state(self):
        return [(self.cursor_name, self.ty)] # TODO: vars...?
    def private_members(self, gen):
        return [
            (self.left_ptr,   RecordType(), gen.null_value()),
            (self.right_ptr,  RecordType(), gen.null_value()),
            (self.parent_ptr, RecordType(), gen.null_value())]
    def gen_type(self, gen):
        return self.ty.gen_type(gen)
    def _too_small(self, gen, node, clip=True):
        if not clip:
            return gen.false_value()
        e = None
        for (mode, bound) in self.mins:
            compare = gen.lt if mode == EXCLUSIVE else gen.le
            ee = compare(self.fieldTy, gen.get_field(node, self.fieldName), bound.name)
            e = gen.either(e, ee) if e is not None else ee
        return e
    def _too_large(self, gen, node, clip=True):
        if not clip:
            return gen.false_value()
        e = None
        for (mode, bound) in self.maxes:
            compare = gen.lt if mode == EXCLUSIVE else gen.le
            ee = compare(self.fieldTy, bound.name, gen.get_field(node, self.fieldName))
            e = gen.either(e, ee) if e is not None else ee
        return e
    def _subtree_ok(self, gen, root, clip=True):
        """could ANY node in the subtree be valid? only checks augdata."""
        if not clip:
            return gen.true_value()
        return gen.true_value()
    def _has_parent(self, gen, node):
        return gen.not_true(gen.is_null(gen.get_field(node, self.parent_ptr)))
    def _is_left_child(self, gen, node):
        return gen.both(self._has_parent(gen, node), gen.same(node, gen.get_field(gen.get_field(node, self.parent_ptr), self.left_ptr)))
    def _is_right_child(self, gen, node):
        return gen.both(self._has_parent(gen, node), gen.same(node, gen.get_field(gen.get_field(node, self.parent_ptr), self.right_ptr)))
    def _find_min(self, gen, root, clip=True):
        """precond: _subtree_ok(root)"""
        root2 = fresh_name("root")
        proc  = gen.decl(root2, self.ty, root)
        root = root2

        x = fresh_name("x")
        proc += gen.decl(x, self.ty, root)

        # recursive alg:
        # if x is too small
        #     if x has right child: return _find_min(right)
        #     else return NULL
        # else if has left child
        #     n <- _find_min(left)
        #     if n is not NULL: return n
        #     else return x too large ? NULL : x
        # else if x is too large, return NULL
        # else return x

        # linearization:
        # mode = DESCEND
        # while True
        # if mode == DESCEND
        #     if x is too small:
        #         if x has right child:
        #             if x is root: root = right
        #             x = right
        #         else if x is not root: x = parent; mode = ASCEND // too small, no right child, not the root... back out!
        #         else: return NULL // x too small, no right child... no answer!
        #     else if x has left child:
        #         x = left
        #     else if x is too large:
        #         if x is not root: x = parent; mode = ASCEND // no left child, x too big: back out!
        #         else: return NULL; // x is root, is too large, and has no left
        #     else if _node_ok(x): return x; // x is not too small or large, and has no left child
        #     else if x is root: x = root = right; // if there is an answer, it lies to the right
        #     else: x = parent; mode = ASCEND
        # else if mode == ASCEND_FROM_LEFT
        #     // x is not too small, or we would be in ASCEND_FROM_RIGHT
        #     // there is no answer in X.left
        #     if x is too large:
        #         return NULL; // if our parent was smaller and ok, it would have returned itself!
        #     else:
        #         // x is not too large but there is no answer in left tree
        #         if _node_ok(x): return x // got it!
        #         else if x has right child:
        #             if x is root: root = right
        #             x = right; mode = DESCEND
        #         else if x is root: return NULL // it isn't X, it isn't in X.left, it isn't in X.right
        #         else: x = x.parent; mode = ASCEND // it isn't X, it isn't in X.left, it isn't in X.right
        # else if mode == ASCEND_FROM_RIGHT:
        #     // no answer is left subtree, x is not answer, no answer in right subtree
        #     if x is root: return NULL // x is not ok, or we would have returned it
        #     else: x = x.parent; mode = ASCEND // no answer in this subtree

        descend = fresh_name("descend")
        from_left = fresh_name("from_left")
        bool_type = NativeTy(gen.bool_type())
        proc += gen.decl(descend, bool_type, gen.true_value())
        proc += gen.decl(from_left, bool_type, gen.true_value())

        parent = gen.get_field(x, self.parent_ptr)
        right  = gen.get_field(x, self.right_ptr)
        left   = gen.get_field(x, self.left_ptr)
        null   = gen.null_value()

        ascend = (
            gen.set(descend, gen.false_value()) +
            gen.set(from_left, self._is_left_child(gen, x)) +
            gen.set(x, parent))

        return_null = (
            gen.set(x, null) +
            gen.break_loop())

        return_x = gen.break_loop()

        descend_right = (
            gen.if_true(gen.same(x, root)) +
            gen.set(root, right) +
            gen.endif() +
            gen.set(x, right))

        proc += gen.while_true(gen.true_value())

        proc += gen.if_true(descend) # descending

        proc += gen.if_true(self._too_small(gen, x, clip))
        proc += gen.if_true(self._has_right(gen, x, clip))
        proc += descend_right
        proc += gen.else_if(gen.same(x, root))
        proc += return_null
        proc += gen.else_true()
        proc += ascend
        proc += gen.endif()
        proc += gen.else_if(self._has_left(gen, x, clip))
        proc += gen.set(x, left)
        proc += gen.else_if(self._too_large(gen, x, clip))
        proc += gen.if_true(gen.same(x, root))
        proc += return_null
        proc += gen.else_true()
        proc += ascend
        proc += gen.endif()
        proc += gen.else_if(self._node_ok(gen, x))
        proc += return_x
        proc += gen.else_if(gen.same(x, root))
        proc += gen.set(root, right) + gen.set(x, right) # descend_right
        proc += gen.else_true()
        proc += ascend
        proc += gen.endif()

        proc += gen.else_if(from_left) # ascending from left

        proc += gen.if_true(self._too_large(gen, x, clip))
        proc += return_null
        proc += gen.else_if(self._node_ok(gen, x, clip))
        proc += return_x
        proc += gen.else_if(self._has_right(gen, x, clip))
        proc += gen.set(descend, gen.true_value())
        proc += descend_right
        proc += gen.else_if(gen.same(x, root))
        proc += return_null
        proc += gen.else_true()
        proc += ascend
        proc += gen.endif()

        proc += gen.else_true() # ascending from right

        proc += gen.if_true(gen.same(x, root))
        proc += return_null
        proc += gen.else_true()
        proc += ascend
        proc += gen.endif()

        proc += gen.endif()

        proc += gen.endwhile()
        return proc, x

    def _has_left(self, gen, node, clip=True):
        return gen.both(
            gen.not_true(gen.is_null(gen.get_field(node, self.left_ptr))),
            self._subtree_ok(gen, gen.get_field(node, self.left_ptr), clip))
    def _has_right(self, gen, node, clip=True):
        return gen.both(
            gen.not_true(gen.is_null(gen.get_field(node, self.right_ptr))),
            self._subtree_ok(gen, gen.get_field(node, self.right_ptr), clip))
    def _node_ok(self, gen, node, clip=True):
        if not clip:
            return gen.true_value()
        return gen.true_value() # TODO
    def gen_query(self, gen, qvars):
        p, m = self._find_min(gen, self.name)
        return p, [m]
    def gen_current(self, gen):
        return "", self.cursor_name
    def gen_advance(self, gen, target=None):
        proc = gen.comment("ADVANCE")
        if target is None:
            target = self.cursor_name
        else:
            proc += gen.set(target, self.cursor_name)

        descend = fresh_name("descend") # are we allowed to descend?
        right_min = fresh_name("right_min")

        proc += gen.decl(descend, NativeTy(gen.bool_type()), gen.true_value())
        proc += gen.do_while()

        # successor of any node with a right child is the min node to the right
        proc += gen.decl(right_min, self.ty, gen.null_value())
        proc += gen.if_true(gen.both(descend, self._has_right(gen, target)))
        p, m = self._find_min(gen, gen.get_field(target, self.right_ptr))
        proc += p
        proc += gen.set(right_min, m)
        proc += gen.endif()

        proc += gen.if_true(gen.not_true(gen.is_null(right_min)))
        proc += gen.set(target, right_min)
        proc += gen.break_loop()

        # If there is no matching node to the right, then successor is
        # elsewhere in the tree.
        proc += gen.else_true()

        # Ascend until we get to a left child (or root)
        proc += gen.while_true(self._is_right_child(gen, target))
        proc += gen.set(target, gen.get_field(target, self.parent_ptr))
        proc += gen.endwhile()

        # Parent of this node *might* be successor, if all the augdata matches.
        proc += gen.set(target, gen.get_field(target, self.parent_ptr))

        proc += gen.endif()

        proc += gen.end_do_while(gen.both(
            gen.not_true(gen.is_null(target)),
            gen.not_true(self._node_ok(gen, target))))

        return proc
    def gen_next(self, gen):
        oldcursor = fresh_name()
        proc  = gen.decl(oldcursor, RecordType(), self.cursor_name)
        proc += self.gen_advance(gen)
        return proc, oldcursor
    def gen_has_next(self, gen):
        return "", gen.not_true(gen.is_null(self.cursor_name))
    def gen_insert(self, gen, x):
        prev = fresh_name("previous")
        curr = fresh_name("current")
        is_left = fresh_name("is_left")

        proc  = gen.decl(prev, self.ty, gen.null_value())
        proc += gen.decl(curr, self.ty, self.name)
        proc += gen.decl(is_left, NativeTy(gen.bool_type()), gen.false_value())

        # find insertion point
        proc += gen.while_true(gen.not_true(gen.is_null(curr)))
        proc += gen.set(prev, curr)
        proc += gen.if_true(gen.lt(self.fieldTy, gen.get_field(x, self.fieldName), gen.get_field(curr, self.fieldName)))
        proc += gen.set(curr, gen.get_field(curr, self.left_ptr))
        proc += gen.set(is_left, gen.true_value())
        proc += gen.else_true()
        proc += gen.set(curr, gen.get_field(curr, self.right_ptr))
        proc += gen.set(is_left, gen.false_value())
        proc += gen.endif()
        proc += gen.endwhile()

        # insert
        proc += gen.if_true(gen.is_null(prev))
        proc += gen.set(self.name, x)
        proc += gen.else_true()
        proc += gen.set(gen.get_field(x, self.parent_ptr), prev)
        proc += gen.if_true(is_left)
        proc += gen.set(gen.get_field(prev, self.left_ptr), x)
        proc += gen.else_true()
        proc += gen.set(gen.get_field(prev, self.right_ptr), x)
        proc += gen.endif()
        proc += gen.endif()

        return proc
    def gen_remove(self, gen, x, parent_structure=None):
        name = self.name if parent_structure is None else gen.get_field(parent_structure, self.name)

        p = fresh_name()
        l = fresh_name()
        r = fresh_name()
        proc  = gen.decl(p, self.ty, gen.get_field(x, self.parent_ptr))
        proc += gen.decl(l, self.ty, gen.get_field(x, self.left_ptr))
        proc += gen.decl(r, self.ty, gen.get_field(x, self.right_ptr))

        # case1: no children
        proc += gen.if_true(gen.both(
            gen.is_null(l),
            gen.is_null(r)))

        # case 1a: no parent
        proc += gen.if_true(gen.is_null(p))
        proc += gen.set(name, gen.null_value())

        # case 1b: is left child
        proc += gen.else_if(gen.lt(self.fieldTy, gen.get_field(x, self.fieldName), gen.get_field(gen.get_field(x, self.parent_ptr), self.fieldName)))
        proc += gen.set(gen.get_field(gen.get_field(x, self.parent_ptr), self.left_ptr), gen.null_value())
        proc += gen.set(gen.get_field(x, self.parent_ptr), gen.null_value())

        # case 1c: is right child
        proc += gen.else_true()
        proc += gen.set(gen.get_field(gen.get_field(x, self.parent_ptr), self.right_ptr), gen.null_value())
        proc += gen.set(gen.get_field(x, self.parent_ptr), gen.null_value())
        proc += gen.endif()

        # case2: only has left child
        proc += gen.else_if(gen.both(
            gen.not_true(gen.is_null(l)),
            gen.is_null(r)))

        proc += gen.set(gen.get_field(l, self.parent_ptr), gen.get_field(x, self.parent_ptr))

        # case 2a: no parent
        proc += gen.if_true(gen.is_null(p))
        proc += gen.set(name, l)

        # case 2b: is left child
        proc += gen.else_if(gen.lt(self.fieldTy, gen.get_field(x, self.fieldName), gen.get_field(p, self.fieldName)))
        proc += gen.set(gen.get_field(p, self.left_ptr), l)
        proc += gen.set(gen.get_field(x, self.parent_ptr), gen.null_value())

        # case 2c: is right child
        proc += gen.else_true()
        proc += gen.set(gen.get_field(p, self.right_ptr), l)
        proc += gen.set(gen.get_field(x, self.parent_ptr), gen.null_value())
        proc += gen.endif()

        proc += gen.set(gen.get_field(x, self.left_ptr), gen.null_value())

        # case3: only has right child
        proc += gen.else_if(gen.both(
            gen.is_null(l),
            gen.not_true(gen.is_null(r))))

        proc += gen.set(gen.get_field(r, self.parent_ptr), p)

        # case 2a: no parent
        proc += gen.if_true(gen.is_null(p))
        proc += gen.set(name, r)

        # case 2b: is left child
        proc += gen.else_if(gen.lt(self.fieldTy, gen.get_field(x, self.fieldName), gen.get_field(p, self.fieldName)))
        proc += gen.set(gen.get_field(p, self.left_ptr), r)
        proc += gen.set(gen.get_field(x, self.parent_ptr), gen.null_value())

        # case 2c: is right child
        proc += gen.else_true()
        proc += gen.set(gen.get_field(p, self.right_ptr), r)
        proc += gen.set(gen.get_field(x, self.parent_ptr), gen.null_value())
        proc += gen.endif()

        proc += gen.set(gen.get_field(x, self.right_ptr), gen.null_value())

        # case4: two children
        proc += gen.else_true()
        p, m = self._find_min(gen, gen.get_field(x, self.right_ptr), clip=False)
        proc += p
        # TODO: remove m, which has a parent and no left child
        # TODO: put m in place!
        proc += gen.endif()

        return proc
    def gen_remove_in_place(self, gen, parent_structure):
        next_record = fresh_name("next_record")
        proc  = gen.decl(next_record, RecordType())
        proc += self.gen_advance(gen, target=next_record)
        proc += self.gen_remove(gen, self.cursor_name, parent_structure=parent_structure)
        proc += gen.set(self.cursor_name, next_record)
        return proc

class SortedSet(Ty):
    def __init__(self, fieldTy, fieldName):
        self.name = fresh_name()
        self.fieldTy = fieldTy
        self.fieldName = fieldName
        self.ty = RecordType()
    def copy(self):
        return SortedSet(self.fieldTy.copy(), self.fieldName)
    def unify(self, other):
        if type(other) is UnsortedSet:
            return self
        if (type(other) is SortedSet or type(other) is AugTree) and other.fieldName == self.fieldName:
            return other
        raise Exception("not unifying {} and {}".format(self, other))
        return None

class UnsortedSet(Ty):
    def __init__(self):
        self.name = fresh_name()
        self.ty = RecordType()
        self.next_ptr = fresh_name()
        self.prev_ptr = fresh_name()
        self.cursor_name = fresh_name()
    def copy(self):
        return UnsortedSet()
    def unify(self, other):
        if type(other) is UnsortedSet or type(other) is SortedSet or type(other) is AugTree:
            return other
        return None
    def fields(self):
        return ((self.name, self.ty),)
    def construct(self, gen):
        return gen.set(self.name, gen.null_value())
    def needs_var(self, v):
        return False
    def state(self):
        return [(self.cursor_name, RecordType())]
    def private_members(self, gen):
        return [
            (self.next_ptr, RecordType(), gen.null_value()),
            (self.prev_ptr, RecordType(), gen.null_value())]
    def gen_type(self, gen):
        return gen.record_type()
    def gen_query(self, gen, qvars):
        return "", [self.name]
    def gen_current(self, gen):
        return "", self.cursor_name
    def gen_next(self, gen):
        oldcursor = fresh_name()
        proc  = gen.decl(oldcursor, RecordType(), self.cursor_name)
        proc += gen.set(self.cursor_name, gen.get_field(self.cursor_name, self.next_ptr))
        return proc, oldcursor
    def gen_has_next(self, gen):
        return "", gen.not_true(gen.is_null(self.cursor_name))
    def gen_insert(self, gen, x):
        proc  = gen.set(gen.get_field(x, self.prev_ptr), gen.null_value())
        proc += gen.set(gen.get_field(x, self.next_ptr), self.name)

        proc += gen.if_true(gen.not_true(gen.is_null(self.name)))
        proc += gen.set(gen.get_field(self.name, self.prev_ptr), x)
        proc += gen.endif()

        proc += gen.set(self.name, x)
        return proc
    def gen_remove(self, gen, x, parent_structure=None):
        name = self.name if parent_structure is None else gen.get_field(parent_structure, self.name)

        proc  = gen.if_true(gen.same(x, name))
        proc += gen.set(name, gen.get_field(x, self.next_ptr))
        proc += gen.endif()

        proc += gen.if_true(gen.not_true(gen.is_null(gen.get_field(x, self.next_ptr))))
        proc += gen.set(
            gen.get_field(gen.get_field(x, self.next_ptr), self.prev_ptr),
            gen.get_field(x, self.prev_ptr))
        proc += gen.endif()

        proc += gen.if_true(gen.not_true(gen.is_null(gen.get_field(x, self.prev_ptr))))
        proc += gen.set(
            gen.get_field(gen.get_field(x, self.prev_ptr), self.next_ptr),
            gen.get_field(x, self.next_ptr))
        proc += gen.endif()

        proc += gen.set(gen.get_field(x, self.prev_ptr), gen.null_value())
        proc += gen.set(gen.get_field(x, self.next_ptr), gen.null_value())
        return proc
    def gen_remove_in_place(self, gen, parent_structure):
        next_record = fresh_name()
        proc  = gen.decl(next_record, RecordType(), gen.get_field(self.cursor_name, self.next_ptr))
        proc += self.gen_remove(gen, self.cursor_name, parent_structure=parent_structure)
        proc += gen.set(self.cursor_name, next_record)
        return proc

class Filtered(Ty):
    def __init__(self, ty, fields, qvars, predicate):
        self.ty = ty
        self._fields = fields
        self.qvars = qvars
        self.predicate = predicate
    # def unify(self, other):
    #     if type(other) is UnsortedSet or type(other) is SortedSet:
    #         return other
    #     return None
    def fields(self):
        return self.ty.fields()
    def construct(self, gen):
        return self.ty.construct(gen)
    def needs_var(self, v):
        return self.ty.needs_var(v)
    def state(self):
        return self.ty.state()
    def private_members(self, gen):
        return self.ty.private_members(gen)
    def gen_type(self, gen):
        return self.ty.gen_type()
    def gen_query(self, gen, qvars):
        return self.ty.gen_query(gen, qvars)
    def gen_current(self, gen):
        return self.ty.gen_current(gen)
    def gen_next(self, gen):
        return self.ty.gen_next(gen)
    def gen_has_next(self, gen):
        return self.ty.gen_has_next(gen)
    def gen_insert(self, gen, x):
        proc = self.ty.gen_insert(gen, x)
        return gen.if_true(gen.predicate(self._fields, self.qvars, self.predicate, x)) + proc + gen.endif()
    def gen_remove(self, gen, x, parent_structure=None):
        proc = self.ty.gen_remove(gen, x)
        return gen.if_true(gen.predicate(self._fields, self.qvars, self.predicate, x)) + proc + gen.endif()
    def gen_remove_in_place(self, gen, parent_structure):
        return self.ty.gen_remove_in_place(gen, parent_structure)

INTERSECT_OP = "intersect"
UNION_OP     = "union"
CONCAT_OP    = "concat"

class Mix(Ty):
    def __init__(self, ty1, ty2, op):
        self.ty1 = ty1
        self.ty2 = ty2
        self.op = op
    # def unify(self, other):
    #     if type(other) is UnsortedSet or type(other) is SortedSet:
    #         return other
    #     return None
    def fields(self):
        return self.ty1.fields() + self.ty2.fields()
    def construct(self, gen):
        return self.ty1.construct(gen) + self.ty2.construct(gen)
    def needs_var(self, v):
        return self.ty1.needs_var(v) or self.ty2.needs_var(v)
    def state(self):
        return self.ty1.state() + self.ty2.state()
    def private_members(self, gen):
        return self.ty1.private_members(gen) + self.ty2.private_members(gen)
    # def gen_type(self, gen):
    #     return self.ty.gen_type()
    def gen_query(self, gen, qvars):
        if self.op == CONCAT_OP:
            proc1, es1 = self.ty1.gen_query(gen, qvars)
            proc2, es2 = self.ty2.gen_query(gen, qvars)
            return (proc1 + proc2, es1 + es2)
    def gen_current(self, gen):
        if self.op == CONCAT_OP:
            proc1, r1 = self.ty1.gen_has_next(gen)
            r = fresh_name()
            proc  = gen.decl(r, RecordType())
            proc += proc1
            proc += gen.if_true(r1)
            next1, r1 = self.ty1.gen_current(gen)
            proc += next1
            proc += gen.set(r, r1)
            proc += gen.else_true()
            next2, r2 = self.ty2.gen_current(gen)
            proc += next2
            proc += gen.set(r, r2)
            proc += gen.endif()
            return proc, r
    def gen_next(self, gen):
        if self.op == CONCAT_OP:
            proc1, r1 = self.ty1.gen_has_next(gen)
            r = fresh_name()
            proc  = gen.decl(r, RecordType())
            proc += proc1
            proc += gen.if_true(r1)
            next1, r1 = self.ty1.gen_next(gen)
            proc += next1
            proc += gen.set(r, r1)
            proc += gen.else_true()
            next2, r2 = self.ty2.gen_next(gen)
            proc += next2
            proc += gen.set(r, r2)
            proc += gen.endif()
            return proc, r
    def gen_has_next(self, gen):
        if self.op == CONCAT_OP:
            proc1, r1 = self.ty1.gen_has_next(gen)
            proc2, r2 = self.ty2.gen_has_next(gen)
            r = fresh_name()
            proc  = proc1
            proc += gen.decl(r, NativeTy(gen.bool_type()), r1)
            proc += gen.if_true(gen.not_true(r))
            proc += proc2
            proc += gen.set(r, r2)
            proc += gen.endif()
            return proc, r
    def gen_insert(self, gen, x):
        if self.op == CONCAT_OP:
            return self.ty1.gen_insert(gen, x) + self.ty2.gen_insert(gen, x)
    def gen_remove(self, gen, x):
        if self.op == CONCAT_OP:
            return self.ty1.gen_remove(gen, x) + self.ty2.gen_remove(gen, x)
    def gen_remove_in_place(self, gen, parent_structure):
        if self.op == CONCAT_OP:
            proc1, r1 = self.ty1.gen_has_next(gen)
            proc  = proc1
            proc += gen.if_true(r1)
            proc += self.ty1.gen_remove_in_place(gen, parent_structure)
            proc += gen.else_true()
            proc += self.ty2.gen_remove_in_place(gen, parent_structure)
            proc += gen.endif()
            return proc

_i = 0
def fresh_name(hint="name"):
    global _i
    _i += 1
    return "_{}{}".format(hint, _i)

def _key_fields(fields, predicate):
    return (v.name for v in predicate.vars() if v.name in fields)

def _make_key_args(fields, predicate):
    d = dict()
    for f, v in predicate.comparisons():
        if f not in fields:
            f, v = v, f
        d[f] = v
    return d

def _make_key_type(fields, key_fields):
    return Tuple({ k : NativeTy(fields[k]) for k in key_fields })

def _concretize(t):
    if type(t) is Iterator:
        yield Array()
        yield LinkedList()
    elif type(t) is SortedIterator:
        yield SortedArray.on_field(t.fieldTy, t.fieldName)
        yield BinaryTree.on_field(t.fieldTy, t.fieldName)
    elif type(t) is HashMap:
        for val_ty in _concretize(t.valueImpl):
            yield HashMap(t.keyTy, t.keyArgs, val_ty)
    elif type(t) is Tuple:
        for t1 in _concretize(t.t1):
            for t2 in _concretize(t.t2):
                yield Tuple(t1, t2, t.op)
    elif type(t) is Guarded:
        for tt in _concretize(t.impl):
            yield Guarded(tt, t.predicate)
    elif type(t) is Filtered:
        for tt in _concretize(t.impl):
            yield Filtered(tt, t.predicate)
    else:
        yield t

def _implement(plan, fields, qvars, resultTy=UnsortedSet()):
    """
    plan           - plans.Plan to implement
    fields         - dict { field_name : type }
    qvars          - dict { var_name   : type }
    resultTy       - what this plan should return
    """

    # if type(plan) is plans.AllWhere:
    #     if plan.predicate == predicates.Bool(True):
    #         return resultTy.copy()
    #     else:
    #         return Filtered(resultTy.copy(), list(fields.items()), list(qvars.items()), plan.predicate)
    # elif type(plan) is plans.HashLookup:
    #     key_fields = list(_key_fields(fields, plan.predicate))
    #     keyTy = _make_key_type(fields, key_fields)
    #     keyArgs = _make_key_args(fields, plan.predicate)
    #     t = HashMap(keyTy, keyArgs, resultTy)
    #     return _implement(plan.plan, fields, qvars, t)
    # elif type(plan) is plans.BinarySearch:
    #     t = resultTy.unify(AugTree(NativeTy(fields[plan.sortField]), plan.sortField, plan.predicate, fields))
    #     return _implement(plan.plan, fields, qvars, t)
    # elif type(plan) is plans.Intersect:
    #     assert type(resultTy) is UnsortedSet
    #     impl1 = _implement(plan.plan1, fields, qvars, resultTy)
    #     impl2 = _implement(plan.plan2, fields, qvars, resultTy)
    #     return Mix(impl1, impl2, INTERSECT_OP)
    # elif type(plan) is plans.Union:
    #     assert type(resultTy) is UnsortedSet
    #     impl1 = _implement(plan.plan1, fields, qvars, resultTy)
    #     impl2 = _implement(plan.plan2, fields, qvars, resultTy)
    #     return Mix(impl1, impl2, UNION_OP)
    # elif type(plan) is plans.Concat:
    #     assert type(resultTy) is UnsortedSet
    #     impl1 = _implement(plan.plan1, fields, qvars, resultTy)
    #     impl2 = _implement(plan.plan2, fields, qvars, resultTy)
    #     return Mix(impl1, impl2, CONCAT_OP)
    # else:
    #     raise Exception("codegen not implemented for {}".format(type(plan)))

    if type(plan) is plans.AllWhere:
        if plan.predicate == predicates.Bool(True):
            return resultTy.copy()
        else:
            return Guarded(resultTy.copy(), list(fields.items()), list(qvars.items()), plan.predicate)
    elif type(plan) is plans.HashLookup:
        key_fields = list(_key_fields(fields, plan.predicate))
        keyTy = _make_key_type(fields, key_fields)
        keyArgs = _make_key_args(fields, plan.predicate)
        t = HashMap(keyTy, keyArgs, resultTy)
        return _implement(plan.plan, fields, qvars, t)
    # elif type(plan) is plans.BinarySearch:
    # elif type(plan) is plans.Intersect:
    # elif type(plan) is plans.Union:
    # elif type(plan) is plans.Concat:
    # elif type(plan) is plans.Filter:
    else:
        raise Exception("codegen not implemented for {}".format(type(plan)))

def capitalize(s):
    return s[0].upper() + s[1:]

def codegen(fields, queries, gen):
    """
    Code generation entry point.
    fields    - list of (field_name, type)
    queries   - list of queries.Query objects with .bestPlan set
    gen       - code generator object
    """

    # gen.begin()

    fields = dict(fields)
    for q in queries:
        vars = dict(q.vars)
        # resultTy = UnsortedSet() if q.sort_field is None else AugTree(
        #     NativeTy(fields[q.sort_field]),
        #     q.sort_field,
        #     predicates.Bool(True),
        #     fields)
        # attrs = () if q.sort_field is None else (SortedBy(q.sort_field))
        resultTy = Iterator()
        for raw_impl in _implement(q.bestPlan, fields, vars, resultTy):
            for impl in _concretize(raw_impl):
                print impl
                q.impl = impl
        # q.impl = _implement(q.bestPlan, fields, vars, resultTy)

    gen.write(fields, queries)

    # gen.declare_record_type(fields, privateFields)
    # gen.declare_datastructure(queries)

    # gen.implement_record_type(fields, privateFields)
    # gen.implement_datastructure(queries)

    # gen.end()
