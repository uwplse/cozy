
class Ty(object):
    def unify(self, other):
        pass

class HashMap(Ty):
    def __init__(self, fieldTy, fieldName, ty):
        self.fieldTy = fieldTy
        self.fieldName = fieldName
        self.ty = ty
    def unify(self, other):
        if type(other) is HashMap and other.fieldName == self.fieldName:
            unif = self.ty.unify(other.ty)
            if unif is not None:
                return HashMap(self.fieldTy, self.fieldName, unif)
        return None

class SortedSet(Ty):
    def __init__(self, fieldTy, fieldName):
        self.fieldTy = fieldTy
        self.fieldName = fieldName
    def unify(self, other):
        if type(other) is UnsortedSet:
            return self
        if type(other) is SortedSet and other.fieldName == self.fieldName:
            return self
        return None

class UnsortedSet(Ty):
    def unify(self, other):
        if type(other) is UnsortedSet or type(other) is SortedSet:
            return other
        return None

_i = 0
def fresh_name():
    global _i
    _i += 1
    return "name{}".format(_i)
