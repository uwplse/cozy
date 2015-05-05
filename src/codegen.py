
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
            return HashMap(self.fieldName, self.ty.unify(other.ty))
        raise Exception("failed to unify {} and {}".format(self, other))

class SortedSet(Ty):
    def __init__(self, fieldTy, fieldName):
        self.fieldTy = fieldTy
        self.fieldName = fieldName
    def unify(self, other):
        if type(other) is UnsortedSet:
            return self
        if type(other) is SortedSet and other.fieldName == self.fieldName:
            return self
        raise Exception("failed to unify {} and {}".format(self, other))

class UnsortedSet(Ty):
    def unify(self, other):
        if type(other) is UnsortedSet or type(other) is SortedSet:
            return other
        raise Exception("failed to unify {} and {}".format(self, other))

_i = 0
def fresh_name():
    global _i
    _i += 1
    return "name{}".format(_i)
