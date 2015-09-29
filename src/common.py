from functools import total_ordering

@total_ordering
class ADT(object):
    def children(self):
        return ()
    def size(self):
        s = 1
        for child in self.children():
            if isinstance(child, ADT):
                s += child.size()
        return s
    def contains_subtree(self, tree):
        if self == tree:
            return True
        for child in self.children():
            if isinstance(child, ADT) and child.contains_subtree(tree):
                return True
    def __str__(self):
        return "{}({})".format(type(self).__name__, ", ".join(str(child) for child in self.children()))
    def __hash__(self):
        return hash(self.children())
    def __eq__(self, other):
        return type(self) is type(other) and self.children() == other.children()
    def __lt__(self, other):
        return (self.children() < other.children()) if (type(self) is type(other)) else (type(self) < type(other))

_i = 0
def fresh_name(hint="name"):
    global _i
    _i += 1
    return "_{}{}".format(hint, _i)

def capitalize(s):
    return (s[0].upper() + s[1:]) if s else s
