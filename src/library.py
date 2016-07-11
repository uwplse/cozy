"""
Concrete data structure implementations.
"""

import syntax
import syntax_tools

class ConcreteType(syntax.Type):
    def prettyprint(self):
        raise NotImplementedError(str(type(self)))

class LinkedList(ConcreteType):
    def __init__(self, t):
        self.t = t
    def prettyprint(self):
        return "LinkedList<{}>".format(syntax_tools.pprint(self.t))

class ArrayList(ConcreteType):
    pass

class HashMap(ConcreteType):
    def __init__(self, key_type, value_type):
        self.k = key_type
        self.v = value_type
    def prettyprint(self):
        return "HashMap<{}, {}>".format(syntax_tools.pprint(self.k), syntax_tools.pprint(self.v))

class AugTree(ConcreteType):
    pass

class Heap(ConcreteType):
    pass

class TrackedSum(ConcreteType):
    pass

class TrackedMinOrMax(ConcreteType):
    pass
