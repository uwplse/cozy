from cozy.common import nested_dict

class NatDict(object):
    def __init__(self, factory):
        self.factory = factory
        self.data = []
    def get(self, i, default=None):
        data = self.data
        if i < 0 or i >= len(data):
            return default
        return data[i]
    def __getitem__(self, i):
        self._extend(i)
        return self.data[i]
    def __setitem__(self, i, val):
        self._extend(i)
        self.data[i] = val
    def values(self):
        return iter(self.data)
    def keys(self):
        return range(len(self.data))
    def items(self):
        data = self.data
        for i in range(len(data)):
            yield (i, data[i])
    def _extend(self, n):
        data = self.data
        if n < len(data):
            return
        factory = self.factory
        data.extend(factory() for i in range(len(data), n + 1))

class Cache(object):
    def __init__(self, items=None):
        # self.data[type_tag][type][size] is list of exprs
        self.data = nested_dict(2, lambda: NatDict(list))
        self.size = 0
        if items:
            for (e, size) in items:
                self.add(e, size)
    def tag(self, t):
        return type(t)
    def is_tag(self, t):
        return isinstance(t, type)
    def add(self, e, size):
        self.data[self.tag(e.type)][e.type][size].append(e)
        self.size += 1
    def evict(self, e, size):
        try:
            self.data[self.tag(e.type)][e.type][size].remove(e)
            self.size -= 1
        except ValueError:
            # this happens if e is not in the list, which is fine
            pass
    def find(self, type=None, size=None):
        type_tag = None
        if type is not None:
            if self.is_tag(type):
                type_tag = type
                type = None
            else:
                type_tag = self.tag(type)
        res = []
        for x in (self.data.values() if type_tag is None else [self.data.get(type_tag, {})]):
            for y in (x.values() if type is None else [x.get(type, {})]):
                for z in (y.values() if size is None else [y.get(size, [])]):
                    res += z
        return res
    def types(self):
        for d in self.data.values():
            yield from d.keys()
    def __iter__(self):
        for x in self.data.values():
            for y in x.values():
                for (size, es) in y.items():
                    for e in es:
                        yield (e, size)
    def __len__(self):
        return self.size
    def random_sample(self, n):
        import random
        es = [ e for (e, size) in self ]
        return random.sample(es, min(n, len(es)))
