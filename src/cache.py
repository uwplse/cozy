from collections import defaultdict

def _expand(l, size):
    while len(l) < size:
        l.append([])

class Cache(object):

    def __init__(self, cost_func, size_func, key_func, allow_multi=False):
        self.cost_func = cost_func
        self.size_func = size_func
        self.key_func = key_func
        self.allow_multi = allow_multi
        self.entries_by_key = defaultdict(list)
        self.entries_by_size = []
        self.costs_by_key = dict()
        self.size = 0

    def put(self, entry, key=None, size=None, cost=None):
        if cost is None:
            cost = self.cost_func(entry)
        if key is None:
            key = self.key_func(entry)
        if size is None:
            size = self.size_func(entry)
        old_cost = self.costs_by_key.get(key)
        if old_cost is not None:
            if old_cost <= cost or (old_cost == cost and not self.allow_multi):
                return self.entries_by_key[key][0]
            if old_cost > cost:
                self.evict(key)
        _expand(self.entries_by_size, size + 1)
        self.entries_by_size[size].append(entry)
        self.entries_by_key[key].append(entry)
        self.costs_by_key[key] = cost
        self.size += 1
        return entry

    def evict_higher_cost_entries(self, cost):
        for key, c in list(self.costs_by_key.items()):
            if c > cost:
                self.size -= len(self.entries_by_key[key])
                for x in self.entries_by_key[key]:
                    self.entries_by_size[self.size_func(x)].remove(x)
                del self.entries_by_key[key]
                del self.costs_by_key[key]

    def evict(self, key):
        for entry in self.get(key):
            self.entries_by_size[self.size_func(entry)].remove(entry)
        if key in self.entries_by_key:
            self.size -= len(self.entries_by_key[key])
            del self.entries_by_key[key]
            del self.costs_by_key[key]

    def get_cost(self, key):
        return self.costs_by_key.get(key)

    def get(self, key):
        return self.entries_by_key.get(key, ())

    def entries_of_size(self, size):
        if size >= len(self.entries_by_size) or size < 0:
            return ()
        return self.entries_by_size[size]

    def all(self):
        for l in self.entries_by_size:
            for x in l:
                yield x

    def __len__(self):
        return self.size

    def __str__(self):
        return "Cache[{}]".format(", ".join(str(e) for e in self.all()))
