
def only_from(it):
    it = iter(it)
    try:
        res = next(it)
    except StopIteration:
        return None
    try:
        next(it)
    except StopIteration:
        return res
    return None

def only_such(it, cond):
    return only_from(filter(cond, it))

def gcd(a,b = None):
    if b is None: # iterative version
        res = 0
        for x in a: res = gcd(res,x)
        return res

    # main algorithm
    while b != 0: a,b = b,a%b
    return a

class LazyList:
    def __init__(self, constructor):
        self.constructor = constructor
        self.l = []
    def __getitem__(self, i):
        if isinstance(i, slice):
            if step > 0: needed_size = i.stop
            else: needed_size = i.start+1
        else: needed_size = i+1
        while len(self.l) < needed_size:
            self.l.append(self.constructor(len(self.l)))
        return self.l[i]

class OrderedSet:
    def __init__(self, l, s):
        self.l = l
        self.s = s

    def __bool__(self): return bool(self.l)
    def __len__(self): return len(self.l)
    def __iter__(self): return iter(self.l)
    def __constains__(self, other): return other in self.s
    def __getitem__(self, i): return self.l[i]

    def __or__(self, other):
        if self is other: return self
        elif other.s <= self.s: return self
        elif not self.l: return other
        else:
            l = list(self.l)
            s = set(self.s)
            for x in other.l:
                if x in s: continue
                l.append(x)
                s.add(x)
            return OrderedSet(l, s)
    def __sub__(self, other):
        l = [x for x in self.l if x not in other.s]
        return OrderedSet(l, set(l))
    def __and__(self, other):
        if self is other or self.s <= other.s: return self
        l = [x for x in self.l if x in other.s]
        return OrderedSet(l, set(l))

    def __delitem__(self, i):
        deleted = self.l[i]
        if isinstance(deleted, list):
            self.s.difference_update(deleted)
        else:
            self.s.remove(deleted)
        del self.l[i]

    def add(self, x):
        if x in self.s: return
        self.s.add(x)
        self.l.append(x)
    def extend(self, other):
        if not self.l:
            self.l = list(other.l)
            self.s = set(other.s)
        else:
            self.l.extend(x for x in other.l if x not in self.s)
            self.s.update(other.s)
    def copy(self):
        return OrderedSet(list(self.l), set(self.s))
    def rev_copy(self):
        return OrderedSet(list(reversed(self.l)), set(self.s))
    def map_uq(self, f):
        return self.from_uq_iter(map(f, self.l))
    def map(self, f):
        return self.from_iter(map(f, self.l))

    @staticmethod
    def empty():
        return OrderedSet([], set())
    @staticmethod
    def singleton(x):
        l = [x]
        return OrderedSet(l, set(l))
    @staticmethod
    def union(*osets):
        res = OrderedSet.empty()
        for oset in osets: res.extend(oset)
        return res
    @staticmethod
    def from_iter(data):
        res = OrderedSet.empty()
        for x in data: res.add(x)
        return res
    @staticmethod
    def from_uq_iter(data):
        l = list(data)
        s = set(l)
        assert len(l) == len(s)
        return OrderedSet(l,s)

    def __str__(self):
        return '`{'+', '.join(map(str, self.l))+'}'
    def __repr__(self):
        return self.__str__()
