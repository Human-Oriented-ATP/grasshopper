from weakref import WeakValueDictionary
from collections import defaultdict
import itertools

FREE_VAR = "FREE_VAR"
SHARED_VAR = "SHARED_VAR"
FIXED_VAR = "FIXED_VAR"

class classproperty(property):
    def __get__(self, cls, owner):
        return classmethod(self.fget).__get__(None, owner)()

class Term:

    _X = None

    def __init__(self, direct_f = None, direct_args = (), direct_meta_args = None, direct_var_name = None, direct_var_type = None):
        if self.initialized: return
        self.f = direct_f
        self.args = direct_args
        self.meta_args = direct_meta_args
        self.var_name = direct_var_name
        self.var_type = direct_var_type
        self._all_vars = None
        if self.f is None:
            assert self.args == ()
            assert self.meta_args is None
            assert isinstance(self.var_name, str)
            assert self.var_type in (FREE_VAR, SHARED_VAR, FIXED_VAR)
            self.is_var = True
        else:
            assert direct_var_type == None
            assert isinstance(self.f, Constant)
            assert self.args is not None
            assert self.meta_args is not None
            self.is_var = False
        self.is_constant = len(self.args) == 0

    def __new__(cls, *args,  **kwargs):
        if cls == Term:
            assert len(args) == 1 and not kwargs
            return to_term(args[0])

        if len(args) == 1 and not kwargs and isinstance(args[0], cls): return args[0]
        if 'direct_f' in kwargs or 'direct_var_name' in kwargs:
            res = super().__new__(cls)
        else:
            assert 'direct_args' not in kwargs
            assert 'direct_meta_args' not in kwargs
            assert 'direct_var_name' not in kwargs
            assert 'direct_var_type' not in kwargs
            res = cls.mk(*args, **kwargs)
        return res

    def __str__(self):
        if self.f is not None:
            return self.f.notation(*self.args, **self.meta_args)
        else:
            return self.var_name

    @property
    def initialized(self):
        return hasattr(self, 'f')

    @property
    def all_vars(self):
        if self._all_vars is None:
            if self.is_var: self._all_vars = frozenset((self,))
            else: self._all_vars = frozenset().union(*(arg.all_vars for arg in self.args))
        return self._all_vars

    __match_args__ = ['f', 'args']

    @staticmethod
    def to_term(x):
        if isinstance(x, Term): return x
        else:
            t = Term.to_type(type(x))
            if t is None:
                raise Exception(f"Cannot convert to a term: {x}")
            return t(x)

    @staticmethod
    def to_type(t):
        if issubclass(t, Term): return t
        elif issubclass(t, bool): return TermBool
        elif issubclass(t, int): return TermInt
        else: return None

    @classmethod
    def free_var(cls, name):
        assert isinstance(name, str)
        return cls(direct_var_name = name, direct_var_type = FREE_VAR)
    @classmethod
    def shared_var(cls, name):
        assert isinstance(name, str)
        return cls(direct_var_name = name, direct_var_type = SHARED_VAR)
    @classmethod
    def fixed_var(cls, name):
        assert isinstance(name, str)
        return cls(direct_var_name = name, direct_var_type = FIXED_VAR)

    @property
    def is_free_var(self):
        return self.is_var and self.var_type == FREE_VAR
    @property
    def is_shared_var(self):
        return self.is_var and self.var_type == SHARED_VAR
    @property
    def is_fixed_var(self):
        return self.is_var and self.var_type == FIXED_VAR

    @classproperty
    def X(cls):
        if cls._X is None:
            cls._X = cls.free_var('X')
        return cls._X

    @classmethod
    def make_app(cls, f, args, meta_args):
        assert isinstance(f, Constant)
        return cls(direct_f = f, direct_args = args, direct_meta_args = meta_args)

    @classmethod
    def new_const(cls, name):
        return Constant(lambda: None, name, cls)()

    def value(self):
        raise Exception("Not implemented")

    def leaf_iter(self, is_leaf):
        if is_leaf(self):
            yield self
        elif self.is_var: return
        else:
            for arg in self.args:
                yield from arg.leaf_iter(is_leaf)

    def subterms_iter(self):
        yield self
        if not self.is_var:
            for arg in self.args:
                yield from arg.subterms_iter()

class Constant:
    def __init__(self, build, name, out_type):
        self._build = build
        self.name = name
        if out_type is None: self.out_type = None
        else: self.out_type = Term.to_type(out_type)
        self._arg_cache = WeakValueDictionary()
        self._build_cache = WeakValueDictionary()

        def notation(*args, **kwargs):
            if not args and not kwargs: return self.name
            else:
                all_args = tuple(
                    str(arg) for arg in args
                ) + tuple(
                    f"{key} = {value}" for key,value in kwargs.items()
                )
                return self.name+'('+', '.join(all_args)+')'
        self.notation = notation

    def __call__(self, *args, **meta_args):
        if self.out_type is None:
            raise Exception(f"out_type of {self.name} has not been set")
        args = tuple(Term.to_term(arg) for arg in args)
        arg_cache_key = args, tuple(meta_args.items())
        term = self._arg_cache.get(arg_cache_key)
        if term is None:

            x = self._build(*args, **meta_args)
            if x is None: x = arg_cache_key
            if Term.to_type(type(x)) == self.out_type:
                term = Term.to_term(x)
            else:
                assert not isinstance(x, Term)
                term = self._build_cache.get(x)
                if term is None:
                    term = self.out_type.make_app(self, args, meta_args)
                    self._build_cache[x] = term
            self._arg_cache[arg_cache_key] = term

        return term

    def __str__(self):
        return self.name
    def __repr__(self):
        return f"Constant({self.name})"

def term_fun(build):
    out_type = build.__annotations__.get('return')
    name = build.__name__
    if name.startswith('_'): name = name[1:]
    return Constant(build, name, out_type)

class TermBool(Term):
    @staticmethod
    def mk(value):
        assert isinstance(value, (bool,int))
        if value: return TermBool.true
        else: return TermBool.false

    @staticmethod
    @term_fun
    def invert(x):
        assert isinstance(x, TermBool)
        if x.f == TermBool.invert: return x.args[0]
        elif x.f == conjunction:
            return disjunction(*(TermBool.invert(y) for y in x.args))
        elif x.f == disjunction:
            return conjunction(*(TermBool.invert(y) for y in x.args))
        elif x == TermBool.true: return TermBool.false
        elif x == TermBool.false: return TermBool.true
        return None

    @staticmethod
    def invert_notation(x):
        if x.f == equals:
            a,b = x.args
            return f"{a} != {b}"
        elif x.f == TermInt.le:
            a,b = x.args
            return f"{a} > {b}"            
        elif x.f == JumpSet._contains:
            a,b = x.args
            return f"{b} !in {a}"
        elif x.f == MineField.getitem:
            a,b = x.args
            return f"{b} !in {a}"
        elif x.f == TermInt.le:
            a,b = x.args
            return f"{a} > {b}"            
        else:
            return '!'+str(x)

    def __invert__(self):
        return TermBool.invert(self)
    def __or__(self, other):
        return disjunction(self, other)
    def __and__(self, other):
        return conjunction(self, other)

    @property
    @term_fun
    def as_int(self):
        assert isinstance(self, TermBool)
        if self.f == TermBool.invert: return TermInt(1) - self.args[0].as_int
        elif self == TermBool.true: return TermInt(1)
        elif self == TermBool.false: return TermInt(0)
        return None

    # conversions to standard boolean
    @property
    def possible(self):
        return self != TermBool.false
    @property
    def guaranteed(self):
        return self == TermBool.true

    @property
    def is_literal(self):
        if self.f == equals:
            return not isinstance(self.args[0], TermBool)
        elif self.f in (conjunction, disjunction):
            return False
        elif self in (TermBool.true, TermBool.false):
            return False
        return True
    @property
    def is_atom(self):
        return self.is_literal and self.f != TermBool.invert
    def literals(self):
        return self.leaf_iter(lambda x: x.is_literal)
    def atoms(self, expand_neg = True):
        return self.leaf_iter(lambda x: x.is_atom)

    @property
    def disj_args(self):
        if self.f == disjunction: return self.args
        else: return (self,)
    @property
    def conj_args(self):
        if self.f == conjunction: return self.args
        else: return (self,)

    # clausification
    def clausify_raw(self):
        if self.f == equals and isinstance(self.args[0], TermBool):
            a,b = self.args
            na = (~a).clausify_raw()
            nb = (~b).clausify_raw()
            a = a.clausify_raw()
            b = b.clausify_raw()
            return (na | b) & (a | nb)
        elif self.f == conjunction:
            return conjunction(*(x.clausify_raw() for x in self.args))
        elif self.f == disjunction:
            options = [x.clausify_raw().conj_args for x in self.args]
            return conjunction(*(
                disjunction(*option)
                for option in itertools.product(*options)
            ))
        else:
            return self
    def drop_subsumed_clauses(self):
        clauses_d = defaultdict(list)
        for clause in self.conj_args:
            clauses_d[len(clause.disj_args)].append(clause)
        clauses_sorted = [
            clauses
            for l, clauses in sorted(clauses_d.items())
        ]
        res = []
        res_sets = []
        for clauses in clauses_sorted:
            cur_sets = []
            for clause in clauses:
                s = set(clause.disj_args)
                if any(x <= s for x in res_sets): continue
                cur_sets.append(s)
                res.append(clause)
            res_sets.extend(cur_sets)
        return conjunction(*res)
    def clausify(self):
        return self.clausify_raw().drop_subsumed_clauses()

    def value(self):
        if self == TermBool.true: return True
        elif self == TermBool.false: return False
        else:
            raise Exception(f"Cannot convert {self} to bool, uncertain value")
    def __bool__(self):
        return self.value()

@term_fun
def conjunction(*args):
    assert all(isinstance(arg, TermBool) for arg in args)
    if TermBool.false in args: return TermBool.false
    elif len(args) == 0: return TermBool.true
    elif len(args) == 1: return args[0]

    simplifiable = any(
        arg.f == conjunction or arg == TermBool.true
        for arg in args
    ) or len(set(args)) != len(args)
    if not simplifiable: return frozenset(args)

    used = set([TermBool.true])
    res = []
    for arg in args:
        if arg in used: continue
        used.add(arg)
        if arg.f == conjunction:
            for arg2 in arg.args:
                if arg2 in used: continue
                used.add(arg2)
                res.append(arg2)
        else:
            res.append(arg)

    return conjunction(*res)

@term_fun
def disjunction(*args):
    assert all(isinstance(arg, TermBool) for arg in args)
    if TermBool.true in args: return TermBool.true
    elif len(args) == 0: return TermBool.false
    elif len(args) == 1: return args[0]

    simplifiable = any(
        arg.f == disjunction or arg == TermBool.false
        for arg in args
    ) or len(set(args)) != len(args)

    if not simplifiable: return frozenset(args)

    used = set([TermBool.false])
    res = []
    for arg in args:
        if arg in used: continue
        used.add(arg)
        if arg.f == disjunction:
            for arg2 in arg.args:
                if arg2 in used: continue
                used.add(arg2)
                res.append(arg2)
        else:
            res.append(arg)

    return disjunction(*res)

TermBool.true = TermBool.new_const('True')
TermBool.false = TermBool.new_const('False')
TermBool.invert.out_type = TermBool
TermBool.invert.notation = TermBool.invert_notation
conjunction.out_type = TermBool
conjunction.notation = lambda *args: '('+' && '.join(map(str, args))+')'
disjunction.out_type = TermBool
disjunction.notation = lambda *args: '('+' || '.join(map(str, args))+')'

@term_fun
def equals(a,b) -> bool:
    assert type(a) == type(b), (type(a), type(b))
    if a == b: return True

    if isinstance(a, TermInt):
        if a.is_num_const and b.is_num_const:
            return False
    elif isinstance(a, TermBool):
        if a == TermBool.true: return b
        elif a == TermBool.false: return ~b
        elif b == TermBool.true: return a
        elif b == TermBool.false: return ~a

    return None
    
equals.notation = lambda a,b: (f"{a} <=> {b}" if isinstance(a, TermBool) else f"{a} = {b}")

class Substitution:
    def __init__(self, base_dict):
        self.base_dict = base_dict
        self.cache = dict(base_dict)
        self.vs = set(base_dict.keys())
        self.var_only = all(v.is_var for v in self.vs)
    def __getitem__(self, term):
        if isinstance(term, Substitution):
            term.substitute(self)
        res = self.cache.get(term)
        if res is None:
            if self.var_only and not (term.all_vars & self.vs): res = term
            else:
                if term.is_var: res = term
                else:
                    args = tuple(self[arg] for arg in term.args)
                    res = term.f(*args, **term.meta_args)
            self.cache[term] = res
        return res
    def substitute(self, subst):
        if not isinstance(subst, Substitution):
            subst = Substitution(subst)
        if not subst.base_dict: return self
        base_dict = {
            key : subst[value]
            for key,value in self.base_dict.items()
        }
        for key, value in subst.base_dict.items():
            base_dict.setdefault(key, value)
        return Substitution(base_dict)

class Model:
    def __init__(self, base_dict):
        self.subst = Substitution(base_dict)
    def __getitem__(self, key):
        return self.subst[key]
    def __setitem__(self, key, value):
        base_dict = dict(self.subst.base_dict)
        base_dict[key] = value
        self.subst = Substitution(base_dict)

class TermInt(Term):
    def __init__(self, *args, **kwargs):
        if self.initialized: return
        super().__init__(*args, **kwargs)
        if self.f == TermInt._mk:
            self.const = self.meta_args['const']
            self.muls = self.meta_args['muls']
            self.summands = self.args
        else:
            self.const = 0
            self.muls = (1,)
            self.summands = (self,)

    @staticmethod
    def mk(*args):
        muls = args[::2]
        summands = args[1::2]
        assert all(isinstance(x, int) for x in muls)
        if len(muls) > len(summands):
            const = muls[-1]
            muls = muls[:-1]
        else:
            const = 0

        return TermInt._mk(*summands, muls = muls, const = const)

    @staticmethod
    def sum(*args, const = 0):
        muls = (1,)*len(args)
        assert all(isinstance(x, int) for x in muls)
        return TermInt._mk(*args, muls = muls, const = const)

    @staticmethod
    @term_fun
    def _mk(*args, muls, const):
        assert all(isinstance(x, TermInt) for x in args)
        assert all(isinstance(x, int) for x in muls)
        assert len(muls) == len(args)
        assert isinstance(const, int)

        simplifiable = (
            len(set(args)) < len(args) or
            any(arg.f == TermInt._mk for arg in args)
            or any(mul == 0 for mul in muls)
        )

        if simplifiable:

            # Simplify sum
            arg_to_mul = defaultdict(int)
            for arg, mul in zip(args, muls):
                for arg2, mul2 in zip(arg.summands, arg.muls):
                    arg_to_mul[arg2] += mul*mul2
                const += mul * arg.const

            args_muls = [
                (arg, mul)
                for arg, mul in arg_to_mul.items()
                if mul != 0
            ]
            args = tuple(arg for (arg, mul) in args_muls)
            muls = tuple(mul for (arg, mul) in args_muls)

            return TermInt._mk(*args, muls = muls, const = const)

        if const == 0 and len(args) == 1 and muls[0] == 1:
            return args[0]
        else:
            return frozenset(zip(args, muls)), const

    @staticmethod
    def mk_notation(*args, muls, const):
        res = []
        def add_summand(x):
            if not res: res.append(str(x))
            elif x.startswith('-'):
                res.append(' - ')
                res.append(x[1:])
            else:
                res.append(' + ')
                res.append(x)
        for mul,arg in zip(muls, args):
            if mul == 1: add_summand(str(arg))
            elif mul == -1: add_summand('-'+str(arg))
            else: add_summand(f"{mul}*{arg}")
        if const: add_summand(str(const))
        if not res: return '0'
        return ''.join(res)

    @property
    def is_num_const(self):
        return self.is_constant and self.f == self._mk
    def value(self):
        if not self.is_num_const:
            raise Exception(f"Cannot evaluate nonconstant integer {self}")
        return self.const
    def __int__(self):
        return self.value()

    def __add__(self, other):
        return TermInt(1,self,1,other)
    def __radd__(self, other):
        return TermInt(1,other,1,self)
    def __sub__(self, other):
        return TermInt(1,self,-1,other)
    def __rsub__(self, other):
        return TermInt(1,other,-1,self)
    def __neg__(self, other):
        return TermInt(-1,self)
    def __mul__(self, c):
        assert isinstance(c, int)
        return TermInt(c,self)
    def __rmul__(self, c):
        assert isinstance(c, int)
        return TermInt(c,self)

    @staticmethod
    @term_fun
    def le(a,b) -> bool:
        assert isinstance(a, TermInt)
        assert isinstance(b, TermInt)
        diff = b - a
        if diff.is_num_const:
            if diff.value() >= 0: return TermBool.true
            else: return TermBool.false
        else:
            return None

    def __le__(self, other):
        return TermInt.le(self, other)
    def __ge__(self, other):
        return TermInt.le(other, self)
    def __lt__(self, other):
        return ~TermInt.le(other, self)
    def __gt__(self, other):
        return ~TermInt.le(self, other)

TermInt._mk.out_type = TermInt
TermInt._mk.notation = TermInt.mk_notation
TermInt.le.notation = lambda x,y: f"{x} <= {y}"
TermBool.as_int.fget.out_type = TermInt

class TermSequence(Term):
    def __init__(self, *args, **kwargs):
        if self.initialized: return
        super().__init__(*args, **kwargs)
        if self.f == type(self).concat:
            self.parts = self.args
        else:
            self.parts = (self,)

        if len(self.parts) == 1:
            self.subsequences = (self,)
        else:
            self.subsequences = tuple(
                part if isinstance(part, type(self)) else type(self)(part)
                for part in self.parts
            )

    def __init_subclass__(cls, default, **kwargs):
        super().__init_subclass__(**kwargs)

        assert isinstance(default, Term)
        base_type = type(default)
        cls.base_type = base_type
        cls.default = default
        
        @term_fun
        def concat(*args) -> cls:
            assert all(isinstance(arg, (cls, base_type)) for arg in args)
            if not any(arg.f == cls.concat for arg in args): return None # just build term
            else: # simplify
                parts = []
                for arg in args:
                    if arg.f == cls.concat:
                        parts.extend(arg.args)
                    else:
                        parts.append(arg)
                return cls.concat(*parts)
        def concat_notation(*args):
            res = []
            for arg in args:
                if isinstance(arg, cls): res.append(str(arg)+'...')
                else: res.append(str(arg))
            return '['+', '.join(res)+']'
        concat.notation = concat_notation

        cls.concat = concat

    def __add__(self, other):
        return self.concat(self, other)

    @property
    def is_explicit_seq(self):
        return (
            (self.f == self._mk) and
            all(isinstance(x, self.base_type) for x in self.args)
        )

    @classmethod
    def mk(cls, *args):
        if len(args) == 1 and isinstance(args[0], (tuple, list)):
            args = args[0]
        args = tuple(arg if isinstance(arg, Term) else cls.base_type(arg) for arg in args)
        return cls.concat(*args)

    def value(self):
        cls = type(self)
        if self.f != cls.concat: raise Exception("Sequence not evaluated")
        elif not all(isinstance(arg, cls.base_type) for arg in self.args):
            raise Exception("Sequence contains unevaluated subsequence")
        return [arg.value() for arg in self.args]

    def __getitem__(self, n):
        return self.getitem(self, n)

class MineField(TermSequence, default = TermBool.false):
    @property
    @term_fun
    def count(self) -> TermInt:
        if self.f == MineField.concat:
            const = 0
            summands = []
            for arg in self.args:
                if isinstance(arg, MineField): summands.append(arg.count)
                else:
                    assert isinstance(arg, TermBool)
                    summands.append(arg.as_int)
            return TermInt.sum(*summands, const = const)
        elif self.f == Jumps.landings.fget:
            return self.args[0].number
        elif self.f == Jump.to_empty_minefield.fget:
            return TermInt(0)
        else:
            return None

    @staticmethod
    @term_fun
    def getitem(self, n) -> TermBool:
        assert isinstance(self, MineField)
        assert isinstance(n, TermInt)
        if self.f == MineField.concat:
            options = []
            for arg in self.args:
                if isinstance(arg, MineField):
                    options.append(arg[n])
                    n = n - arg.length
                elif isinstance(arg, TermBool):
                    options.append(arg & equals(n, 0))
                    n = n - 1
                else:
                    raise Exception(f"Unexpected arg type {type(arg)}: {arg}")
            return disjunction(*options)
        elif self.f == Jump.to_empty_minefield.fget:
            return TermBool.false
        elif (n < 0).guaranteed:
            return TermBool.false
        else:
            return None

    @property
    @term_fun
    def length(self) -> TermInt:
        assert isinstance(self, MineField)
        if self.f == MineField.concat:
            const = 0
            summands = []
            for arg in self.args:
                if isinstance(arg, TermBool): const += 1
                else: summands.append(arg.length)
            return TermInt.sum(*summands, const = const)
        elif self.f == Jump.to_empty_minefield.fget:
            return TermInt(self.args[0].length-1)
        elif self.f == Jumps.landings.fget:
            return TermInt(self.args[0].length)
        else:
            return None

MineField.getitem.notation = lambda s,n: f"{n} in {s}"

class Jump(Term): # positive integer

    @staticmethod
    def mk(n):
        if isinstance(n, Jump): return n
        else: return Jump._mk(length = n)
    @staticmethod
    @term_fun
    def _mk(*, length):
        assert isinstance(length, int) and length > 0
        return None

    @property
    @term_fun
    def length(self) -> int:
        if self.f == Jump._mk: return TermInt(self.meta_args['length'])
        else: return None
    @property
    @term_fun
    def to_empty_minefield(self) -> MineField:
        if self.f == Jump._mk:
            return MineField([False] * (self.meta_args['length']-1))
        else:
            return None

    def __add__(self, other):
        return Jumps.concat(self, other)

    def is_num_const(self):
        return self.f == self._mk
    def value(self):
        if not self.is_num_const:
            raise Exception(f"Cannot evaluate nonconstant jump {self}")
        return self.meta_args['length']
    def __int__(self):
        return self.value()

Jump._mk.out_type = Jump
Jump._mk.notation = lambda length: f"({length})"

class JumpSet(Term):
    def __init__(self, *args, **kwargs):
        if self.initialized: return
        super().__init__(*args, **kwargs)
        if self.f == JumpSet.merge:
            self.merge_args = self.args
        else:
            self.merge_args = (self,)

    @staticmethod
    def mk(jumps):
        return JumpSet.merge(*map(Jump, jumps))

    @property
    @term_fun
    def some_order(self):
        assert isinstance(self, JumpSet)
        if self.f == JumpSet.merge:
            if all(isinstance(arg, Jump) for arg in self.args):
                if all(jump.is_num_const for jump in self.args):
                    seq = sorted(self.args, key = int)
                    return Jumps(seq)
        return None

    @property
    @term_fun
    def length(self) -> TermInt:
        assert isinstance(self, JumpSet)
        if self.f == JumpSet.merge:
            return TermInt.sum(*(arg.length for arg in self.args))
        else:
            return None

    @property
    @term_fun
    def number(self) -> TermInt:
        assert isinstance(self, JumpSet)
        if self.f == JumpSet.merge:
            const = 0
            summands = []
            for arg in self.args:
                if isinstance(arg, Jump): const += 1
                else: summands.append(arg.number)
            return TermInt.sum(*summands, const = const)
        else:
            return None

    @staticmethod
    @term_fun
    def merge(*args):
        assert all(isinstance(arg, (Jump, JumpSet)) for arg in args)
        if any(arg.f == JumpSet.merge for arg in args):
            simp_args = []
            for arg in args:
                if arg.f == JumpSet.merge: simp_args.extend(arg.args)
                else: simp_args.append(arg)
            return JumpSet.merge(*simp_args)
        else:
            key = dict()
            for arg in args:
                if arg in key: key[arg] += 1
                else: key[arg] = 1
            return frozenset(key.items())
    @staticmethod
    def merge_notation(*args):
        arg_str = []
        for arg in args:
            if isinstance(arg, Jump): arg_str.append(str(arg))
            else: arg_str.append(str(arg)+'...')
        return '{' + ', '.join(arg_str) + '}'

    @staticmethod
    @term_fun
    def _contains(self, jump) -> TermBool:
        assert isinstance(self, JumpSet)
        assert isinstance(jump, Jump)
        if self.f != JumpSet.merge: return None
        options = []
        for arg in self.args:
            if isinstance(arg, Jump):
                options.append(equals(jump.length, arg.length))
            else:
                options.append(arg.contains(jump))
        return disjunction(*options)

    def contains(self, jump):
        return self._contains(self, jump)

    @staticmethod
    @term_fun
    def disjoint(self, other) -> TermBool:
        assert isinstance(self, (Jump, JumpSet))
        assert isinstance(other, (Jump, JumpSet))
        if isinstance(self, Jump):
            if isinstance(other, Jump):
                return ~equals(self.length, other.length)
            else:
                return ~other.contains(self)
        else:
            if isinstance(other, Jump):
                return ~self.contains(other)
            else:
                if self.f != JumpSet.merge and other.f != JumpSet.merge: return None
                return conjunction(*(
                    JumpSet.disjoint(a,b)
                    for a,b in itertools.product(self.merge_args, other.merge_args)
                ))

    @property
    @term_fun
    def nodup(self) -> TermBool:
        assert isinstance(self, JumpSet)
        if self.f != JumpSet.merge: return None
        options = []
        return conjunction(*(
            a.nodup
            for a in self.args
            if isinstance(a, JumpSet)
        )) & conjunction(*(
            JumpSet.disjoint(a,b)
            for a,b in itertools.combinations(self.args, 2)
        ))

    def value(self):
        if self.f != JumpSet.merge: raise Exception("JumpSet not evaluated")
        elif not all(isinstance(arg, Jump) for arg in self.args):
            raise Exception("JumpSet contains unevaluated subset")
        res_l = [arg.value() for arg in self.args]
        res = set(res_l)
        if len(res_l) > len(res):
            raise Exception("JumpSet contains a jump twice")
        return res

JumpSet.merge.out_type = JumpSet
JumpSet.merge.notation = JumpSet.merge_notation
JumpSet._contains.notation = lambda s,j: f"{j} in {s}"

class Jumps(TermSequence, default = Jump(1)):
    @property
    @term_fun
    def landings(self) -> MineField:
        if self.f != Jumps.concat: return None
        res = []
        for jumps_part in self.parts:
            if isinstance(jumps_part, Jumps):
                res.append(jumps_part.landings)
            else:
                assert isinstance(jumps_part, Jump)
                res.append(jumps_part.to_empty_minefield)
                res.append(TermBool.true)
        return MineField.concat(*res)

    @property
    def length(self) -> TermInt:
        return self.s.length
    @property
    def number(self) -> TermInt:
        return self.s.number

    @staticmethod
    @term_fun
    def _solve(self, mines):
        assert isinstance(self, Jumps)
        assert isinstance(mines, MineField)
        if self.all_vars or mines.all_vars: return None
        jumps_val = list(self.value())
        mines_val = mines.value()
        if sum(mines_val) >= len(jumps_val): return None # there must be more jumps than mines
        if sum(jumps_val) != len(mines_val)+1: return None # the length must fit
        if self._search(0, -1, jumps_val, mines_val):
            return Jumps(jumps_val)
        else:
            return None

    def solve(self, mines):
        return Jumps._solve(self, mines)

    @staticmethod
    def _search(index, pos, jumps, mines):
        if pos >= len(mines): return True
        if pos >= 0 and mines[pos]: return False
        if index >= len(jumps): return True
        for i2 in range(index, len(jumps)):
            jumps[index], jumps[i2] = jumps[i2], jumps[index]
            if Jumps._search(index+1, pos+jumps[index], jumps, mines): return True
            jumps[index], jumps[i2] = jumps[i2], jumps[index]
        return False

    @property
    @term_fun
    def s(self) -> JumpSet:
        assert isinstance(self, Jumps)
        if self.f == Jumps.concat:
            return JumpSet.merge(*(
                (arg if isinstance(arg, Jump) else arg.s)
                for arg in self.args
            ))
        else:
            return None

Jumps._solve.out_type = Jumps
JumpSet.some_order.fget.out_type = Jumps

if __name__ == "__main__":

    a = TermBool.fixed_var('a')
    b = TermBool.fixed_var('b')
    c = TermBool.fixed_var('c')
    d = TermBool.fixed_var('d')
    prop = (a & b) | (c & d)
    print(prop)
    print(prop.clausify_raw())
    print(prop.clausify_raw().drop_subsumed_clauses())
    exit()
    
    import random
    jumps_val = Jumps([1,2,4])
    mines_val = MineField([0,0,1,0,1,0])
    print(jumps_val)
    print(mines_val)
    print(jumps_val.length)
    print(mines_val.length)
    jumps = Jumps.fixed_var('jumps')
    mines = MineField.fixed_var('mines')
    print(jumps)
    jumps2 = jumps+jumps+Jump(5)
    print(jumps2)
    print(jumps2.number)
    print(mines)
    subst = Substitution({jumps: jumps_val})
    print(subst[jumps2])
    print(jumps2.length)
    print(subst[jumps2].length)
    print(subst[jumps2.length])

    print()
    print("Test solve")
    for _ in range(20):
        last = 0
        jumps = []
        for _ in range(random.randint(2,5)):
            last += random.randint(1,2)
            jumps.append(last)
        random.shuffle(jumps)
        # jumps = [4,1,3]
        print(jumps)
        mines = [False]*(sum(jumps)-1)
        if True:
            for _ in range(len(jumps)-1):
                i = random.randint(0,len(mines)-1)
                mines[i] = True
        else:
            mines[0] = True
            mines[3] = True
        print('Mines:', ''.join(['_','*'][x] for x in mines))
        sol = Jumps(jumps).solve(MineField(mines))
        sol = sol.landings.value()
        print('Jumps:', ''.join(['_','*'][x] for x in sol))
        assert not any(a and b for a,b in zip(mines, sol))
