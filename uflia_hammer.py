from logic import TermInt, TermBool, Jump, Jumps, MineField, JumpSet, term_fun, equals, conjunction, disjunction

class UFLIA:
    def __init__(self):
        self.sorts = dict()
        self.special_functions = dict()
        self.functions = dict()
        self.fixed_vars = dict()
        self.free_vars = dict()
        self.used_names = set()
        self.constraints = []

    def make_name(self, name, capitalize = False):
        last_c = None
        res = []
        for c in name:
            if c != '_' and not c.isalnum(): continue
            if last_c is None and c == '_': continue
            if last_c is None and c.isnumeric(): res.append('x')
            if last_c is not None and last_c.islower() and c.isupper(): res.append('_')
            res.append(c.lower())
            last_c = c
        if capitalize:
            res[0] = res[0].upper()
        res = ''.join(res)
        if res in self.used_names:
            i = 1
            while True:
                cand = res+'_c'+str(i)
                if cand not in self.used_names:
                    res = cand
                    break
                i += 1
        self.used_names.add(res)
        return res

    def register_in_dict(self, get_name, obj, d):
        if obj in d: return None
        name = get_name()
        d[obj] = name
        return name

    def register_sort(self, obj_type):
        name = lambda: self.make_name('t_'+obj_type.__name__)
        self.register_in_dict(name, obj_type, self.sorts)
    def register_function(self, f, in_types, out_type):
        assert f is not None
        if f in self.special_functions:
            name = lambda: self.special_functions[f]
        else:
            name = lambda: self.make_name(f.name)
        self.register_in_dict(name, (f, in_types, out_type), self.functions)
    def register_fixed_var(self, v):
        assert v.is_fixed_var
        name = lambda: self.make_name(v.var_name)
        self.register_in_dict(name, v, self.fixed_vars)

    def register_term(self, term):
        for subterm in term.subterms_iter():
            self.register_sort(type(subterm))
            if subterm.is_var:
                if subterm.is_free_var: continue
                else:
                    assert subterm.is_fixed_var
                    self.register_fixed_var(subterm)
            else:
                in_types = tuple(type(arg) for arg in subterm.args)
                out_type = type(subterm)
                self.register_function(subterm.f, in_types, out_type)

    def add_constraint(self, constraint):
        self.register_term(constraint)
        self.constraints.append(constraint)

    def export_problem(self, stream):
        stream.write(self.header())
        stream.write(self.comment("Sorts"))
        for sort, sort_name in self.sorts.items():
            if sort not in (TermBool, TermInt):
                stream.write(self.sort_decl(sort_name)+'\n')
        stream.write('\n')
        stream.write(self.comment("Functions and constants"))
        for (f, in_types, out_type), f_name in self.functions.items():
            in_types = tuple(self.sorts[in_type] for in_type in in_types)
            out_type = self.sorts[out_type]
            if f not in self.special_functions:
                stream.write(self.function_decl(f_name, in_types, out_type)+'\n')
        for v,var_name in self.fixed_vars.items():
            out_type = self.sorts[type(v)]
            stream.write(self.function_decl(var_name, (), out_type)+'\n')
        stream.write('\n')
        stream.write(self.comment("Constraints"))
        for i,constraint in enumerate(self.constraints):
            stream.write(self.export_constraint(constraint, i)+'\n')
        stream.write(self.footer())

    def get_constant(self, term):
        if term.is_var:
            if term.is_free_var: return self.free_vars[term]
            elif term.is_fixed_var: return self.fixed_vars[term]
            else: raise Exception(f"Variable {term} is not free nor fixed")
        elif len(term.args) == 0 and not term.meta_args:
            return self.functions[term.f, (), type(term)]
        else:
            return None
    def get_function(self, term):
        in_types = tuple(type(arg) for arg in term.args)
        out_type = type(term)
        return self.functions[term.f, in_types, out_type]

    def comment(self, comment):
        return ''
    def header(self):
        return ''
    def footer(self):
        return ''
    def sort_decl(self, sort_name):
        raise Exception("Not implemented")
    def function_decl(self, f_name, in_types, out_type):
        raise Exception("Not implemented")
    def export_constraint(self, constraint):
        raise Exception("Not implemented")

class UFLIA_TFF(UFLIA):
    def __init__(self):
        super().__init__()
        self.sorts.update({
            TermBool : '$o',
            TermInt : '$int',
        })
        self.special_functions.update({
            TermBool.true.f : '$true',
            TermBool.false.f : '$false',
            TermBool.invert : '~',
            conjunction : '&', # not used, just to prevent creating new names
            disjunction : '|', # not used, just to prevent creating new names
            equals : '=', # not used, just to prevent creating new names
            TermInt.le : '$lesseq',
            TermInt._mk : '$sum', # not used, just to prevent creating new names
        })

    def comment(self, comment):
        return '% '+comment+'\n'
    def sort_decl(self, sort_name):
        return f"tff({sort_name}_type, type, {sort_name} : $tType)."
    def function_decl(self, f_name, in_types, out_type):
        if len(in_types) == 0: f_type = out_type
        else:
            if len(in_types) == 1: [in_types] = in_types
            else: in_types = '('+' * '.join(in_types)+')'
            f_type = in_types + ' > ' + out_type
        return f"tff({f_name}_type, type, {f_name} : {f_type})."

    def export_term(self, term):
        const = self.get_constant(term)
        if const is not None: return const
        if term.f == conjunction:
            return '('+' & '.join(map(self.export_term, term.args))+')'
        elif term.f == disjunction:
            return '('+' | '.join(map(self.export_term, term.args))+')'
        elif term.f == TermInt._mk:
            summands = []
            for summand, coef in zip(term.summands, term.muls):
                summand = self.export_term(summand)
                if coef == 1: summands.append(summand)
                else: summands.append(f"$product({coef}, {summand})")
            if term.const != 0: summands.append(str(term.const))
            if not summands:
                return '0'
            else:
                res = summands[0]
                for summand in summands[1:]:
                    res = f"$sum({res}, {summand})"
                return res
        elif term.f == equals:
            a,b = map(self.export_term, term.args)
            if isinstance(term.args[0], TermBool):
                return f"({a} <=> {b})"
            else:
                return f"{a} = {b}"
        else:
            f = self.get_function(term)
            return f + '('+', '.join(map(self.export_term, term.args))+')'

    def export_constraint(self, constraint, index):
        assert not self.free_vars
        for x in constraint.all_vars:
            if x.is_free_var:
                name = lambda: self.make_name(x.var_name, capitalize = True)
                self.register_in_dict(name, x, self.free_vars)
        constraint = self.export_term(constraint)
        if self.free_vars:
            var_list = [
                f"{v_name}:{self.sorts[type(v)]}"
                for v, v_name in self.free_vars.items()
            ]
            var_list = ', '.join(var_list)
            constraint = f"![{var_list}] : {constraint}"
        for name in self.free_vars.values():
            self.used_names.remove(name)
        self.free_vars = dict()
        return f"tff('constraint_{index}', axiom, {constraint})."

class UFLIA_SMT(UFLIA):
    def __init__(self):
        super().__init__()
        self.sorts.update({
            TermBool : 'Bool',
            TermInt : 'Int',
        })
        self.special_functions.update({
            TermBool.true.f : 'true',
            TermBool.false.f : 'false',
            TermBool.invert : 'not',
            conjunction : 'and',
            disjunction : 'or',
            equals : '=',
            TermInt.le : '<=',
            TermInt._mk : '+', # not used, just to prevent creating new names
        })

    def comment(self, comment):
        return '; '+comment+'\n'
    def header(self):
        return '(set-logic AUFLIA)\n\n'
    def footer(self):
        return '\n(check-sat)\n'
    def sort_decl(self, sort_name):
        return f"(declare-sort {sort_name} 0)"
    def function_decl(self, f_name, in_types, out_type):
        if in_types:
            in_types = ' '.join(in_types)
            return f"(declare-fun {f_name} ({in_types}) {out_type})"
        else:
            return f"(declare-const {f_name} {out_type})"

    def export_int(self, i):
        assert isinstance(i, int)
        if i >= 0: return str(i)
        else: return f"(- {-i})"

    def export_term(self, term):
        const = self.get_constant(term)
        if const is not None: return const
        if term.f == TermInt._mk:
            summands = []
            for summand, coef in zip(term.summands, term.muls):
                summand = self.export_term(summand)
                if coef == 1: summands.append(summand)
                else: summands.append(f"(* {self.export_int(coef)} {summand})")
            if term.const != 0: summands.append(self.export_int(term.const))
            if len(summands) == 0: return '0'
            elif len(summands) == 1: return summands[0]
            else: return '(+ '+' '.join(summands)+')'
        else:
            f = self.get_function(term)
            args = [self.export_term(arg) for arg in term.args]
            return '(' + ' '.join([f]+args) + ')'

    def export_constraint(self, constraint, index):
        assert not self.free_vars
        for x in constraint.all_vars:
            if x.is_free_var:
                name = lambda: self.make_name(x.var_name)
                self.register_in_dict(name, x, self.free_vars)
        constraint = self.export_term(constraint)
        if self.free_vars:
            var_list = [
                f"({v_name} {self.sorts[type(v)]})"
                for v, v_name in self.free_vars.items()
            ]
            var_list = ' '.join(var_list)
            constraint = f"(forall ({var_list}) {constraint})"
        for name in self.free_vars.values():
            self.used_names.remove(name)
        self.free_vars = dict()
        return f"(assert (! {constraint} :named constraint-{index}))"

# expressing manipulation of jumps / mines without auto-simplification 

empty_jumps = Jumps.new_const('empty_jumps')
empty_minefield = MineField.new_const('empty_minefield')
empty_jumpset = JumpSet.new_const('empty_jumpset')
@term_fun
def _jumps_concat(a,b) -> Jumps:
    assert isinstance(a, Jumps)
    assert isinstance(b, Jumps)
    return None
@term_fun
def _jumps_singleton(a) -> Jumps:
    assert isinstance(a, Jump)
    return None
@term_fun
def _jumpset_merge(a,b) -> JumpSet:
    assert isinstance(a, JumpSet)
    assert isinstance(b, JumpSet)
    return None
@term_fun
def _jumpset_singleton(a) -> JumpSet:
    assert isinstance(a, Jump)
    return None
@term_fun
def _minefield_concat(a,b) -> MineField:
    assert isinstance(a, MineField)
    assert isinstance(b, MineField)
    return None
@term_fun
def _minefield_singleton(a) -> MineField:
    assert isinstance(a, TermBool)
    return None
@term_fun
def _jump_over(a) -> MineField:
    assert isinstance(a, Jump)
    return None
@term_fun
def _landings(a) -> MineField:
    assert isinstance(a, Jumps)
    return None

def binary_composer(empty, singleton, concat):
    def compose(*args):
        if not args: return empty
        t = type(empty)
        args = [
            arg if type(arg) == type(empty) else singleton(arg)
            for arg in args
        ]
        res = args[0]
        for arg in args[1:]:
            res = concat(res, arg)
        return res
    return compose

jumps_compose = binary_composer(empty_jumps, _jumps_singleton, _jumps_concat)
jumpset_compose = binary_composer(empty_jumpset, _jumpset_singleton, _jumpset_merge)
mines_compose = binary_composer(empty_minefield, _minefield_singleton, _minefield_concat)
function_replace_d = {
    Jumps.concat : jumps_compose,
    JumpSet.merge : jumpset_compose,
    MineField.concat : mines_compose,
    Jump.to_empty_minefield.fget : _jump_over,
    Jumps.landings.fget : _landings,
}
def replace_functions(term):
    if term.is_var: return term
    f = function_replace_d.get(term.f, term.f)
    args = tuple(replace_functions(arg) for arg in term.args)
    return f(*args, **term.meta_args)

def make_extra_axioms():
    JSA = JumpSet.free_var('JSA')
    JSB = JumpSet.free_var('JSB')
    JSC = JumpSet.free_var('JSC')
    JA = Jumps.free_var('JA')
    JB = Jumps.free_var('JB')
    JC = Jumps.free_var('JC')
    JX = Jump.free_var('JX')
    JY = Jump.free_var('JY')
    X = TermInt.X
    MA = MineField.free_var('MA')
    MB = MineField.free_var('MB')
    MC = MineField.free_var('MC')
    extra_axioms = [
        # group laws
        equals(_jumps_concat(empty_jumps, JA), JA),
        equals(_jumps_concat(JA, empty_jumps), JA),
        equals(_jumps_concat(_jumps_concat(JA,JB),JC), _jumps_concat(JA,_jumps_concat(JB,JC))),
        equals(_jumpset_merge(empty_jumpset, JSA), JSA),
        equals(_jumpset_merge(JSA, empty_jumpset), JSA),
        equals(_jumpset_merge(JSA, JSB), _jumpset_merge(JSB, JSA)),
        equals(_jumpset_merge(_jumpset_merge(JSA,JSB),JSC), _jumpset_merge(JSA,_jumpset_merge(JSB,JSC))),
        equals(_minefield_concat(empty_minefield, MA), MA),
        equals(_minefield_concat(MA, empty_minefield), MA),
        equals(_minefield_concat(_minefield_concat(MA,MB),MC), _minefield_concat(MA,_minefield_concat(MB,MC))),

        # conversion to jumps -> jumpset is a homomrphism
        equals(empty_jumps.s, empty_jumpset),
        equals(_jumps_singleton(JX).s, _jumpset_singleton(JX)),
        equals(_jumps_concat(JA,JB).s, _jumpset_merge(JA.s, JB.s)),

        # linearity of length / count / number / singleton
        equals(empty_jumps.length, TermInt(0)),
        equals(empty_jumps.number, TermInt(0)),
        equals(_jumpset_singleton(JX).length, JX.length),
        equals(_jumpset_singleton(JX).number, TermInt(1)),
        equals(_jumpset_merge(JSA, JSB).length, JSA.length + JSB.length),
        equals(_jumpset_merge(JSA, JSB).number, JSA.number + JSB.number),
        equals(empty_minefield.length, TermInt(0)),
        equals(empty_minefield.count, TermInt(0)),
        equals(_minefield_singleton(TermBool.X).length, TermInt(1)),
        equals(_minefield_singleton(TermBool.true).count, TermInt(1)),
        equals(_minefield_singleton(TermBool.false).count, TermInt(0)),
        equals(_minefield_concat(MA, MB).length, MA.length + MB.length),
        equals(_minefield_concat(MA, MB).count, MA.count + MB.count),

        # landings -- empty / singleton / concat / count
        equals(_landings(_jumps_concat(JA, JB)), _minefield_concat(_landings(JA), _landings(JB))),
        equals(_landings(JA).count, JA.number),
        equals(_landings(empty_jumps), empty_minefield),
        equals(_landings(_jumps_singleton(JX)), _minefield_concat(_jump_over(JX), _minefield_singleton(TermBool.true))),
        # JumpSet.nodup, disjoint, contains
        empty_jumpset.nodup,
        _jumpset_singleton(JX).nodup,
        ~_jumpset_merge(JSA, JSB).nodup | JSA.nodup,
        ~_jumpset_merge(JSA, JSB).nodup | JSB.nodup,
        ~_jumpset_merge(JSA, JSB).nodup | ~JSA.contains(JX) | ~JSB.contains(JX),
        equals(_jumpset_singleton(JX).contains(JY), equals(JX, JY)),
        ~empty_jumpset.contains(JX),

        # MineField.getitem -- concat, singleton
        ~empty_minefield[X],
        equals(_minefield_singleton(TermBool.true)[X], (equals(X,0))),
        ~_minefield_singleton(TermBool.false)[X],
        equals(_minefield_concat(MA, MB)[X], MA[X] | MB[X - MA.length]),

        # _jump_over -- getitem, count, number
        ~_jump_over(JX)[X],
        equals(_jump_over(JX).length, JX.length - 1),
        equals(_jump_over(JX).count, 0),
    ]
    return extra_axioms

def record_grasshopper_task(constraints, basename):
    extra_axioms = make_extra_axioms()
    constraints = extra_axioms + [
        replace_functions(constraint) for constraint in constraints
    ]

    print("Exporting:", basename)
    for uflia, fname in [(UFLIA_SMT(), basename+'.smt'), (UFLIA_TFF(), basename+'.p')]:
        for constraint in constraints:
            uflia.add_constraint(constraint)
        with open(fname, 'w') as f:
            uflia.export_problem(f)
