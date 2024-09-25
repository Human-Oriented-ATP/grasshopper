import re
from contextlib import contextmanager
from logic import *
from prover import prove_contradiction, FailedProof
import prover
import os

class Parser:
    spec_char = re.compile('[,()\t\n ]')
    @staticmethod
    def tokenize(line):
        i1 = 0
        for spec_char_occur in Parser.spec_char.finditer(line):
            i2 = spec_char_occur.start()
            if i2 > i1: yield line[i1:i2]
            c = line[i2]
            if not c.isspace(): yield c
            i1 = i2+1
        i2 = len(line)
        if i2 > i1: yield line[i1:i2]

    def __init__(self):
        self.name_to_type = {
            'JumpSet' : JumpSet,
            'Jumps' : Jumps,
            'Jump' : Jump,
            'MineField' : MineField,
            'Bool' : TermBool,
            'ℤ' : TermInt,
        }
        self.name_to_const = {
            'true' : TermBool.true,
            'false' : TermBool.false,
            'True' : TermBool.true,
            'False' : TermBool.false,
            '[]' : MineField(),
        }
        def singleton(x):
            if isinstance(x, Jump): return Jumps(x)
            elif isinstance(x, TermBool): return MineField(x)
            else:
                raise Exception(f"Cannot build singleton out of {x} of type {type(x)}")
        def cons(x,y):
            if isinstance(x, Jump):
                if isinstance(y, MineField) and not y.parts:
                    return Jumps(x)
                return Jumps(x,y)
            elif isinstance(x, TermBool): return MineField(x,y)
            else:
                raise Exception(f"Cannot build cons out of {x} of type {type(x)}")
        def mul(x,y):
            if x.is_num_const: return x.value()*y
            elif x.is_num_const: return y.value()*x
            else: raise Exception(f"Cannot multiply: {x} * {y}")
        self.name_to_fun = {
            '↑' : (lambda x : x), # ignore coersion
            'Nat.cast': (lambda x : x), # ignore coersion
            'HAppend.hAppend' : lambda a,b: a.concat(a,b),
            'Multiset.sizeOf' : JumpSet.number.fget,
            'Multiset.Nodup'  : JumpSet.nodup.fget,
            'Multiset.cons' : JumpSet.merge,
            'Membership.mem' : lambda x,s : s.contains(x),
            'JumpSet.sum'     : JumpSet.length.fget,
            'JumpSet.singleton' : JumpSet.merge,
            'MineField.length'     : MineField.length.fget,
            'MineField.countMines' : MineField.count.fget,
            'List.getIndexD'      : MineField.getitem,
            'Jumps.s'        : Jumps.s.fget,
            'Jumps.landings' : Jumps.landings.fget,
            'Jumps.sum'      : lambda x: x.length,
            'Jumps.length'   : lambda x: x.number,
            'Jump.length'    : Jump.length.fget,
            'HAdd.hAdd' : lambda x,y: (TermInt.sum if isinstance(x, TermInt) else JumpSet.merge)(x,y),
            'HMul.hMul' : mul,
            'HSub.hSub' : lambda a,b: a-b,
            'singleton' : singleton,
            'List.cons' : cons,
            'LT' : lambda a,b: TermBool.invert(TermInt.le(b,a)),
            'LE' : TermInt.le,
            'OR' : disjunction,
            'AND' : conjunction,
            'EQUALS' : equals,
            'NOT' : TermBool.invert,
            'IMPLIES'  : lambda a,b: ~a | b,
            'or'  : disjunction,
            'and' : conjunction,
        }

    def parse_tokens(self, tokens, i):
        assert i < len(tokens)
        assert tokens[i] not in (',', '(', ')'), (i, tokens[i])
        if i+1 < len(tokens) and tokens[i+1] == '(':
            # function
            main_f = tokens[i]
            i += 1
            args = []
            while True:
                i += 1
                arg, i = self.parse_tokens(tokens, i)
                args.append(arg)
                assert i < len(tokens)
                if tokens[i] == ')': break
                else: assert tokens[i] == ','
            main_f = self.name_to_fun[main_f]
            res = main_f(*args)
            return res, i+1
        else:
            # constant
            if tokens[i].isnumeric() or tokens[i][0] == '-' and tokens[i][1:].isnumeric():
                res = TermInt(int(tokens[i]))
            else:
                res = self.name_to_const[tokens[i]]
            return res, i+1

    def parse_line(self, line):
        if ' :: ' in line:
            free_vars, body = line.split(' :: ')
            var_to_type = dict()
            for vt in free_vars.split(','):
                v,t = vt.split(':')
                v = v.strip()
                t = t.strip()
                var_to_type[v] = t
        else:
            body = line
            var_to_type = dict()

        tokens = list(self.tokenize(body))
        with self.context_free_vars(var_to_type):
            res, i = self.parse_tokens(tokens, 0)
        assert i == len(tokens)
        return res

    @contextmanager
    def context_const(self, name_to_const):
        ori = {
            name : self.name_to_const[name]
            for name in name_to_const.keys()
            if name in self.name_to_const
        }
        self.name_to_const.update(name_to_const)
        yield
        for name in name_to_const.keys():
            if name in ori:
                self.name_to_const[name] = ori[name]
            else:
                del self.name_to_const[name]

    def context_free_vars(self, name_to_type):
        return self.context_const({
            name : self.name_to_type[t].free_var(name)
            for name, t in name_to_type.items()
        })

    def context_fixed_vars(self, name_to_type):
        return self.context_const({
            name : self.name_to_type[t].fixed_var(name)
            for name, t in name_to_type.items()
        })

def parse_problem_stream(f):
    parser = Parser()
    type_lines = []
    constraint_lines = []
    mode = 'type'
    for line in f:
        line = line.strip()
        if not line: continue
        elif line == '---':
            if mode == 'constraint': break
            else: mode = 'constraint'
        elif mode == 'type':
            type_lines.append(line)
        elif mode == 'constraint':
            constraint_lines.append(line)
        else:
            raise Exception(f"unexpected mode: {mode}")

    var_to_type = dict()
    for line in type_lines:
        v,t = line.split(':')
        v = v.strip()
        t = t.strip()
        if v in var_to_type:
            print(f"Double variable '{v}'")
        var_to_type[v] = t
    constraints = []
    with parser.context_fixed_vars(var_to_type):
        for line in constraint_lines:
            constraints.append(parser.parse_line(line))

    return constraints

def parse_problem_file(fname):
    with open(fname) as f:
        return parse_problem_stream(f)

if __name__ == "__main__":

    univ_theorems = prover.get_univ_theorems()
    dirname = "/home/mirek/gowers/lean-tactics"
    fnames = [
        fname
        for fname in os.listdir(dirname)
        if fname.endswith('.txt')
    ]
    fnames.sort()
    fnames = ['auto-at-line-248-character-10.txt']

    dirname = ""
    fnames = ["test_problem"]
    debug = (len(fnames) == 1)
    num_proven = 0
    num_total = 0
    for fname in fnames:
        # print(fname)
        try:
            constraints = parse_problem_file(os.path.join(dirname, fname))
        except:
            print("Error in:", fname)
            raise
        if debug:
            print()
            for constraint in constraints:
                print(constraint)
            print("--------------------------------------------")
        prover.debug = debug
        try:
            res = prove_contradiction(univ_theorems + constraints)
            num_proven += 1
        except FailedProof:
            print(f"{fname}: Proof failed")
        num_total += 1
            
    print(f"Proven: {num_proven} / {num_total}")
