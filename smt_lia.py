from subprocess import Popen, PIPE
from collections import defaultdict
import itertools
import re
import sys

from logic import *

########      Parsing SMT solver's response

def lisp_lexer(lines):
    for line in lines:
        i = line.find(';')
        if i >= 0: line = line[:i]
        parenth_pos = [m.start() for m in re.finditer('[()]', line)]
        last = 0
        for i in parenth_pos:
            yield from iter(line[last:i].split())
            yield line[i]
            last = i+1
        yield from iter(line[last:].split())
def _lisp_parse_tokens(first_token, token_iter):
    if first_token == ')': raise Exception("unmatched parenthesis")
    elif first_token == '(':
        res = []
        for token in token_iter:
            if token == ')': break
            res.append(_lisp_parse_tokens(token, token_iter))
        return res
    else:
        return first_token
def lisp_parse_tokens(token_iter):
    return _lisp_parse_tokens(next(token_iter), token_iter)
def lisp_parse_lines(lines):
    return lisp_parse_tokens(lisp_lexer(lines))

class LiaChecker:
    bool_const_to_smt = {
        TermBool.true : 'true',
        TermBool.false : 'false',
    }
    bool_op_to_smt = {
        equals : '=',
        TermBool.invert : 'not',
        conjunction : 'and',
        disjunction : 'or',
    }
    int_op_to_smt = {
        equals : '=',
        TermInt.le : '<=',
    }

    def __init__(self):
        self.int_vars = []
        self.int_vars_d = dict()
        self.bool_vars = []
        self.bool_vars_d = dict()
        self.constraints = []
        self.constraints_s = set()
        self.satisfiable = False
        self.unsatisfiable = False
        self.unsat_core = None
        self.unsat_core_ids = None
        self.sat_model = None

    def clone(self): # only constraints & terms, not cloning solver's outcome
        res = LiaChecker()
        res.int_vars = list(self.int_vars)
        res.int_vars_d = dict(self.int_vars_d)
        res.bool_vars = list(self.bool_vars)
        res.bool_vars_d = dict(self.bool_vars_d)
        res.constraints = list(self.constraints)
        res.constraints_s = set(self.constraints_s)
        return res

    def add_term(self, term):
        for subterm in term.subterms_iter():
            if isinstance(subterm, TermInt) and subterm.f != TermInt._mk:
                if subterm not in self.int_vars_d:
                    self.int_vars_d[subterm] = 'i'+str(len(self.int_vars))
                    self.int_vars.append(subterm)
            elif isinstance(subterm, TermBool) and not (self._has_bool_op(subterm) or self._has_int_op(subterm)):
                if subterm not in self.bool_vars_d:
                    self.bool_vars_d[subterm] = 'b'+str(len(self.bool_vars))
                    self.bool_vars.append(subterm)

    def add_constraint(self, constraint):
        if constraint == TermBool.true: return
        if constraint in self.constraints_s: return
        assert isinstance(constraint, TermBool)
        self.add_term(constraint)
        self.constraints.append(constraint)
        self.constraints_s.add(constraint)

    ##########   Basic term examination

    def _has_bool_op(self, prop):
        return (
            (prop.f == equals and isinstance(prop.args[0], TermBool)) or
            prop.f in (TermBool.invert, conjunction, disjunction) or
            prop in (TermBool.true, TermBool.false )
        )
    def _has_int_op(self, prop):
        return (
            (prop.f == equals and isinstance(prop.args[0], TermInt)) or
            prop.f == TermInt.le
        )

    ########      Search for congruance

    @staticmethod
    def get_skeleton(term, arg_list = None):
        if arg_list is None:
            arg_list = []
        elif isinstance(term, (TermBool, TermInt)):
            arg_list.append(term)
            return type(term).X, arg_list
        if term.is_var: return term, arg_list
        return (
            term.f(*(
                LiaChecker.get_skeleton(arg, arg_list)[0]
                for arg in term.args
            )),
            arg_list,
        )

    def get_congruence_theorems(self):
        skeleton_to_instances = defaultdict(list)
        for term in itertools.chain(self.bool_vars, self.int_vars):
            skeleton, arg_list = self.get_skeleton(term)
            instances = skeleton_to_instances[skeleton]
            for term2, arg_list2 in instances:
                assert len(arg_list2) == len(arg_list)
                assert type(term) == type(term2)
                yield ~conjunction(*(
                    equals(arg1,arg2)
                    for arg1,arg2 in zip(arg_list, arg_list2)
                )) | equals(term, term2)
            instances.append((term, arg_list))

    def add_congruence_theorems(self):
        self.constraints.extend(self.get_congruence_theorems())

    ########  Conversion to SMT

    @staticmethod
    def _smt_str(*args):
        return '(' + ' '.join(args) + ')'

    def _prop_to_smt(self, prop):
        if prop in self.bool_vars_d: return self.bool_vars_d[prop]
        elif prop in self.bool_const_to_smt: return self.bool_const_to_smt[prop]
        elif self._has_bool_op(prop):
            args = [self._prop_to_smt(arg) for arg in prop.args]
            return self._smt_str(self.bool_op_to_smt[prop.f], *args)
        elif self._has_int_op(prop):
            args = [self._term_int_to_smt(arg) for arg in prop.args]
            return self._smt_str(self.int_op_to_smt[prop.f], *args)

    def _term_int_to_smt(self, term):
        if term.f == TermInt._mk:
            if not term.args:
                if term.const >= 0: return str(term.const)
                else:
                    return self._smt_str('-', str(-term.const))
            elif len(term.args) == 1 and not term.const:
                coef = self._term_int_to_smt(TermInt(term.muls[0]))
                v = self._term_int_to_smt(term.args[0])
                return self._smt_str('*', coef, v)
            else:
                summands = [mul * arg for mul, arg in zip(term.muls, term.args)]
                if term.const != 0: summands.append(TermInt(term.const))
                summands = map(self._term_int_to_smt, summands)
                return self._smt_str('+', *summands)
        elif term in self.int_vars_d:
            return self.int_vars_d[term]
        else:
            raise Exception(f"Cannot convert to SMT: {term}")

    def write_smt(self, stream):
        header = """(set-option :produce-unsat-cores true)
(set-option :produce-models true)
(set-logic LIA)
"""
        stream.write(header)
        stream.write("\n; declarations\n")
        for v in self.bool_vars_d.values():
            stream.write(f"(declare-const {v} Bool)\n")
        for v in self.int_vars_d.values():
            stream.write(f"(declare-const {v} Int)\n")
        stream.write("\n; constraints\n")
        for i,constraint in enumerate(self.constraints):
            stream.write(f"(assert (! {self._prop_to_smt(constraint)} :named constraint-{i}))\n")
        stream.write("(check-sat)\n")

    ########  Running a solver

    def solve(self, cmd = ('z3', '-in', '-smt2')):
        popen = Popen(cmd, stdin = PIPE, stdout = PIPE, bufsize=1,
                      universal_newlines=True)
        self.write_smt(popen.stdin)
        # self.write_smt(sys.stdout)

        response = popen.stdout.readline()
        if response.strip() == "sat":
            self.satisfiable = True
            model_str,_ = popen.communicate("(get-model)\n")
            model_lisp = lisp_parse_lines(model_str.split('\n'))
            assert model_lisp[0] == 'model'
            model = {}

            var_name_to_var = dict()
            for v,name in self.bool_vars_d.items(): var_name_to_var[name] = v
            for v,name in self.int_vars_d.items(): var_name_to_var[name] = v

            for (define_fun, var_name, empty, t, value) in model_lisp[1:]:
                assert define_fun == 'define-fun'
                v = var_name_to_var[var_name]
                assert empty == []
                if isinstance(v, TermInt):
                    assert t == 'Int'
                    if isinstance(value, str):
                        assert value.isnumeric()
                        value = int(value)
                    else:
                        assert len(value) == 2 and value[0] == '-' and value[1].isnumeric()
                        value = -int(value[1])
                    value = TermInt(value)
                elif isinstance(v, TermBool):
                    assert t == 'Bool'
                    assert isinstance(value, str)
                    if value == 'true': value = True
                    elif value == 'false': value = False
                    else: raise Exception(f"Unexpected bool value {value}")
                    value = TermBool(value)
                else:
                    raise Exception(f"Unexpected term type {type(v)}: {v}")
                model[v] = value
            self.sat_model = Substitution(model)
        elif response.strip() == "unsat":
            self.unsatisfiable = True
            unsat_core_str, _ = popen.communicate("(get-unsat-core)\n")
            unsat_core_lisp = lisp_parse_lines(unsat_core_str.split('\n'))
            used_indices = []
            for label in unsat_core_lisp:
                assert isinstance(label, str) and '-' in label
                label,i = label.split('-')
                assert label == "constraint"
                i = int(i)
                assert 0 <= i < len(self.constraints)
                used_indices.append(i)
            assert len(set(used_indices)) == len(used_indices)
            used_constraints = [self.constraints[i] for i in used_indices]
            self.unsat_core_ids = used_indices
            self.unsat_core = used_constraints
        else:
            finish, _ = popen.communicate('')
            print(response, end = '')
            print(finish)
            raise Exception("Didn't get an answer from an SMT solver")

    #######  Printing

    def show_constraints(self):
        print("Constraints:")
        for constraint in self.constraints:
            print(f"  {constraint}")
        print()
    def show_congruence(self):
        print("Congruence Constraints:")
        for constraint in self.get_congruence_theorems():
            print(f"  {constraint}")
        print()
    def show_model(self):
        if self.sat_model is None:
            print("No available model")
        else:
            print("Model:")
            for v,value in self.sat_model.base_dict.items():
                print(f"  {v} = {value}")
    def show_core(self):
        if self.unsat_core is None:
            print("No unsat core")
        else:
            print("Unsat core:")
            for constraint in self.unsat_core:
                print(f"  {constraint}")
            print()
