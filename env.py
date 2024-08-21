import sys
import itertools
from itertools import combinations

from smt_lia import LiaChecker
from logic import *
import prover
from prover import FailedProof, simplify_exist_clause

class FailedProofDisjoint(FailedProof):
    def __init__(self, model, seq1, seq2, boom):
        self.model = model
        self.seq1 = seq1
        self.seq2 = seq2
        self.boom = boom

    def seq_str(self, seq):
        res = []
        for part in seq.parts:
            if isinstance(part, TermBool):
                part = self.model[part]
                if part.guaranteed: res.append('*')
                elif part.possible: res.append('-')
                else: res.append('.')
            else:
                l = int(self.model[part.length])
                if l == 0: continue
                if equals(self.model[part.count], 0).guaranteed: item = '.'
                elif equals(self.model[part.count], self.model[part.length]).guaranteed: item = '*'
                else: item = '-'
                res.append(' '.join([item]*l))

        return '|'.join(res)

    def boom_str(self):
        lines = [
            self.seq_str(self.seq1),
            self.seq_str(self.seq2),
            '  '*int(self.model[self.boom]) + '#',
        ]
        return '\n'.join(lines)

    def __str__(self):
        return "Disjointness Proof Failed!\n"+self.boom_str()

class FailedProofSubgoal(FailedProof):
    def __init__(self, subgoal):
        self.subgoal = subgoal
    def __str__(self):
        return f"Failed to prove: {self.subgoal}"

class AnnotatedFact:
    def __init__(self, prop, initial = False, assumed = False, deconstruction = False):
        self.initial = initial
        self.assumed = assumed
        self.prop = prop
        self.deconstruction = deconstruction

class LogicContext:
    def __init__(self, facts, var_to_value, model_constraints, cached_model):
        self.facts = list(facts)
        self.var_to_value = dict(var_to_value)
        self.model_constraints = list(model_constraints)
        self._model = cached_model

    @property
    def raw_facts(self):
        return [fact.prop for fact in self.facts]

    def clone(self):
        return LogicContext(self.facts, self.var_to_value, self.model_constraints, self._model)

    def add_var(self, v):
        assert v.is_fixed_var
        assert v not in self.var_to_value
        self.var_to_value[v] = None
        self._model = None

    def add_fact(self, prop, assumed = False, deconstruction = False):
        assert isinstance(prop, TermBool)
        for v in prop.all_vars:
            if v.is_fixed_var and v not in self.var_to_value:
                cur_vars = list(self.var_to_value.keys())
                raise Exception(f"Variable {v} in {prop} not covered by current variables: {cur_vars}")
        self.facts.append(AnnotatedFact(prop, assumed = assumed, deconstruction = deconstruction))
        self._model = None

    def add_model_constraints(self, *props, prioritized = True):
        assert all(isinstance(prop, TermBool) for prop in props)
        if prioritized:
            self.model_constraints = list(props) + self.model_constraints
        else:
            self.model_constraints.extend(self.model_constraints)
        self._model = None

    def deconstruct(self, v, value):
        assert v.is_fixed_var
        assert v in self.var_to_value
        assert self.var_to_value[v] is None
        self.var_to_value[v] = value
        for value_v in value.all_vars:
            assert value_v.is_fixed_var
            assert value_v not in self.var_to_value
            self.var_to_value[value_v] = None
        self.add_fact(equals(v, value), deconstruction = True)

    def show_assumed(self):
        print("Assumptions:")
        for fact in self.facts:
            if fact.assumed:
                print('*', fact.prop)
    def show_all(self):
        print("Facts:")
        for fact in self.facts:
            if fact.assumed: bullet = '*'
            else: bullet = '.'
            print(bullet, fact.prop)
    def show_last_assump(self, bullet = ' *'):
        n = -1
        last = None
        for fact in self.facts:
            if fact.assumed:
                n += 1
                last = fact
        if last is not None:
            print('  '*n + bullet + ' '+ str(fact.prop))

    def remove_facts(self, removed):
        self.facts = list(filter(lambda fact: fact not in removed, self.facts))
        self._model = None

    def remove_var(self, removed):
        assert removed in self.var_to_value and self.var_to_value[removed] is None
        for v, value in self.var_to_value.items():
            if value is not None and removed in value.all_vars:
                # TODO: allow removing multiple variables at once
                assert len(value.all_vars) == 1
                self.var_to_value[v] = None
        self.facts = list(filter(lambda fact: removed not in fact.prop.all_vars, self.facts))
        self._model = None

    def get_model(self):
        extra_terms = []
        important_terms = []
        for v, value in self.var_to_value.items():
            if isinstance(v, Jump): cur_extra = [v.length]
            elif isinstance(v, Jumps): cur_extra = [v.length, v.number]
            elif isinstance(v, JumpSet): cur_extra = [v.length, v.number]
            elif isinstance(v, MineField): cur_extra = [v.length, v.count]
            else: cur_extra = []
            extra_terms.extend(cur_extra)
            if value is None: important_terms.extend(cur_extra)
        model = prover.get_model(self.raw_facts, self.model_constraints, extra_terms = extra_terms)
        if model is None: return None

        # add model constraints to copy the found model
        known_values = set()
        for term in self.model_constraints:
            if term.f != equals: continue
            a,b = term.args
            if not isinstance(a, TermInt): continue
            if not b.is_num_const: continue
            known_values.add(a)
        for term in important_terms:
            if term in known_values: continue
            self.model_constraints.append(equals(term, model[term]))

        return model

    @property
    def model(self):
        if self._model is None:
            self._model = self.get_model()
        return self._model

    @staticmethod
    def from_props(props, ini_vars):
        ini_vars_s = ini_vars
        for prop in props:
            for v in prop.all_vars:
                if v.is_fixed_var and v not in ini_vars_s:
                    raise Exception(f"Variable {v} in {prop} not covered by initial variables: {ini_vars}")
        return LogicContext(
            [AnnotatedFact(prop, initial = True) for prop in props],
            { v : None for v in ini_vars },
            [],
            None,
        )

def model_display_mines(mines, model):
    dummy = FailedProofDisjoint(model, None, None, None)
    print(dummy.seq_str(mines))

class GrasshopperEnv:
    def __init__(self, auto_assume = False, record_uflia = False, show_record_step = False):
        self.size = TermInt.fixed_var('size')
        self.jumps = JumpSet.fixed_var('jumps')
        self.mines = MineField.fixed_var('mines')
        univ_theorems = prover.get_univ_theorems()
        ctx_theorems = [
            self.jumps.nodup,
            equals(self.jumps.length, self.size+1),
            equals(self.mines.length, self.size),
            self.jumps.number > self.mines.count,
        ]
        self.ctx = LogicContext.from_props(
            univ_theorems + ctx_theorems,
            [self.size, self.jumps, self.mines],
        )
        self.ctx_stack = []
        self.proven = False
        self.prover_kwargs = {
            'record_uflia' : record_uflia,
            'show_step' : show_record_step,
        }
        self.auto_assume = auto_assume

    def prove(self, goal):
        remains_to_check = []
        try:
            prover.prove_contradiction(self.ctx.raw_facts + [~goal], **self.prover_kwargs)
        except FailedProof as e:
            if goal.f == conjunction:
                remains_to_check = goal.args
            elif self.auto_assume:
                self.split_case(goal, automatic = True)
            else:
                raise FailedProofSubgoal(goal) from e

        for subgoal in remains_to_check:
            self.prove(subgoal)

    def split_case(self, prop, automatic = False):
        assert isinstance(prop, TermBool)
        ctx2 = self.ctx.clone()
        ctx2.add_fact(~prop, assumed = True)
        self.ctx_stack.append(ctx2)
        self.ctx.add_fact(prop, assumed = True)

        if automatic: bullet = 'A*'
        else: bullet = 'M*'
        self.ctx.show_last_assump(bullet)

    def solve_with_jumps(self, jumps):

        assert isinstance(jumps, Jumps)
        self.prove(equals(jumps.s, self.jumps))

        boom = TermInt.fixed_var('boom')
        landings_boom = jumps.landings[boom]
        mines_boom = self.mines[boom]

        # finish case

        remaining_cases = []
        try:
            prover.prove_contradiction(
                self.ctx.raw_facts + [landings_boom, mines_boom],
                **self.prover_kwargs,
            )
        except FailedProof as e:
            _, subst = prover.extract_subst(self.ctx.raw_facts)
            landings_boom = subst[landings_boom]
            mines_boom = subst[mines_boom]
            for landings_boom_case in landings_boom.disj_args:
                for mines_boom_case in mines_boom.disj_args:
                    try:
                        prover.prove_contradiction(
                            self.ctx.raw_facts + [landings_boom_case, mines_boom_case]
                        )
                    except:
                        boom_case = simplify_exist_clause(
                            landings_boom_case & mines_boom_case,
                            can_eliminate = lambda v: v == boom,
                        )
                        remaining_cases.append(boom_case)
            if any(boom in boom_case.all_vars for boom_case in remaining_cases) or not self.auto_assume:
                if e.model is not None:
                    raise FailedProofDisjoint(
                        e.model,
                        subst[self.mines],
                        subst[jumps.landings],
                        boom,
                    ) from e
                else:
                    raise

        for boom_case in remaining_cases:
            self.split_case(~boom_case, automatic = True)

        self._next_goal()

    def _next_goal(self):
        if self.ctx_stack:
            self.ctx = self.ctx_stack.pop()
            self.ctx.show_last_assump()
        else:
            self.ctx = None
            self.proven = True

    ######  Domain specific operations

    def order_jumps(self, jumps):
        assert isinstance(jumps, JumpSet) and jumps.is_var
        jumpso = Jumps.fixed_var(jumps.var_name + 'o')
        self.ctx.deconstruct(jumps, jumpso.s)
        return jumpso

    def pop_max_jump(self, jumps):
        assert isinstance(jumps, JumpSet) and jumps.is_var, jumps
        self.prove(jumps.number > 0)
        J = Jump.fixed_var(jumps.var_name+'_max')
        jumpsr = JumpSet.fixed_var(jumps.var_name+'r')
        self.ctx.deconstruct(jumps, JumpSet.merge(J, jumpsr))
        self.ctx.add_fact(~jumpsr.contains(Jump.X) | (Jump.X.length <= J.length))
        return J, jumpsr

    def pop_avoiding_jump(self, jumps, mines):
        assert isinstance(jumps, JumpSet) and jumps.is_var, jumps
        assert isinstance(mines, MineField)
        self.prove(jumps.number > mines.count)
        J = Jump.fixed_var(jumps.var_name+'_avoid')
        jumpsr = JumpSet.fixed_var(jumps.var_name+'r')
        self.ctx.deconstruct(jumps, JumpSet.merge(J, jumpsr))
        self.ctx.add_fact(~mines[J.length-1])
        return J, jumpsr

    def pop_first_jump(self, jumps):
        assert isinstance(jumps, Jumps) and jumps.is_var, jumps
        self.prove(jumps.number > 0)
        J = Jump.fixed_var(jumps.var_name+'0')
        jumpsr = Jumps.fixed_var(jumps.var_name+'r')
        self.ctx.deconstruct(jumps, Jumps.concat(J, jumpsr))
        return J, jumpsr

    def split_mines(self, mines, i):
        assert isinstance(mines, MineField) and mines.is_var
        assert isinstance(i, TermInt)
        self.prove((i >= 0) & (i <= mines.length))
        mines0 = MineField.fixed_var(mines.var_name+'0')
        mines1 = MineField.fixed_var(mines.var_name+'1')
        self.ctx.deconstruct(mines, mines0 + mines1)
        self.ctx.add_fact(equals(mines0.length, i))
        return mines0, mines1

    def induction(self, jumps, mines):
        assert isinstance(jumps, JumpSet)
        assert isinstance(mines, MineField)
        requirements = [
            jumps.number < self.jumps.number,
            jumps.nodup,
            equals(jumps.length, mines.length+1),
            jumps.number > mines.count,
        ]
        self.prove(conjunction(*requirements))

        jumps_ih = Jumps.fixed_var('jumps_ih')
        self.ctx.deconstruct(jumps, jumps_ih.s)
        self.ctx.add_fact(
            ~jumps_ih.landings[TermInt.X] |
            ~mines[TermInt.X]
        )
        return jumps_ih

    def split_first_mine(self, mines):
        assert isinstance(mines, MineField) and mines.is_var
        self.prove(mines.count > 0)
        
        mines0 = MineField.fixed_var(mines.var_name+'0')
        mines1 = MineField.fixed_var(mines.var_name+'1')
        self.ctx.deconstruct(mines, MineField(mines0, True, mines1))
        self.ctx.add_fact(equals(mines0.count, 0))
        return mines0, mines1

    def split_jump_landings(self, jumps, i):
        assert isinstance(jumps, Jumps) and jumps.is_var
        self.prove((i >= 0) & (i < jumps.length))
        jumps0 = Jumps.fixed_var(jumps.var_name+'0')
        jumps1 = Jumps.fixed_var(jumps.var_name+'1')
        J = Jump.fixed_var(jumps.var_name+'_mid')
        self.ctx.deconstruct(jumps, Jumps.concat(jumps0, J, jumps1))
        self.ctx.add_fact(jumps0.length <= i)
        self.ctx.add_fact(jumps0.length+J.length > i)
        return jumps0, J, jumps1

    def union_mines(self, mines1, mines2):
        assert isinstance(mines1, MineField) and isinstance(mines2, MineField)
        # self.prove(equals(mines1.length, mines2.length))
        mines = MineField.fixed_var('mines_un')
        self.ctx.add_var(mines)
        self.ctx.add_fact(~mines1[TermInt.X] | mines[TermInt.X])
        self.ctx.add_fact(~mines2[TermInt.X] | mines[TermInt.X])
        self.ctx.add_fact(~(mines1.length >= mines2.length) | equals(mines.length, mines1.length))
        self.ctx.add_fact(~(mines2.length >= mines1.length) | equals(mines.length, mines2.length))
        self.ctx.add_fact(mines1.count <= mines.count)
        self.ctx.add_fact(mines2.count <= mines.count)
        self.ctx.add_fact(mines.count <= mines1.count + mines2.count)
        return mines

    def check_solved(self):
        if self.proven: print("Problem Solved!")
        else: print("Not solved yet!")
