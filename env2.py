import sys
import itertools
from itertools import combinations

from smt_lia import LiaChecker
from uflia_hammer import record_grasshopper_task
from logic import *
import prover

def model_display_mines(mines, model):
    res = []
    for part in mines.parts:
        if isinstance(part, TermBool):
            part = model[part]
            if part.guaranteed: res.append('*')
            elif part.possible: res.append('-')
            else: res.append('.')
        else:
            l = int(model[part.length])
            if l == 0: continue
            if equals(model[part.count], 0).guaranteed: item = '.'
            elif equals(model[part.count], model[part.length]).guaranteed: item = '*'
            else: item = '-'
            res.append(' '.join([item]*l))

    print('|'.join(res))

last_problem_index = -1

class LogicContext:
    def __init__(self, env, facts, assumed_ids, res_jumps, boom):
        self.env = env
        self.facts = list(facts)
        self.assumed_ids = list(assumed_ids)
        self.res_jumps = res_jumps
        self.boom = boom

    def clone(self):
        return LogicContext(self.env, self.facts, self.assumed_ids, self.res_jumps, self.boom)
    def add_fact(self, fact, assumed = False):
        if assumed: self.assumed_ids.append(len(self.facts))
        assert isinstance(fact, TermBool)
        self.facts.append(fact)

    def prove_contradiction(self, record_uflia = False, show_model = True):
        # print('Proving subgoal...', end = '')
        if record_uflia:
            global last_problem_index
            last_problem_index += 1
            hammer_fname = "hammer_problems/grasshopper"+str(last_problem_index)
            record_grasshopper_task(self.facts, hammer_fname)

        res = prover.prove_contradiction(self.facts, show_model = show_model)
        # print('   DONE')
        if isinstance(res, prover.UnsatProof): return True
        elif isinstance(res, Substitution):
            _, subst = prover.extract_subst(self.facts)
            if show_model:
                model_display_mines(subst[self.env.mines], res)
                if self.res_jumps is not None:
                    model_display_mines(subst[self.res_jumps].landings, res)
                if self.boom is not None:
                    print('  '*int(res[self.boom]) + '#')
        return False

    def prove(self, goal, record_uflia = False, show_model = True):
        ctx = self.clone()
        ctx.add_fact(~goal)
        return ctx.prove_contradiction(record_uflia = record_uflia, show_model = show_model)

    def show_assumed(self):
        print("Assumptions:")
        for idx in self.assumed_ids:
            print('*', self.facts[idx])
    def show_last_assump(self, bullet = ' *'):
        if not self.assumed_ids: return
        n = len(self.assumed_ids)
        idx = self.assumed_ids[n-1]
        print('  '*(n-1) + bullet + ' '+ str(self.facts[idx]))        

class GrasshopperEnv:
    def __init__(self, record_uflia = False, auto_assume = False):
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
        self.ctx = LogicContext(self, univ_theorems + ctx_theorems, [], None, None)
        self.ctx_stack = []
        self.proven = False
        self.record_uflia = record_uflia
        self.auto_assume = auto_assume

    def prove(self, goal):
        show_model = (goal.f == conjunction) and not self.auto_assume
        if not self.ctx.prove(goal, record_uflia = self.record_uflia, show_model = show_model):
            if goal.f == conjunction:
                for subgoal in goal.args:
                    self.prove(subgoal)
            elif self.auto_assume:
                self.split_case(goal, automatic = True)
            else:
                raise Exception("Failed to prove: "+str(goal))
    def prove_contradiction(self):
        if not self.ctx.prove_contradiction(record_uflia = self.record_uflia):
            raise Exception("Failed to prove contradiction")

    def split_case(self, prop, automatic = False):
        assert isinstance(prop, TermBool)
        ctx2 = self.ctx.clone()
        ctx2.add_fact(~prop, assumed = True)
        self.ctx_stack.append(ctx2)
        self.ctx.add_fact(prop, assumed = True)

        if automatic: bullet = 'A*'
        else: bullet = 'M*'
        self.ctx.show_last_assump(bullet)

    def provide_jumps(self, jumps):
        assert isinstance(jumps, Jumps)
        self.prove(equals(jumps.s, self.jumps))
        boom = TermInt.fixed_var('boom')
        self.ctx.add_fact(jumps.landings[boom])
        self.ctx.add_fact(self.mines[boom])
        self.ctx.boom = boom
        self.ctx.res_jumps = jumps
        return boom

    def finish_case(self):

        self.prove_contradiction()

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
        self.ctx.add_fact(equals(jumps, jumpso.s))
        return jumpso

    def pop_max_jump(self, jumps):
        assert isinstance(jumps, JumpSet) and jumps.is_var, jumps
        self.prove(jumps.number > 0)
        J = Jump.fixed_var(jumps.var_name+'_max')
        jumpsr = JumpSet.fixed_var(jumps.var_name+'r')
        self.ctx.add_fact(equals(jumps, JumpSet.merge(J, jumpsr)))
        self.ctx.add_fact(~jumpsr.contains(Jump.X) | (Jump.X.length <= J.length))
        return J, jumpsr

    def pop_avoiding_jump(self, jumps, mines):
        assert isinstance(jumps, JumpSet) and jumps.is_var, jumps
        assert isinstance(mines, MineField)
        self.prove(jumps.number > mines.count)
        J = Jump.fixed_var(jumps.var_name+'_max')
        jumpsr = JumpSet.fixed_var(jumps.var_name+'r')
        self.ctx.add_fact(equals(jumps, JumpSet.merge(J, jumpsr)))
        self.ctx.add_fact(~mines[J.length])
        return J, jumpsr

    def pop_first_jump(self, jumps):
        assert isinstance(jumps, Jumps) and jumps.is_var, jumps
        self.prove(jumps.number > 0)
        J = Jump.fixed_var(jumps.var_name+'0')
        jumpsr = Jumps.fixed_var(jumps.var_name+'r')
        self.ctx.add_fact(equals(jumps, Jumps.concat(J, jumpsr)))
        return J, jumpsr

    def split_mines(self, mines, i):
        assert isinstance(mines, MineField) and mines.is_var
        assert isinstance(i, TermInt)
        self.prove((i >= 0) & (i <= mines.length))
        mines0 = MineField.fixed_var(mines.var_name+'0')
        mines1 = MineField.fixed_var(mines.var_name+'1')
        self.ctx.add_fact(equals(mines, mines0 + mines1))
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
        self.ctx.add_fact(equals(jumps, jumps_ih.s))
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
        self.ctx.add_fact(equals(mines, MineField(mines0, True, mines1)))
        self.ctx.add_fact(equals(mines0.count, 0))
        return mines0, mines1

    def split_jump_landings(self, jumps, i):
        assert isinstance(jumps, Jumps) and jumps.is_var
        self.prove((i >= 0) & (i < jumps.length))
        jumps0 = Jumps.fixed_var(jumps.var_name+'0')
        jumps1 = Jumps.fixed_var(jumps.var_name+'1')
        J = Jump.fixed_var(jumps.var_name+'_mid')
        self.ctx.add_fact(equals(jumps, Jumps.concat(jumps0, J, jumps1)))
        self.ctx.add_fact(jumps0.length <= i)
        self.ctx.add_fact(jumps0.length+J.length > i)
        return jumps0, J, jumps1

    def union_mines(self, mines1, mines2):
        assert isinstance(mines1, MineField) and isinstance(mines2, MineField)
        # self.prove(equals(mines1.length, mines2.length))
        mines = MineField.fixed_var('mines_un')
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
