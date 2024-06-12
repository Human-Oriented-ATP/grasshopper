import sys
import itertools
from itertools import combinations

from smt_lia import LiaChecker
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

class LogicContext:
    def __init__(self, env, facts, res_jumps, boom):
        self.env = env
        self.facts = list(facts)
        self.res_jumps = res_jumps
        self.boom = boom

    def clone(self):
        return LogicContext(self.env, self.facts, self.res_jumps, self.boom)
    def add_fact(self, fact):
        assert isinstance(fact, TermBool)
        self.facts.append(fact)

    def prove_contradiction(self):
        # print('Proving subgoal...', end = '')
        res = prover.prove_contradiction(self.facts)
        # print('   DONE')
        if isinstance(res, prover.UnsatProof): return True
        elif isinstance(res, Substitution):
            _, subst = prover.extract_subst(self.facts)
            model_display_mines(subst[self.env.mines], res)
            if self.res_jumps is not None:
                model_display_mines(subst[self.res_jumps].landings, res)
            if self.boom is not None:
                print('  '*int(res[self.boom]) + '#')
        return False

    def prove(self, goal):
        ctx = self.clone()
        ctx.add_fact(~goal)
        return ctx.prove_contradiction()

class GrasshopperEnv:
    def __init__(self):
        self.size = TermInt.fixed_var('size')
        self.jumps = JumpSet.fixed_var('jumps')
        self.mines = MineField.fixed_var('mines')
        univ_theorems = [
            Jump.X.length > 0,
            JumpSet.X.length >= 0,
            JumpSet.X.number >= 0,
            JumpSet.X.number <= JumpSet.X.length,
            ~equals(JumpSet.X.number, 0) | equals(JumpSet.X.length, 0),
            MineField.X.length >= 0,
            MineField.X.count >= 0,
            MineField.X.length >= MineField.X.count,
        ]
        X = TermInt.X
        A = MineField.free_var('A')
        univ_theorems.extend([
            ~A[X] | (X >= 0),
            ~A[X] | (X < A.length),
            ~A[X] | (A.count > 0),
            ~(A.count >= A.length) | ~(X >= 0) | ~(X < A.length) | A[X],
        ])
        ctx_theorems = [
            self.jumps.nodup,
            equals(self.jumps.length, self.size+1),
            equals(self.mines.length, self.size),
            self.jumps.number > self.mines.count,
        ]
        self.ctx = LogicContext(self, univ_theorems + ctx_theorems, None, None)
        self.ctx_stack = []
        self.proven = False

    def split_case(self, prop):
        assert isinstance(prop, TermBool)
        ctx2 = self.ctx.clone()
        ctx2.add_fact(~prop)
        self.ctx_stack.append(ctx2)
        self.ctx.add_fact(prop)

    def provide_jumps(self, jumps):
        assert isinstance(jumps, Jumps)
        if not self.ctx.prove(equals(jumps.s, self.jumps)):
            raise Exception("Failed to prove that we keep the same set of jumps")
        boom = TermInt.fixed_var('boom')
        self.ctx.add_fact(boom > 0)
        self.ctx.add_fact(boom < self.size)
        self.ctx.add_fact(jumps.landings[boom])
        self.ctx.add_fact(self.mines[boom])
        self.ctx.boom = boom
        self.ctx.res_jumps = jumps
        return boom

    def finish_case(self):

        if self.ctx.prove_contradiction():
            if self.ctx_stack:
                self.ctx = self.ctx_stack.pop()
            else:
                self.ctx = None
                self.proven = True
        else:
            raise Exception("Failed to prove contradiction")

    ######  Domain specific operations

    def order_jumps(self, jumps):
        assert isinstance(jumps, JumpSet) and jumps.is_var
        jumpso = Jumps.fixed_var(jumps.var_name + 'o')
        self.ctx.add_fact(equals(jumps, jumpso.s))
        return jumpso

    def pop_max_jump(self, jumps):
        assert isinstance(jumps, JumpSet) and jumps.is_var, jumps
        if not self.ctx.prove(jumps.number > 0):
            raise Exception(f"pop_max_jump: Failed to prove that {jumps} is non-empty")
        J = Jump.fixed_var(jumps.var_name+'_max')
        jumpsr = JumpSet.fixed_var(jumps.var_name+'r')
        self.ctx.add_fact(equals(jumps, JumpSet.merge(J, jumpsr)))
        self.ctx.add_fact(~jumpsr.contains(Jump.X) | (Jump.X.length <= J.length))
        return J, jumpsr

    def pop_first_jump(self, jumps):
        assert isinstance(jumps, Jumps) and jumps.is_var, jumps
        if not self.ctx.prove(jumps.number > 0):
            raise Exception(f"pop_first_jump: Failed to prove that {jumps} is non-empty")
        J = Jump.fixed_var(jumps.var_name+'0')
        jumpsr = Jumps.fixed_var(jumps.var_name+'r')
        self.ctx.add_fact(equals(jumps, Jumps.concat(J, jumpsr)))
        return J, jumpsr

    def split_mines(self, mines, i):
        assert isinstance(mines, MineField) and mines.is_var
        assert isinstance(i, TermInt)
        if not self.ctx.prove((i >= 0) & (i <= mines.length)):
            raise Exception(f"split_mines: Failed to prove that {i} points inside {mines}")
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
        if not self.ctx.prove(conjunction(*requirements)):
            for i,req in enumerate(requirements):
                if not self.ctx.prove(req):
                    raise Exception(f"Using induction: Failed to prove {i}: {req}")

        jumps_ih = Jumps.fixed_var('jumps_ih')
        self.ctx.add_fact(equals(jumps, jumps_ih.s))
        self.ctx.add_fact(
            ~jumps_ih.landings[TermInt.X] |
            ~mines[TermInt.X]
        )
        return jumps_ih

    def split_first_mine(self, mines):
        assert isinstance(mines, MineField) and mines.is_var
        if not self.ctx.prove(mines.count > 0):
            raise Exception(f"split_first_mine: Failed to prove that {mines} contains a mine")
        
        mines0 = MineField.fixed_var(mines.var_name+'0')
        mines1 = MineField.fixed_var(mines.var_name+'1')
        self.ctx.add_fact(equals(mines, MineField(mines0, True, mines1)))
        self.ctx.add_fact(equals(mines0.count, 0))
        return mines0, mines1

    def split_jump_landings(self, jumps, i):
        assert isinstance(jumps, Jumps) and jumps.is_var
        if not self.ctx.prove((i >= 0) & (i < jumps.length)):
            raise Exception(f"split_jump_langings: {i} doesn't point inside {jumps}")
        jumps0 = Jumps.fixed_var(jumps.var_name+'0')
        jumps1 = Jumps.fixed_var(jumps.var_name+'1')
        J = Jump.fixed_var(jumps.var_name+'_mid')
        self.ctx.add_fact(equals(jumps, Jumps.concat(jumps0, J, jumps1)))
        self.ctx.add_fact(jumps0.length <= i)
        self.ctx.add_fact(jumps0.length+J.length > i)
        return jumps0, J, jumps1

    def union_mines(self, mines1, mines2):
        assert isinstance(mines1, MineField) and isinstance(mines2, MineField)
        if not self.ctx.prove(equals(mines1.length, mines2.length)):
            raise Exception(f"union_mines: {mines1} are not of the same length as {mines2}")
        mines = MineField.fixed_var('mines_un')
        self.ctx.add_fact(~mines1[TermInt.X] | mines[TermInt.X])
        self.ctx.add_fact(~mines2[TermInt.X] | mines[TermInt.X])
        self.ctx.add_fact(equals(mines.length, mines1.length))
        self.ctx.add_fact(equals(mines.length, mines2.length))
        self.ctx.add_fact(mines1.count <= mines.count)
        self.ctx.add_fact(mines2.count <= mines.count)
        self.ctx.add_fact(mines.count <= mines1.count + mines2.count)
        return mines
