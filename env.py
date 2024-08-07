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

def model_display_mines(mines, model):
    dummy = FailedProofDisjoint(model, None, None, None)
    print(dummy.seq_str(mines))

class LogicContext:
    def __init__(self, env, facts, assumed_ids):
        self.env = env
        self.facts = list(facts)
        self.assumed_ids = list(assumed_ids)

    def clone(self):
        return LogicContext(self.env, self.facts, self.assumed_ids)
    def add_fact(self, fact, assumed = False):
        if assumed: self.assumed_ids.append(len(self.facts))
        assert isinstance(fact, TermBool)
        self.facts.append(fact)

    def show_assumed(self):
        print("Assumptions:")
        for idx in self.assumed_ids:
            print('*', self.facts[idx])
    def show_all(self):
        print("Facts:")
        assumed_set = set(self.assumed_ids)
        for idx, fact in enumerate(self.facts):
            if idx in assumed_set: bullet = '*'
            else: bullet = '.'
            print(bullet, fact)
    def show_last_assump(self, bullet = ' *'):
        if not self.assumed_ids: return
        n = len(self.assumed_ids)
        idx = self.assumed_ids[n-1]
        print('  '*n + bullet + ' '+ str(self.facts[idx]))
    def remove_facts(self, removed):
        removed = set(removed)
        facts = list(filter(lambda fact: fact not in removed, self.facts))
        new_to_ori = [idx for idx,fact in enumerate(self.facts) if fact not in removed]
        ori_to_new = {ori:new for new,ori in enumerate(new_to_ori)}
        assumed_ids = [ori_to_new[idx] for idx in self.assumed_ids if idx in ori_to_new]
        self.facts = facts
        self.assumed_ids = assumed_ids

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
        self.ctx = LogicContext(self, univ_theorems + ctx_theorems, [])
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
            prover.prove_contradiction(self.ctx.facts + [~goal], **self.prover_kwargs)
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
                self.ctx.facts + [landings_boom, mines_boom],
                **self.prover_kwargs,
            )
        except FailedProof as e:
            _, subst = prover.extract_subst(self.ctx.facts)
            landings_boom = subst[landings_boom]
            mines_boom = subst[mines_boom]
            for landings_boom_case in landings_boom.disj_args:
                for mines_boom_case in mines_boom.disj_args:
                    try:
                        prover.prove_contradiction(
                            self.ctx.facts + [landings_boom_case, mines_boom_case]
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
        J = Jump.fixed_var(jumps.var_name+'_avoid')
        jumpsr = JumpSet.fixed_var(jumps.var_name+'r')
        self.ctx.add_fact(equals(jumps, JumpSet.merge(J, jumpsr)))
        self.ctx.add_fact(~mines[J.length-1])
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
