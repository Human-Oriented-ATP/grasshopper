from logic import equals, MineField
from env import GrasshopperEnv
import prover

def solution(env):
    jumps = env.jumps
    mines = env.mines

    J, jumps = env.pop_max_jump(jumps)

    mines0, mines1 = env.split_mines(mines, J.length)

    jumpso = env.induction(jumps, mines1)
    env.solve_with_jumps(J + jumpso)

    env.ctx.remove_facts(env.ctx.facts[-3:-1]) # a hack to traceback before IH step

    mines00, mines01 = env.split_mines(mines0, J.length-1)

    mines10, mines11 = env.split_mines(mines1, mines00.length)
    mines_un = env.union_mines(mines00, mines10)
    jumpso = env.induction(jumps, mines_un + mines11)
    J2, jumpso = env.pop_first_jump(jumpso)
    env.solve_with_jumps(J2 + J + jumpso)

    mines00, _ = env.split_mines(mines00, mines1.length)
    mines_un = env.union_mines(mines00, mines1)
    jumpso = env.induction(jumps, mines_un)
    J2, jumpso = env.pop_first_jump(jumpso)
    env.solve_with_jumps(J2 + J + jumpso)

    mines10, mines11 = env.split_first_mine(mines1)
    jumpso = env.induction(jumps, MineField(mines10, False, mines11))

    env.solve_with_jumps(J + jumpso)

    jumps0, J2, jumps1 = env.split_jump_landings(jumpso, mines10.length+1)
    env.solve_with_jumps(jumps0 + J2 + J + jumps1)

    jumpso = env.order_jumps(jumps)
    env.solve_with_jumps(J+jumpso)

if __name__ == "__main__":
    env = GrasshopperEnv(auto_assume = True)
    solution(env)    
    env.check_solved()
