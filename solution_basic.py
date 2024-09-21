from logic import equals, MineField, Jumps
from env import GrasshopperEnv
import prover

def solution(env):
    jumps = env.jumps
    mines = env.mines

    J, jumps = env.pop_max_jump(jumps)

    # single jump
    env.split_case(equals(jumps.number, 0))
    env.solve_with_jumps(Jumps.concat(J))

    # mines are nonempty
    mines0, mines1 = env.split_mines(mines, J.length)
    mines00, mines01 = env.split_mines(mines0, J.length-1)

    # no mine on the first jump
    # print("no mine on the first jump")
    env.split_case(~mines01[0])

    # mine before the first jump
    # print("mine before the first jump")
    env.split_case(mines1.count < jumps.number)
    jumpso = env.induction(jumps, mines1)
    env.solve_with_jumps(J + jumpso)

    # no mine before the first jump
    # print("no mine before the first jump")

    mines10, mines11 = env.split_first_mine(mines1)
    jumpso = env.induction(jumps, MineField(mines10, False, mines11))

    # no landing at the removed mine
    # print("no landing at the removed mine")
    env.split_case(~jumpso.landings[mines10.length])
    env.solve_with_jumps(J + jumpso)

    # landing at the removed mine
    # print("landing at the removed mine")
    jumps0, J2, jumps1 = env.split_jump_landings(jumpso, mines10.length+1)
    env.solve_with_jumps(jumps0 + J2 + J + jumps1)

    # mine on the first jump
    # print("mine on the first jump")

    # the first segment is smaller than the rest
    # print("the first segment is smaller than the rest")
    env.split_case(mines00.length <= mines1.length)

    mines10, mines11 = env.split_mines(mines1, mines00.length)
    mines_un = env.union_mines(mines00, mines10)
    jumpso = env.induction(jumps, mines_un + mines11)
    J2, jumpso = env.pop_first_jump(jumpso)
    env.solve_with_jumps(J2 + J + jumpso)

    # the first segment is bigger than the rest
    # print("the first segment is bigger than the rest")

    mines00, _ = env.split_mines(mines00, mines1.length)
    mines_un = env.union_mines(mines00, mines1)
    jumpso = env.induction(jumps, mines_un)
    J2, jumpso = env.pop_first_jump(jumpso)
    env.solve_with_jumps(J2 + J + jumpso)

if __name__ == "__main__":
    env = GrasshopperEnv(record_uflia = True, show_record_step = True)
    solution(env)    
    env.check_solved()
