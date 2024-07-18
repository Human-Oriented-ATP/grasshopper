from logic import equals, MineField
from env2 import GrasshopperEnv
import prover

env = GrasshopperEnv(auto_assume = True)

jumps = env.jumps
mines = env.mines

J, jumps = env.pop_max_jump(jumps)

mines0, mines1 = env.split_mines(mines, J.length)
mines00, mines01 = env.split_mines(mines0, J.length-1)

env.split_case(~mines01[0])

jumpso = env.induction(jumps, mines1)
boom = env.provide_jumps(J + jumpso)
env.finish_case()

mines10, mines11 = env.split_first_mine(mines1)
jumpso = env.induction(jumps, MineField(mines10, False, mines11))

env.split_case(~jumpso.landings[mines10.length])
boom = env.provide_jumps(J + jumpso)
env.finish_case()

jumps0, J2, jumps1 = env.split_jump_landings(jumpso, mines10.length+1)
boom = env.provide_jumps(jumps0 + J2 + J + jumps1)
env.finish_case()

mines10, mines11 = env.split_mines(mines1, mines00.length)
mines_un = env.union_mines(mines00, mines10)
jumpso = env.induction(jumps, mines_un + mines11)
J2, jumpso = env.pop_first_jump(jumpso)
boom = env.provide_jumps(J2 + J + jumpso)
env.finish_case()

mines00, _ = env.split_mines(mines00, mines1.length)
mines_un = env.union_mines(mines00, mines1)
jumpso = env.induction(jumps, mines_un)
J2, jumpso = env.pop_first_jump(jumpso)
boom = env.provide_jumps(J2 + J + jumpso)
env.finish_case()

jumpso = env.order_jumps(jumps)
boom = env.provide_jumps(J+jumpso)
env.finish_case()

env.check_solved()
