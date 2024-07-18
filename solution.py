from logic import equals, MineField
from env2 import GrasshopperEnv
import prover

env = GrasshopperEnv(record_uflia = False)

jumps = env.jumps
mines = env.mines

# mines are empty
env.split_case(equals(mines.count, 0))
jumpso = env.order_jumps(jumps)
boom = env.provide_jumps(jumpso)
env.finish_case()

# mines are nonempty
J, jumps = env.pop_max_jump(jumps)

mines0, mines1 = env.split_mines(mines, J.length)
mines00, mines01 = env.split_mines(mines0, J.length-1)

# no mine on the first jump
# print("no mine on the first jump")
env.split_case(~mines01[0])

# mine before the first jump
# print("mine before the first jump")
env.split_case(~equals(mines0.count, 0))
jumpso = env.induction(jumps, mines1)
boom = env.provide_jumps(J + jumpso)
env.finish_case()

# no mine before the first jump
# print("no mine before the first jump")

mines10, mines11 = env.split_first_mine(mines1)
jumpso = env.induction(jumps, MineField(mines10, False, mines11))

# no landing at the removed mine
# print("no landing at the removed mine")
env.split_case(~jumpso.landings[mines10.length])
boom = env.provide_jumps(J + jumpso)
env.finish_case()

# landing at the removed mine
# print("landing at the removed mine")
jumps0, J2, jumps1 = env.split_jump_landings(jumpso, mines10.length+1)
boom = env.provide_jumps(jumps0 + J2 + J + jumps1)
env.finish_case()

# mine on the first jump
# print("mine on the first jump")

# the first segment is smaller than the rest
# print("the first segment is smaller than the rest")
env.split_case(mines00.length <= mines1.length)

mines10, mines11 = env.split_mines(mines1, mines00.length)
mines_un = env.union_mines(mines00, mines10)
jumpso = env.induction(jumps, mines_un + mines11)
J2, jumpso = env.pop_first_jump(jumpso)
boom = env.provide_jumps(J2 + J + jumpso)
env.finish_case()

# the first segment is bigger than the rest
# print("the first segment is bigger than the rest")

mines00, _ = env.split_mines(mines00, mines1.length)
mines_un = env.union_mines(mines00, mines1)
jumpso = env.induction(jumps, mines_un)
J2, jumpso = env.pop_first_jump(jumpso)
boom = env.provide_jumps(J2 + J + jumpso)
env.finish_case()

env.check_solved()
