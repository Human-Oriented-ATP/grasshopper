from logic import equals, MineField
from env2 import GrasshopperEnv
import prover

env = GrasshopperEnv(record_uflia = False, show_record_step = False)

jumps = env.jumps
mines = env.mines

# mines are empty
env.split_case(equals(mines.count, 0))
jumpso = env.order_jumps(jumps)
env.solve_with_jumps(jumpso)

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

# no mine before the first jump
# print("no mine before the first jump")
env.split_case(equals(mines00.count, 0))

jumpso = env.induction(jumps, mines1)
J2, jumpso = env.pop_first_jump(jumpso)
env.solve_with_jumps(J2 + J + jumpso)

# mine before the first jump, and at the first jump
# print("mine before the first jump")

mines_un = env.union_mines(mines00, mines1)
J2, jumps2 = env.pop_avoiding_jump(jumps, mines_un)
mines10, mines11 = env.split_mines(mines1, J2.length)
jumpso = env.induction(jumps2, mines11)
env.solve_with_jumps(J2 + J + jumpso)

env.check_solved()
