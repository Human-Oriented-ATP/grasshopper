from env import GrasshopperEnv
from solution_basic import solution as solution_basic
from solution_a3m2 import solution as solution_a3m2
from solution_a5 import solution as solution_a5
from solution2_basic import solution as solution2_basic

def test_solution(name, solution, **kwargs):
    print(f"Solution {name}:")
    print()
    env = GrasshopperEnv(**kwargs)
    solution(env)    
    env.check_solved()
    print()

if __name__ == "__main__":
    test_solution("basic", solution_basic)
    test_solution("A3 M2", solution_a3m2, auto_assume = True)
    test_solution("A5", solution_a5, auto_assume = True)
    test_solution("variant2", solution2_basic)

