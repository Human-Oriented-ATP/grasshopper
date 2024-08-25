#!/usr/bin/python3

from parser import parse_problem_stream
from prover import prove_contradiction, constraints_to_lia, get_univ_theorems, FailedProof
import sys
import argparse

cmd_parser = argparse.ArgumentParser(prog='check_exported_lean.py',
                                     description='Tries to prove a list of constraints about grasshopper contradictory',
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)

cmd_parser.add_argument('--add_thms',  default=False, action=argparse.BooleanOptionalAction,
                        help = "Add a default list of universally quantified theorems")
cmd_parser.add_argument('--substitute',  default=False, action=argparse.BooleanOptionalAction,
                        help = "Substitutes given equalities")
cmd_parser.add_argument('--instantiate',  default=False, action=argparse.BooleanOptionalAction,
                        help = "Instantiate universally quantified constraints (default: ignore them)")
cmd_parser.add_argument('--congruence',  default=False, action=argparse.BooleanOptionalAction,
                        help = "Add congruence rules to the SMT solver")
cmd_parser.add_argument('--solver',  default=None, type=str,
                        help = "Solver to run: z3, cvc4, cvc5, or a full command. If not specified, print smt input")

config = cmd_parser.parse_args()

try:
    constraints = parse_problem_stream(sys.stdin)
except:
    print("Parse error")
    raise

if config.add_thms:
    constraints = get_univ_theorems() + constraints

if config.instantiate: max_inst_iters = 1
else: max_inst_iters = 0

if config.solver is None:
    lia = constraints_to_lia(
        constraints,
        substitute = config.substitute,
        max_inst_iters = max_inst_iters,
        congruence = config.congruence,
    )
    lia.write_smt(
        sys.stdout,
    )
else:
    if config.solver == 'z3': solver_cmd = ('z3', '-in', '-smt2')
    elif config.solver in ('cvc4', 'cvc5'): solver_cmd = (config.solver, '-m', '--lang', 'smt')
    else: solver_cmd = tuple(config.solver.split(' '))
    try:
        prove_contradiction(
            constraints,
            substitute = config.substitute,
            max_inst_iters = max_inst_iters,
            congruence = config.congruence,
            solver_cmd = solver_cmd,
        )
        print("Proven")
    except FailedProof as e:
        print(e)
        print("No contradiction found. Satisfiable?")
