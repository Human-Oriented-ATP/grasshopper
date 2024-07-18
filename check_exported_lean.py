#!/usr/bin/python

from parser import parse_problem_stream
from prover import prove_contradiction, constraints_to_lia, get_univ_theorems, UnsatProof
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
cmd_parser.add_argument('--extensionality',  default=False, action=argparse.BooleanOptionalAction,
                        help = "Add extensionality rules to the SMT solver")
cmd_parser.add_argument('--to_smt',  default=False, action=argparse.BooleanOptionalAction,
                        help = "Outputs an smt-file rather than calling a solver")

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

if config.to_smt:
    lia = constraints_to_lia(
        constraints,
        substitute = config.substitute,
        max_inst_iters = max_inst_iters,
    )
    lia.write_smt(
        sys.stdout,
        require_congruence = config.extensionality,
    )
else:
    res = prove_contradiction(
        constraints,
        substitute = config.substitute,
        max_inst_iters = max_inst_iters,
        extensionality = config.extensionality,
        show_model = True,
    )
    if isinstance(res, UnsatProof): print("Proven")
    else: print("No contradiction found. Satisfiable?")
