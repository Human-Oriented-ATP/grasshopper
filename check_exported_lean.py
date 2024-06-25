#!/usr/bin/python

from parser import parse_problem_stream
from prover import prove_contradiction, get_univ_theorems, UnsatProof
import sys

try:
    constraints = parse_problem_stream(sys.stdin)
except:
    print("Parse error")
    raise

univ_theorems = get_univ_theorems()

res = prove_contradiction(univ_theorems + constraints, show_model = True)
if isinstance(res, UnsatProof): print("Proven")
else: print("No contradiction found. Satisfiable?")
