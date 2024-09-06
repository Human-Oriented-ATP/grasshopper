from logic import equals, Substitution, TermBool, TermInt, Jump, Jumps, MineField, JumpSet, FREE_VAR
from auto_inst import AutoInstance
from smt_lia import LiaChecker
from uflia_hammer import record_grasshopper_task

debug = False
default_solver = ('cvc4', '-m', '--lang', 'smt')

class ProvenTrivially:
    pass

class FailedProof(Exception):
    def __init__(self, model):
        self.model = model

    def model_str(self):
        lines = []
        if self.model is None:
            lines.append("No available model")
        else:
            lines.append("Model:")
            for v,value in self.model.base_dict.items():
                lines.append(f"  {v} = {value}")
                if v.f is not None:
                    v_simp = v.f(*self.model[v.args])
                else:
                    v_simp = v
                if v != v_simp:
                    lines.append(f"[simp]  {v_simp} = {value}")
        return '\n'.join(lines)
        
    def __str__(self):
        return "Proof Failed!\n"+self.model_str()

# looks for oriented equations "a = f(b,c)"
# and tries to transform them into a substitution

def extract_subst(constraints):
    res = []
    subst = Substitution({})
    for constraint in constraints:
        if constraint.f != equals or not constraint.args[0].is_var:
            res.append(constraint)
            continue
        constraint = subst[constraint]
        if constraint.f != equals or not constraint.args[0].is_var:
            res.append(constraint)
            continue
        lhs,rhs = constraint.args
        subst = subst.substitute({lhs : rhs})
    res = [subst[constraint] for constraint in res]
    return res, subst    

# automatically closes assumptions of the form (X = ...) where X is free
def simplify_clause(clause, can_eliminate = lambda x: x.var_type == FREE_VAR):
    changed = True
    while changed:
        changed = False
        for literal in clause.disj_args:
            nlit = ~literal
            if nlit.f == equals and isinstance(nlit.args[0], TermInt):
                zero = nlit.args[0] - nlit.args[1]
                for x,coef in zip(zero.summands, zero.muls):
                    if x.is_var and can_eliminate(x) and abs(coef) == 1:
                        subst = Substitution({ x : zero*(-coef) + x })
                        clause = subst[clause]
                if changed: break
    return clause

# analog to simplify_clause assuming existentially quantified variables and conjunctive clause
def simplify_exist_clause(clause, *args, **kwargs):
    return ~simplify_clause(~clause, *args, **kwargs)

# splits constraints into lists of ground terms, and quantified AutoInstances 

def separate_ground(constraints):
    ground = []
    quantified = []

    for constraint in constraints:
        if not any(v.is_free_var for v in constraint.all_vars):
            if debug: print(constraint)
            ground.append(constraint)
        else:
            constraint = constraint.clausify()
            for clause in constraint.conj_args:
                # try to simplify a dis-equality
                clause = simplify_clause(clause)
                if any(x.is_free_var for x in clause.all_vars):
                    quantified.append(AutoInstance(clause))
                else:
                    if debug: print(clause)
                    ground.append(clause)

    return ground, quantified

# adds instances of quantified formulas to match the ground terms from lia

def add_instances(lia, quantified, max_inst_iters):
    iteration = 0
    bool_i = 0
    int_i = 0
    while iteration < max_inst_iters:
        cur_terms = lia.bool_vars[bool_i:] + lia.int_vars[int_i:]
        bool_i = len(lia.bool_vars)
        int_i = len(lia.int_vars)
        if not cur_terms: break
        for constraint in quantified:
            for ground_constraint in constraint.get_instances(cur_terms):
                if debug: print(ground_constraint)
                lia.add_constraint(ground_constraint)
        iteration += 1

# tries to prove a contradiction from the given list of terms
# (1) it looks for rewriting rules for fixed variables a = f(b,c),
#     and transforms them into a substitution applied to all the constraints
# (2) it separates constraints with free variables
#     clausify them & converts them into a matchable terms
# (3) puts all the ground constraints into a QF_LIA environment
# (4) in a few iterations, adds extra instances of clauses with free variables
#     that match the ground constraints

def constraints_to_lia(constraints, extra_terms = (), substitute = True, max_inst_iters = 1, congruence = True):

    if debug:
        print("\nConstraints:\n")
        for x in constraints: print(x)

    # substitute directed equations
    if substitute:
        constraints2, subst = extract_subst(constraints)
    else:
        constraints2 = constraints
        subst = Substitution({})
    if debug:
        print("\nSubstitution:\n")
        for x,value in subst.base_dict.items(): print(f"{x} -> {value}")

    if TermBool.false in constraints:
        return ProvenTrivially()

    if debug:
        print("\nSubstituted, all:\n")
        for x in constraints2: print(x)

        print("\nSubstituted, unquantified:\n")

    # separate quantified, feed the rest to a LIA
    ground, quantified = separate_ground(constraints2)
    lia = LiaChecker()
    for constraint in ground:
        lia.add_constraint(constraint)
    for term in extra_terms:
        lia.add_term(term)

    if debug:
        print("\nSubstituted, quantified:\n")
        for x in quantified:
            print(x.generic)

    if debug:
        print("\nExtra instances:\n")

    # add instances of quantified constraints
    add_instances(lia, quantified, max_inst_iters)

    if congruence:
        lia.add_congruence_theorems()

    if debug:
        print()

    return lia

last_problem_index = -1

def prove_contradiction(constraints, record_uflia = False, show_step = False, solver_cmd = default_solver, **kwargs):
    global last_problem_index
    lia = constraints_to_lia(constraints, **kwargs)

    if isinstance(lia, ProvenTrivially): return
    lia.solve(solver_cmd)

    if not lia.unsatisfiable:
        if lia.satisfiable:
            _, subst = extract_subst(constraints)
            raise FailedProof(subst.substitute(lia.sat_model))
        else:
            raise FailedProof(None)

    # record as a problem
    last_problem_index += 1
    if show_step:
        print(last_problem_index)
    if record_uflia:
        hammer_fname = "hammer_problems/grasshopper"+str(last_problem_index)
        record_grasshopper_task(self.facts, hammer_fname)

# the list optional_constraints gets reduced to a satisfiable beginning
def get_model(hard_constraints, optional_constraints, extra_terms = (), solver_cmd = default_solver, **kwargs):

    hard_constraints, subst = extract_subst(hard_constraints)
    optional_constraints_ori = list(optional_constraints)

    lia_base = constraints_to_lia(
        hard_constraints,
        substitute = False,
        extra_terms = [subst[term] for term in extra_terms],
        **kwargs,
    )
    if isinstance(lia_base, ProvenTrivially): return None

    def finish_model(model):
        if extra_terms:
            enriched_dict = dict(model.base_dict)
            for term in extra_terms:
                if term not in enriched_dict:
                    enriched_dict[term] = model[subst[term]]
            model = Substitution(enriched_dict)
        return model        

    def try_constraints():
        lia = lia_base.clone()
        for constraint in optional_constraints:
            lia.add_constraint(subst[constraint])
        lia.solve(solver_cmd)
        if lia.satisfiable and lia.sat_model is not None:
            return lia.sat_model
        else:
            return None

    model = try_constraints()
    if model is not None:
        return finish_model(model)

    del optional_constraints[:]
    model = try_constraints()
    if model is None: # there is no model even without optional constraints
        optional_constraints.extend(optional_constraints_ori)
        return None

    for constraint in optional_constraints_ori:
        optional_constraints.append(constraint)
        model2 = try_constraints()
        if model2 is None:
            optional_constraints.pop()
        else:
            model = model2

    return finish_model(model)

def get_univ_theorems():
    univ_theorems = [
        Jump.X.length > 0,
        JumpSet.X.length >= 0,
        JumpSet.X.number >= 0,
        JumpSet.X.number <= JumpSet.X.length,
        ~equals(JumpSet.X.number, 0) | equals(JumpSet.X.length, 0),
        MineField.X.length >= 0,
        MineField.X.count >= 0,
        MineField.X.length >= MineField.X.count,
    ]
    X = TermInt.X
    A = MineField.free_var('A')
    univ_theorems.extend([
        ~A[X] | (X >= 0),
        ~A[X] | (X < A.length),
        ~A[X] | (A.count > 0),
        ~(A.count >= A.length) | ~(X >= 0) | ~(X < A.length) | A[X],
    ])
    return univ_theorems
