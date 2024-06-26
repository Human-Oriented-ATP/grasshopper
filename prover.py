from logic import equals, Substitution, TermBool, TermInt, Jump, Jumps, MineField, JumpSet
from auto_inst import AutoInstance
from smt_lia import LiaChecker

# long-term TODO: tracking a model / unsat core

class UnsatProof:
    pass

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

debug = False

# tries to prove a contradiction from the given list of terms
# (1) it looks for rewriting rules for fixed variables a = f(b,c),
#     and transforms them into a substitution applied to all the constraints
# (2) it separates constraints with free variables
#     clausify them & converts them into a matchable terms
# (3) puts all the ground constraints into a QF_LIA environment
# (4) in a few iterations, adds extra instances of clauses with free variables
#     that match the ground constraints

def constraints_to_lia(constraints, substitute = True, max_inst_iters = 1):

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

    if TermBool.false in constraints: return True

    if debug:
        print("\nSubstituted, all:\n")
        for x in constraints2: print(x)

        print("\nSubstituted, unquantified:\n")

    # separate quantified, feed the rest to a LIA
    lia = LiaChecker()
    quantified = []
    for constraint in constraints2:
        if not any(v.is_free_var for v in constraint.all_vars):
            if debug: print(constraint)
            lia.add_constraint(constraint)
        else:
            constraint = constraint.clausify()
            for clause in constraint.conj_args:
                # try to simplify a dis-equality
                changed = True
                while changed:
                    changed = False
                    for literal in clause.disj_args:
                        nlit = ~literal
                        if nlit.f == equals and isinstance(nlit.args[0], TermInt):
                            zero = nlit.args[0] - nlit.args[1]
                            for x,coef in zip(zero.summands, zero.muls):
                                if x.is_free_var and abs(coef) == 1:
                                    subst = Substitution({ x : zero*(-coef) + x })
                                    clause = subst[clause]
                            if changed: break
                if any(x.is_free_var for x in clause.all_vars):
                    quantified.append(AutoInstance(clause))
                else:
                    if debug: print(clause)
                    lia.add_constraint(clause)

    if debug:
        print("\nSubstituted, quantified:\n")
        for x in quantified:
            print(x.generic)

    if debug:
        print("\nExtra instances:\n")
    # add instances of quantified constraints
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
    if debug:
        print()

    return lia

def prove_contradiction(constraints, show_model = True, extensionality = True, **kwargs):
    lia = constraints_to_lia(constraints)

    lia.solve(require_congruence = extensionality)

    if lia.satisfiable:
        if show_model: lia.show_model()
        _, subst = extract_subst(constraints)
        return subst.substitute(lia.sat_model)
    elif lia.unsatisfiable:
        return UnsatProof()
    else:
        return None

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
