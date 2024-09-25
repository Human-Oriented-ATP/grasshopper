import sys
from logic import *

header = """
import Grasshopper.ProcessingAndAutomation

set_option grasshopper.add_theorems true
"""

solution_skeleton = """:= by
  intros
  auto
"""

type_to_lean = {
    TermBool: "Prop",
    TermInt: "Int",
    Jump: "Jump",
    Jumps: "Jumps",
    JumpSet: "JumpSet",
    MineField: "MineField",
}

def int_comb_lean(*args, const = None, muls = None):
    summands = []
    for arg,mul in zip(args, muls):
        if mul == 1: summands.append(arg)
        else: summands.append(f"{mul}*{arg}")
    if const != 0: summands.append(str(const))
    if len(summands) == 0: return '0'
    elif len(summands) == 1: return summands[0]
    else: return '('+' + '.join(summands)+')'

def concat_lean(*args):
    if not args:
        return "[]"
    else:
        summands = []
        for arg in args:
            arg_str = term_to_lean_str(arg)
            if isinstance(arg, TermSequence):
                summands.append(arg_str)
            else:
                summands.append('['+arg_str+']')
        return ' ++ '.join(summands)

def merge_jumpset_lean(*args):
    if not args:
        res = "{}"
    else:
        summands = []
        for arg in args:
            arg_str = term_to_lean_str(arg)
            if isinstance(arg, JumpSet):
                summands.append(arg_str)
            else:
                summands.append(f"(JumpSet.singleton {arg_str})")
        res = ' + '.join(summands)
        return f"({res} : JumpSet)"

fun_to_lean = {
    TermBool.true.f: "true",
    TermBool.false.f: "false",
    TermBool.invert: "¬",
    disjunction: (lambda *args: '('+' ∨ '.join(args)+')'),
    conjunction: (lambda *args: '('+' ∧ '.join(args)+')'),
    TermBool.as_int.fget: lambda arg: f"(Bool.toNat {arg} : Int)",
    equals: lambda a,b: f"{a} = {b}",
    TermInt._mk: int_comb_lean,
    TermInt.le: lambda a,b: f"{a} <= {b}",
    MineField.concat: concat_lean,
    MineField.count.fget: "MineField.countMines",
    MineField.getitem: lambda mines, i: f"↑(List.getIndexD {mines} {i})",
    MineField.length.fget: "MineField.length",
    MineField.empty_copy.fget: "MineField.emptyCopy",
    Jump._mk: "↑",
    Jump.length.fget: "Jump.length",
    Jump.to_empty_minefield.fget: "jumpOver",
    JumpSet.merge: merge_jumpset_lean,
    JumpSet.length.fget: "JumpSet.sum",
    JumpSet.number.fget: "Multiset.sizeOf",
    JumpSet.subtract: lambda a,b: f"({a} - {b})",
    JumpSet._contains: lambda a,b: f"{b} ∈ {a}",
    JumpSet.disjoint: lambda a,b: f"{a} ∩ {b} = "+"{}",
    JumpSet.nodup.fget: "Multiset.Nodup",
    Jumps.concat: concat_lean,
    Jumps.landings.fget: "Jumps.landings",
    Jumps.s.fget: "Jumps.s",
}

def term_to_lean_str(term):
    if term.is_var:
        return term.var_name
    lean_f = fun_to_lean[term.f]
    args = [
        term_to_lean_str(arg)
        for arg in term.args
    ]
    if isinstance(lean_f, str):
        if not args: return lean_f
        else: return '(' + ' '.join([lean_f]+args) + ')'
    else:
        if term.f in (MineField.concat, Jumps.concat, JumpSet.merge):
            args = term.args
        return lean_f(*args, **term.meta_args)

def prop_to_lean_str(prop):
    if len(prop.all_vars) != len(set(v.var_name for v in prop.all_vars)):
        raise Exception(f"Duplicite variable in: {prop.all_vars}")
    assert all(v.var_type in (FIXED_VAR, FREE_VAR) for v in prop.all_vars)
    free_vars = [v for v in prop.all_vars if v.var_type == FREE_VAR]
    free_vars.sort(key = lambda v: v.var_name)
    prop_str = term_to_lean_str(prop)
    if not free_vars: return prop_str
    q_args = [
        f"({v.var_name} : {type_to_lean[type(v)]})"
        for v in free_vars
    ]
    q_args = ' '.join(q_args)
    return f"(∀ {q_args}, {prop_str})"

export_stream = sys.stdout
skip_first = 0 # first n theorems will be the universal theorems

def start_export(skip_first_arg, fname = "Grasshopper/HammerProblems.lean"):
    global export_stream, skip_first
    skip_first = skip_first_arg
    export_stream = open(fname, 'w')
    export_stream.write(header)

def finish_export():
    global export_stream
    if export_stream == sys.stdout: return
    export_stream.close()
    export_stream = sys.stdout

def export_problem(constraints, problem_num):
    constraints = constraints[skip_first:]
    fixed_vars = set()
    for constraint in constraints:
        fixed_vars.update(
            v for v in constraint.all_vars
            if v.var_type == FIXED_VAR
        )
    fixed_vars = list(fixed_vars)
    fixed_vars.sort(key = lambda v: v.var_name)
    if len(set(v.var_name for v in fixed_vars)) != len(fixed_vars):
        raise Exception(f"Duplicite name among {fixed_vars}")
    thm_name = f"hammer_problem_{problem_num}"
    print(file = export_stream)
    #print(f"theorem {thm_name}", file = export_stream)
    print(f"example -- {problem_num}", file = export_stream)
    for v in fixed_vars:
        print(f"  ({v.var_name} : {type_to_lean[type(v)]})", file = export_stream)
    prefix = ': '
    for constraint in constraints:
        constraint_str = prop_to_lean_str(constraint)
        print(prefix+constraint_str+' →', file = export_stream)
        prefix = '  '
    print(prefix+"False", file = export_stream)
    print(solution_skeleton, file = export_stream)
