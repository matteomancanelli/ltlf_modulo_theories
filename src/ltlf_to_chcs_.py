from formula import *
from utils import *

def generate_chcs_from_ltl(formula):
    formula = to_nnf(formula)
    closure = list(formula.get_closure())
    pos_dict = {subformula: idx for idx, subformula in enumerate(closure)}
    dim = len(closure)

    print(f"Position dictionary: {pos_dict}")

    formula_index = pos_dict[formula]
    last_index = pos_dict[Last()]

    header = getHeader(pos_dict, dim)
    body = getBody(formula_index, last_index, dim)

    return header + body


def getHeader(pos_dict, dim):
    header = "(set-logic HORN)\n\n"
    #header += "(set-option :timeout 10000)\n(set-option :smt.qi.eager_threshold 100)\n(set-option :smt.mbqi true)"

    bitvector = f"(declare-fun R ((_ BitVec {dim})) Bool)\n\n"
    in_set = f"(define-fun in-set ((q (_ BitVec {dim})) (i (_ BitVec {dim}))) Bool\n\t(= (bvand q (bvshl (_ bv1 {dim}) i)) (bvshl (_ bv1 {dim}) i)))\n\n"

    loc = getLoc(pos_dict, dim)
    trans = getTrans(pos_dict, dim)

    header += bitvector + in_set + loc + trans
    return header


def getLoc(pos_dict, dim):
    next_form_dict = {form_idx: formula for formula, form_idx in pos_dict.items() if isinstance(formula, Next)}
    until_form_dict = {form_idx: formula for formula, form_idx in pos_dict.items() if isinstance(formula, Until)}

    loc = f"""(define-fun Loc ((q (_ BitVec {dim}))) Bool\n  (and\n"""
    
    # Group similar formula types to help the solver recognize patterns
    # Process propositional operators first
    prop_constraints = ""
    temp_constraints = ""
    
    for formula, form_idx in pos_dict.items():
        if isinstance(formula, Negation):
            prop_constraints += f"    (=> (in-set q (_ bv{form_idx} {dim})) (not (in-set q (_ bv{pos_dict[formula.arg]} {dim}))))\n\n"
        
        if isinstance(formula, Conjunction):
            prop_constraints += f"    (=> (in-set q (_ bv{form_idx} {dim})) (and (in-set q (_ bv{pos_dict[formula.left]} {dim})) (in-set q (_ bv{pos_dict[formula.right]} {dim}))))\n\n"
        
        if isinstance(formula, Disjunction):
            prop_constraints += f"    (=> (in-set q (_ bv{form_idx} {dim})) (or (in-set q (_ bv{pos_dict[formula.left]} {dim})) (in-set q (_ bv{pos_dict[formula.right]} {dim}))))\n\n"
        
        if isinstance(formula, Until):
            temp_constraints += f"    (=> (in-set q (_ bv{form_idx} {dim})) (or (in-set q (_ bv{pos_dict[formula.left]} {dim})) (in-set q (_ bv{pos_dict[formula.right]} {dim}))))\n\n"
        
        if isinstance(formula, Release):
            temp_constraints += f"    (=> (in-set q (_ bv{form_idx} {dim})) (in-set q (_ bv{pos_dict[formula.right]} {dim})))\n\n"
        
        if isinstance(formula, Globally):
            temp_constraints += f"    (=> (in-set q (_ bv{form_idx} {dim})) (and (in-set q (_ bv{pos_dict[formula.arg]} {dim})) (in-set q (_ bv{pos_dict[WeakNext(formula)]} {dim}))))\n\n"
        
        if isinstance(formula, Finally):
            temp_constraints += f"    (=> (in-set q (_ bv{form_idx} {dim})) (or (in-set q (_ bv{pos_dict[formula.arg]} {dim})) (in-set q (_ bv{pos_dict[Next(formula)]} {dim}))))\n\n"

        if isinstance(formula, Last):
            temp_constraints += f"""    (=> (in-set q (_ bv{form_idx} {dim}))\n      (and\n"""

            for next_idx in next_form_dict.keys():
                temp_constraints += f"        (not (in-set q (_ bv{next_idx} {dim})))\n"

            for until_idx, until_form in until_form_dict.items():
                temp_constraints += f"        (=> (in-set q (_ bv{until_idx} {dim})) (in-set q (_ bv{pos_dict[until_form.right]} {dim})))\n"
            
            temp_constraints += f"      ))\n\n"

    loc += prop_constraints + temp_constraints + "  ))\n\n"
    return loc

def getTrans(pos_dict, dim):
    trans = f"""(define-fun Trans ((q (_ BitVec {dim})) (q_prime (_ BitVec {dim}))) Bool\n  (and\n"""
    
    trans += f"    (not (in-set q (_ bv{pos_dict[Last()]} {dim})))\n\n"
    
    # Process temporal operators with similar patterns together
    until_constraints = ""
    release_constraints = ""
    next_constraints = ""

    for formula, form_idx in pos_dict.items():
        if isinstance(formula, Until):
            until_constraints += f"    (=> (in-set q (_ bv{form_idx} {dim})) (or (in-set q (_ bv{pos_dict[formula.right]} {dim})) (in-set q_prime (_ bv{form_idx} {dim}))))\n\n"
        
        if isinstance(formula, Release):
            release_constraints += f"    (=> (in-set q (_ bv{form_idx} {dim})) (or (in-set q (_ bv{pos_dict[formula.left]} {dim})) (in-set q_prime (_ bv{form_idx} {dim}))))\n\n"
        
        if isinstance(formula, Next):
            next_constraints += f"    (=> (in-set q (_ bv{form_idx} {dim})) (and (in-set q_prime (_ bv{pos_dict[formula.arg]} {dim})) (not (in-set q_prime (_ bv{pos_dict[Last()]} {dim})))))\n\n"
        
        if isinstance(formula, WeakNext):
            next_constraints += f"    (=> (in-set q (_ bv{form_idx} {dim})) (or (in-set q_prime (_ bv{pos_dict[formula.arg]} {dim})) (in-set q_prime (_ bv{pos_dict[Last()]} {dim}))))\n\n"

    trans += until_constraints + release_constraints + next_constraints + "  ))\n\n"
    return trans
        
def getBody(formula_index, last_index, dim):
    first_chc = f"""(assert\n  (forall ((q (_ BitVec {dim})))\n    (=> (and (Loc q) (in-set q (_ bv{formula_index} {dim})))\n        (R q))))\n\n"""
    
    second_chc = f"""(assert\n  (forall ((q (_ BitVec {dim})) (q_prime (_ BitVec {dim})))\n    (=> (and (R q) (Loc q_prime) (Trans q q_prime))\n        (R q_prime))))\n\n"""

    third_chc = f"""(assert\n  (forall ((q (_ BitVec {dim})))\n    (=> (and (R q) (in-set q (_ bv{last_index} {dim})))\n        false)))\n\n"""
    
    return first_chc + second_chc + third_chc + "(check-sat)"
    #return first_chc + second_chc + third_chc + f"(declare-const witness_q (_ BitVec {dim}))\n(assert (R witness_q))\n(check-sat)\n(get-model)"