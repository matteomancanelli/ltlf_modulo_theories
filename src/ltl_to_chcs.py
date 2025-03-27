def generate_chcs_from_ltl(automaton_str):
    return 


def generate_loc_constraint(closure):
    """Generate the Local consistency constraint for a formula based on its closure."""
    constraints = []
    
    # For negated atomic propositions
    for formula in closure:
        if isinstance(formula, Negation) and isinstance(formula.arg, Atom):
            constraints.append(f"(=> (member {formula} q) (not (member {formula.arg} q)))")
    
    # For conjunctions
    for formula in closure:
        if isinstance(formula, Conjunction):
            constraints.append(f"(=> (member {formula} q) (and (member {formula.left} q) (member {formula.right} q)))")
    
    # For disjunctions
    for formula in closure:
        if isinstance(formula, Disjunction):
            constraints.append(f"(=> (member {formula} q) (or (member {formula.left} q) (member {formula.right} q)))")
    
    # For Until formulas
    for formula in closure:
        if isinstance(formula, Until):
            constraints.append(f"(=> (member {formula} q) (or (member {formula.right} q) (and (member {formula.left} q) (member (X {formula}) q))))")
    
    # For Release formulas
    for formula in closure:
        if isinstance(formula, Release):
            constraints.append(f"(=> (member {formula} q) (and (member {formula.right} q) (or (member {formula.left} q) (member (WX {formula}) q))))")
    
    # Last implies
    last_implies = []
    
    # No Next formulas in the last position
    next_formulas = [f for f in closure if isinstance(f, Next)]
    if next_formulas:
        next_constraint = "(= (filter (lambda (x) (is-next x)) q) (as emptyset (Set Formula)))"
        last_implies.append(next_constraint)
    
    # Until formulas in the last position
    for formula in closure:
        if isinstance(formula, Until):
            last_implies.append(f"(member {formula.right} q)")
    
    if last_implies:
        constraints.append(f"(=> (member last q) (and {' '.join(last_implies)}))")
    
    return "(and " + " ".join(constraints) + ")"

def generate_trans_constraint(closure):
    """Generate the Transition consistency constraint for a formula based on its closure."""
    constraints = ["(not (member last q))"]
    
    # For Next formulas
    for formula in closure:
        if isinstance(formula, Next):
            constraints.append(f"(=> (member {formula} q) (member {formula.arg} q'))")
    
    # For Weak Next formulas
    for formula in closure:
        if isinstance(formula, WeakNext):
            constraints.append(f"(=> (member {formula} q) (or (member last q) (member {formula.arg} q')))")
    
    return "(and " + " ".join(constraints) + ")"

def generate_chc_system(formula):
    """Generate the CHC system for a formula."""
    # First, convert to NNF
    nnf_formula = to_nnf(formula)
    
    # Then, compute the closure
    closure = nnf_formula.get_closure()
    
    # Define Formula datatype
    chcs = []
    chcs.append(";; Formula datatype\n(declare-datatypes () ((Formula")
    for sf in sorted(closure, key=str):
        sf_str = str(sf).replace("&", "and").replace("|", "or")
        chcs.append(f"  ({sf_str})")
    chcs.append(")))\n")
    
    # Define the set type for Formula
    chcs.append("(define-sort FormulaSet () (Set Formula))\n")
    
    # Define the uninterpreted predicate R
    chcs.append("(declare-fun R (FormulaSet) Bool)\n")
    
    # Define functions to check if a formula is a specific type
    chcs.append("(define-fun is-next ((f Formula)) Bool")
    chcs.append("  (match f")
    for sf in closure:
        if isinstance(sf, Next):
            chcs.append(f"    (({sf}) true)")
    chcs.append("    (_ false)))\n")
    
    # Define the Loc function
    loc_constraint = generate_loc_constraint(closure)
    chcs.append(f"(define-fun Loc ((q FormulaSet)) Bool\n  {loc_constraint})\n")
    
    # Define the Trans function
    trans_constraint = generate_trans_constraint(closure)
    chcs.append(f"(define-fun Trans ((q FormulaSet) (q' FormulaSet)) Bool\n  {trans_constraint})\n")
    
    # Add the CHC rules
    chcs.append(";; CHC rules")
    chcs.append(f"(assert (forall ((q FormulaSet)) (=> (and (Loc q) (member {formula} q)) (R q))))")
    chcs.append(f"(assert (forall ((q FormulaSet) (q' FormulaSet)) (=> (and (R q) (Loc q') (Trans q q')) (R q'))))")
    chcs.append(f"(assert (forall ((q FormulaSet)) (=> (and (R q) (member last q)) false)))")
    
    # Add the check-sat command
    chcs.append("(check-sat)")
    
    return "\n".join(chcs)

