from formula import *
from utils import *

def generate_chcs_from_ltl(formula):
    formula = to_nnf(formula)
    closure = list(formula.get_closure())
    pos_dict = {subformula: idx for idx, subformula in enumerate(closure)}

    print(f"Position dictionary: {pos_dict}")

    formula_index = pos_dict[formula]
    last_index = pos_dict[Last()]

    header = getHeader(pos_dict)
    body = getBody(formula_index, last_index, pos_dict)

    return header + body

def getHeader(pos_dict):
    header = "(set-logic HORN)\n\n"

    dim = len(pos_dict)
    
    # Declare boolean state variables
    for i in range(dim):
        header += f"(declare-fun f{i} () Bool)\n"
    header += "\n"

    header += "(declare-fun R (" + " ".join(["Bool"] * dim) + ") Bool)\n\n"

    header += getLoc(pos_dict)
    header += getTrans(pos_dict)
    return header

def getLoc(pos_dict):
    dim = len(pos_dict)
    args = " ".join([f"(f{i} Bool)" for i in range(dim)])
    loc = f"(define-fun Loc ({args}) Bool\n  (and\n"

    for formula, idx in pos_dict.items():
        if isinstance(formula, Negation):
            arg_idx = pos_dict[formula.arg]
            loc += f"    (=> f{idx} (not f{arg_idx}))\n"

        if isinstance(formula, Conjunction):
            left_idx = pos_dict[formula.left]
            right_idx = pos_dict[formula.right]
            loc += f"    (=> f{idx} (and f{left_idx} f{right_idx}))\n"

        if isinstance(formula, Disjunction):
            left_idx = pos_dict[formula.left]
            right_idx = pos_dict[formula.right]
            loc += f"    (=> f{idx} (or f{left_idx} f{right_idx}))\n"

        if isinstance(formula, Until):
            left_idx = pos_dict[formula.left]
            right_idx = pos_dict[formula.right]
            loc += f"    (=> f{idx} (or f{left_idx} f{right_idx}))\n"

        if isinstance(formula, Release):
            right_idx = pos_dict[formula.right]
            loc += f"    (=> f{idx} f{right_idx})\n"

        if isinstance(formula, Globally):
            arg_idx = pos_dict[formula.arg]
            wx_idx = pos_dict[WeakNext(formula)]
            loc += f"    (=> f{idx} (and f{arg_idx} f{wx_idx}))\n"

        if isinstance(formula, Finally):
            arg_idx = pos_dict[formula.arg]
            x_idx = pos_dict[Next(formula)]
            loc += f"    (=> f{idx} (or f{arg_idx} f{x_idx}))\n"

        if isinstance(formula, Last):
            loc += f"    (=> f{idx} \n      (and\n"
            for f2, j in pos_dict.items():
                if isinstance(f2, Next):
                    loc += f"        (not f{j})\n"
            for f2, j in pos_dict.items():
                if isinstance(f2, Until):
                    right_idx = pos_dict[f2.right]
                    loc += f"        (=> f{j} f{right_idx})\n"
            loc += f"      ))\n"

    loc += "  ))\n\n"
    return loc

def getTrans(pos_dict):
    dim = len(pos_dict)
    args = " ".join([f"(f{i} Bool)" for i in range(dim)])
    args_p = " ".join([f"(f{i}_p Bool)" for i in range(dim)])

    trans = f"(define-fun Trans ({args} {args_p}) Bool\n  (and\n"

    trans += f"    (not f{pos_dict[Last()]})\n"

    for formula, idx in pos_dict.items():
        if isinstance(formula, Until):
            right_idx = pos_dict[formula.right]
            trans += f"    (=> f{idx} (or f{right_idx} f{idx}_p))\n"

        if isinstance(formula, Release):
            left_idx = pos_dict[formula.left]
            trans += f"    (=> f{idx} (or f{left_idx} f{idx}_p))\n"

        if isinstance(formula, Next):
            arg_idx = pos_dict[formula.arg]
            trans += f"    (=> f{idx} (and f{arg_idx}_p (not f{pos_dict[Last()]}_p)))\n"

        if isinstance(formula, WeakNext):
            arg_idx = pos_dict[formula.arg]
            trans += f"    (=> f{idx} (or f{arg_idx}_p f{pos_dict[Last()]}_p))\n"

    trans += "  ))\n\n"
    return trans

def getBody(formula_index, last_index, pos_dict):
    dim = len(pos_dict)
    args = " ".join([f"(f{i} Bool)" for i in range(dim)])
    args_p = " ".join([f"(f{i}_p Bool)" for i in range(dim)])

    vars = " ".join([f"f{i}" for i in range(dim)])
    vars_p = " ".join([f"f{i}_p" for i in range(dim)])

    first_chc = f"""(assert
  (forall ({args})
    (=> (and (Loc {vars}) f{formula_index})
        (R {vars}))))\n\n"""

    second_chc = f"""(assert
  (forall ({args} {args_p})
    (=> (and (R {vars})
             (Loc {vars_p})
             (Trans {vars} {vars_p}))
        (R {vars_p}))))\n\n"""

    third_chc = f"""(assert
  (forall ({args})
    (=> (and (R {vars}) f{last_index})
        false)))\n\n"""

    return first_chc + second_chc + third_chc + "(check-sat)\n"
