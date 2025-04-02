from formula import *
from utils import *

def generate_chcs_from_ltlmt(formula, type_dict):
    closure = list(formula.get_closure())
    pos_dict = {subformula: idx for idx, subformula in enumerate(closure)}
    dim = len(pos_dict)

    formula_index = pos_dict[formula]
    last_index = pos_dict[Last()]

    header = getHeader(pos_dict, type_dict)
    body = getBody(formula_index, last_index, dim)

    return header + body

def getHeader(pos_dict, type_dict):
    header = "(set-logic HORN)\n\n"

    vars = set()
    expr_map = {}
    for formula in pos_dict:
        if isinstance(formula, Atom) and not isinstance(formula, Last):
            prefix = infix_to_prefix(formula.name)
            smt_expr, used_vars = transform(prefix)
            expr_map[formula] = smt_expr
            vars.update(used_vars)

    decl_datatypes_str = "(declare-datatypes () ((Registers (mk-state\n"
    for var in vars:
        base_var = var.rsplit('_', 1)[0]
        decl_datatypes_str += f"   ({var} {type_dict[base_var]})\n"
    decl_datatypes_str += "))))\n\n"

    duplicates = get_multiple_suffix_variables(vars)
    data_buffer_str = "(define-fun buff_upd ((reg Registers) (regN Registers)) Bool\n(and \n"
    if duplicates:
        for var in duplicates:
            data_buffer_str += f"   (= ({var}_2 regN) ({var}_1 reg))\n"
    else:
        data_buffer_str += f"true\n"
    data_buffer_str += "))\n\n"

    header += decl_datatypes_str + data_buffer_str

    # Declare propositional state variables as Booleans
    for i in range(len(pos_dict)):
        header += f"(declare-fun f{i} () Bool)\n"
    header += "\n"

    header += "(declare-fun R (Registers " + " ".join(["Bool"] * len(pos_dict)) + ") Bool)\n\n"

    header += getLoc(pos_dict, expr_map)
    header += getTrans(pos_dict)
    return header

def getLoc(pos_dict, expr_map):
    loc = "(define-fun Loc ((reg Registers) " + " ".join([f"(f{i} Bool)" for i in range(len(pos_dict))]) + ") Bool\n  (and\n"

    for formula, idx in pos_dict.items():
        if isinstance(formula, Atom) and not isinstance(formula, Last):
            smt_expr = expr_map[formula]
            loc += f"    (=> f{idx} {smt_expr})\n"

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
    trans = "(define-fun Trans ((reg Registers) (regN Registers) " + \
             " ".join([f"(f{i} Bool)" for i in range(len(pos_dict))]) + " " + \
             " ".join([f"(f{i}_p Bool)" for i in range(len(pos_dict))]) + ") Bool\n  (and\n"

    trans += f"    (buff_upd reg regN)\n"
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

def getBody(formula_index, last_index, dim):
    args = " ".join([f"(f{i} Bool)" for i in range(dim)])
    args_p = " ".join([f"(f{i}_p Bool)" for i in range(dim)])

    vars = " ".join([f"f{i}" for i in range(dim)])
    vars_p = " ".join([f"f{i}_p" for i in range(dim)])

    first_chc = f"""(assert
  (forall ((reg Registers) {args})
    (=> (and (Loc reg {vars}) f{formula_index})
        (R reg {vars}))))\n\n"""

    second_chc = f"""(assert
  (forall ((reg Registers) (regN Registers) {args} {args_p})
    (=> (and (R reg {vars})
             (Loc regN {vars_p})
             (Trans reg regN {vars} {vars_p}))
        (R regN {vars_p}))))\n\n"""

    third_chc = f"""(assert
  (forall ((reg Registers) {args})
    (=> (and (R reg {vars}) f{last_index})
        false)))\n\n"""

    return first_chc + second_chc + third_chc + "(check-sat)\n"
