import argparse
import black_sat

def expand(formula):
    if isinstance(formula, black_sat.negation):
        return '!(' + expand(formula.argument) + ')'
    elif isinstance(formula, black_sat.tomorrow):
        return 'X(alive & ' + expand(formula.argument) + ')'
    elif isinstance(formula, black_sat.w_tomorrow):
        return 'X(!alive | ' + expand(formula.argument) + ')'
    elif isinstance(formula, black_sat.always):
        return 'G(!alive | ' + expand(formula.argument) + ')'
    elif isinstance(formula, black_sat.eventually):
        return 'F(alive & ' + expand(formula.argument) + ')'
    elif isinstance(formula, black_sat.conjunction):
        return '(' + expand(formula.left) + ' & ' + expand(formula.right) + ')'
    elif isinstance(formula, black_sat.disjunction):
        return '(' + expand(formula.left) + ' | ' + expand(formula.right) + ')'
    elif isinstance(formula, black_sat.implication):
        return '(' + expand(formula.left) + ' -> ' + expand(formula.right) + ')'
    elif isinstance(formula, black_sat.iff):
        return '(' + expand(formula.left) + ' <-> ' + expand(formula.right) + ')'
    elif isinstance(formula, black_sat.until):
        return '((alive & ' + expand(formula.left) + ') U (alive & ' + expand(formula.right) + '))'
    elif isinstance(formula, black_sat.w_until):
        return '((alive & ' + expand(formula.left) + ') U (alive & ' + expand(formula.right) + ')) | G(!alive | ' + expand(formula.left) + '))'
    else:
        return '"' + str(formula) + '"'

def preprocess(formula):
    return 'alive & ' + expand(formula) + ' & (alive U (G !alive))'

def main():
    parser = argparse.ArgumentParser(description="Read a formula from a file and process it.")
    parser.add_argument("filename", type=str, help="The name of the file containing the formula.")
    parser.add_argument("param_N", type=str, help="The value of parameter N.")
    args = parser.parse_args()

    # Read the formula from the file
    try:
        with open(args.filename, 'r') as file:
            formula_str = file.read().strip()
    except FileNotFoundError:
        print(f"Error: File '{args.filename}' not found.")
        return
    
    # Instantiate N
    formula_str = formula_str.replace("N", args.param_N)

    # Parse the formula using black_sat
    alphabet = black_sat.alphabet()
    try:
        formula = black_sat.parse_formula(alphabet, formula_str)
    except Exception as e:
        print(f"Error parsing formula: {e}")
        return
    
    formula = preprocess(formula)
    with open(args.filename.replace(".ltlmt", ".ltl"), 'w') as file:
        file.write(formula)
    
if __name__ == "__main__":
    main()
