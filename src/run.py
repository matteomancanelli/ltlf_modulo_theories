import os
import argparse
import time

from parser import parse_and_convert_black_formula
from automaton_to_chcs import generate_chcs_from_automata
from ltlf_to_chcs import generate_chcs_from_ltl
from ltlmt_to_chcs import generate_chcs_from_ltlmt
from cli import launch
from utils import *

def main():
    argparser = argparse.ArgumentParser(description="Read a formula from a file and process it.")
    argparser.add_argument("--file", type=str, default="./input/LIA1.ltlmt", help="The name of the file containing the formula.")
    argparser.add_argument("--method", type=str, default="symbolic", help="Choose among 'automata' and 'symbolic'.")
    args = argparser.parse_args()

    input_file = args.file
    basename = os.path.basename(input_file)

    curr_dir = os.getcwd()
    output_dir = os.path.relpath("output")
    os.makedirs(output_dir, exist_ok=True)

    ltlf_file = os.path.join(output_dir, basename.replace(".ltlmt", ".ltlf"))
    automaton_file = os.path.join(output_dir, basename.replace(".ltlmt", ".automaton"))
    chcs_file = os.path.join(output_dir, basename.replace(".ltlmt", ".chcs"))
    
    formula_str, type_dict = read_formula(args.file)

    start = time.time()

    print("Parsing formula...")
    formula = parse_and_convert_black_formula(formula_str)
    formula = discard_wnext(formula)

    if args.method == "automata":
        print("Converting formula to automaton...")    
        cli = f"ltlfilt --from-ltlf -f '{formula.to_string()}' | ltl2tgba -B | autfilt --to-finite > {automaton_file}"
        launch(cli, cwd=curr_dir)

        with open(automaton_file, 'r') as file:
            automaton_str = file.read().strip()

        print("Converting automaton to CHCs...")
        chcs_str = generate_chcs_from_automata(automaton_str, type_dict)

        if chcs_str == "unsat":
            print("LTLMT formula is unsatisfiable.")
            return
        
    elif args.method == "ltlf":
        print("Converting LTLMT formula to LTLf...")
        formula, _ = ltlmt_to_ltlf(formula)
        
        formula = to_nnf(formula)
        formula = simplify(formula)

        with open(ltlf_file, 'w') as file:
            file.write(formula.to_string())

        print("Converting formula to CHCs...")
        chcs_str = generate_chcs_from_ltl(formula)
    elif args.method == "symbolic":
        formula = to_nnf(formula)
        formula = simplify(formula)

        print("Converting LTLMT formula to CHCs...")
        chcs_str = generate_chcs_from_ltlmt(formula, type_dict)
    else:
        raise Exception(f"Unknown method: {args.method}")
    
    with open(chcs_file, 'w') as file:
        file.write(chcs_str)
    

    print("Running Z3 solver...")    
    cli = f"z3 -T:600 {chcs_file}"
    result = launch(cli, cwd=curr_dir, capture_output=True)

    if result == "unsat":
        print("CHC system is unsatisfiable.")
        print("LTLMT formula is satisfiable.")
    elif result == "sat": 
        print("CHC system is satisfiable.")
        print("LTLMT formula is unsatisfiable.")
    else:
        print("Unexpected result from Z3 solver.")
        print("Result:\n", result)
    
    end = time.time()
    print("Time taken: {:.2f} seconds.".format(end - start))


if __name__ == "__main__":
    main()
