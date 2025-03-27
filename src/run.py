import os
import argparse

from parser import parse_and_convert_black_formula
from automaton_to_chcs import generate_chcs_from_automata
from ltl_to_chcs import generate_chcs_from_ltl
from cli import launch
from utils import strtobool

def main():
    argparser = argparse.ArgumentParser(description="Read a formula from a file and process it.")
    argparser.add_argument("--file", type=str, default="./input/LIA1.ltlmt", help="The name of the file containing the formula.")
    argparser.add_argument("--N", type=str, default="10", help="The value of parameter N.")
    argparser.add_argument("--automata", type=strtobool, default=False, help="Choose between the automata-based method (true) and the direct translation method (false).")
    args = argparser.parse_args()

    input_file = args.file
    basename = os.path.basename(input_file)

    curr_dir = os.getcwd()
    output_dir = os.path.relpath("output")

    ltl_file = os.path.join(output_dir, basename.replace(".ltlmt", ".ltl"))
    automaton_file = os.path.join(output_dir, basename.replace(".ltlmt", ".automaton"))
    chcs_file = os.path.join(output_dir, basename.replace(".ltlmt", ".chcs"))

    with open(args.file, 'r') as file:
        formula_str = file.read().strip()

    formula_str = formula_str.replace("N", args.N)

    print("Parsing formula...")
    formula = parse_and_convert_black_formula(formula_str, put_alive=True)
    
    with open(ltl_file, 'w') as file:
        file.write(formula.to_string())

    if args.automata:
        print("Converting formula to automaton...")    
        cli = f"ltl2tgba -B -F {ltl_file} | autfilt --to-finite > {automaton_file}"
        launch(cli, cwd=curr_dir)

        with open(automaton_file, 'r') as file:
            automaton_str = file.read().strip()

        print("Converting automaton to CHCs...")
        chcs_str = generate_chcs_from_automata(automaton_str)
    else:
        print("Converting formula to CHCs...")
        chcs_str = generate_chcs_from_ltl(formula)
    
    with open(chcs_file, 'w') as file:
        file.write(chcs_str)
    
    print("Running Z3 solver...")    
    cli = f"z3 {chcs_file}"
    result = launch(cli, cwd=curr_dir, capture_output=True)

    if result == "unsat":
        print("CHC system is unsatisfiable.")
        print("LTLMT formula is satisfiable.")
    else:
        print("CHC system is satisfiable.")
        print("LTLMT formula is unsatisfiable.")


if __name__ == "__main__":
    main()
