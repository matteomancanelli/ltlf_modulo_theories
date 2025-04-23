import argparse
import time
from pathlib import Path

from parser import parse_and_convert_black_formula
from automaton_to_chcs import generate_chcs_from_automata
from ltlf_to_chcs import generate_chcs_from_ltl
from ltlmt_to_chcs import generate_chcs_from_ltlmt
from cli import launch
from utils import *

def main():
    argparser = argparse.ArgumentParser(description="Read a formula from a file and process it.")
    argparser.add_argument("--file", type=str, default="./input/LIA1-10.ltlmt", help="The name of the file containing the formula.")
    argparser.add_argument("--method", type=str, default="symbolic", help="Choose among 'automata' and 'symbolic'.")
    args = argparser.parse_args()

    # Base paths
    project_root = Path(__file__).resolve().parent.parent
    input_path = Path(args.file)
    if not input_path.is_absolute():
        input_path = project_root / input_path

    output_dir = project_root / "output"
    output_dir.mkdir(exist_ok=True)

    basename = input_path.stem  # name without extension
    ltlf_file = output_dir / f"{basename}.ltlf"
    automaton_file = output_dir / f"{basename}.automaton"
    chcs_file = output_dir / f"{basename}.chcs"

    formula_str, type_dict = read_formula(str(input_path))

    start = time.time()

    print("Parsing formula...")
    formula = parse_and_convert_black_formula(formula_str)
    formula = discard_wnext(formula)

    if args.method == "automata":
        print("Converting formula to automaton...")    
        cli = f"ltlfilt --from-ltlf -f '{formula.to_string()}' | ltl2tgba -B | autfilt --to-finite > {automaton_file}"
        launch(cli, cwd=str(project_root))

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
    result = launch(cli, cwd=str(project_root), capture_output=True)

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
