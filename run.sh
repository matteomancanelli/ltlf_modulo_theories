#!/bin/bash

# Parameters
input_file="$1"
param_N="$2"

parsed_file="${input_file%.ltlmt}.ltl"
automaton_file="${input_file%.ltlmt}.automaton"
chcs_file="${input_file%.ltlmt}.chcs"

python parse_formula.py "$input_file" "$param_N"
ltl2tgba -B -F "$parsed_file" | autfilt --to-finite > "$automaton_file"
python automaton_to_chcs.py "$automaton_file"

result=$(z3 "$chcs_file")
if [[ "$result" == "sat" ]]; then
    echo "unsat"
elif [[ "$result" == "unsat" ]]; then
    echo "sat"
else
    echo "Unknown result: $result"
fi