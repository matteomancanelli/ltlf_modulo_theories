#!/bin/bash

# Load the library path for Black Python bindings
LIB_PATH="submodules/black/build/src/lib"
LIB_DIR_ABS=$(cd "$LIB_PATH" 2>/dev/null && pwd)
if [ -n "$LIB_DIR_ABS" ]; then
    export LD_LIBRARY_PATH="$LIB_DIR_ABS:$LD_LIBRARY_PATH"
else
    echo "Warning: Could not find Black library directory. If import errors occur, run setup.sh first."
fi

# Parameters
input_file="$1"
param_N="$2"

# Check if input file is provided
if [ -z "$input_file" ]; then
    echo "Usage: $0 <input_file> [param_N]"
    exit 1
fi


mkdir -p output
base_name=$(basename "${input_file%.ltlmt}")

parsed_file="./output/${base_name}.ltl"
automaton_file="./output/${base_name}.automaton"
chcs_file="./output/${base_name}.chcs"

echo "Parsing formula..."
python ./src/parse_formula.py "$input_file" "$param_N"

echo "Converting to automaton..."
ltl2tgba -B -F "$parsed_file" | autfilt --to-finite > "$automaton_file"

echo "Converting automaton to CHCs..."
python ./src/automaton_to_chcs.py "$automaton_file"

echo "Running Z3 solver..."
result=$(z3 "$chcs_file")
if [[ "$result" == "sat" ]]; then
    echo "Result: unsat"
elif [[ "$result" == "unsat" ]]; then
    echo "Result: sat"
else
    echo "Unknown result: $result"
fi