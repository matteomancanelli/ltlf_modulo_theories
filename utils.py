import re
from collections import Counter

def infix_to_prefix(expression):
    # Operator precedence and associativity
    precedence = {'+': 1, '-': 1, '*': 2, '/': 2, '<': 0, '<=': 0, '>': 0, '>=': 0, '=': 0}
    operators = precedence.keys()
    
    # Function to handle precedence and associativity
    def precedence_of(op):
        return precedence[op]

    # Helper function to process operators
    def process_operator(op_stack, out_stack):
        operator = op_stack.pop()
        right = out_stack.pop()
        left = out_stack.pop()
        out_stack.append(f"({operator} {left} {right})")

    op_stack = []   # Operator stack
    out_stack = []  # Output stack

    # Tokenize the expression (separate operators, parentheses, and operands)
    tokens = re.findall(r'next\([^)]+\)|wnext\([^)]+\)|[+\-*/<>=()]+|\w+', expression)
    #tokens = re.findall(r'[+\-*/<>=()]+|\w+', expression)
    for token in tokens:
        token = token.strip()
        if re.match(r'next\([^)]+\)|wnext\([^)]+\)|\w+', token):  # Operand (variable, number, etc.)
        #if token.isalnum():  # Operand (variable, number, etc.)
            out_stack.append(token)
        elif token in operators:  # Operator
            while (op_stack and op_stack[-1] != '(' and precedence_of(op_stack[-1]) >= precedence_of(token)):
                process_operator(op_stack, out_stack)
            op_stack.append(token)
        elif token == '(':
            op_stack.append(token)
        elif token == ')':
            while op_stack and op_stack[-1] != '(':
                process_operator(op_stack, out_stack)
            op_stack.pop()  # Pop the '(' from the stack

    # Process remaining operators
    while op_stack:
        process_operator(op_stack, out_stack)

    return out_stack[-1]

def transform(prop):
    def rename_variable(var):
        match = re.match(r"(?:next|wnext)\(([^)]+)\)", var)

        if match:
            base_var = match.group(1)

            if f"next({base_var})" not in var_map:
                if f"base({base_var})" not in var_map:
                    var_map[f"next({base_var})"] = f"({base_var}1 reg)"
                else:
                    var_map[f"next({base_var})"] = f"({base_var}2 reg)"
            
            return var_map[f"next({base_var})"]
        else:
            base_var = var

            if f"base({base_var})" not in var_map:
                if f"next({base_var})" not in var_map:
                    var_map[f"base({base_var})"] = f"({base_var}1 reg)"
                else:
                    var_map[f"base({base_var})"] = f"({base_var}2 reg)"
            
            return var_map[f"base({base_var})"]

    var_map = {}
    pattern = r'next\([^)]+\)|wnext\([^)]+\)|[a-zA-Z][a-zA-Z0-9]*'
    matches = re.finditer(pattern, prop)

    offset = 0
    for match in matches:
        start = match.start() + offset
        end = match.end() + offset
        replacement = rename_variable(match.group(0))
        prop = prop[:start] + replacement + prop[end:]
        offset += len(replacement) - (end - start)

    vars = set([re.match(r"\(([^ ]+) reg\)", elem).group(1) for elem in var_map.values()])
    return prop, vars

def get_multiple_suffix_variables(vars):
    # Counter to store occurrences of base variables
    base_counts = Counter(re.match(r"([a-zA-Z]+)\d*", var).group(1) for var in vars)
    
    # Return variables with more than one occurrence
    return {base for base, count in base_counts.items() if count > 1}