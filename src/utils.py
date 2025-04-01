import re
from collections import Counter

from formula import *

def to_nnf(formula):
    """Convert a formula to Negation Normal Form."""
    if isinstance(formula, Atom):
        return formula
    
    if isinstance(formula, Negation):
        if isinstance(formula.arg, Negation):
            return to_nnf(formula.arg.arg)
        
        if isinstance(formula.arg, Atom):
            return formula
        
        if isinstance(formula.arg, Conjunction):
            return Disjunction(to_nnf(Negation(formula.arg.left)), to_nnf(Negation(formula.arg.right)))
        
        if isinstance(formula.arg, Disjunction):
            return Conjunction(to_nnf(Negation(formula.arg.left)), to_nnf(Negation(formula.arg.right)))
        
        if isinstance(formula.arg, Next):
            if isinstance(formula.arg.arg, TrueFormula):
                return Last()
            
            return Disjunction(Last(), Next(to_nnf(Negation(formula.arg.arg))))
        
        if isinstance(formula.arg, WeakNext):
            return Next(to_nnf(Negation(formula.arg.arg)))
        
        if isinstance(formula.arg, Until):
            return Release(to_nnf(Negation(formula.arg.right)), to_nnf(Negation(formula.arg.left)))
        
        if isinstance(formula.arg, Release):
            return Until(to_nnf(Negation(formula.arg.left)), to_nnf(Negation(formula.arg.right)))
        
        if isinstance(formula.arg, Finally):
            return Globally(to_nnf(Negation(formula.arg.arg)))
        
        if isinstance(formula.arg, Globally):
            return Finally(to_nnf(Negation(formula.arg.arg)))
    
    if isinstance(formula, Conjunction):
        return Conjunction(to_nnf(formula.left), to_nnf(formula.right))
    
    if isinstance(formula, Disjunction):
        return Disjunction(to_nnf(formula.left), to_nnf(formula.right))
    
    if isinstance(formula, Next):
        return Next(to_nnf(formula.arg))
    
    if isinstance(formula, WeakNext):
        return WeakNext(to_nnf(formula.arg))
    
    if isinstance(formula, Until):
        return Until(to_nnf(formula.left), to_nnf(formula.right))
    
    if isinstance(formula, Release):
        return Release(to_nnf(formula.left), to_nnf(formula.right))
    
    if isinstance(formula, Finally):
        return Finally(to_nnf(formula.arg))
    
    if isinstance(formula, Globally):
        return Globally(to_nnf(formula.arg))
    
    raise ValueError(f"Unknown formula type: {type(formula)}")

def to_xnf(formula):
    """Convert formula to next normal form (to_xnf)."""
    # Base cases
    if isinstance(formula, Atom):
        return formula
    
    if isinstance(formula, Next) or isinstance(formula, WeakNext):
        return formula
    
    if isinstance(formula, Negation):
        return Negation(to_xnf(formula.arg))
    
    if isinstance(formula, Conjunction):
        return Conjunction(to_xnf(formula.left), to_xnf(formula.right))
    
    if isinstance(formula, Disjunction):
        return Disjunction(to_xnf(formula.left), to_xnf(formula.right))
    
    if isinstance(formula, Finally):
        return Disjunction(to_xnf(formula.arg), Next(formula))
    
    if isinstance(formula, Globally):
        return Conjunction(to_xnf(formula.arg), WeakNext(formula))
    
    if isinstance(formula, Until):
        return Disjunction(to_xnf(formula.right), Conjunction(to_xnf(formula.left), Next(formula)))
    
    if isinstance(formula, Release):
        return Conjunction(to_xnf(formula.right), Disjunction(to_xnf(formula.left), WeakNext(formula)))
    
    raise ValueError(f"Unknown formula type: {type(formula)}")


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
                    var_map[f"next({base_var})"] = f"({base_var}_1 reg)"
                else:
                    var_map[f"next({base_var})"] = f"({base_var}_2 reg)"
            
            return var_map[f"next({base_var})"]
        else:
            base_var = var

            if f"base({base_var})" not in var_map:
                if f"next({base_var})" not in var_map:
                    var_map[f"base({base_var})"] = f"({base_var}_1 reg)"
                else:
                    var_map[f"base({base_var})"] = f"({base_var}_2 reg)"
            
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
    base_counts = Counter(re.match(r"([a-zA-Z0-9]+)\d*", var).group(1) for var in vars)
    
    # Return variables with more than one occurrence
    return {base for base, count in base_counts.items() if count > 1}


def strtobool(val):
    """Convert a string representation of truth to true (1) or false (0).
    True values are 'y', 'yes', 't', 'true', 'on', and '1'; false values
    are 'n', 'no', 'f', 'false', 'off', and '0'.  Raises ValueError if
    'val' is anything else.
    """
    if isinstance(val, bool):
        return val
    
    val = val.lower()
    if val in ('y', 'yes', 't', 'true', 'on', '1'):
        return True
    elif val in ('n', 'no', 'f', 'false', 'off', '0'):
        return False
    else:
        raise ValueError("invalid truth value %r" % (val,))


def discard_wnext(formula):
    if isinstance(formula, Atom):
        if "wnext" not in formula.name:
            return formula
            
        a = max_nested_next(formula.name, constructor="wnext")
        b = max_nested_next(formula.name, constructor="next")

        left = Atom(formula.name.replace("wnext", "next"))
        right = Negation(create_nested_tomorrow(TrueFormula(), a))
        disjunction = Disjunction(left, right)

        if b == 0:
            return disjunction
        else:
            right = create_nested_tomorrow(TrueFormula(), b)
            return Conjunction(disjunction, right)
    
    if isinstance(formula, Negation):
        return Negation(discard_wnext(formula.arg))
    
    if isinstance(formula, Conjunction):
        return Conjunction(discard_wnext(formula.left), discard_wnext(formula.right))
    
    if isinstance(formula, Disjunction):
        return Disjunction(discard_wnext(formula.left), discard_wnext(formula.right))
    
    if isinstance(formula, Next):
        return Next(discard_wnext(formula.arg))
    
    if isinstance(formula, WeakNext):
        return WeakNext(discard_wnext(formula.arg))
    
    if isinstance(formula, Until):
        return Until(discard_wnext(formula.left), discard_wnext(formula.right))
    
    if isinstance(formula, Release):
        return Release(discard_wnext(formula.left), discard_wnext(formula.right))
    
    if isinstance(formula, Finally):
        return Finally(discard_wnext(formula.arg))
    
    if isinstance(formula, Globally):
        return Globally(discard_wnext(formula.arg))


def max_nested_next(expression, constructor="next"):
    if constructor == "next":
        pattern = re.compile(r'\b(next)\s*\(')
    elif constructor == "wnext":
        pattern = re.compile(r'\b(wnext)\s*\(')
    else:
        pattern = re.compile(r'\b(next|wnext)\s*\(')
    
    max_depth = 0
    stack = []
    i = 0

    while i < len(expression):
        match = pattern.match(expression, i)
        if match:
            stack.append('next')
            max_depth = max(max_depth, len(stack))
            i = match.end()
        elif expression[i] == ')':
            if stack:
                stack.pop()
            i += 1
        else:
            i += 1

    return max_depth

def create_nested_tomorrow(formula, lookahead):
    if lookahead == 0:
        return formula
    else:
        return Next(create_nested_tomorrow(formula, lookahead - 1))


def ltlmt_to_ltlf(ltlmt, mapping={}):
    """Convert LTLf-MT formula to LTLf formula."""
    if isinstance(ltlmt, Atom):
        if ltlmt.name == "last" or ltlmt.name == "true" or ltlmt.name == "false":
            return ltlmt, mapping

        if ltlmt.name in mapping.values():
            for key, value in mapping.items():
                if value == ltlmt.name:
                    return Atom(key), mapping
        
        max_lookahead = max_nested_next(ltlmt.name)
        new_var = f"nv{len(mapping)}"
        mapping[new_var] = ltlmt.name
        return create_nested_tomorrow(Atom(new_var), max_lookahead), mapping

    if isinstance(ltlmt, Negation):
        arg, mapping = ltlmt_to_ltlf(ltlmt.arg, mapping)
        return Negation(arg), mapping
    
    if isinstance(ltlmt, Conjunction):
        left, mapping = ltlmt_to_ltlf(ltlmt.left, mapping)
        right, mapping = ltlmt_to_ltlf(ltlmt.right, mapping)
        return Conjunction(left, right), mapping
    
    if isinstance(ltlmt, Disjunction):
        left, mapping = ltlmt_to_ltlf(ltlmt.left, mapping)
        right, mapping = ltlmt_to_ltlf(ltlmt.right, mapping)
        return Disjunction(left, right), mapping
    
    if isinstance(ltlmt, Next):
        arg, mapping = ltlmt_to_ltlf(ltlmt.arg, mapping)
        return Next(arg), mapping
    
    if isinstance(ltlmt, WeakNext):
        arg, mapping = ltlmt_to_ltlf(ltlmt.arg, mapping)
        return WeakNext(arg), mapping
    
    if isinstance(ltlmt, Until):
        left, mapping = ltlmt_to_ltlf(ltlmt.left, mapping)
        right, mapping = ltlmt_to_ltlf(ltlmt.right, mapping)
        return Until(left, right), mapping
    
    if isinstance(ltlmt, Release):
        left, mapping = ltlmt_to_ltlf(ltlmt.left, mapping)
        right, mapping = ltlmt_to_ltlf(ltlmt.right, mapping)
        return Release(left, right), mapping
    
    if isinstance(ltlmt, Finally):
        arg, mapping = ltlmt_to_ltlf(ltlmt.arg, mapping)
        return Finally(arg), mapping
    
    if isinstance(ltlmt, Globally):
        arg, mapping = ltlmt_to_ltlf(ltlmt.arg, mapping)
        return Globally(arg), mapping


def simplify(formula):
    if isinstance(formula, Atom):
        return formula
    
    if isinstance(formula, Negation):
        arg_simplified = simplify(formula.arg)

        if isinstance(arg_simplified, TrueFormula):
            return FalseFormula()

        if isinstance(arg_simplified, FalseFormula):
            return TrueFormula()

        if isinstance(arg_simplified, Negation):
            return simplify(arg_simplified.arg)
        
        if isinstance(arg_simplified, Conjunction):
            return Disjunction(simplify(Negation(arg_simplified.left)), simplify(Negation(arg_simplified.right)))
        
        if isinstance(arg_simplified, Disjunction):
            return Conjunction(simplify(Negation(arg_simplified.left)), simplify(Negation(arg_simplified.right)))

        if isinstance(arg_simplified, Next) and isinstance(arg_simplified.arg, TrueFormula):
            return Last()
        
        return Negation(arg_simplified)

    if isinstance(formula, Conjunction):
        left_simplified = simplify(formula.left)
        right_simplified = simplify(formula.right)

        if isinstance(left_simplified, TrueFormula):
            return right_simplified
        if isinstance(right_simplified, TrueFormula):
            return left_simplified
        if isinstance(left_simplified, FalseFormula) or isinstance(right_simplified, FalseFormula):
            return FalseFormula()
        
        if left_simplified == right_simplified:
            return left_simplified
        if is_contradiction(left_simplified, right_simplified):
            return FalseFormula()

        return Conjunction(left_simplified, right_simplified)
    
    if isinstance(formula, Disjunction):
        left_simplified = simplify(formula.left)
        right_simplified = simplify(formula.right)

        if isinstance(left_simplified, FalseFormula):
            return right_simplified
        if isinstance(right_simplified, FalseFormula):
            return left_simplified
        if isinstance(left_simplified, TrueFormula) or isinstance(right_simplified, TrueFormula):
            return TrueFormula()
        
        if left_simplified == right_simplified:
            return left_simplified
        if is_contradiction(left_simplified, right_simplified):
            return TrueFormula()

        return Disjunction(left_simplified, right_simplified)
    
    if isinstance(formula, Next):
        arg_simplified = simplify(formula.arg)
        
        if isinstance(arg_simplified, FalseFormula):
            return FalseFormula()
            
        if isinstance(arg_simplified, TrueFormula):
            return Negation(Last())
            
        return Next(arg_simplified)
    
    if isinstance(formula, WeakNext):
        arg_simplified = simplify(formula.arg)
        
        if isinstance(arg_simplified, TrueFormula):
            return TrueFormula()
            
        if isinstance(arg_simplified, FalseFormula):
            return Last()
            
        return WeakNext(arg_simplified)
    
    if isinstance(formula, Until):
        left_simplified = simplify(formula.left)
        right_simplified = simplify(formula.right)
        
        if isinstance(left_simplified, FalseFormula):
            return right_simplified
            
        if isinstance(right_simplified, TrueFormula):
            return TrueFormula()
            
        if isinstance(left_simplified, TrueFormula):
            return Finally(right_simplified)
            
        if isinstance(right_simplified, FalseFormula):
            return FalseFormula()
            
        if left_simplified == right_simplified:
            return left_simplified
            
        return Until(left_simplified, right_simplified)
    
    if isinstance(formula, Release):
        left_simplified = simplify(formula.left)
        right_simplified = simplify(formula.right)
        
        if isinstance(left_simplified, TrueFormula):
            return right_simplified
            
        if isinstance(right_simplified, FalseFormula):
            return FalseFormula()
            
        if isinstance(left_simplified, FalseFormula):
            return Globally(right_simplified)
            
        if isinstance(right_simplified, TrueFormula):
            return TrueFormula()
            
        if left_simplified == right_simplified:
            return left_simplified
            
        return Release(left_simplified, right_simplified)
    
    if isinstance(formula, Finally):
        arg_simplified = simplify(formula.arg)
        
        if isinstance(arg_simplified, TrueFormula):
            return TrueFormula()
            
        if isinstance(arg_simplified, FalseFormula):
            return FalseFormula()
            
        if isinstance(arg_simplified, Finally):
            return arg_simplified
            
        if isinstance(arg_simplified, Disjunction):
            return Disjunction(simplify(Finally(arg_simplified.left)), simplify(Finally(arg_simplified.right)))
            
        return Finally(arg_simplified)
    
    if isinstance(formula, Globally):
        arg_simplified = simplify(formula.arg)
        
        if isinstance(arg_simplified, FalseFormula):
            return FalseFormula()
            
        if isinstance(arg_simplified, TrueFormula):
            return TrueFormula()
            
        if isinstance(arg_simplified, Globally):
            return arg_simplified
            
        if isinstance(arg_simplified, Conjunction):
            return Conjunction(simplify(Globally(arg_simplified.left)), simplify(Globally(arg_simplified.right)))
            
        return Globally(arg_simplified)
    
    return formula


def is_contradiction(formula1, formula2):
    """Check if formula1 and formula2 are contradictory."""
    # Check if one is the negation of the other
    if isinstance(formula1, Negation) and formula1.arg == formula2:
        return True
    if isinstance(formula2, Negation) and formula2.arg == formula1:
        return True
    
    return False