import black_sat
from formula import *

def parse_and_convert_black_formula(formula_str):
    """Parse a formula string using black_sat and convert it to our internal representation."""
    alphabet = black_sat.alphabet()
    formula = black_sat.parse_formula(alphabet, formula_str)
    
    return convert_from_black(formula)


def convert_from_black(formula):
    """Convert a Black formula to our internal representation."""
    
    if isinstance(formula, black_sat.negation):
        return Negation(convert_from_black(formula.argument))
    
    if isinstance(formula, black_sat.conjunction):
        return Conjunction(convert_from_black(formula.left), convert_from_black(formula.right))
    
    if isinstance(formula, black_sat.disjunction):
        return Disjunction(convert_from_black(formula.left), convert_from_black(formula.right))
    
    if isinstance(formula, black_sat.implication):
        return Disjunction(Negation(convert_from_black(formula.left)), convert_from_black(formula.right))
    
    if isinstance(formula, black_sat.iff):
        left = convert_from_black(formula.left)
        right = convert_from_black(formula.right)

        return Disjunction(Conjunction(left, right), Conjunction(Negation(left), Negation(right)))
    
    if isinstance(formula, black_sat.tomorrow):
        return Next(convert_from_black(formula.argument))
    
    if isinstance(formula, black_sat.w_tomorrow):
        return WeakNext(convert_from_black(formula.argument))
    
    if isinstance(formula, black_sat.until):
        return Until(convert_from_black(formula.left), convert_from_black(formula.right))
    
    if isinstance(formula, black_sat.w_until):
        left = convert_from_black(formula.left)
        right = convert_from_black(formula.right)

        return Disjunction(Until(left, right), Globally(left))
    
    if isinstance(formula, black_sat.always):
        return Globally(convert_from_black(formula.argument))
    
    if isinstance(formula, black_sat.eventually):
        return Finally(convert_from_black(formula.argument))
    
    if str(formula) == "true" or str(formula) == "T":
        return TrueFormula()
    
    if str(formula) == "false" or str(formula) == "F":
        return FalseFormula()
    
    if str(formula) == "last":
        return Last()
    
    return Atom(str(formula))
