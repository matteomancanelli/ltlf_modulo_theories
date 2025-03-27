
class Formula:
    """Base class for all LTLf formulas."""
    
    def to_string(self):
        return self.__str__()

    def get_closure(self):
        """Get the Fischer-Ladner closure of the formula."""
        closure = set()
        self._add_to_closure(closure)
        return closure
    
    def _add_to_closure(self, closure):
        # To be implemented by subclasses
        pass

class Atom(Formula):
    """Atomic proposition."""
    def __init__(self, name):
        self.name = name
        
    def __str__(self):
        return '"' + str(self.name) + '"'
    
    def __repr__(self):
        return self.__str__()
    
    def __hash__(self):
        return hash(str(self))
    
    def __eq__(self, other):
        if not isinstance(other, Atom):
            return False
        return self.name == other.name
    
    def _add_to_closure(self, closure):
        closure.add(self)

class Last(Atom):
    """Special atom representing the end of the trace."""
    def __init__(self):
        super().__init__("last")

class Alive(Atom):
    def __init__(self):
        super().__init__("alive")

class TrueFormula(Atom):
    """Formula representing logical true."""
    def __init__(self):
        super().__init__("true")

class FalseFormula(Atom):
    """Formula representing logical false."""
    def __init__(self):
        super().__init__("false")

class Negation(Formula):
    """Negation of a formula."""
    def __init__(self, arg):
        self.arg = arg
            
    def __str__(self):
        return f"!{self.arg}"
    
    def __repr__(self):
        return self.__str__()
    
    def __hash__(self):
        return hash(str(self))
    
    def __eq__(self, other):
        if not isinstance(other, Negation):
            return False
        return self.arg == other.arg
    
    def _add_to_closure(self, closure):
        if self in closure:
            return
        
        closure.add(self)
        self.arg._add_to_closure(closure)
        
        if isinstance(self.arg, Atom):
            closure.add(self.arg)

class Conjunction(Formula):
    """Conjunction of two formulas."""
    def __init__(self, left, right):
        self.left = left
        self.right = right
            
    def __str__(self):
        return f"({self.left} & {self.right})"
    
    def __repr__(self):
        return self.__str__()
    
    def __hash__(self):
        return hash(str(self))
    
    def __eq__(self, other):
        if not isinstance(other, Conjunction):
            return False
        return self.left == other.left and self.right == other.right
    
    def _add_to_closure(self, closure):
        if self in closure:
            return
        
        closure.add(self)
        self.left._add_to_closure(closure)
        self.right._add_to_closure(closure)

class Disjunction(Formula):
    """Disjunction of two formulas."""
    def __init__(self, left, right):
        self.left = left
        self.right = right
            
    def __str__(self):
        return f"({self.left} | {self.right})"
    
    def __repr__(self):
        return self.__str__()
    
    def __hash__(self):
        return hash(str(self))
    
    def __eq__(self, other):
        if not isinstance(other, Disjunction):
            return False
        return self.left == other.left and self.right == other.right
    
    def _add_to_closure(self, closure):
        if self in closure:
            return

        closure.add(self)
        self.left._add_to_closure(closure)
        self.right._add_to_closure(closure)

class Next(Formula):
    """Next operator (X)."""
    def __init__(self, arg):
        self.arg = arg
            
    def __str__(self):
        return f"X({self.arg})"
    
    def __repr__(self):
        return self.__str__()
    
    def __hash__(self):
        return hash(str(self))
    
    def __eq__(self, other):
        if not isinstance(other, Next):
            return False
        return self.arg == other.arg
    
    def _add_to_closure(self, closure):
        if self in closure:
            return
        
        closure.add(self)
        self.arg._add_to_closure(closure)

class WeakNext(Formula):
    """Weak Next operator (WX)."""
    def __init__(self, arg):
        self.arg = arg
            
    def __str__(self):
        return f"WX({self.arg})"
    
    def __repr__(self):
        return self.__str__()
    
    def __hash__(self):
        return hash(str(self))
    
    def __eq__(self, other):
        if not isinstance(other, WeakNext):
            return False
        return self.arg == other.arg
    
    def _add_to_closure(self, closure):
        if self in closure:
            return
        
        closure.add(self)
        self.arg._add_to_closure(closure)

class Until(Formula):
    """Until operator (U)."""
    def __init__(self, left, right):
        self.left = left
        self.right = right
            
    def __str__(self):
        return f"({self.left} U {self.right})"
    
    def __repr__(self):
        return self.__str__()
    
    def __hash__(self):
        return hash(str(self))
    
    def __eq__(self, other):
        if not isinstance(other, Until):
            return False
        return self.left == other.left and self.right == other.right
    
    def _add_to_closure(self, closure):
        if self in closure:
            return
        
        closure.add(self)
        # As per the paper: φ1 U φ2 ∈ cl(φ) implies φ1, φ2, X(φ1 U φ2) ∈ cl(φ)
        self.left._add_to_closure(closure)
        self.right._add_to_closure(closure)
        Next(self)._add_to_closure(closure)
        
        # According to the fixpoint expansion: φ1 U φ2 ≡ φ2 ∨ (φ1 ∧ X(φ1 U φ2))
        expansion = Disjunction(
            self.right,
            Conjunction(self.left, Next(self))
        )
        expansion._add_to_closure(closure)

class Release(Formula):
    """Release operator (R)."""
    def __init__(self, left, right):
        self.left = left
        self.right = right
            
    def __str__(self):
        return f"({self.left} R {self.right})"
    
    def __repr__(self):
        return self.__str__()
    
    def __hash__(self):
        return hash(str(self))
    
    def __eq__(self, other):
        if not isinstance(other, Release):
            return False
        return self.left == other.left and self.right == other.right
    
    def _add_to_closure(self, closure):
        if self in closure:
            return
        closure.add(self)
        # As per the paper: φ1 R φ2 ∈ cl(φ) implies φ1, φ2, WX(φ1 R φ2) ∈ cl(φ)
        self.left._add_to_closure(closure)
        self.right._add_to_closure(closure)
        WeakNext(self)._add_to_closure(closure)
        
        # According to the fixpoint expansion: φ1 R φ2 ≡ φ2 ∧ (φ1 ∨ WX(φ1 R φ2))
        expansion = Conjunction(
            self.right,
            Disjunction(self.left, WeakNext(self))
        )
        expansion._add_to_closure(closure)

class Finally(Formula):
    """Finally operator (F)."""
    def __init__(self, arg):
        self.arg = arg
            
    def __str__(self):
        return f"F({self.arg})"
    
    def __repr__(self):
        return self.__str__()
    
    def __hash__(self):
        return hash(str(self))
    
    def __eq__(self, other):
        if not isinstance(other, Finally):
            return False
        return self.arg == other.arg
    
    def _add_to_closure(self, closure):
        if self in closure:
            return
        closure.add(self)
        # As per the paper: Fφ ∈ cl(φ) implies φ, X(Fφ) ∈ cl(φ)
        self.arg._add_to_closure(closure)
        Next(self)._add_to_closure(closure)
        
        # According to the fixpoint expansion: Fφ ≡ φ ∨ X(Fφ)
        expansion = Disjunction(self.arg, Next(self))
        expansion._add_to_closure(closure)

class Globally(Formula):
    """Globally operator (G)."""
    def __init__(self, arg):
        self.arg = arg
            
    def __str__(self):
        return f"G({self.arg})"
    
    def __repr__(self):
        return self.__str__()
    
    def __hash__(self):
        return hash(str(self))
    
    def __eq__(self, other):
        if not isinstance(other, Globally):
            return False
        return self.arg == other.arg
    
    def _add_to_closure(self, closure):
        if self in closure:
            return
        closure.add(self)
        # As per the paper: Gφ ∈ cl(φ) implies φ, WX(Gφ) ∈ cl(φ)
        self.arg._add_to_closure(closure)
        WeakNext(self)._add_to_closure(closure)
        
        # According to the fixpoint expansion: Gφ ≡ φ ∧ WX(Gφ)
        expansion = Conjunction(self.arg, WeakNext(self))
        expansion._add_to_closure(closure)
