from hoa.parsers import HOAParser
from hoa.core import HOA
from hoa.ast.label import LabelExpression, LabelAtom
from hoa.ast.boolean_expression import And, Not, Or

from utils import *

def generate_chcs_from_automata(automaton_str, type_dict):
    hoa_parser = HOAParser()
    automaton = hoa_parser(automaton_str)

    is_satisfiable = check_automaton_satisfiability(automaton)
    if not is_satisfiable:
        return "unsat"

    chcs = automatonToCHCs(automaton, type_dict)
    return chcs

def check_automaton_satisfiability(automaton: HOA):
    # Check if there are any accepting states
    has_accepting_states = False
    for state in automaton.body.state2edges:
        if state.acc_sig is not None:
            has_accepting_states = True
            break
    
    if not has_accepting_states:
        return False
    
    # Check if there are any transitions
    has_transitions = False
    for state, edges in automaton.body.state2edges.items():
        if edges:
            has_transitions = True
            break
    
    if not has_transitions:
        return False
    
    return True

def automatonToCHCs(automaton: HOA, type_dict):
    if (automaton.header.acceptance.name != "Buchi"):
        raise Exception("The input automaton does not have the Buchi acceptance condition.")
    
    header = getHeader(automaton, type_dict)
    body = getBody(automaton)

    return header + body

def getHeader(automaton: HOA, type_dict):
    props = [infix_to_prefix(prop) for prop in automaton.header.propositions]
    header = "(set-logic HORN)\n\n"

    vars = set()
    constraints = ""
    for i, prop in enumerate(props):
        constraints += f"(define-fun C{i} ((reg Registers)) Bool\n"
        prop, new_vars = transform(prop)
        vars.update(new_vars)
        constraints += f"   {prop}\n)\n\n"

    decl_datatypes_str = "(declare-datatypes () ((Registers (mk-state\n"
    for var in vars:
        base_var = var.rsplit('_', 1)[0]
        decl_datatypes_str += f"   ({var} {type_dict[base_var]})\n"
    decl_datatypes_str += "))))\n\n"

    duplicates = get_multiple_suffix_variables(vars)
    data_buffer_str = "(define-fun buff_upd ((reg Registers) (regN Registers)) Bool\n(and \n"
    if duplicates:
        for var in duplicates:
            data_buffer_str += f"   (= ({var}_2 regN) ({var}_1 reg))\n"
    else:
        data_buffer_str += f"true\n"
    data_buffer_str += "))\n\n"

    header += decl_datatypes_str + data_buffer_str + constraints     
    return header

def getBody(automaton: HOA):
    body = ""

    n_prop = len(automaton.header.propositions)
    if n_prop == 0:
        raise Exception("No atomic propositions found.")

    # Declare states as uninterpreted predicates
    i = 0
    for state in automaton.body.state2edges:
        body += f"(declare-fun Q{i} (Registers) Bool)\n"
        i = i + 1
    
    # The Fact, based on the initial state
    initial_state_id = None
    initial_states = automaton.header.start_states    
    if initial_states is None:
        raise Exception("No initial state found.")
    if len(initial_states) != 1:
        raise Exception("More than one initial state found.")
    initial_states = initial_states.__iter__().__next__()
    if len(initial_states) != 1:
        raise Exception("More than one initial state found.")
    
    initial_state_id = initial_states.__iter__().__next__()
    body += f"(assert (forall ((regI Registers)) (Q{initial_state_id} regI)))\n"

    # The Rules
    counter = 0
    for state, edges in automaton.body.state2edges.items():
        for edge in edges:
            dests = edge.state_conj
            if len(dests)>1:
                raise Exception("An edge has more than one destination.")
            src_id = state.index
            dest_id = dests[0]

            decoded_labels = decodeLabel(edge.label, n_prop)

            # Compute constraints
            # The first constraint is common to all rules and is meant to update the
            # data buffer of the symbolic automaton
            for label in decoded_labels:
                h = f"(Q{dest_id} regNext{counter})"
                
                constraint = f"(buff_upd reg{counter} regNext{counter})"
                for i in range(n_prop):
                    if label[i] is True:
                        constraint += f" (C{i} regNext{counter})"
                    elif label[i] is False:
                        constraint += f" (not (C{i} regNext{counter}))"
                
                b = f"(and (Q{src_id} reg{counter}) {constraint})"
                body += f"(assert (forall ((reg{counter} Registers) (regNext{counter} Registers))\n   (=> {b} {h})))\n"
                counter = counter + 1
            
    # The Queries, based on the accepting states
    for state in automaton.body.state2edges:
        if state.acc_sig is not None:
            state_id = state.index
            body += f"(assert (forall ((regF Registers)) (=> (Q{state_id} regF) false)))\n"

    body += "(check-sat)"
    return body

def decodeLabel(label: LabelExpression, n: int):
    """Decodes a SPOT label into one or more vectors of {True, False, None} values, one for each AP."""
    def DecodeSingleProp(label):
        if isinstance(label, LabelAtom):
            return (label.proposition, True)
        elif isinstance(label, Not):
            atom = label.argument
            if not isinstance(atom, LabelAtom):
                raise Exception("Unsupported label {0}.".format(label))
            return (atom.proposition, False)
        else:
            raise Exception("Unsupported label {0}.".format(label))
    
    def DecodeAnd(andLabel):
        result = [None] * n
        for op in andLabel.operands:
            (prop, val) = DecodeSingleProp(op)
            result[prop] = val
        return result

    if isinstance(label, And):
        return [DecodeAnd(label)]
    elif isinstance(label, Or):
        result = []
        for op in label.operands:
            result.append(DecodeAnd(op))
        return result
    else:
        result = [None] * n
        (prop, val) = DecodeSingleProp(label)
        result[prop] = val
        return [result]
        #raise Exception("We have a problem")
        # return DecodeSingleProp(label)
