from hoa.parsers import HOAParser
from hoa.core import HOA
from hoa.ast.label import LabelExpression, LabelAtom
from hoa.ast.boolean_expression import And, Not, Or

from utils import *

def generate_chcs_from_automata(automaton_str):
    hoa_parser = HOAParser()
    automaton = hoa_parser(automaton_str)
    chcs = automatonToCHCs(automaton)
    return chcs

def automatonToCHCs(automaton: HOA):
    if (automaton.header.acceptance.name != "Buchi"):
        raise Exception("The input automaton does not have the Buchi acceptance condition.")
    
    header = getHeader(automaton)
    body = getBody(automaton)

    return header + body

def getHeader(automaton: HOA):
    props = [infix_to_prefix(prop) for prop in automaton.header.propositions]
    header = ""

    vars = set()
    for i, prop in enumerate(props):
        header += f"(define-fun C{i} ((reg Registers)) Bool\n"
        prop, i_vars = transform(prop)
        vars.update(i_vars)
        header += f"   {prop}\n)\n\n"

    decl_datatypes_str = "(declare-datatypes () ((Registers (mk-state\n"
    for var in vars:
        decl_datatypes_str += f"   ({var} Int)\n"
    decl_datatypes_str += "))))\n\n"

    data_buffer_str = "(define-fun Trans ((reg Registers) (regN Registers)) Bool\n(and \n"
    for var in get_multiple_suffix_variables(vars):
        data_buffer_str += f"   (= ({var}2 regN) ({var}1 reg))\n"
    data_buffer_str += "))\n\n"

    header = "(set-logic HORN)\n\n" + decl_datatypes_str + data_buffer_str + header     
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
                
                constraint = f"(Trans reg{counter} regNext{counter})"
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
