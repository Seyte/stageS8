from state import State
from transition import Transition
import pygraphviz as pgv
import filecomparator
from pysmt.shortcuts import Symbol, Bool, Int, And, Or, Not, Implies, Iff, GT, LT, GE, LE, simplify, Solver, get_model, is_sat, is_unsat, is_valid
from pysmt.fnode import FNode
from collections import defaultdict, deque


class FSM :
   def __init__(self, initState=None, data=None) :
      self._initial = initState
      self._states = []
      self._statesById = dict() 
      self._outputSet =set()
      self._transitionsById =dict()

   def getTransitions(self):
      return self._transitionsById.values()     

   def nextStateId(self) -> int :
      return len(self._statesById.keys())
   
   def nextTransitionId(self) -> int :
      return len(self._transitionsById.keys())
   
   
   def getInitialState(self) -> State :
      return self._initial

   def addState(self, state: State) -> State :
      id = self.nextStateId()
      self._statesById[id] = state
      state.setID(id)
      if (self._initial==None) :
         self._initial= state 
      self._states.append(state)
      return state 
   
   def getStates(self):
      return self._states
   
   def getState(self,id:int) -> State :
      return self._statesById[id]
   
   def addTransition(self, idSrc, idTgt, input, output) -> Transition:
      srcState = self.getState(idSrc)
      tgtState = self.getState(idTgt)
      if (srcState!=None and tgtState!=None and input!=None and output!=None) :
         transition = Transition(srcState, tgtState, input, output)
         srcState.addOutTr(transition)
         tgtState.addInTr(transition)
         id = self.nextTransitionId()
         self._transitionsById[id] = transition
         transition.setID(id)

         self._outputSet.add(output)
         return transition
      return None
   def removeTransition(self, transition):
      # Remove the transition from source state's outgoing transitions
      transition.getSrcState().removeOutTr(transition)
      # Remove the transition from target state's incoming transitions
      transition.getTgtState().removeInTr(transition)
      # Remove the transition from FSM's transitions
      del self._transitionsById[transition.getID()]
      # If the transition's output is no longer produced by any other transition,
      # remove it from the outputSet
      if not any(t.getOutput() == transition.getOutput() for t in self.getTransitions()):
         self._outputSet.remove(transition.getOutput())

   def nbTransitions(self):
      return len(self._transitionsById.keys())
   
   def __str__(self) -> str:
      pass
  
   def toDot(self) -> str :
      rst =""
      rst+= f'digraph fsm' + "{"
      for cle in self._statesById.keys() :
         rst += "\n\t" + self._statesById[cle].toDot()
      
      for cle in self._transitionsById.keys() :
         rst += "\n\t" + self._transitionsById[cle].toDot()
      rst+="\n}"
      return rst  

   def toNL(self) -> str :
      rst =""
      for cle in self._transitionsById.keys() :
         rst +=  " "+self._transitionsById[cle].toNL() + ".\n"
      return rst 
#    --------------------------------- getOutputSet --------------------------------- 
   def deterministic_executions(self, input_symbols):
        queue = deque([(self._initial, input_symbols, [], [])])  
        final_results = set()

        while queue:
            current_state, remaining_inputs, previous_outputs, previous_symbols = queue.popleft()

            if not remaining_inputs:  
                final_results.add((tuple(previous_outputs), tuple(previous_symbols)))  
            else:
                current_input = remaining_inputs[0]  
                next_inputs = remaining_inputs[1:]  

                matching_transitions = [t for t in current_state.getOutTransitions() if is_valid(Implies(t.getInput(), current_input))]


                for transition in matching_transitions:
                    next_state = transition.getTgtState()
                    next_outputs = previous_outputs + [transition.getOutput()]  
                    next_symbols = previous_symbols + [transition.getTransitionSymbol()]  
                    queue.append((next_state, next_inputs, next_outputs, next_symbols))  

        return final_results




''' --------------------------------- Algorithme de Moore ---------------------------------  '''

def partition_states_by_output(fsm):
    # Assuming a state is "accepting" if it has a unique output. Modify as needed.
    partitions = defaultdict(set)
    for state in fsm.getStates():
        for tr in state.getOutTransitions():
            partitions[tr.getOutput()].add(state)
            break  # Assuming each state has one unique output through its transitions
    return list(partitions.values())

def refine_partitions(fsm, partitions, alphabet):
    # For each partition and each symbol, check if states need further splitting
    new_partitions = []
    for partition in partitions:
        split_dict = defaultdict(set)

        for state in partition:
            key = []
            for symbol in alphabet:
                matching_transitions = [t for t in state.getOutTransitions() if t.getTransitionSymbol() == symbol]
                if matching_transitions:
                    destination = matching_transitions[0].getTgtState()
                    for p in partitions:
                        if destination in p:
                            key.append(tuple(p))
                            break
                else:
                    key.append(None)
            split_dict[tuple(key)].add(state)

        new_partitions.extend(split_dict.values())

    return new_partitions

def moore_minimization(fsm, alphabet):
    partitions = partition_states_by_output(fsm)

    while True:
        new_partitions = refine_partitions(fsm, partitions, alphabet)
        if new_partitions == partitions:  # No further refinement possible
            break
        partitions = new_partitions

    # Construct new FSM from partitions
    minimized_fsm = FSM()

    state_mapping = {}
    for partition in partitions:
        new_state = minimized_fsm.addState(State())  # Assuming State class exists
        for state in partition:
            state_mapping[state] = new_state

    for transition in fsm.getTransitions():
        src_state = state_mapping[transition.getSrcState()]
        tgt_state = state_mapping[transition.getTgtState()]
        minimized_fsm.addTransition(src_state.getID(), tgt_state.getID(), transition.getTransitionSymbol(), transition.getOutput())

    return minimized_fsm


''' --------------------------------- FromDot ---------------------------------  '''


def fromDot(filePath):
    # Load the .dot file and create a graph from it
    graph = pgv.AGraph(filePath)

    fsm = FSM()

    # Create the states
    for node in graph.nodes():
        # Parse node details (like label) if needed
        label = node.attr.get('label')
        state_id = int(node.name.replace('s_', '')) # Extract state id
        state = State(label, state_id)
        fsm.addState(state)

    # Create the transitions
    for edge in graph.edges():
        # Parse edge details
        src_id = int(edge[0][2:])
        tgt_id = int(edge[1][2:])
        input_output = edge.attr.get('label').split('/')
        input_conditions = input_output[0].split(' & ')
        output = input_output[1]

        # Add the transition to the fsm
        fsm.addTransition(src_id, tgt_id, input_conditions, output) # use ids, not State objects

    return fsm

''' --------------------------------- multiply_fsm ---------------------------------  '''

def simplify_fsm(fsm):
    def is_subsumed(cond1, cond2):
      cond1 = cond1.replace("(", "").replace(")", "").replace("\'", "").replace("\"", "").replace(" ", "")
      cond2 = cond2.replace("(", "").replace(")", "").replace("\'", "").replace("\"", "").replace(" ", "")
      return set(cond1.split('&')).issubset(set(cond2.split('&')))

    for state in fsm.getStates():
        out_transitions = state.getOutTransitions()
        for transition in out_transitions[:]:
            for other_transition in out_transitions:
                if transition != other_transition and transition.getTgtState() == other_transition.getTgtState():
                    if is_subsumed(str(transition.getInput()), str(other_transition.getInput())):
                        fsm.removeTransition(transition)
                        break


def multiply_fsm(fsm1, fsm2):
    new_fsm = FSM()
    state_dict = {}
    sink_state = State("sink")
    new_fsm.addState(sink_state)

    for state1 in fsm1.getStates():
        for state2 in fsm2.getStates():
            new_label = state1.getLabel() + "-" + state2.getLabel()
            new_state = State(new_label)
            new_fsm.addState(new_state)
            state_dict[(state1.getID(), state2.getID())] = new_state

    for transition1 in fsm1.getTransitions():
        for transition2 in fsm2.getTransitions():
            intersection = And(transition1.getInput(), transition2.getInput())
            simplified_intersection = simplify(intersection)
            str_intersection = str(simplified_intersection).strip("() '\"")
            unique_conditions = ' & '.join(set(str_intersection.split(' & ')))
            if transition1.getOutput() == transition2.getOutput():
                if not simplified_intersection.is_false():
                    src_state = state_dict[(transition1.getSrcState().getID(), transition2.getSrcState().getID())]
                    tgt_state = state_dict[(transition1.getTgtState().getID(), transition2.getTgtState().getID())]
                    new_fsm.addTransition(src_state.getID(), tgt_state.getID(), unique_conditions, transition1.getOutput())
            else:
                if not simplified_intersection.is_false():
                    src_state = state_dict[(transition1.getSrcState().getID(), transition2.getSrcState().getID())]
                    new_fsm.addTransition(src_state.getID(), sink_state.getID(), unique_conditions, transition1.getOutput())
    simplify_fsm(new_fsm)
    return new_fsm

''' --------------------------------- encodage en pySMT ---------------------------------  '''

def encode_xi_T(state):
    transitions_by_input = defaultdict(list)
    for transition in state.getOutTransitions():
        transitions_by_input[transition.getInput()].append(transition)

    cnf_formulas = []
    for input_value, input_transitions in transitions_by_input.items():
        n = len(input_transitions)
        terms = []
        for k in range(0, n-1):
            t_k = input_transitions[k]
            for j in range(k+1, n):
                t_j = input_transitions[j]

                # (¬tk∨ ¬tj) 
                terms.append(Or(Not(t_k.getTransitionSymbol()), Not(t_j.getTransitionSymbol())))
        # create a CNF formula for this input
        if terms:
            cnf_formula = And(Or(*(t_k.getTransitionSymbol() for t_k in input_transitions)), *terms)
        else:
            cnf_formula = And(*(t_k.getTransitionSymbol() for t_k in input_transitions))
        cnf_formulas.append(cnf_formula)
        # (Debug) print the state, input and the generated condition
        #print(f"encode_xi_T of state {state.getLabel()} with input {input_value} gives the conditions {cnf_formula}")

    # Create a conjunction of all CNF formulas
    xi_T = And(*cnf_formulas)
    return xi_T

def encode_deterministic_fsm(fsm):
    states = fsm.getStates()
    phi_M = And(*[encode_xi_T(state) for state in states])
    return phi_M


''' --------------------------------- Algo de selection des transitions pour rendre l'automate deterministe ---------------------------------  '''

# recupere tous les modèles (toutes les combinaisons de transitions) qui satisfont la formule (description de l'automate non deterministe)
def get_all_models(formula):
    solver = Solver()
    solver.add_assertion(formula)
    
    models = []
    while solver.solve():
        model = solver.get_model()
        models.append(model)
        
        blocking_clause = Not(And([Or(k, Not(v)) if v.is_true() else Or(Not(k), v)
                                   for k, v in model]))
        solver.add_assertion(blocking_clause)
    
    return models

# find_paths_to_initial permets de trouver un chemin entre l'état en paramètre et l'état initial
def find_paths_from_initial(state, M): 
    paths = []
    initial_state = M.getInitialState()
    stack = [(state, [])]
    visited = set()
    while stack:
        current_state, path_so_far = stack.pop()
        if current_state in visited:
            continue
        visited.add(current_state)
        for in_transition in current_state.getInTransitions():
            src_state = in_transition.getSrcState()
            condition = in_transition.getInput()
            new_path = [condition] + path_so_far
            if src_state == initial_state:
                paths.append(new_path)
            else:
                stack.append((src_state, new_path))
    return paths

# are two fsm pysmt description equivalent?
def are_equivalent(phi_M1, phi_M2):
    # too fsms are equivalent if when we multiply them, there is no delta state (sink state)
    pass
    
def delete_transitions (fsm, transitions_to_delete):
    for transition in transitions_to_delete:
        fsm.removeTransition(transition)


# find a minimal distinguishing test for two non equivalent DFSMs
def minimal_distinguishing_test_for_two_non_equivalent_DFSMs(M,phi):
    pass
    
def verify_test_adequacy_for_mining(M, phiM, TS, S):

    def at_least_two_non_equivalent_DFSMs(phi):
        solutions = get_all_models(phi)
        if len(solutions) < 2:
            return False
        for i in range(len(solutions)):
            for j in range(i + 1, len(solutions)):
                if not are_equivalent(solutions[i], solutions[j]):
                    return True
        return False
    
    # recupere tous les modèles (toutes les combinaisons de transitions en PySMT) qui satisfont la formule (automate non deterministe)
    def deterministic_executions_producing_y_on_test_x(all_executions, y):
        executions_producing_y = set()

        for execution in all_executions:
            output, _ = execution
            if output == y:
                executions_producing_y.add(execution)

        return executions_producing_y
    
    # & de toutes les transitions de l'execution
    def encode_execution(execution):
        _, transitions = execution
        return And(*transitions)

    def encode_DFSMs_in_M_producing_y_on_test_x(Exy, original_formula):
        execution_formulas = [encode_execution(execution) for execution in Exy]
        combined_execution_formula = Or(*execution_formulas)
        combined_formula = And(original_formula, combined_execution_formula)
        return combined_formula

    # supprime les transitions qui ne peuvent pas être dans l'automate
    def determine_Mx_y(M, Exy, YMx):
        # Identify the invalid transitions
        invalid_transitions = set()
        for execution1 in YMx:
            output1, transitions1 = execution1
            for execution2 in Exy:
                output2, transitions2 = execution2
                if output1 != output2: # different output on the same input
                    for i in range(len(transitions1)): # assuming len(transitions1) == len(transitions2)
                        if transitions1[i] != transitions2[i]: # this is the divergence, we took the wrong transition
                            invalid_transitions.add(transitions1[i])
                            break

        # Create a new model Mx_y by deleting the invalid transitions from M
        Mx_y = delete_transitions(M, invalid_transitions)

        return Mx_y


    phi = phiM
    verdict = True if not at_least_two_non_equivalent_DFSMs(phi) else False
    xd = None
    while TS and not verdict:
        x = TS.pop()  # Sélectionne et supprime un test de TS
        # on execute l'automate M sur le test x
        YMx = M.deterministic_executions(x)  
        # on simule l'automate S sur le test x 
        # TODO: remplacer ça par une question à l'utilisateur
        y = S.deterministic_executions(x) 
        Exy = deterministic_executions_producing_y_on_test_x(YMx, y)
        phi = And(phi, encode_DFSMs_in_M_producing_y_on_test_x(Exy, phi)) 
        M = determine_Mx_y(M, Exy, YMx)
        #if at_least_two_non_equivalent_DFSMs(phi):
        xd = minimal_distinguishing_test_for_two_non_equivalent_DFSMs(M,phi)  
        if xd != None: # xd est un test qui distingue deux automates non deterministes
            verdict = True
    return verdict, M, phi, xd

''' ------------------------- mining oracle ------------------------- '''
def precise_oracle_mining(M, TS, S):
    phiM = encode_deterministic_fsm(M)
    TSm = TS.copy()
    verdict, M_prime, phi_prime, xd = verify_test_adequacy_for_mining(M, phiM, TS, S)
    while verdict == False:
        TSm.append(xd)
        phiM = phi_prime
        M = M_prime
        verdict, M_prime, phi_prime, xd = verify_test_adequacy_for_mining(M, phiM, TS, S)

    # TODO: extraire la solution de phi_prime (pour l'instant je vérifie manuellement)
    P = phi_prime

    return TSm, P


if __name__ == '__main__':
    fsm = fromDot("./first_snippets/data/fsm5.dot")
    #result = fsm.deterministic_executions([Symbol('a'),Symbol('b')])
    #print(result)
    #stateToReach = fsm.getStates()[1]
    #print(find_paths_to_initial(stateToReach, fsm))


    
    
