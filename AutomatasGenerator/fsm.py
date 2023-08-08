from state import State
from transition import Transition
import pygraphviz as pgv
import filecomparator
from pysmt.shortcuts import Symbol, Bool, Int, And, Or, Not, Implies, Iff, GT, LT, GE, LE, simplify, Solver, get_model, is_sat, is_unsat, is_valid, get_free_variables
from pysmt.fnode import FNode
from collections import defaultdict, deque
from pysmt.typing import BOOL

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
   
   def setInitialState(self, state: State) :
        self._initial = state

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
      print("Error: addTransition")
      return None

   def removeTransition(self, transition):
      transition.getSrcState().removeOutTr(transition)
      transition.getTgtState().removeInTr(transition)
      del self._transitionsById[transition.getID()]
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
   
   #TODO: modifier ça en O(1) au lieu de O(n)
   def getSinkState(self) -> State :
       # retourne l'état nommé sink s'il existe, None sinon
         for state in self._states:
            if state.getLabel() == "sink":
               return state
         return None
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

def multiply_fsm(fsm1, fsm2):
    new_fsm = FSM()
    state_dict = {}

    for state1 in fsm1.getStates():
        for state2 in fsm2.getStates():
            new_label = state1.getLabel() + "-" + state2.getLabel()
            new_state = State(new_label)
            new_fsm.addState(new_state)
            state_dict[(state1.getID(), state2.getID())] = new_state

    sink_state = State("sink")
    new_fsm.addState(sink_state)

    for transition1 in fsm1.getTransitions():
        for transition2 in fsm2.getTransitions():
            print("---------------------------")
            print("Transition 1 input : ", transition1.getInput())
            print("Transition 2 input : ", transition2.getInput())
            intersection = And(transition1.getInput(), transition2.getInput())
            print("Intersection : ", intersection)
            simplified_intersection = simplify(intersection)
            
             # Get individual symbols from the transition inputs
            symbols_t1 = get_free_variables(transition1.getInput())
            symbols_t2 = get_free_variables(transition2.getInput())

            # Print the type of each symbol
            for sym in symbols_t1:
                print("Type of symbol ",sym," in transition1 input:", sym.get_type())
            for sym in symbols_t2:
                print("Type of symbol ",sym," in transition2 input:", sym.get_type())

            print(get_model(simplified_intersection))
            print("is it satisfaible: ",not simplified_intersection.is_false())
    
            src_state = state_dict[(transition1.getSrcState().getID(), transition2.getSrcState().getID())]
            if(transition1.getSrcState().getLabel() == "A" and transition2.getSrcState().getLabel() == "A"):
                tgt_state = state_dict[(transition1.getTgtState().getID(), transition2.getTgtState().getID())]
                print("tgt_state : ", tgt_state.getLabel())
                print("is solvable :", not simplified_intersection.is_false())
                print("source state label", src_state.getLabel())
            # si les transitions ont la même sortie et que l'input est solvable
            if transition1.getOutput() == transition2.getOutput() and not simplified_intersection.is_false():
                tgt_state = state_dict[(transition1.getTgtState().getID(), transition2.getTgtState().getID())]
                new_fsm.addTransition(src_state.getID(), tgt_state.getID(), str(simplified_intersection), transition1.getOutput())
            else:
                # sinon cela veut dire que input1 ou input2 provoque une sortie différente -> sink
                # on rajoute deux transitions avec input1 et input2
                print(" Creation of transition to sink")
                print("from ", src_state.getLabel(), " to ", sink_state.getLabel(), " with input ", str(transition1.getInput()), " and output ", transition1.getOutput())
                new_fsm.addTransition(src_state.getID(), sink_state.getID(), str(transition1.getInput()), transition1.getOutput())
                new_fsm.addTransition(src_state.getID(), sink_state.getID(), str(transition2.getInput()), transition2.getOutput())
                print("from ", src_state.getLabel(), " to ", sink_state.getLabel(), " with input ", str(transition2.getInput()), " and output ", transition2.getOutput())
    # set initial state 
    new_fsm.setInitialState(state_dict[(fsm1.getInitialState().getID(), fsm2.getInitialState().getID())])
    print("label of initial state ", new_fsm.getInitialState().getLabel())
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

''' --------------------------------- Algo de selection des transitions pour rendre l'automate deterministe ---------------------------------  '''

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

# create a new automata from phi
def create_automata_from_phi(M,phi):
    # solver phi to get which transitions should be disabled in M
    # then create a new automata from M with the disabled transitions and return it
    model = get_model(phi)

    new_fsm = FSM()
    for state in M.getStates():
        new_fsm.addState(state)

    # add transitions to the new automaton only if they are active
    for var, value in model:
        transition_id_str = str(var) # les variables sont de la forme "t_3"
        transition_id = int(transition_id_str.split('_')[1]) # on extrait l'id de la transition
        if value.is_true():
            transition = M._transitionsById[transition_id]
            new_fsm.addTransition(transition.getSrcState().getID(), transition.getTgtState().getID(), str(transition.getInput()), str(transition.getOutput()))

    return new_fsm


# are two fsm pysmt description equivalent?
def are_equivalent(M, phi_M1, phi_M2):
    # too fsms are equivalent if when we multiply them, there is no path to the sink state
    # we use phi1 and phi2 using solvers to know which transitions are used in the two fsms
    # we shall use create_automata_from_phi and multiply_fsm.
    M1 = create_automata_from_phi(M, phi_M1)
    print("===============================")
    print("M1")
    print(M1.toDot())
    M2 = create_automata_from_phi(M, phi_M2)
    print("===============================")
    print("M2")
    print(M2.toDot())
    M1_M2 = multiply_fsm(M1, M2)
    sink_M1_M2 = M1_M2.getSinkState()
    paths_to_sink = find_paths_from_initial(sink_M1_M2, M1_M2)
    return len(paths_to_sink) == 0
    
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

''' --------------------------------- mining oracle --------------------------------- '''
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
    fsm = fromDot("./first_snippets/data/fsm6.dot")
    #phi = And(Symbol('t_1'), Not(Symbol('t_2')), Not(Symbol('t_3')), Symbol('t_0'))

    #M = create_automata_from_phi(fsm,phi)
    print(fsm.toDot())
    #print(M.toDot())   
    # for each transition, print the id, the source state, the destination state, the label
    for transition in fsm.getTransitions():
        # print "Inputstate -> output state" for each transitions
        print(transition.getID(), transition.getSrcState().getLabel(), transition.getTgtState().getLabel(), transition.getInput())
    # phi toutes transitions actives 5 transitions 0->4
    # 3 et 4 osef
    # 
    #phi1 & phi2 non & équivalent
    phi1 = And(Not(Symbol('t_0',BOOL)), Symbol('t_1',BOOL), Symbol('t_2',BOOL), Symbol('t_3',BOOL), Symbol('t_4',BOOL))
    phi2 = And(Symbol('t_0',BOOL), Not(Symbol('t_1',BOOL)), Symbol('t_2',BOOL), Symbol('t_3',BOOL), Symbol('t_4',BOOL))
    M1 = create_automata_from_phi(fsm,phi1)
    M2 = create_automata_from_phi(fsm,phi2)
    #M1 = fromDot("./first_snippets/data/fsm7.dot")
    #M2 = fromDot("./first_snippets/data/fsm8.dot")
    M1xM2 = multiply_fsm(M1,M2)
    # enregistrer M1 dans temp1 et M2 dans temp2 (fichiers) et M1xM2
    with open('temp1.dot', 'w') as f:
        f.write(M1.toDot())
    with open('temp2.dot', 'w') as f:
        f.write(M2.toDot())
    with open('temp3.dot', 'w') as f:
        f.write(M1xM2.toDot())
    print( find_paths_from_initial(M1xM2.getSinkState(), M1xM2))
    print( are_equivalent(fsm,phi1,phi2))

    
    
