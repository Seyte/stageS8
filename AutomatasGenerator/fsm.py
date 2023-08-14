from state import State
from transition import Transition
import pygraphviz as pgv
import filecomparator
from pysmt.shortcuts import Symbol, And, Or, Not, Iff, Solver, get_model, is_sat, simplify
from pysmt.fnode import FNode
from collections import defaultdict, deque
from pysmt.typing import BOOL
from copy import deepcopy

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
   
   def addTransition(self, idSrc, idTgt, input, output, id = None) -> Transition:
      srcState = self.getState(idSrc)
      tgtState = self.getState(idTgt)
      if (srcState!=None and tgtState!=None and input!=None and output!=None) :
         transition = Transition(srcState, tgtState, input, output)
         srcState.addOutTr(transition)
         tgtState.addInTr(transition)
         if id == None:
            id = self.nextTransitionId()
         self._transitionsById[id] = transition
         transition.setID(id)

         self._outputSet.add(output)
         return transition
      print("Error: addTransition")
      return None
   
   def transitionExists(self, idSrc, idTgt, input, output) -> bool:
        srcState = self.getState(idSrc)
        tgtState = self.getState(idTgt)
        if (srcState!=None and tgtState!=None and input!=None and output!=None) :
             for tr in srcState.getOutTransitions() :
                if (tr.getTgtState()==tgtState and not Iff(tr.getInput(),input).is_false() and tr.getOutput()==output) :
                 return True
        return False

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
        queue = deque([(self._initial, input_symbols, [])])
        final_results = set()

        while queue:
            current_state, remaining_inputs, previous_execution_steps = queue.popleft()

            if not remaining_inputs:
                final_results.add(tuple(previous_execution_steps))
            else:
                current_input = remaining_inputs[0]
                next_inputs = remaining_inputs[1:]

                matching_transitions = [t for t in current_state.getOutTransitions() if is_sat(And(t.getInput(), current_input))]

                for transition in matching_transitions:
                    next_state = transition.getTgtState()
                    next_output = transition.getOutput()
                    transition_symbol = transition.getTransitionSymbol()  # Getting the transition symbol
                    # Creating a tuple for each step with the format (input used, output, transition symbol)
                    next_execution_steps = previous_execution_steps + [(current_input, next_output, transition_symbol)]
                    queue.append((next_state, next_inputs, next_execution_steps))
        return final_results




''' --------------------------------- FromDot ---------------------------------  '''


def fromDot(filePath : str):
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
        if state_id == 0:
            fsm.setInitialState(state)

    # Create the transitions
    for edge in graph.edges():
        # Parse edge details
        src_id = int(edge[0][2:])
        tgt_id = int(edge[1][2:])
        input_output = edge.attr.get('label').split('/')
        input_conditions = input_output[0].split(' & ')
        output = input_output[1]
        real_id = edge.attr.get('myattribute')  # Retrieve the myattribute value
        if real_id:
            real_id = int(real_id.replace('t_', ''))  # Extract the real id if present  
            fsm.addTransition(src_id, tgt_id, input_conditions, output,real_id) # use ids, not State objects

        else:
        # Add the transition to the fsm
            fsm.addTransition(src_id, tgt_id, input_conditions, output) # use ids, not State objects

    return fsm

''' --------------------------------- multiply_fsm ---------------------------------  '''

def multiply_fsm(fsm1 : FSM, fsm2 : FSM) -> FSM:
    new_fsm = FSM()
    state_dict = {}

    for state1 in fsm1.getStates():
        for state2 in fsm2.getStates():
            new_label = state1.getLabel() + "-" + state2.getLabel()
            new_state = State(new_label)
            new_fsm.addState(new_state)
            state_dict[(state1, state2)] = new_state

    sink_state = State("sink")
    new_fsm.addState(sink_state)

    for transition1 in fsm1.getTransitions():
        for transition2 in fsm2.getTransitions():
            intersection = And(transition1.getInput(), transition2.getInput())
            simplified_intersection = simplify(intersection)
            src_state = state_dict[(transition1.getSrcState(), transition2.getSrcState())]
            # si les transitions ont la même sortie et que l'input est solvable
            if transition1.getOutput() == transition2.getOutput() and not simplified_intersection.is_false():

                tgt_state = state_dict[(transition1.getTgtState(), transition2.getTgtState())]
                t = new_fsm.addTransition(src_state.getID(), tgt_state.getID(), simplified_intersection, transition1.getOutput())

            elif not simplified_intersection.is_false(): # juste les outputs diffèrent 
                new_fsm.addTransition(src_state.getID(), sink_state.getID(), simplified_intersection, transition1.getOutput())
    # reverse state_dict, to get the uple of states from the originals fsms from the new fsm state into state_reverse_dict
    state_reverse_dict = {v: k for k, v in state_dict.items()}
    for state in new_fsm.getStates():
        non_sink_inputs = [Not(transition.getInput()) for transition in state.getOutTransitions() if transition.getTgtState() != sink_state]
        if (len(non_sink_inputs) >= 1):
            input = simplify(And(non_sink_inputs))
            # on récupère les états de fsm1 et fsm2 correspondant à l'état du nouveau fsm
            state1, state2 = state_reverse_dict[state]
            # s'il existe une transition sortante de state1 ou state2 tel que And(input, transition.getInput()) est satisfiable
            # on rajoute cette transition au nouveau fsm vers le sink
            for transition1 in state1.getOutTransitions():
                intersection = And(input, transition1.getInput())
                if is_sat(intersection):
                    # si la transition n'existe pas déjà
                    if not new_fsm.transitionExists(state.getID(), sink_state.getID(), intersection, transition1.getOutput()):
                        new_fsm.addTransition(state.getID(), sink_state.getID(), intersection, transition1.getOutput())
            
            for transition2 in state2.getOutTransitions():
                intersection = And(input, transition2.getInput())
                if is_sat(intersection):
                    # si la transition n'existe pas déjà
                    if not new_fsm.transitionExists(state.getID(), sink_state.getID(), intersection, transition2.getOutput()):
                        new_fsm.addTransition(state.getID(), sink_state.getID(), intersection, transition2.getOutput())
    # set initial state 
    new_fsm.setInitialState(state_dict[(fsm1.getInitialState(), fsm2.getInitialState())])
    return new_fsm

''' --------------------------------- encodage en pySMT ---------------------------------  '''

def encode_xi_T(state : State):
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

    # Create a conjunction of all CNF formulas
    xi_T = And(*cnf_formulas)
    return xi_T

def encode_deterministic_fsm(fsm : FSM):
    states = fsm.getStates()
    phi_M = And(*[encode_xi_T(state) for state in states])
    return phi_M

# recupere tous les modèles (toutes les combinaisons de transitions) qui satisfont la formule (description de l'automate non deterministe)
def get_all_models(formula : FNode):
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
def find_paths_from_initial(state : State, M : FSM): 
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
def create_automata_from_phi(M : FSM,phi : FNode):
    # solver phi to get which transitions should be disabled in M
    # then create a new automata from M with the disabled transitions and return it

    model = None
    #TODO: I should be able to remove this, have to double check
    if isinstance(phi, FNode):
    
        model = get_model(phi)
    else:
        model = phi


    new_fsm = FSM()
    for state in M.getStates():
        new_state = State(state.getLabel(), state.getID())
        new_fsm.addState(new_state)
        if state == M.getInitialState():
            new_fsm.setInitialState(new_state)

    # add transitions to the new automaton only if they are active
    for var, value in model:
        transition_id_str = str(var) # les variables sont de la forme "t_3"
        transition_id = int(transition_id_str.split('_')[1]) # on extrait l'id de la transition
        if value.is_true():
            transition = M._transitionsById[transition_id]
            new_fsm.addTransition(transition.getSrcState().getID(), transition.getTgtState().getID(), transition.getInput(), str(transition.getOutput()), transition.getID())

    return new_fsm


# are two fsm pysmt description equivalent?
def are_equivalent(M : FSM, phi_M1 , phi_M2 ):
    
    # too fsms are equivalent if when we multiply them, there is no path to the sink state
    # we use phi1 and phi2 using solvers to know which transitions are used in the two fsms
    # we shall use create_automata_from_phi and multiply_fsm.
    M1 = create_automata_from_phi(M, phi_M1)
    M2 = create_automata_from_phi(M, phi_M2)
    M1_M2 = multiply_fsm(M1, M2)

    sink_M1_M2 = M1_M2.getSinkState()
    paths_to_sink = find_paths_from_initial(sink_M1_M2, M1_M2)

    return (len(paths_to_sink) == 0,paths_to_sink)
    
def delete_transitions(fsm, transitions_to_delete):
    fsm_copy = deepcopy(fsm)
    transitions = list(fsm_copy.getTransitions())  # Make a copy of the transitions
    for transition in transitions:
        if transition.getTransitionSymbol() in transitions_to_delete:
            fsm_copy.removeTransition(transition)
    return fsm_copy

def determine_Mx_y(M, phi):
    models = get_all_models(phi)
    transitions__symbols = set()
    valid_transitions__symbols = set()
    for transition in M.getTransitions():
        symbol = transition.getTransitionSymbol()  
        transitions__symbols.add(symbol)
    # si var est vrai dans au moins un modèle, alors la transition est valide
    for model in models:
        for transition in transitions__symbols:
            if model[transition].is_true():
                valid_transitions__symbols.add(transition)
    invalid_transitions_symbols = transitions__symbols - valid_transitions__symbols
    
    # Create a new model Mx_y by deleting the invalid transitions from M
    Mx_y = delete_transitions(M, invalid_transitions_symbols)
    return Mx_y
def verify_test_adequacy_for_mining(M : FSM, phiM : FNode, TS : list, S : FSM):

    def at_least_two_non_equivalent_DFSMs(M : FSM,phi : FNode):

        solutions = get_all_models(phi)
        if len(solutions) < 2:
            return False
        for i in range(len(solutions)):
            for j in range(i + 1, len(solutions)):
                if not are_equivalent(M,solutions[i], solutions[j])[0]:
                    return True
        return False
    
    # find a minimal distinguishing test for two non equivalent DFSMs
    def minimal_distinguishing_test_for_two_non_equivalent_DFSMs(M : FSM,phi : FNode):
        solutions = get_all_models(phi)
        if len(solutions) < 2:
            return False, None
        return_value = False
        all_tests = []
        for i in range(len(solutions)):
            for j in range(i + 1, len(solutions)):
                equivalency_test = are_equivalent(M, solutions[i], solutions[j])
                if not equivalency_test[0]: # [Ø] car are_equivalent renvoie un tuple
                    # on a trouvé deux modèles non équivalents
                    return_value = True
                    all_tests.extend(equivalency_test[1])
        shortest_test = None
        if len(all_tests)>0:
            shortest_test = min(all_tests, key=len)
        return return_value, shortest_test

    
    # recupere tous les modèles (toutes les combinaisons de transitions en PySMT) qui satisfont la formule (automate non deterministe)

    def deterministic_executions_producing_y_on_test_x(all_executions : list, y):
        symbols = set()
        valid_execution = None
        if len(y) != 1:
            print("Error : y is not a single execution")
        execution_y = y.pop()
        # pour toutes les executions non deterministes de M
        for execution_all in all_executions:
            valid = True
            if (len(execution_all)!=len(execution_y)):
                print("Error : the test is not long enough to produce the output y")
            for i in range (len(execution_all)):
                input_all, output_all, transition_symbol_all = execution_all[i]
                input_y, output_y, transition_symbol = execution_y[i]
                if not(input_all == input_y and output_all == output_y and transition_symbol_all == transition_symbol):
                    valid = False
            if valid:
                valid_execution = execution_all

        for _, _, transition_symbol in valid_execution:
            symbols.add(transition_symbol)
        
        # Return the symbols using And logic if more than one symbol is found
        if len(symbols) > 1:
            return And(*symbols)
        elif len(symbols) == 1:
            return next(iter(symbols))
        else:
            return None

    phi = phiM
    verdict = True if not at_least_two_non_equivalent_DFSMs(M,phi) else False

    xd = None
    while TS and not verdict:
        x = TS.pop()  # Sélectionne et supprime un test de TS
        # on execute l'automate M sur le test x
        YMx = M.deterministic_executions(x)
        # on simule l'automate S sur le test x 
        # TODO: remplacer ça par une question à l'utilisateur
        y = S.deterministic_executions(x) 
        Exy = deterministic_executions_producing_y_on_test_x(YMx, y)

        # if Exy is a Fnode print something
        phi = And(phi, Exy) 
        M = determine_Mx_y(M, phi)
        test = minimal_distinguishing_test_for_two_non_equivalent_DFSMs(M, phi)
        if test[0]:
            xd = test[1]
        else: # pas de test minimal trouvé
            verdict = True
    return verdict, M, phi, xd

''' --------------------------------- mining oracle --------------------------------- '''
def precise_oracle_mining(M: FSM, TS: list, S : FSM):
    phiM = encode_deterministic_fsm(M)
    TSm = TS.copy()
    verdict, M_prime, phi_prime, xd = verify_test_adequacy_for_mining(M, phiM, TS, S)
    while verdict == False:
        TSm.append(xd)
        phiM = phi_prime
        M = M_prime
        TS = [xd]
        verdict, M_prime, phi_prime, xd = verify_test_adequacy_for_mining(M, phiM, TS, S)

    P = create_automata_from_phi(M, phi_prime)

    return TSm, P

''' --------------------------------- compare_automatas ---------------------------------'''
# are_equivalent function use phi which is a description of the automatas transitions
# however we can't use it because the transitions names is not consistent throughout the automatas rafinement
# so we need to compare the automatas by their transitions one by one

def compare_automatas(M : FSM, P : FSM) -> bool:
    def simplify_automata(M : FSM):
        # the automatas are deterministic 
        # however, there can be multiple transitions with the same target and output from the same source
        # we need to simplify the automata by merging these transitions
        # we can do this by creating a new automata with the same states and transitions

        grouped_transitions = {}
        for transition in M.getTransitions():
            key = (transition.getSrcState().getID(), transition.getTgtState().getID(), transition.getOutput())
            if key not in grouped_transitions:
                grouped_transitions[key] = []
            grouped_transitions[key].append(transition)

        # Iterate over grouped transitions and merge them if needed
        for transitions in grouped_transitions.values():
            if len(transitions) > 1:  # Multiple transitions with same source, target, and output
                src_state = transitions[0].getSrcState()
                tgt_state = transitions[0].getTgtState()
                output = transitions[0].getOutput()

                merged_input = Or(*[transition.getInput() for transition in transitions])

                # Remove original transitions
                for transition in transitions:
                    M.removeTransition(transition)

                # Add new merged transition
                M.addTransition(src_state.getID(), tgt_state.getID(), merged_input, output)
    #simplify_automata(M)
    #simplify_automata(P)
    # TODO: compare the automatas
    # we start from the init state for both automatas
    # we check if there is a transition with the same output and with and equivalent (Iff) input
    # if there is, since the automatas are deterministic, we can go to the accessible states and check if they are equivalent
    # return whether all accessible states are equivalent
    queue = deque([(M.getInitialState(), P.getInitialState())])

    visited = set()

    while queue:
        state_m, state_p = queue.popleft()

        if (state_m, state_p) in visited:
            continue

        visited.add((state_m, state_p))

        transitions_m = state_m.getOutTransitions()
        transitions_p = state_p.getOutTransitions()

        if len(transitions_m) != len(transitions_p):
            return False  # Different number of transitions, automatas are not equivalent

        for transition_m in transitions_m:
            matched = False
            for transition_p in transitions_p:
                if (transition_m.getOutput() == transition_p.getOutput() and
                        is_sat(Iff(transition_m.getInput(), transition_p.getInput()))):

                    # Enqueue the target states for further comparison
                    queue.append((transition_m.getTgtState(), transition_p.getTgtState()))
                    matched = True
                    break
            if not matched:
                print("No matching transition found for transition", transition_m)
                return False  # No matching transition found, automatas are not equivalent

    return True  # All corresponding states and transitions matched, automatas are equivalent



if __name__ == '__main__':
    non_deterministic_fsm = fromDot("./first_snippets/data/fsm4.dot")
    # pour tous les états de l'automate imprimer les transitions sortantes
    expected_fsm = fromDot("./first_snippets/data/fsm4_expected.dot")
    symbol_a = Symbol("a", BOOL)
    symbol_b = Symbol("b", BOOL)
    # first_test should be baa each letter should be coded as a conjonction b & !a or !b & a
    first_test = [[And(symbol_b, Not(symbol_a)), And(Not(symbol_b), symbol_a),And(Not(symbol_b), symbol_a)]]
    # first_test = [[symbol_a]]
    mined_automata = precise_oracle_mining(non_deterministic_fsm, first_test, expected_fsm)
    new_fsm = mined_automata[1]
    # enregister dans le fichier tmp.dot
    print(new_fsm.toDot())
    with open("tmp.dot", "w") as file:
        file.write(new_fsm.toDot())
    print(expected_fsm.toDot())
    print(new_fsm.toDot())
    print(compare_automatas(expected_fsm, new_fsm))

    
    
