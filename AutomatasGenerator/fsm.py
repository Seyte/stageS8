from state import State
from transition import Transition
import pygraphviz as pgv
import filecomparator
from pysmt.shortcuts import Symbol, Bool, Int, And, Or, Not, Implies, Iff, GT, LT, GE, LE, simplify, Solver, get_model, is_sat, is_unsat
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
   
   
   def getInitialSate(self) -> State :
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

   def deterministic_executions(self, input_symbols):
        # Start with the initial state, the given sequence of input symbols, and an empty list of previous outputs
        queue = deque([(self._initial, input_symbols, [])])
        final_outputs = set()

        while queue:
            current_state, remaining_inputs, previous_outputs = queue.popleft()

            if not remaining_inputs:  # No more input symbols, so collect the output
                final_outputs.add(tuple(previous_outputs))  # Store the sequence of outputs
            else:
                current_input = remaining_inputs[0]  # Take the first input symbol
                next_inputs = remaining_inputs[1:]   # Remaining input symbols

                # Find the transitions corresponding to the current input symbol
                matching_transitions = [t for t in current_state.getOutTransitions() if is_sat(And(t.getInput(), current_input))]

                for transition in matching_transitions:
                    next_state = transition.getTgtState()
                    next_outputs = previous_outputs + [transition.getOutput()]  # Concatenate the current output with previous ones
                    queue.append((next_state, next_inputs, next_outputs))  # Continue exploring with the next state and remaining inputs

        return final_outputs






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
                terms.append(Or(Not(Symbol(f't_{t_k.getID()}')), Not(Symbol(f't_{t_j.getID()}'))))

        # create a CNF formula for this input
        if terms:
            cnf_formula = And(Or(*(Symbol(f't_{t_k.getID()}') for t_k in input_transitions)), *terms)
        else:
            cnf_formula = And(*(Symbol(f't_{t_k.getID()}') for t_k in input_transitions))
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

# recupere tous les modèles (toutes les combinaisons de transitions) qui satisfont la formule (automate non deterministe)
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

# are two fsm pysmt description equivalent?
def are_equivalent(phi_M1, phi_M2):
    equivalence_formula = And(phi_M1, phi_M2)
    
    # Use a solver to check if the formula is satisfiable
    with Solver() as solver:
        solver.add_assertion(equivalence_formula)
        return solver.solve()

def verify_test_adequacy_for_mining(M, phiM, TS, S):
    def at_least_two_non_equivalent_DFSMs(phi):
        # Énumérez toutes les solutions de l'encodage booléen phi
        solutions = get_all_models(phi)
        
        # Si le nombre de solutions est inférieur à 2, alors phi ne sélectionne pas au moins deux DFSMs non équivalents
        if len(solutions) < 2:
            return False

        # Sinon, vérifiez si au moins deux des solutions sont non équivalentes
        for i in range(len(solutions)):
            for j in range(i + 1, len(solutions)):
                if not are_equivalent(solutions[i], solutions[j]):
                    return True
        return False

    def encode_DFSMs_in_M_producing_y_on_test_x(Exy, y):
        # Cette fonction devrait retourner l'encodage boolean des DFSMs dans M qui produisent y sur le test x
        pass

    def minimal_distinguishing_test_for_two_non_equivalent_DFSMs():
        # Cette fonction devrait retourner un test minimal qui distingue deux DFSM non équivalents
        pass

    phi = phiM
    verdict = True if not at_least_two_non_equivalent_DFSMs(phi) else False
    while TS and not verdict:
        x = TS.pop()  # Sélectionne et supprime un test de TS
        # on execute l'automate M sur le test x
        YMx = M.deterministic_executions(x)  # Remplacez ceci par l'appel de fonction réel
        # on simule l'automate S sur le test x
        y = S.emulate(x)  # Remplacez ceci par l'appel de fonction réel
        Exy = M.deterministic_executions_producing_y_on_test_x(y, x)  # Remplacez ceci par l'appel de fonction réel
        phi = And(phi, encode_DFSMs_in_M_producing_y_on_test_x(Exy, y))  # Remplacez ceci par l'appel de fonction réel
        M = Mx_y  # Vous avez besoin d'une fonction pour déterminer Mx/y
        if at_least_two_non_equivalent_DFSMs(phi):
            xd = minimal_distinguishing_test_for_two_non_equivalent_DFSMs()  # Remplacez ceci par l'appel de fonction réel
        else:
            verdict = True
    return verdict, M, phi, xd



if __name__ == '__main__':
    fsm = fromDot("./first_snippets/data/fsm4.dot")
    encoding = encode_deterministic_fsm(fsm)
    print("encode_deterministic_fsm returns",encoding)
    models = get_all_models(encoding)
    print ("get_all_models returns", models)
