from state import State
from transition import Transition
import pygraphviz as pgv
import filecomparator
from pysmt.shortcuts import Symbol, Bool, Int, And, Or, Not, Implies, Iff, GT, LT, GE, LE
from pysmt.shortcuts import simplify
from pysmt.fnode import FNode


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

def simplify_fsm(fsm):
    def is_subsumed(cond1, cond2):
        return set(cond1.split(' & ')).issubset(set(cond2.split(' & ')))

    for state in fsm.getStates():
        out_transitions = state.getOutTransitions()
        for transition in out_transitions[:]:
            for other_transition in out_transitions:
                if transition != other_transition and transition.getTgtState() == other_transition.getTgtState():
                    if is_subsumed(transition.getInput(), other_transition.getInput()):
                        fsm.removeTransition(transition)
                        break


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



from collections import defaultdict
from collections import defaultdict

from collections import defaultdict

def encode_xi_T(state):
    # Group transitions by their input
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

                # Construct (¬tk∨ ¬tj) for each pair
                terms.append(Or(Not(Symbol(f't_{t_k.getID()}')), Not(Symbol(f't_{t_j.getID()}'))))

        # Create a CNF formula for this input
        if terms:
            # We should flatly add symbols and terms into And function
            cnf_formula = And(Or(*(Symbol(f't_{t_k.getID()}') for t_k in input_transitions)), *terms)
        else:
            cnf_formula = And(*(Symbol(f't_{t_k.getID()}') for t_k in input_transitions))
        cnf_formulas.append(cnf_formula)
        
        # Print the state, input and the generated condition
        print(f"encode_xi_T of state {state.getLabel()} with input {input_value} gives the conditions {cnf_formula}")

    # Create a conjunction of all CNF formulas
    xi_T = And(*cnf_formulas)
    return xi_T

def encode_deterministic_fsm(fsm):
    states = fsm.getStates()
    phi_M = And(*[encode_xi_T(state) for state in states])
    return phi_M



if __name__ == '__main__':
    fsm = fromDot("./first_snippets/data/fsm4.dot")
    print("encode_deterministic_fsm returns",encode_deterministic_fsm(fsm))


'''
if __name__ == '__main__':
   fsm1 = fromDot("./first_snippets/data/fsm1.dot")
   fsm2 = fromDot("./first_snippets/data/fsm2.dot")
   new_fsm = multiply_fsm(fsm1, fsm2)
   print(new_fsm.toDot())
   print(encode_deterministic_fsm(new_fsm))
'''
'''
# test for fromDot and toDot
if __name__ == '__main__' :
   # gen fsm from ./data/exemple1/fsm.dot
   fsm = fromDot("./data/exemple1/fsm.dot")
   # save fsm in tmp.dot
   dot_content = fsm.toDot()
   dot_content = dot_content.replace("('", "")
   dot_content = dot_content.replace("')", "")
   dot_content = dot_content.replace("'","")

   with open("./tmp.dot", "w") as f:
      f.write(dot_content)


   # compare tmp.dot and ./data/exemple1/fsm.dot
   print(filecomparator.compare_files("./tmp.dot", "./data/exemple1/fsm.dot"))

'''