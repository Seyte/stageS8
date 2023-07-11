from state import State
from transition import Transition
import pygraphviz as pgv
import filecomparator
from pysmt.shortcuts import Symbol, Bool, Int, And, Or, Not, Implies, Iff, GT, LT, GE, LE

class FSM :
   def __init__(self, initState=None, data=None) :
      self._initial = initState
      self._states = []
      self._statesById = dict() 
      self._inputSet =set()
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
         self._inputSet.add(tuple(input))

         self._outputSet.add(output)
         return transition
      return None

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

def multiply_fsm(fsm1, fsm2):
    new_fsm = FSM()
    state_dict = {}

    for state1 in fsm1.getStates():
        for state2 in fsm2.getStates():
            new_label = state1.getLabel() + "-" + state2.getLabel()
            new_state = State(new_label)
            new_fsm.addState(new_state)
            state_dict[new_label] = new_state
            
    for transition1 in fsm1.getTransitions():
        for transition2 in fsm2.getTransitions():
            src_label = transition1.getSrcState().getLabel() + "-" + transition2.getSrcState().getLabel()
            tgt_label = transition1.getTgtState().getLabel() + "-" + transition2.getTgtState().getLabel()

            # Retrieve the new states from the state_dict
            src_state = state_dict[src_label]
            tgt_state = state_dict[tgt_label]
            input = str(transition1.getInput())
            input = input.replace("('", "")
            input = input.replace("')", "")
            input = input.replace("'","")
            print("source=",src_state.getID())
            print("target=",tgt_state.getID())
            print("input=",input)
            print("output=",transition1.getOutput())
            new_fsm.addTransition(src_state.getID(), tgt_state.getID(),input,str(transition1.getOutput()))

    return new_fsm




if __name__ == '__main__':
   fsm1 = fromDot("./data/exemple1/fsm.dot")
   fsm2 = fromDot("./data/exemple2/fsm.dot")
   new_fsm = multiply_fsm(fsm1, fsm2)
   print(new_fsm.toDot())
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