import random
from transition import Transition

class State :
   def __init__(self, label=None, id = -1, accepting=False):
      self._label = label
      self._id = -1
      self._accepting=accepting
      self._outTr = [] # Changed to a list
      self._inTr = []  # Changed to a list

   def setID(self, id) :
      self._id = id

   def getID(self) :
      return self._id
   
   def getLabel(self) :
      return self._label 
   
   def isAccepting(self) :
      return self._accepting
   
   def addOutTr(self, transition:Transition) :
      self._outTr.append({"input": transition.getInput(), "output": transition.getOutput(), "transition": transition})

   def addInTr(self, transition:Transition) :
      self._inTr.append({"input": transition.getInput(), "output": transition.getOutput(), "transition": transition})

   def __str__(self) :
      if (self.isAccepting()) :
         return  f'c{self._label}[{self._id}]'
      else :
         return  f'f{self._label}[{self._id}]'
   
   def toDot(self) :
      if (self.isAccepting()) :
         return f's_{self._id} [label="{self._label}" shape="square"]'
      else : 
         return f's_{self._id} [label="{self._label}" shape="circle"]'
      
   def toNL(self) :
      descCandidate = [f"state {self._label}",f"{self._label}"]
      rst = random.choice(descCandidate)
      return rst
   
   def defineTransitionOn(self, label):
      return any(tr["input"] == label for tr in self._outTr)

   def removeOutTr(self, transition:Transition):
      self._outTr = [tr for tr in self._outTr if tr["transition"] != transition]

   def removeInTr(self, transition:Transition):
      self._inTr = [tr for tr in self._inTr if tr["transition"] != transition]


   def getOutTransitions(self):
       return [tr["transition"] for tr in self._outTr]

   def getInTransitions(self):
       return [tr["transition"] for tr in self._inTr]