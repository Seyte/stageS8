import random
from transition import Transition
class State :
   def __init__(self, label=None, id = -1, accepting=False):
      self._label = label
      self._id = -1
      self._accepting=accepting
      self._outTr = {}
      self._inTr = {}

   def setID(self, id) :
      self._id = id

   def getID(self) :
      return self._id
   
   def getLabel(self) :
      return self._label 
   
   def isAccepting(self) :
      return self._accepting
   
   def addOutTr(self, transition:Transition) :
      if not(transition.getInput() in self._outTr.keys()) :
         self._outTr[transition.getInput()] = {}
      if not(transition.getOutput() in self._outTr[transition.getInput()].keys()) :
         self._outTr[transition.getInput()][transition.getOutput()] = []
      self._outTr[transition.getInput()][transition.getOutput()].append(transition)
   
   def addInTr(self, transition:Transition) :
      if not(transition.getInput() in self._inTr.keys()) :
         self._inTr[transition.getInput()] = {}
      if not(transition.getOutput() in self._inTr[transition.getInput()].keys()) :
         self._inTr[transition.getInput()][transition.getOutput()] = []
      self._inTr[transition.getInput()][transition.getOutput()].append(transition)
   
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
      return  label in self._outTr.keys()

