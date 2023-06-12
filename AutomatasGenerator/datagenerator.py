import os
import random
from fsm import FSM
from state import State


def buildExampleFsm() -> FSM :
   fsm = FSM()
   states=[State(0), State(1), State(2), State(3)]
   for state in states :
      fsm.addState(state)
   fsm.addTransition(0, 1, "b", "0")
   fsm.addTransition(0, 0, "a", "0")
   fsm.addTransition(1, 2, "a", "0")
   fsm.addTransition(1, 1, "b", "0")
   fsm.addTransition(2, 3, "b", "0")
   fsm.addTransition(2, 2, "a", "0")
   fsm.addTransition(3, 0, "a", "1")
   fsm.addTransition(3, 3, "b", "0")


   return fsm

def fsmRandomGenInputComplete(nbStates =2,inputAlphabet =['a','b','c'], outputAlphabet =[0,1,2]) -> FSM :
    fsm = FSM()
    maxNbTransition = nbStates *  len(inputAlphabet)
    stateIds = [i for i in range(0,nbStates)]
    for i in stateIds :
      fsm.addState(State(i))
    fin = (fsm.nbTransitions()>=maxNbTransition) 
    while not(fin) :
        idSrcState = random.choice(stateIds)
        idTgtState = random.choice(stateIds)
        input = random.choice(inputAlphabet)
        if not (fsm.getState(idSrcState).defineTransitionOn(input)):
            output = random.choice(outputAlphabet)
            tr = fsm.addTransition(idSrcState,idTgtState,input,output)
            print(tr.toDot()) 
        fin = (fsm.nbTransitions()>=maxNbTransition)  
    return fsm  
    




if __name__ == '__main__' :
   #cwd = os.getcwd()  # Get the current working directory (cwd)
   #files = os.listdir(cwd)  # Get all the files in that directory
   #print("Files in %r: %s" % (cwd, files))
    #buildExampleFsm()
   
   for k in range(1, 10):
      #nbState = random.randrange(6,15)
      nbState = 3
      fsm = fsmRandomGenInputComplete(nbState)
      os.makedirs(f"./data/exemple{k}",exist_ok=True)
      f = open(f"./data/exemple{k}/fsm.dot", "w")
      f.write(fsm.toDot())
      f.close()
      for i in range(1,10) :
          r= open(f"./data/exemple{k}/requirement{i}.txt", "w")
          r.write(fsm.toNL())
          r.close()
   
def generate_files(nbState,nbExamples,nbRequirements):
      for k in range(1, nbExamples + 1):
        fsm = fsmRandomGenInputComplete(nbState)
        os.makedirs(f"./data/exemple{k}",exist_ok=True)
        f = open(f"./data/exemple{k}/fsm.dot", "w")
        f.write(fsm.toDot())
        f.close()
        for i in range(1,nbRequirements + 1) :
            r= open(f"./data/exemple{k}/requirement{i}.txt", "w")
            r.write(fsm.toNL())
            r.close()