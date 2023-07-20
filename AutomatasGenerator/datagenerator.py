import os
import random
from fsm import FSM
from state import State


def generate_comparison(inputAlphabetInt):
    input_variable = random.choice(inputAlphabetInt)
    remaining_vars = [v for v in inputAlphabetInt if v != input_variable]
    input_value = str(random.randint(0, 10)) if len(remaining_vars) == 0 or random.choice(['integer', 'variable']) == 'integer' else random.choice(remaining_vars)
    operator = random.choice(['>', '<', '>=', '<='])
    input = input_variable.strip() + operator.strip() + input_value.strip()
    return input

def fsmRandomGenInputComplete(nbStates=2, inputAlphabet=['a', 'b', 'c'], outputAlphabet=[0, 1, 2]) -> FSM:
    fsm = FSM()
    maxNbTransition = nbStates * len(inputAlphabet)
    stateIds = [i for i in range(0, nbStates)]
    for i in stateIds:
        fsm.addState(State(i))

    # Split the input alphabet into two halves.
    inputAlphabetBool = inputAlphabet[:len(inputAlphabet) // 2]
    inputAlphabetInt = inputAlphabet[len(inputAlphabet) // 2:]

    # Generate transitions
    fin = (fsm.nbTransitions() >= maxNbTransition)
    while not(fin):
        idSrcState = random.choice(stateIds)
        idTgtState = random.choice(stateIds)
        
        # Choose randomly between a single comparison/boolean and a list.
        choice = random.choice(['comparison', 'boolean', 'list'])
        if choice == 'comparison':
            input = generate_comparison(inputAlphabetInt)
            # Include negation one third of the time
            if random.choices([True, False], [1, 2])[0]:
                input = '!' + input
        elif choice == 'boolean':
            input = random.choice(inputAlphabetBool)
            # Include negation one third of the time
            if random.choices([True, False], [1, 2])[0]:
                input = '!' + input
        elif choice == 'list':
            nb_elements = random.randint(1, 5)  # Choose a random number of elements for the list
            input = []
            for _ in range(nb_elements):
                if random.choice(['boolean', 'comparison']) == 'boolean':
                    element = random.choice(inputAlphabetBool)
                else:
                    element = generate_comparison(inputAlphabetInt)
                # Include negation one third of the time
                if random.choices([True, False], [1, 2])[0]:
                    element = '!' + element
                input.append(element)

        if not (fsm.getState(idSrcState).defineTransitionOn(input)):
            output = random.choice(outputAlphabet)
            tr = fsm.addTransition(idSrcState,idTgtState,input,output)
            #print(tr.toDot()) 
        fin = (fsm.nbTransitions()>=maxNbTransition)  
    return fsm



if __name__ == '__main__' :
   #cwd = os.getcwd()  # Get the current working directory (cwd)
   #files = os.listdir(cwd)  # Get all the files in that directory
   #print("Files in %r: %s" % (cwd, files))
    #buildExampleFsm()
   alphabet = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i']
   for k in range(1, 10):
      #nbState = random.randrange(6,15)
      nbState = 5
      fsm = fsmRandomGenInputComplete(nbState, alphabet)
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