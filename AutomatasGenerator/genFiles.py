
import os
from fsm import FSM
from state import State
from datagenerator import fsmRandomGenInputComplete
NB_STATE = 10
NB_AUTOMATES_PER_STATE = 100
# On génère des automates de 1 à NB_STATE états
for state in range (1,NB_STATE+1):
    for automata in range (NB_AUTOMATES_PER_STATE):
        fsm = fsmRandomGenInputComplete(state)
        dot = fsm.toDot()
        NL = fsm.toNL()
        # On crée le dossier s'il n'existe pas
        if not os.path.exists("./data"):
            os.makedirs("./data")
        # on save le fichier dot
        with open("./data/automata_"+str(state)+"_"+str(automata)+".dot", "w") as file:
            file.write(dot)
        # on save le fichier NL
        with open("./data/automata_"+str(state)+"_"+str(automata)+".txt", "w") as file:
            file.write(NL)
