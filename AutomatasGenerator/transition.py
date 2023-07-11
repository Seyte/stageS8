import random
from pysmt.shortcuts import Symbol, Bool, Int, And, Or, Not, Implies, Iff, GT, LT, GE, LE
import state

class Transition :
    def __init__(self, src, tgt, input=None, output=None, id=-1) -> None:
        self._src = src 
        self._tgt = tgt 
        self._input = self.parse_input(input)
        self._output = output
        self._id = id
        
    def parse_input(self, input):
        if isinstance(input, list):
            # Handles the list of strings case and constructs a conjunction
            return And([self.parse_input(i) for i in input])
        elif isinstance(input, str):
            if '&' in input:
                # If input contains '&', split it and parse each condition separately
                return And([self.parse_input(i) for i in input.split('&')])
            input = input.strip()
            if ' ' in input:
                x, op, y = input.split(' ')
                if op == '>':
                    return GT(self.parse_input(x), self.parse_input(y))
                elif op == '<':
                    return LT(self.parse_input(x), self.parse_input(y))
                elif op == '>=':
                    return GE(self.parse_input(x), self.parse_input(y))
                elif op == '<=':
                    return LE(self.parse_input(x), self.parse_input(y))
                else:
                    raise ValueError(f"Unknown operator: {op}")
            elif input.isdigit():
                return Int(int(input))
            else:
                return Symbol(input)
        else:
            raise ValueError(f"Unknown input: {input}")


        
    def setID(self, id) :
      self._id = id

    def getID(self) :
      return self._id
    
    def getInput(self) :
       return self._input
    
    def getOutput(self) :
       return self._output
    
    def __str__(self) -> str:
        rst = "\n\t" + f"s_{self._src.getID()} -> s_{self._tgt.getID()}"
        rst+= f'[label="{self._input}/{self._output}"]'
        return rst
    
    def toDot(self) -> str :
        rst = "\n\t" + f"s_{self._src.getID()} -> s_{self._tgt.getID()}"
        rst += f'[label="{self._input}/{self._output}"]'
        return rst
    
    def toNL(self) -> str :
       liste = [f"{self._fromtoNL()} {self._outputtoNL()} and {self._movetoNL()} {self._inputtoNL()}", 
                f"{self._outputtoNL()} and {self._movetoNL()} {self._inputtoNL()} {self._fromtoNL()}"]
       rst = random.choice(liste)
       return rst
    
    def _systemtoNL(self) ->str :
       liste = ["it", "the system", "the application"]
       rst = random.choice(liste)
       return rst
    
    def _fromtoNL(self) -> str :
        liste = [f"from {self._src.toNL()}",
                 f"from state {self._src.toNL()}",
                 f"in state {self._src.toNL()}",
                 f"in  {self._src.toNL()}",
                 f"when the system is in {self._src.toNL()}",
                 f"when it is in {self._src.toNL()}"]
        rst = random.choice(liste)
        return rst
    
    def _movetoNL(self) -> str :
        liste = [f"{self._systemtoNL()} moves to {self._tgt.toNL()}",
                 f"{self._systemtoNL()} reaches {self._tgt.toNL()}",
                 f"{self._tgt.toNL()} is reached"]
        rst = random.choice(liste)
        return rst
    
    def _inputtoNL(self) -> str :
        liste= [f"if the input is {self._input}",
                f"if the input {self._input} occurs",
                f"if  {self._input} occurs",
                f"on occurence of input {self._input}",
                f"on occurence of {self._input}"]
        rst = random.choice(liste)
        return rst
    
    def _outputtoNL(self) -> str :
        liste= [f"{self._systemtoNL()} produces {self._output}",
                f"{self._systemtoNL()} returns {self._output}",
                f", {self._output} is produced",
                f"the output {self._output} is produced",
                f", {self._output} is returned"]
        rst = random.choice(liste)
        return rst
    

    def getSrcState(self):
        return self._src

    def getTgtState(self):
        return self._tgt
