import random
from pysmt.shortcuts import Symbol, And, Not, GT, LT, GE, LE, Int, BOOL, INT, get_free_variables, Or
from pysmt.fnode import FNode
import state

        
class Transition :
    def __init__(self, src, tgt, input=None, output=None, id=-1) -> None:
        self._src = src 
        self._tgt = tgt 
        self._symbol_list = []
        self._input = self.parse_input(input)
        self._output = output
        self._id = id

    def parse_input(self, input):
        def clean_symbol(symbol):
            symbol = symbol.strip()  # remove leading and trailing spaces
            symbol = symbol.replace('\'', '')  # remove single quotes
            symbol = symbol.replace('(', '')  # remove left parentheses
            symbol = symbol.replace(')', '')  # remove right parentheses
            symbol = symbol.replace('=', '')  # remove equal sign
            symbol = symbol.replace(' ', '')  # remove spaces
            return symbol
        
        def parse_condition(input):
            input = input.strip()
            input = clean_symbol(input)            
            if '&' in input:
                return And([parse(i) for i in input.split('&')])
            if '|' in input:
                return Or([parse(i) for i in input.split('|')])
            # Check for negation at the start of the string
            if input.startswith('!'):
                return Not(parse(input[1:].strip()))

            # The input is a single symbol (boolean)
            else:
                return Symbol(input, BOOL)
        
        def parse_inequality(input):
            operators = ['>=', '<=', '>', '<']
            op = next((x for x in operators if x in input), None)
            if op is not None:
                x, y = map(str.strip, input.split(op))
                if x.isdigit():
                    x = Int(int(x))
                else:
                    x = Symbol(clean_symbol(x), INT)
                
                if y.isdigit():
                    y = Int(int(y))
                else:
                    y = Symbol(clean_symbol(y), INT)
                
                if op == '>':
                    return GT(x, y)
                elif op == '<':
                    return LT(x, y)
                elif op == '>=':
                    return GE(x, y)
                elif op == '<=':
                    return LE(x, y)
            else:
                raise ValueError(f"Unknown operator in: {input}")

        def parse(input):
            # si c'est un object de pysmt (FNode) on le garde tel quel
            if isinstance(input, FNode):
                return input
            
            if isinstance(input, list):
                # Handles the list of strings case and constructs a conjunction
                return And([parse(i) for i in input])
            elif isinstance(input, str):
                if any(op in input for op in ['!', '&', '|']):
                    return parse_condition(input)
                if any(op in input for op in ['>', '<', '>=', '<=']):
                    return parse_inequality(input)
                elif input.isdigit():
                    return Int(int(input))
                else:
                    return Symbol(clean_symbol(input), BOOL)
            else:
                raise ValueError(f"Unknown input: {input}")

        return parse(input)

    def print_symbol_types(self):
        free_vars = get_free_variables(self._input)
        for var in free_vars:
            print(f"Symbol: {var}, Type: {var.get_type()}")

        
    def setID(self, id) :
      self._id = id

    def getID(self) :
      return self._id
    
    def getInput(self) :
       return self._input
    
    def getTransitionSymbol(self) :
         return Symbol(f"t_{self.getID()}", BOOL)
    
    def getOutput(self) :
       return self._output
    
    def __str__(self) -> str:
        rst = "\n\t" + f"s_{self._src.getID()} -> s_{self._tgt.getID()}"
        rst+= f'[label="{self._input}/{self._output}"]'
        return rst
    
    def toDot(self) -> str :
        rst = "\n\t" + f"s_{self._src.getID()} -> s_{self._tgt.getID()}"
        rst += f'[label="{self._input}/{self._output}", myattribute= "t_{self.getID()}"]'
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
