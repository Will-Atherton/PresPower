import random

class Variable:
    def __init__(self, ident, quant = None):
        self.ident = ident + str(random.randint(1, 99))
        self.quant = quant
        self.linearTerms = []
        self.powerTerms = []
    
    def numVariables(self):
        return len(self.linearTerms) + len(self.powerTerms)
    
    def __repr__(self):
        return self.ident