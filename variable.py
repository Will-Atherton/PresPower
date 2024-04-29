class Variable:
    def __init__(self, ident, quant = None):
        #self.originalIdent = ident
        self.originalVariable = self
        #self.ident = globals.getNextIdent(ident)
        self.ident = ident
        self.quant = quant
        self.linearTerms = []
        self.powerTerms = []
    
    def numVariables(self):
        return len(self.linearTerms) + len(self.powerTerms)
    
    def clone(self):
        #varObj = Variable(self.originalIdent, self.quant)
        varObj = Variable(self.ident, self.quant)
        varObj.originalVariable = self.originalVariable
        return varObj

    def equiv(self, otherVar):
        return self.originalVariable == otherVar.originalVariable
    
    def resetTerms(self):
        self.linearTerms = []
        self.powerTerms = []
    
    def __repr__(self):
        return self.ident