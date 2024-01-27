from variable import Variable

class TreeNode:
    def __init__(self, type, parent = None, children = []):
        self.type = type
        self.children = children
        self.parent = parent

    def clone(self, parent, varDict = {}):
        node = TreeNode(self.type, parent)
        clonedChildren = []
        for child in self.children:
            clonedChildren.append(child.clone(node, varDict))
        node.children = clonedChildren
        return node
    
    def delete(self):
        for child in self.children:
            child.delete()

    def replaceChild(self, oldChild, newChild):
        for i in range(len(self.children)):
            child = self.children[i]
            if child == oldChild:
                self.children[i] = newChild
                return
        raise Exception("Replace Child Failure - Child Not Found")
    
    def replace(self, newNode):
        if self.parent == None:
            newNode.parent = None
        else:
            self.parent.replaceChild(self, newNode)

    def simplify(self):
        # Boolean Operators
        if self.type == "NOT":
            child = self.children[0]
            if child.type == "NOT":
                child.children[0].parent = self.parent
                self.replace(child.children[0])
                return child.children[0]
            if child.type == "TOP":
                botNode = TreeNode("BOT", self.parent)
                self.replace(botNode)
                return botNode
            if child.type == "BOT":
                topNode = TreeNode("TOP", self.parent)
                self.replace(topNode)
                return topNode
            if child.type == "EXISTS":
                child.type = "FORALL"
                child.parent = self.parent
                self.replace(child)
                return child
            if child.type == "FORALL":
                child.type = "EXISTS"
                child.parent = self.parent
                self.replace(child)
                return child

        if self.type == "AND":
            child1 = self.children[0]
            child2 = self.children[1]
            if child1.type == "BOT":
                child2.delete()
                botNode = TreeNode("BOT", self.parent)
                self.replace(botNode)
                return botNode
            
            if child2.type == "BOT":
                child1.delete()
                botNode = TreeNode("BOT", self.parent)
                self.replace(botNode)
                return botNode
                 
            if child1.type == "TOP":
                child2.parent = self.parent
                self.replace(child2)  
                return child2
            
            if child2.type == "TOP":
                child1.parent = self.parent
                self.replace(child1)
                return child1
                
            if child1.type == "EXISTS" or child1.type == "FORALL":
                child1.parent = self.parent
                self.children[0] = child1.children
                child1.children = [self]
                self.replace(child1)
                return child1
            
            if child2.type == "EXISTS" or child2.type == "FORALL":
                child2.parent = self.parent
                self.children[1] = child2.children
                child2.children = [self]
                self.replace(child2)
                return child2
        
        # LT and DIV nodes are handled by their respective classes

    def normalizeRec(self, replacementDict = {}):
        for child in self.children:
            replacementDict = child.normalizeRec(replacementDict)
        
        return self.normalize(replacementDict)

    def normalize(self, replacementDict):
        # REPLACEMENTS

        if self.type == "GT":
            ltNode = TreeNode("LT", self.parent, self.children[::-1])
            for child in self.children:
                child.parent = ltNode
            self.replace(ltNode)
            return ltNode.normalize(replacementDict)
        
        if self.type == "GTE":
            ltNode = TreeNode("LT", children=self.children)
            for child in self.children:
                child.parent = ltNode
            notNode = TreeNode("NOT", self.parent, [ltNode])
            ltNode.parent = notNode
            self.replace(notNode)
            replacementDict = ltNode.normalize(replacementDict)
            return notNode.normalize(replacementDict)
        
        if self.type == "LTE":
            ltNode = TreeNode("LT", children=self.children[::-1])
            for child in self.children:
                child.parent = ltNode
            notNode = TreeNode("NOT", self.parent, [ltNode])
            ltNode.parent = notNode
            self.replace(notNode)
            replacementDict = ltNode.normalize(replacementDict)
            return notNode.normalize(replacementDict)
        
        if self.type == "NEQ" or self.type == "EQ":
            clonedChildren = []
            for child in self.children:
                clonedChildren.append(child.clone())
            ltNode1 = TreeNode("LT", children=self.children[::-1])
            for child in self.children:
                child.parent = ltNode1
            ltNode2 = TreeNode("LT", children=clonedChildren)
            for child in ltNode2.children:
                child.parent = ltNode2
            orNode = TreeNode("OR", children=[ltNode1, ltNode2])
            ltNode1.parent = orNode
            ltNode2.parent = orNode
            if self.type == "NEQ":
                orNode.parent = self.parent
                self.replace(orNode)
            else:
                notNode = TreeNode("NOT", self.parent, [orNode])
                orNode.parent = notNode
                self.replace(notNode)
            replacementDict = ltNode1.normalize(replacementDict)
            replacementDict = ltNode2.normalize(replacementDict)
            replacementDict = orNode.normalize(replacementDict)
            if self.type == "EQ":
                return notNode.normalize(replacementDict)
            return replacementDict
    
        if self.type == "OR":
            notNode1 = TreeNode("NOT", children=[self.children[0]])
            self.children[0].parent = notNode1
            notNode2 = TreeNode("NOT", children=[self.children[1]])
            self.children[0].parent = notNode2
            andNode = TreeNode("AND", children=[notNode1, notNode2])
            notNode1.parent = andNode
            notNode2.parent = andNode
            notNode3 = TreeNode("NOT", self.parent, [andNode])
            andNode.parent = notNode3
            self.replace(notNode3)
            replacementDict = notNode1.normalize(replacementDict)
            replacementDict = notNode2.normalize(replacementDict)
            replacementDict = andNode.normalize(replacementDict)
            return notNode3.normalize(replacementDict)
        
        if self.type == "IMP":
            notNode = TreeNode("NOT", children=[self.children[1]])
            self.children[1].parent = notNode
            orNode = TreeNode("OR", self.parent, [self.children[0], notNode])
            self.children[0].parent = orNode
            notNode.parent = orNode
            self.parent.replaceChild(self. orNode)
            replacementDict = notNode.normalize(replacementDict)
            return orNode.normalize(replacementDict)
        
        if self.type == "DIMP":
            clonedChildren = []
            for child in self.children:
                clonedChildren.append(child.clone())
            impNode1 = TreeNode("IMP", children=self.children[::-1])
            for child in self.children:
                child.parent = impNode1
            impNode2 = TreeNode("IMP", children=clonedChildren)
            for child in clonedChildren:
                child.parent = impNode2
            andNode = TreeNode("AND", self.parent, [impNode1, impNode2])
            impNode1.parent = andNode
            impNode2.parent = andNode
            self.replace(andNode)
            replacementDict = impNode1.normalize(replacementDict)
            replacementDict = impNode2.normalize(replacementDict)
            return andNode.normalize(replacementDict)
        
        # TERMS

        if self.type == "PLUS":
            child1 = self.children[0]
            child2 = self.children[1]
            if child1.type == "INT" and child2.type == "INT":
                intNode = IntegerNode(child1.int+child2.int, parent=self.parent)
                self.replace(intNode)
                return replacementDict
            
            if child1.type == "INT":
                child2.constant += child1.int
                child2.parent = self.parent
                self.replace(child2)
                return replacementDict
            
            child1.parent = self.parent
            self.replace(child1)

            if child2.type == "INT":
                child1.constant += child2.int
            else:
                child1.add(child2)

            return replacementDict
        
        if self.type == "MIN":
            child2 = self.children[1]
            if child2.type == "INT":
                child2.int = -child2.int
            else:
                # child2.type == TERM
                child2.negate()
            
            plusNode = TreeNode("PLUS", self.parent, [self.children[0], child2])
            self.replace(plusNode)
            return plusNode.normalize(replacementDict)
        
        if self.type == "UMIN":
            child = self.children[0]
            if child.type == "INT":
                child.int = -child.int
            else:
                # child.type == TERM
                child.negate
            child.parent = self.parent
            self.replace(child)
            return replacementDict

        if self.type == "MUL":
            child1 = self.children[0]
            child2 = self.children[1]
            if child1.type != "INT":
                raise Exception("Bad Formula - Non-Constant Multiplication")
            
            child2.parent = self.parent
            self.replace(child2)

            if child2.type == "INT":
                child2.int *= child1.int
            else:
                # child2.type == TERM
                child2.multiply(child1.int)

            return replacementDict
        
        if self.type == "POW":
            child = self.children[0]
            if child.type == "INT":
                child.int = 2**abs(child.int)
                child.parent = self.parent
                self.replace(child)
                return replacementDict
            
            # child.type == TERM
            if child.isVariable():
                variable = list(child.linearDict.keys())[0]
                termNode = makePower(variable, self.parent)
                child.delete()
                self.replace(termNode)
                return replacementDict
            
            # need to replace 2^t with 2^n for new n
            # pass the replacement up to the first non-term node (i.e. comparison or divisibility constraint)
            child.delete()

            varObj = None
            for term in replacementDict.keys():
                if child.equiv(term):
                    varObj = replacementDict[term]
            
            if varObj == None:
                varObj = Variable("n")
                replacementDict[child] = varObj

            node = makePower(varObj, self.parent)
            self.replace(node)
            return replacementDict

        # replace LT and DIV nodes with their classes
        if self.type == "LT":
            child1 = self.children[0]
            child2 = self.children[1]
            if child1.type == "INT" and child2.type == "INT":
                if child1.int < child2.int:
                    topNode = TreeNode("TOP", self.parent)
                    self.replace(topNode)
                    return replacementDict
                botNode = TreeNode("BOT", self.parent)
                self.replace(botNode)
                return replacementDict
            if child2.type == "INT":
                # child1.type == TERM
                child1.constant -= child2.int
                ltNode = LTNode(parent=self.parent, children=[child1])
                child1.parent = ltNode
            else:
                # child2.type == TERM
                child2.negate()
                if child1.type == "INT":
                    child2.constant += child1.int
                    ltNode = LTNode(parent=self.parent, children=[child2])
                    child2.parent = ltNode
                else:
                    ltNode = LTNode(parent = self.parent, children=[child1])
                    child1.parent = ltNode
                    child1.add(child2)
            self.replace(ltNode)
            ltNode.simplify()
            return replacementDict
        
        if self.type == "DIV":
            child1 = self.children[0]
            child2 = self.children[1]
            assert(child1.type == "INT")
            divNode = DivisibilityNode(child1.int, parent=self.parent, children=[child2])
            child2.parent = divNode
            self.replace(divNode)
            divNode.simplify()
            return replacementDict

        self.simplify()

        return replacementDict
    
    def addReplacements(self, replacementDict):
        if self.type == "FORALL" or self.type == "EXISTS" or self.type == "ROOT":
            return self.children[0].addReplacements(replacementDict)
        
        eqNodes = []
        existsNodes = []
        
        for term in replacementDict.keys():
            varObj = replacementDict[term]

            if varObj.numVariables() == 0:
                # variable was deleted in the formula (through simplification)
                # don't need to do anything
                continue

            varNode = makeVariable(varObj)
            eqNode = TreeNode("EQ", children=[varNode, term])
            varNode.parent = eqNode
            term.parent = eqNode
            eqNodes.append(eqNode)
            
            existsNode = QuantifierNode("EXISTS", varObj)
            varObj.quant = existsNode
            existsNodes.append(existsNode)

        if len(existsNodes) == 0:
            # no variables needed to be added, so nothing needs to be done
            return
        
        existsNode = existsNodes[0]
        existsNode.parent = self.parent
        self.replace(existsNode)

        currentParent = existsNode
        for existsNode in existsNodes[1:]:
            existsNode.parent = currentParent
            currentParent.children = [existsNode]
            currentParent = existsNode

        # len(eqNodes) == len(existsNodes), so len(eqNodes) > 0
        eqNode = eqNodes[0]
        andNode = TreeNode("AND", currentParent, [eqNode])
        currentParent.children = [andNode]
        eqNode.parent = andNode
        eqNode.normalize({})

        for eqNode in eqNodes[1:]:
            newAnd = TreeNode("AND", andNode, [eqNode])
            andNode.children.append(newAnd)
            eqNode.parent = newAnd
            eqNode.normalize({})
            andNode = newAnd

        andNode.children.append(self)
        self.parent = andNode

    def __repr__(self):
        if self.type == "ROOT":
            return str(self.children[0])
        
        if self.children == []:
            return self.type

        return self.type + ": " + str(self.children)
    
class QuantifierNode(TreeNode):
    def __init__(self, type, variable, parent = None, children = []):
        assert(type == "EXISTS" or type == "FORALL")
        super().__init__(type, parent, children)
        self.variable = variable

    def clone(self, parent, varDict = {}):
        varObj = Variable(self.variable.ident)
        varDict[self.variable] = varObj
        quantNode = QuantifierNode(self.type, varObj, parent)
        childClone = self.children[0].clone(quantNode, varDict)
        quantNode.children = [childClone]
        varObj.quant = quantNode
        return quantNode
    
    def delete(self):
        super().delete()
        self.variable.quant = None
    
    def __repr__(self):
        return self.type + "-" + self.variable.ident + ":" + str(self.children)

class IntegerNode(TreeNode):
    def __init__(self, int, type = "INT", parent = None, children = []):
        assert(children == [] and type == "INT")
        super().__init__("INT", parent)
        self.int = int

    def clone(self, parent, varDict = {}):
        return IntegerNode(self.int, "INT", parent, [])
    
    def modulus(self, divisor):
        while (self.int < 0):
            self.int += divisor

        while (self.int >= divisor):
            self.int -= divisor
    
    def __repr__(self):
        return "INT:" + str(self.int)
    
class DivisibilityNode(TreeNode):
    def __init__(self, divisor, type = "DIV", parent = None, children = []):
        assert(type == "DIV")
        super().__init__("DIV", parent, children)
        self.divisor = divisor

    def simplify(self):
        term = self.children[0]
        if self.divisor < 0:
            self.divisor = -self.divisor
        
        term.modulus(self.divisor)

        topNode = TreeNode("TOP", self.parent)
        botNode = TreeNode("BOT", self.parent)
        if self.divisor == 1:
            term.delete()
            self.replace(topNode)
        elif term.type == "INT":
            if term.int % self.divisor == 0:
                self.replace(topNode)
            else:
                self.replace(botNode)

    def clone(self, parent, varDict = {}):
        divNode = DivisibilityNode(self.divisor, parent=parent)
        term = self.children[0].clone(divNode, varDict)
        divNode.children = [term]
        return divNode
    
    def __repr__(self):
        return str(self.divisor) + " | " + str(self.children[0])

class LTNode(TreeNode):
    def __init__(self, type = "LT", parent = None, children = []):
        assert(type == "LT")
        super().__init__("LT", parent, children)

    def simplify(self):
        topNode = TreeNode("TOP", self.parent)
        botNode = TreeNode("BOT", self.parent)
        term = self.children[0]
        if term.type == "INT":
            if term.int < 0:
                self.replace(topNode)
            else:
                self.replace(botNode)
        elif term.isPositive():
            term.delete()
            self.replace(botNode)
        elif term.isNegative():
            term.delete()
            self.replace(topNode)

    def clone(self, parent, varDict = {}):
        ltNode = LTNode("LT", parent)
        term = self.children[0].clone(ltNode, varDict)
        ltNode.children = [term]
        return ltNode
    
    def __repr__(self):
        return str(self.children[0]) + " < 0"
    
class TermNode(TreeNode):
    def __init__(self, type = "TERM", parent = None, children = []):
        assert(type == "TERM" and children == [])
        super().__init__(type, parent, children)
        self.linearDict = {}
        self.powerDict = {}
        self.constant = 0

    def clone(self, parent, varDict = {}):
        newTerm = TermNode("TERM", parent)
        newLinear = {}
        for variable in self.linearDict.keys():
            if variable in varDict.keys():
                newLinear[varDict[variable]] = self.linearDict[variable]
                varDict[variable].linearTerms.append(newTerm)
            else:
                newLinear[variable] = self.linearDict[variable]
                variable.linearTerms.append(newTerm)
        newTerm.linearDict = newLinear
        
        newPower = {}
        for variable in self.powerDict.keys():
            if variable in varDict.keys():
                newPower[varDict[variable]] = self.powerDict[variable]
                varDict[variable].powerTerms.append(newTerm)
            else:
                newPower[variable] = self.powerDict[variable]
                variable.powerTerms.append(newTerm)
        newTerm.powerDict = newPower

        newTerm.constant = self.constant

        return newTerm
    
    def delete(self):
        for variable in self.linearDict.keys():
            variable.linearTerms.remove(self)
        
        for variable in self.powerDict.keys():
            variable.powerTerms.remove(self)

    def negate(self):
        for variable in self.linearDict.keys():
            self.linearDict[variable] = -self.linearDict[variable]

        for variable in self.powerDict.keys():
            self.powerDict[variable] = -self.powerDict[variable]
        
        self.constant = -self.constant

    def add(self, otherTerm):
        # remove the variables pointers to the other term
        otherTerm.delete()

        for variable in otherTerm.linearDict:
            if variable in self.linearDict.keys():
                sum = self.linearDict[variable] + otherTerm.linearDict[variable]
                if sum != 0:
                    self.linearDict[variable] = sum
                else:
                    variable.linearTerms.remove(self)
                    del self.linearDict[variable]
            else:
                self.linearDict[variable] = otherTerm.linearDict[variable]
                variable.linearTerms.append(self)
        
        for variable in otherTerm.powerDict:
            if variable in self.powerDict.keys():
                sum = self.powerDict[variable] + otherTerm.powerDict[variable]
                if sum != 0:
                    self.powerDict[variable] = sum
                else:
                    variable.powerDict.remove(self)
                    del self.powerDict[variable]
            else:
                self.powerDict[variable] = otherTerm.powerDict[variable]
                variable.powerTerms.append(self)

        self.constant = self.constant + otherTerm.constant

        if self.linearDict == {} and self.powerDict == {}:
            # need to replace with an integer
            integerNode = IntegerNode(self.constant, parent=self.parent)
            self.replace(integerNode)

    def multiply(self, constant):
        if constant == 0:
            intNode = IntegerNode(0, parent=self.parent)
            self.delete()
            self.replace(intNode)
        else:
            for variable in self.linearDict.keys():
                self.linearDict[variable] = self.linearDict[variable]*constant

            for variable in self.powerDict.keys():
                self.powerDict[variable] = self.powerDict[variable]*constant
            
            self.constant *= constant

    def modulus(self, divisor):
        for variable in self.linearDict.keys():
            while self.linearDict[variable] < 0:
                self.linearDict[variable] += divisor

            while self.linearDict[variable] >= divisor:
                self.linearDict[variable] -= divisor
            
            if self.linearDict[variable] == 0:
                variable.linearTerms.remove(self)
                del self.linearDict[variable]

        for variable in self.powerDict.keys():
            while self.powerDict[variable] < 0:
                self.powerDict[variable] += divisor
            
            while self.powerDict[variable] >= divisor:
                self.powerDict[variable] -= divisor

            if self.powerDict[variable] == 0:
                variable.powerTerms.remove(self)
                del self.powerDict[variable]

        while self.constant < 0:
            self.constant += divisor
        
        while self.constant >= divisor:
            self.constant -= divisor

        if len(self.linearDict) == 0 and len(self.powerDict) == 0:
            intNode = IntegerNode(self.constant, parent=self.parent)
            self.replace(intNode)

    def isVariable(self):
        if len(self.linearDict) != 1:
            return False

        variable = list(self.linearDict.keys())[0]
        if self.linearDict[variable] != 1 and self.linearDict[variable] != -1:
            return False
        
        return len(self.powerDict) == 0 and self.constant == 0
    
    def isPositive(self):
        if len(self.linearDict) != 0:
            return False
        
        minValue = self.constant

        for variable in self.powerDict.keys():
            coefficient = self.powerDict[variable]
            if coefficient < 0:
                return False
            else:
                # minimum value for the term is increased by the coefficient
                # as 2^|x| >= 1
                minValue += coefficient

        return minValue > 0
        
    def isNegative(self):
        if len(self.linearDict) != 0:
            return False
        
        maxValue = self.constant

        for variable in self.powerDict.keys():
            coefficient = self.powerDict[variable]
            if coefficient > 0:
                return False
            else:
                # max value for the term reduced by coefficient (which is negative)
                # as 2^|x| >= 1
                maxValue += coefficient

        return maxValue < 0
    
    def equiv(self, otherTerm):
        for variable in self.linearDict.keys():
            if variable not in otherTerm.linearDict.keys():
                return False
            
            if otherTerm.linearDict[variable] != self.linearDict[variable]:
                return False
            
        for variable in self.powerDict.keys():
            if variable not in otherTerm.powerDict.keys():
                return False
            
            if otherTerm.powerDict[variable] != self.powerDict[variable]:
                return False
            
        return self.constant == otherTerm.constant

    def __repr__(self):
        linearPairs = []
        for variable in self.linearDict.keys():
            if self.linearDict[variable] == 1:
                linearPairs.append(variable.ident)
            elif self.linearDict[variable] == -1:
                linearPairs.append("-" + variable.ident)
            else:
                linearPairs.append(str(self.linearDict[variable]) + "." + variable.ident)
        
        powerPairs = []
        for variable in self.powerDict.keys():
            if self.powerDict[variable] == 1:
                powerPairs.append("2^(" + variable.ident + ")")
            elif self.powerDict[variable] == -1:
                powerPairs.append("-2^(" + variable.ident + ")")
            else:
                powerPairs.append(str(self.powerDict[variable]) + ".2^(" + variable.ident + ")")

        strRep = " + ".join(linearPairs)
        if strRep != "" and powerPairs != []:
            strRep += " + "
        strRep += " + ".join(powerPairs)
        if self.constant != 0:
            strRep += " + " + str(self.constant)

        return strRep

def makeVariable(variable, parent = None):
    termNode = TermNode(parent = parent)
    termNode.linearDict[variable] = 1
    variable.linearTerms.append(termNode)
    return termNode

def makePower(variable, parent = None):
    termNode = TermNode(parent = parent)
    termNode.powerDict[variable] = 1
    variable.powerTerms.append(termNode)
    return termNode

def convertTokenTree(tokenTree, variableDict = {}, parent = None):
    basicConversions = {
        "POW": ("POW", 1),
        "+": ("PLUS", 2),
        ".": ("MUL", 2),
        "<": ("LT", 2),
        ">": ("GT", 2),
        "<=": ("LTE", 2),
        ">=": ("GTE", 2),
        "==": ("EQ", 2),
        "!=": ("NEQ", 2),
        "DIV": ("DIV", 2),
        "TOP": ("TOP", 0),
        "BOT": ("BOT", 0),
        "AND": ("AND", 2),
        "OR": ("OR", 2),
        "->": ("IMP", 2),
        "<->": ("DIMP", 2),
        "¬": ("NOT", 1),
    }

    newVarDict = variableDict.copy()

    if tokenTree.type == "EXISTS" or tokenTree.type == "FORALL":
        assert(len(tokenTree.children) == 1)
        varToken = tokenTree.value
        varIdent = varToken.value
        varObj = Variable(varIdent)
        newVarDict[varIdent] = varObj

        node = QuantifierNode(tokenTree.type, varObj)
        varObj.quant = node
    elif tokenTree.type == "VAR":
        assert(tokenTree.children == [])
        ident = tokenTree.value
        if ident in variableDict.keys():
            return makeVariable(variableDict[ident])
        raise Exception("Bad Formula - Free Variable " + ident)
    elif tokenTree.type == "INT":
        assert(tokenTree.children == [])
        return IntegerNode(int(tokenTree.value))
    elif tokenTree.type == "-":
        assert(len(tokenTree.children) == 1 or len(tokenTree.children) == 2)
        if len(tokenTree.children) == 1:
            node = TreeNode("UMIN")
        else:
            node = TreeNode("MIN")
    else:
        assert(tokenTree.type in basicConversions.keys())
        (nodeType, numChildren) = basicConversions[tokenTree.type]
        assert(len(tokenTree.children) == numChildren)
        node = TreeNode(nodeType)

    node.parent = parent

    children = []
    for child in tokenTree.children:
        children.append(convertTokenTree(child, newVarDict, node))

    node.children = children

    if parent == None:
        rootNode = TreeNode("ROOT", children=[node])
        node.parent = rootNode
        return rootNode
    
    return node

formula = "EXISTS x EXISTS y -2.POW(x) < POW(y)"
from parsing import getTokenTree
tokenTree = getTokenTree(formula)
print(tokenTree)
formulaTree = convertTokenTree(tokenTree)
print(formulaTree)
replacementDict = formulaTree.normalizeRec()
print(formulaTree)
print(replacementDict)
formulaTree.addReplacements(replacementDict)
print(formulaTree)