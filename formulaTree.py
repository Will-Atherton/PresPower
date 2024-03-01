from variable import Variable
import math

class TreeNode:
    def __init__(self, type, parent = None, children = None):
        self.type = type

        # python doesn't like empty list defaults for class instantiation
        if children == None:
            self.children = []
        else:
            self.children = children

        self.parent = parent

    def clone(self, parent = None, varDict = {}, varReplace = None, formReplace = None):
        if formReplace != None:
            # replace if equivalent to a formula here
            for form in formReplace.keys():
                if self.equiv(form):
                    # replace with replacement
                    node = formReplace[form]
                    node.parent = parent
                    return (node, varDict)
        
        node = TreeNode(self.type, parent)
        clonedChildren = []
        for child in self.children:
            (childClone, varDict) = child.clone(node, varDict, varReplace, formReplace)
            clonedChildren.append(childClone)
        node.children = clonedChildren
        return (node, varDict)
    
    def equiv(self, otherNode):
        if self.type != otherNode.type:
            return False
        
        if len(self.children) != len(otherNode.children):
            return False

        for i in range(len(self.children)):
            if not self.children[i].equiv(otherNode.children[i]):
                return False
        
        return True
    
    def delete(self):
        for child in self.children:
            child.delete()

    def remove(self, node):
        if self == node:
            # needs to have exactly on child
            assert(len(self.children) == 1)
            self.replace(self.children[0])
        else:
            for child in self.children:
                child.remove(node)

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
            newNode.parent = self.parent

    def getLowestQuant(self):
        if self.type != "EXISTS" and self.type != "FORALL":
            return None
        
        if self.children[0].type != "EXISTS" and self.children[0].type != "FORALL":
            return self
        
        return self.children[0].getLowestQuant()
    
    def getNonSimple(self):
        nonSimples = []
        for child in self.children:
            nonSimples += child.getNonSimple()

        return nonSimples
    
    def getLinAndMod(self):
        maxLin = 2
        mod = 1
        for child in self.children:
            (cMaxLin, cMod) = child.getLinAndMod()
            if cMaxLin > maxLin:
                maxLin = cMaxLin
            
            mod = math.lcm(mod, cMod)
        
        return (maxLin, mod)
    
    def setVariablePointers(self, vList):
        for child in self.children:
            child.setVariablePointers(vList)

    def simplifyRec(self):
        for child in self.children:
            child.simplifyRec()

        return self.simplify()

    def simplify(self):
        # Boolean Operators
        if self.type == "NOT":
            child = self.children[0]
            if child.type == "NOT":
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
            
        if self.type == "AND":
            newChildren = []
            for child in self.children:
                if child.type == "BOT":
                    # BOT AND x = BOT
                    botNode = TreeNode("BOT", self.parent)
                    self.replace(botNode)
                    self.delete()
                    return botNode
                
                if child.type == "TOP":
                    # TOP AND x = x
                    # just don't add to newChildren
                    continue

                if child.type == "AND":
                    # combine the ANDs
                    newChildren += child.children
                    for newChild in child.children:
                        newChild.parent = self
                    continue

                # otherwise just keep the child
                newChildren.append(child)

            # if no children, replace with top
            if len(newChildren) == 0:
                topNode = TreeNode("TOP", self.parent)
                self.replace(topNode)
                
                # remove variable pointers to other children
                self.delete()
                return topNode
            
            # if 1 child, replace with child
            if len(newChildren) == 1:
                self.replace(newChildren[0])
                return newChildren[0]
            
            self.children = newChildren
            return self
        
        if self.type == "OR":
            newChildren = []
            for child in self.children:
                if child.type == "TOP":
                    # TOP OR x = TOP
                    topNode = TreeNode("TOP", self.parent)

                    self.replace(topNode)

                    # remove variable pointers to other children
                    self.delete()
                    return topNode
                
                if child.type == "BOT":
                    # BOT OR x = x
                    # just don't add to newChildren
                    continue

                if child.type == "OR":
                    # combine the ORs
                    newChildren += child.children
                    for newChild in child.children:
                        newChild.parent = self
                    continue

                # otherwise just keep the child
                newChildren.append(child)

            # if no children, replace with bot
            if len(newChildren) == 0:
                botNode = TreeNode("BOT", self.parent)
                self.replace(botNode)
                self.delete()
                return botNode
            
            # if 1 child, replace with child
            if len(newChildren) == 1:
                self.replace(newChildren[0])
                return newChildren[0]
            
            self.children = newChildren
            return self

        # LT and DIV nodes are handled by their respective classes
            
        return self

    def normalizeRec(self, replacementDict = {}):
        for child in self.children:
            (_, replacementDict) = child.normalizeRec(replacementDict)
        
        return self.normalize(replacementDict)

    def normalize(self, replacementDict = {}):
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
            (_, replacementDict) = ltNode.normalize(replacementDict)
            return notNode.normalize(replacementDict)
        
        if self.type == "LTE":
            ltNode = TreeNode("LT", children=self.children[::-1])
            for child in self.children:
                child.parent = ltNode
            notNode = TreeNode("NOT", self.parent, [ltNode])
            ltNode.parent = notNode
            self.replace(notNode)
            (_, replacementDict) = ltNode.normalize(replacementDict)
            return notNode.normalize(replacementDict)
        
        if self.type == "NEQ" or self.type == "EQ":
            ltNode1 = TreeNode("LT")
            clonedChildren = []
            for child in self.children:
                (childClone, _) = child.clone(ltNode1)
                clonedChildren.append(childClone)
            ltNode1.children = clonedChildren
            ltNode2 = TreeNode("LT", children=self.children[::-1])
            for child in self.children:
                child.parent = ltNode2
            orNode = TreeNode("OR", children=[ltNode1, ltNode2])
            ltNode1.parent = orNode
            ltNode2.parent = orNode
            if self.type == "NEQ":
                self.replace(orNode)
            else:
                notNode = TreeNode("NOT", self.parent, [orNode])
                orNode.parent = notNode
                self.replace(notNode)
            (_, replacementDict) = ltNode1.normalize(replacementDict)
            (_, replacementDict) = ltNode2.normalize(replacementDict)
            (orNode, replacementDict) = orNode.normalize(replacementDict)
            if self.type == "EQ":
                return notNode.normalize(replacementDict)
            return (orNode, replacementDict)
    
        if self.type == "IMP":
            notNode = TreeNode("NOT", children=[self.children[0]])
            self.children[0].parent = notNode
            orNode = TreeNode("OR", self.parent, [notNode, self.children[1]])
            self.children[1].parent = orNode
            notNode.parent = orNode
            self.parent.replaceChild(self, orNode)
            (_, replacementDict) = notNode.normalize(replacementDict)
            return orNode.normalize(replacementDict)
        
        if self.type == "DIMP":
            impNode1 = TreeNode("IMP")
            clonedChildren = []
            for child in self.children:
                (childClone, _) = child.clone(impNode1)
                clonedChildren.append(childClone)
            impNode1.children = clonedChildren
            impNode2 = TreeNode("IMP", children=self.children[::-1])
            for child in self.children:
                child.parent = impNode2
            andNode = TreeNode("AND", self.parent, [impNode1, impNode2])
            impNode1.parent = andNode
            impNode2.parent = andNode
            self.replace(andNode)
            (_, replacementDict) = impNode1.normalize(replacementDict)
            (_, replacementDict) = impNode2.normalize(replacementDict)
            return andNode.normalize(replacementDict)
        
        # TERMS

        if self.type == "PLUS":

            child1 = self.children[0]
            child2 = self.children[1]
            child1.add(child2)
            
            self.replace(child1)

            return (child1, replacementDict)
        
        if self.type == "MIN":
            child2 = self.children[1]
            child2.negate()
            
            plusNode = TreeNode("PLUS", self.parent, [self.children[0], child2])
            self.replace(plusNode)
            return plusNode.normalize(replacementDict)
        
        if self.type == "UMIN":
            child = self.children[0]
            child.negate()
            self.replace(child)
            return (child, replacementDict)

        if self.type == "MUL":
            child1 = self.children[0]
            child2 = self.children[1]
            if not child1.isInteger():
                raise Exception("Bad Formula - Non-Constant Multiplication")
            
            self.replace(child2)

            child2.multiply(child1.constant)

            return (child2, replacementDict)
        
        if self.type == "POW":
            child = self.children[0]
            if child.isInteger():
                child.constant = 2**abs(child.constant)
                self.replace(child)
                return (child, replacementDict)
            
            # child.type == TERM
            if child.isVariable():
                variable = list(child.linearDict.keys())[0]
                termNode = makePower(variable, self.parent)
                child.delete()
                self.replace(termNode)
                return (termNode, replacementDict)
            
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
            return (node, replacementDict)

        # replace LT and DIV nodes with their classes
        if self.type == "LT":
            child1 = self.children[0]
            child2 = self.children[1]
            child2.negate()
            child1.add(child2)
            ltNode = LTNode(children=[child1])
            child1.parent = ltNode
            self.replace(ltNode)
            ltNode = ltNode.simplify()
            return (ltNode, replacementDict)
        
        if self.type == "DIV":
            child1 = self.children[0]
            child2 = self.children[1]
            assert(child1.isInteger)
            divNode = DivisibilityNode(child1.constant, children=[child2])
            child2.parent = divNode
            self.replace(divNode)
            divNode = divNode.simplify()
            return (divNode, replacementDict)


        # Boolean Operators - push quantifiers up
        if self.type == "NOT":
            child = self.children[0]
            if child.type == "EXISTS":
                child.type = "FORALL"
                self.replace(child)
                return (child, replacementDict)
            if child.type == "FORALL":
                child.type = "EXISTS"
                self.replace(child)
                return (child, replacementDict)

    
        if self.type == "AND" or self.type == "OR":
            for i in range(len(self.children)):
                child = self.children[i]
                if child.type == "EXISTS" or child.type == "FORALL":
                    self.children[i] = child.children[0]
                    child.children = [self]
                    self.replace(child)
                    self.simplify()
                    return (child, replacementDict)    

        self = self.simplify()

        return (self, replacementDict)
    
    def addReplacements(self, replacementDict):
        if self.type == "FORALL" or self.type == "EXISTS":
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
        eqNode.normalize()

        for eqNode in eqNodes[1:]:
            newAnd = TreeNode("AND", andNode, [eqNode])
            andNode.children.append(newAnd)
            eqNode.parent = newAnd
            eqNode.normalize()
            andNode = newAnd

        andNode.children.append(self)
        self.parent = andNode

    def __repr__(self):
        if self.children == []:
            return self.type

        return self.type + ": " + str(self.children)
    
class QuantifierNode(TreeNode):
    def __init__(self, type, variable, parent = None, children = None):
        assert(type == "EXISTS" or type == "FORALL")
        super().__init__(type, parent, children)
        self.variable = variable

    def normalize(self, replacementDict = {}):
        # need to define this to do nothing, so it doesn't call normalize on TreeNode
        return (self, replacementDict)

    def clone(self, parent = None, varDict = {}, varReplace = None, formReplace = None):
        if formReplace != None:
            # replace if equivalent to a formula here
            for form in formReplace.keys():
                if self.equiv(form):
                    # replace with replacement
                    node = formReplace[form]
                    node.parent = parent
                    return (node, varDict)
        
        varObj = self.variable.clone()
        varDict[self.variable] = varObj
        quantNode = QuantifierNode(self.type, varObj, parent)
        (childClone, varDict) = self.children[0].clone(quantNode, varDict, varReplace, formReplace)
        quantNode.children = [childClone]
        varObj.quant = quantNode
        return (quantNode, varDict)
    
    def equiv(self, otherNode):
        if not super().equiv(otherNode):
            return False
        
        return self.variable.equiv(otherNode.variable)

    def delete(self):
        super().delete()
        self.variable.quant = None
    
    def __repr__(self):
        return self.type + "-" + self.variable.ident + ":" + str(self.children)

class DivisibilityNode(TreeNode):
    def __init__(self, divisor, type = "DIV", parent = None, children = None):
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

        term = self.children[0]
        if self.divisor == 1:
            term.delete()
            self.replace(topNode)
            return topNode
        
        if term.isInteger():
            if term.constant % self.divisor == 0:
                self.replace(topNode)
                return topNode
            else:
                self.replace(botNode)
                return botNode

        return self
    
    def normalize(self, replacementDict = {}):
        # need to define this to do nothing, so it doesn't call normalize on TreeNode
        return (self, replacementDict)

    def clone(self, parent = None, varDict = {}, varReplace = None, formReplace = None):
        if formReplace != None:
            # replace if equivalent to a formula here
            for form in formReplace.keys():
                if self.equiv(form):
                    # replace with replacement
                    node = formReplace[form]
                    node.parent = parent
                    return (node, varDict)

        divNode = DivisibilityNode(self.divisor, parent=parent)
        (term, multiplier) = self.children[0].clone(divNode, varDict, varReplace, formReplace)
        divNode.children = [term]
        divNode.divisor *= multiplier
        return (divNode, varDict)
    
    def equiv(self, otherNode):
        if not super().equiv(otherNode):
            return False
        
        return self.divisor == otherNode.divisor
    
    def getNonSimple(self):
        if self.isSimple():
            return []
        
        return [self]

    def isSimple(self):
        term = self.children[0]
        if len(term.linearDict) + len(term.powerDict) != 1:
            return False
        
        for var in term.linearDict.keys():
            return term.linearDict[var] == 1
            
        for var in term.powerDict.keys():
            return term.powerDict[var] == 1

    def getLinAndMod(self):
        maxLin = self.children[0].getMax()
        if maxLin < 2:
            maxLin = 2
        mod = self.divisor
        return (maxLin, mod)

    def __repr__(self):
        return str(self.divisor) + " | " + str(self.children[0])

class LTNode(TreeNode):
    def __init__(self, type = "LT", parent = None, children = None):
        assert(type == "LT")
        super().__init__("LT", parent, children)

    def simplify(self):
        topNode = TreeNode("TOP", self.parent)
        botNode = TreeNode("BOT", self.parent)
        term = self.children[0]
        term.simplifyComp()
        if term.isInteger():
            if term.constant < 0:
                self.replace(topNode)
                return topNode
            else:
                self.replace(botNode)
                return botNode
            
        if term.isPositive():
            term.delete()
            self.replace(botNode)
            return botNode
        
        if term.isNegative():
            term.delete()
            self.replace(topNode)
            return topNode
        
    def normalize(self, replacementDict = {}):
        # need to define this to do nothing, so it doesn't call normalize on TreeNode
        return (self, replacementDict)

    def clone(self, parent = None, varDict = {}, varReplace = None, formReplace = None):
        if formReplace != None:
            # replace if equivalent to a formula here
            for form in formReplace.keys():
                if self.equiv(form):
                    # replace with replacement
                    node = formReplace[form]
                    node.parent = parent
                    return (node, varDict)

        ltNode = LTNode("LT", parent)
        (term, _) = self.children[0].clone(ltNode, varDict, varReplace, formReplace)
        ltNode.children = [term]
        return (ltNode, varDict)

    def getLinAndMod(self):
        maxLin = self.children[0].getMax()
        if maxLin < 2:
            maxLin = 2
        return (maxLin, 1)
    
    def inPowCmp(self):
        term = self.children[0]
        if len(term.linearDict) != 0:
            return False
        
        if len(term.powerDict) > 2:
            return False
        
        if len(term.powerDict) == 2 and term.constant != 0:
            return False
        
        return True
    
    def __repr__(self):
        return str(self.children[0]) + " < 0"
    
class TermNode(TreeNode):
    def __init__(self, type = "TERM", parent = None, children = None):
        assert(type == "TERM" and children == None)
        super().__init__(type, parent, children)
        self.linearDict = {}
        self.powerDict = {}
        self.lambdaDict = {}
        self.constant = 0

    def clone(self, parent = None, varDict = {}, varReplace = None, formReplace = None):
        newTerm = TermNode("TERM", parent)
        newLinear = {}
        termsToAdd = []
        multiplier = 1
        for variable in self.linearDict.keys():
            if (varReplace != None and ("linear", variable) in varReplace.keys()):
                (replacement, mult) = varReplace[("linear", variable)]
                termsToAdd.append((replacement, self.linearDict[variable]))
                multiplier *= mult
            else:
                if variable in varDict.keys():
                    newLinear[varDict[variable]] = self.linearDict[variable]
                    varDict[variable].linearTerms.append(newTerm)
                else:
                    newLinear[variable] = self.linearDict[variable]
                    variable.linearTerms.append(newTerm)
        newTerm.linearDict = newLinear
        
        newPower = {}
        for variable in self.powerDict.keys():
            if (varReplace != None and ("power", variable) in varReplace.keys()):
                (replacement, mult) = varReplace[("power", variable)]
                termsToAdd.append((replacement, self.powerDict[variable]))
                multiplier *= mult
            else:
                if variable in varDict.keys():
                    newPower[varDict[variable]] = self.powerDict[variable]
                    varDict[variable].powerTerms.append(newTerm)
                else:
                    newPower[variable] = self.powerDict[variable]
                    variable.powerTerms.append(newTerm)
        newTerm.powerDict = newPower

        newLambda = {}
        for sig in self.lambdaDict.keys():
            foundRep = False
            if varReplace != None:
                # check if need to replace
                for (typ, toRep) in varReplace.keys():
                    if typ == "lambda" and sig.equiv(toRep):
                        (replacement, mult) = varReplace[("lambda", toRep)]
                        termsToAdd.append((replacement, self.lambdaDict[sig]))
                        multiplier *= mult
                        foundRep = True
                        break
            if not foundRep:
                newLambda[sig] = self.lambdaDict[sig]
        newTerm.lambdaDict = newLambda

        newTerm.constant += self.constant

        if multiplier != 1:
            newTerm.multiply(multiplier)


        for (term, mult) in termsToAdd:
            # clone the term
            (tClone, _) = term.clone(varDict = varDict)
            tClone.multiply(mult)
            newTerm.add(tClone)

        return (newTerm, multiplier)
    
    def split(self, varList):
        yesTerm = TermNode()
        noTerm = TermNode()

        for variable in self.linearDict.keys():
            if variable in varList:
                yesTerm.linearDict[variable] = self.linearDict[variable]
            else:
                noTerm.linearDict[variable] = self.linearDict[variable]

        for variable in self.powerDict.keys():
            if variable in varList:
                yesTerm.powerDict[variable] = self.powerDict[variable]
            else:
                noTerm.powerDict[variable] = self.powerDict[variable]
        
        return (yesTerm, noTerm)
    
    def match(self, yesTerm, noTerm):
        # PRE: yesTerm and noTerm are distinct

        # check that all self's variables are in either yesTerm or noTerm, and coefficients are the same
        for variable in self.linearDict.keys():
            if variable in yesTerm.linearDict.keys():
                if yesTerm.linearDict[variable] != self.linearDict[variable]:
                    return False
            elif variable in noTerm.linearDict.keys():
                if noTerm.linearDict[variable] != self.linearDict[variable]:
                    return False
            else:
                return False
            
        for variable in self.powerDict.keys():
            if variable in yesTerm.powerDict.keys():
                if yesTerm.powerDict[variable] != self.powerDict[variable]:
                    return False
            elif variable in noTerm.powerDict.keys():
                if noTerm.powerDict[variable] != self.powerDict[variable]:
                    return False
            else:
                return False
            
        # check that all variables in yesTerm or noTerm are in self
        for variable in yesTerm.linearDict.keys():
            if variable not in self.linearDict.keys():
                return False
            
        for variable in noTerm.linearDict.keys():
            if variable not in self.linearDict.keys():
                return False
            
        for variable in yesTerm.powerDict.keys():
            if variable not in self.powerDict.keys():
                return False
            
        for variable in noTerm.powerDict.keys():
            if variable not in self.powerDict.keys():
                return False
            
        return True
    
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

        for sig in self.lambdaDict.keys():
            self.lambdaDict[sig] = -self.lambdaDict[sig]
        
        self.constant = -self.constant

    def add(self, otherTerm):
        # remove the variables pointers to the other term
        otherTerm.delete()

        for variable in otherTerm.linearDict.keys():
            if variable in self.linearDict.keys():
                self.linearDict[variable] += otherTerm.linearDict[variable]
            else:
                self.linearDict[variable] = otherTerm.linearDict[variable]
                variable.linearTerms.append(self)
        
        for variable in otherTerm.powerDict.keys():
            if variable in self.powerDict.keys():
                self.powerDict[variable] += otherTerm.powerDict[variable]
            else:
                self.powerDict[variable] = otherTerm.powerDict[variable]
                variable.powerTerms.append(self)

        for sig in otherTerm.lambdaDict.keys():
            if sig in self.lambdaDict.keys():
                self.lambdaDict[sig] += otherTerm.lambdaDict[sig]
            else:
                self.lambdaDict[sig] = otherTerm.lambdaDict[sig]

        self.constant = self.constant + otherTerm.constant

        self.simplify()

    def multiply(self, constant):
        linearVars = list(self.linearDict.keys())
        for variable in linearVars:
            self.linearDict[variable] = self.linearDict[variable]*constant
            if constant == 0:
                variable.linearTerms.remove(self)
                del self.linearDict[variable]

        powerVars = list(self.powerDict.keys())
        for variable in powerVars:
            self.powerDict[variable] = self.powerDict[variable]*constant
            if constant == 0:
                variable.powerDict.remove(self)
                del self.powerDict[variable]

        lambdaSigs = list(self.lambdaDict.keys())
        for sig in lambdaSigs:
            self.lambdaDict[sig] = self.lambdaDict[sig]*constant
            if constant == 0:
                del self.lambdaSigs[variable]

        self.constant *= constant

        self.simplify()

    def modulus(self, divisor):
        for variable in self.linearDict.keys():
            while self.linearDict[variable] < 0:
                self.linearDict[variable] += divisor

            while self.linearDict[variable] >= divisor:
                self.linearDict[variable] -= divisor

        for variable in self.powerDict.keys():
            while self.powerDict[variable] < 0:
                self.powerDict[variable] += divisor
            
            while self.powerDict[variable] >= divisor:
                self.powerDict[variable] -= divisor

        for sig in self.lambdaDict.keys():
            while self.lambdaDict[sig] < 0:
                self.lambdaDict[sig] += divisor

            while self.lambdaDict[sig] >= divisor:
                self.lambdaDict[sig] -= divisor

        while self.constant < 0:
            self.constant += divisor
        
        while self.constant >= divisor:
            self.constant -= divisor

        self.simplify()

    def isVariable(self):
        if len(self.linearDict) != 1:
            return False

        variable = list(self.linearDict.keys())[0]
        if self.linearDict[variable] != 1 and self.linearDict[variable] != -1:
            return False
        
        return len(self.powerDict) == 0 and len(self.lambdaDict) == 0 and self.constant == 0
    
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

        for sig in self.lambdaDict.keys():
            coefficient = self.lambdaDict[sig]
            if coefficient < 0:
                # Lambda(sig) >= 0
                return False

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

        for sig in self.lambdaDict.keys():
            coefficient = self.lambdaDict[sig]
            if coefficient > 0:
                # Lambda(sig) >= 0
                return False

        return maxValue < 0
    
    def isInteger(self):
        return len(self.linearDict) == 0 and len(self.powerDict) == 0 and len(self.lambdaDict) == 0
    
    def simplify(self):
        linearVars = list(self.linearDict.keys())
        for variable in linearVars:
            if self.linearDict[variable] == 0:
                del self.linearDict[variable]
                variable.linearTerms.remove(self)
        
        powerVars = list(self.powerDict.keys())
        for variable in powerVars:
            if self.powerDict[variable] == 0:
                del self.powerDict[variable]
                variable.powerTerms.remove(self)

        lambdaSigs = list(self.lambdaDict.keys())
        for sig in lambdaSigs:
            if self.lambdaDict[sig] == 0:
                del self.lambdaDict[variable]

        return self

    def simplifyComp(self):
        self.simplify()

        gcd = None

        for variable in self.linearDict.keys():
            if gcd == None:
                gcd = self.linearDict[variable]
            else:
                gcd = math.gcd(gcd, self.linearDict[variable])

        for variable in self.powerDict.keys():
            if gcd == None:
                gcd = self.powerDict[variable]
            else:
                gcd = math.gcd(gcd, self.powerDict[variable])

        for sig in self.lambdaDict.keys():
            if gcd == None:
                gcd = self.lambdaDict[sig]
            else:
                gcd = math.gcd(gcd, self.lambdaDict[sig])

        if gcd != None and gcd > 1:
            for variable in self.linearDict.keys():
                assert(self.linearDict[variable] % gcd == 0)
                self.linearDict[variable] = self.linearDict[variable] // gcd
            
            for variable in self.powerDict.keys():
                assert(self.powerDict[variable] % gcd == 0)
                self.powerDict[variable] = self.powerDict[variable] // gcd

            for sig in self.lambdaDict.keys():
                assert(self.lambdaDict[sig] % gcd == 0)
                self.lambdaDict[sig] = self.lambdaDict[sig] // gcd
            
            if self.constant % gcd != 0:
                # can round self.constant down to nearest gcd
                self.constant -= self.constant % gcd
            
            assert(self.constant % gcd == 0)
            self.constant = self.constant // gcd
    
    def equiv(self, otherTerm):
        otherLinear = list(otherTerm.linearDict.keys())
        for variable in self.linearDict.keys():
            # find equivalent variable in otherTerm's linear variables
            foundEquiv = False
            for otherVariable in otherLinear:
                if variable.equiv(otherVariable):
                    if otherTerm.linearDict[otherVariable] != self.linearDict[variable]:
                        return False
                    
                    foundEquiv = True
                    otherLinear.remove(otherVariable)
                    break

            if not foundEquiv:
                return False
        # check otherTerm doesn't have extra variable
        if len(otherLinear) != 0:
            return False

        otherPower = list(otherTerm.powerDict.keys()) 
        for variable in self.powerDict.keys():
            # find equivalent variable in otherTerm's power variables
            foundEquiv = False
            for otherVariable in otherPower:
                if variable.equiv(otherVariable):
                    if otherTerm.powerDict[otherVariable] != self.powerDict[variable]:
                        return False
                    
                    foundEquiv = True
                    otherPower.remove(otherVariable)
                    break

            if not foundEquiv:
                return False
        if len(otherPower) != 0:
            return False
        
        otherSigs = list(otherTerm.lambdaDict.keys()) 
        for sig in self.lambdaDict.keys():
            # find equivalent term in otherTerm's lambda terms
            foundEquiv = False
            for otherSig in otherSigs:
                if sig.equiv(otherSig):
                    if otherTerm.lambdaDict[otherSig] != self.lambdaDict[sig]:
                        return False
                    
                    foundEquiv = True
                    otherSigs.remove(otherSig)
                    break

            if not foundEquiv:
                return False
        if len(otherSigs) != 0:
            return False
            
        if self.constant != otherTerm.constant:
            return False
        
        return True
    
    def getMax(self):
        max = abs(self.constant)

        for variable in self.linearDict.keys():
            if abs(self.linearDict[variable]) > max:
                max = abs(self.linearDict[variable])

        for variable in self.powerDict.keys():
            if abs(self.powerDict[variable]) > max:
                max = abs(self.powerDict[variable])

        return max
    
    def getSum(self):
        sum = abs(self.constant)

        for variable in self.linearDict.keys():
            sum += abs(self.linearDict[variable])
        
        for variable in self.powerDict.keys():
            sum += abs(self.powerDict[variable])
        return sum
    
    def setVariablePointers(self, varList):
        for variable in self.linearDict.keys():
            if variable in varList:
                variable.linearTerms.append(self)

        for variable in self.powerDict.keys():
            if variable in varList:
                variable.powerTerms.append(self)

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
                powerPairs.append("2^|" + variable.ident + "|")
            elif self.powerDict[variable] == -1:
                powerPairs.append("-2^|" + variable.ident + "|")
            else:
                powerPairs.append(str(self.powerDict[variable]) + ".2^|" + variable.ident + "|")

        lambdaPairs = []
        for sig in self.lambdaDict.keys():
            if self.lambdaDict[sig] == 1:
                lambdaPairs.append("Lambda(" + str(sig) + ")")
            elif self.lambdaDict[sig] == -1:
                lambdaPairs.append("-Lambda(" + str(sig) + ")")
            else:
                lambdaPairs.append(str(self.lambdaDict[sig]) + ".Lambda(" + str(sig) + ")")

        strRep = " + ".join(linearPairs)

        if strRep != "" and powerPairs != []:
            strRep += " + "
        strRep += " + ".join(powerPairs)

        if strRep != "" and lambdaPairs != []:
            strRep += " + "
        strRep += " + ".join(lambdaPairs)

        if strRep == "":
            return strRep + str(self.constant)

        if self.constant != 0:
            return strRep + " + " + str(self.constant)
            
        return strRep

def makeVariable(variable, parent = None, coef = 1):
    termNode = TermNode(parent = parent)
    termNode.linearDict[variable] = coef
    variable.linearTerms.append(termNode)
    return termNode

def makePower(variable, parent = None, coef = 1):
    termNode = TermNode(parent = parent)
    termNode.powerDict[variable] = coef
    variable.powerTerms.append(termNode)
    return termNode

def makeLambda(sig, parent = None, coef = 1):
    termNode = TermNode(parent = parent)
    termNode.lambdaDict[sig] = coef
    return termNode

def makeInteger(int, parent = None):
    termNode = TermNode(parent = parent)
    termNode.constant = int
    return termNode

"""
Creates absolute value replacement
e.g.
    a.|x| < phi
is replaced by
    (NOT (x < 0) --> a.x < phi) AND
    (x < 0 --> -a.x < phi)

`posForm` is the a.x < phi in this instance
`variable` is x in this instance
returns the full formula, with parent node `parent`

can take multiple variables to create the absolute value replacement for
"""
def makeAbs(variables, posForm, parent=None):
    assert(len(variables) > 0)
    variable = variables[0]
    if len(variables) > 1:
        posForm = makeAbs(variables[1:], posForm)

    varReplace = {}
    negX = makeVariable(variable, coef=-1)
    varReplace[("linear", variable)] = (negX, 1)
    (negForm, _) = posForm.clone(varReplace=varReplace)
    # remove pointers to negX
    negX.delete()

    andNode = TreeNode("AND", parent)

    impNode = TreeNode("IMP", andNode)
    andNode.children.append(impNode)

    notNode = TreeNode("NOT", impNode)
    impNode.children.append(notNode)
    ltNode = LTNode(parent=notNode)
    notNode.children = [ltNode]
    varNode = makeVariable(variable, ltNode)
    ltNode.children = [varNode]

    posForm.parent = impNode
    impNode.children.append(posForm)

    impNode = TreeNode("IMP", andNode)
    andNode.children.append(impNode)

    ltNode = LTNode(parent=impNode)
    impNode.children.append(ltNode)
    varNode = makeVariable(variable, ltNode)
    ltNode.children = [varNode]

    negForm.parent = impNode
    impNode.children.append(negForm)

    (andNode, _) = andNode.normalizeRec()
    return andNode

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
        return makeInteger(int(tokenTree.value))
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
    
    return node