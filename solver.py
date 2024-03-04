from strParsing import getTokenTree
from smtParsing import parseSMTFile
from formulaTree import *
import globals
import math, itertools

def Lambda(n):
    if n == 0:
        return 0
    
    n = abs(n)
    pow = math.floor(math.log2(n))
    return 2 ** pow

class Solver:
    def __init__(self):
        globals.resetIdents()
        self.formulaTree = None
        self.addedQuants = []
        self.workList = []
        self.finishedList = [] # should be unique w.r.t. equiv

    def makeFormulaFromStr(self, strFormula):
        # reset globals
        globals.resetIdents()

        tokenTree = getTokenTree(strFormula)
        self.formulaTree = convertTokenTree(tokenTree)

        self.normalizeFormula()

    def makeFormulaFromSmt(self, smtFName, verbose):
        # reset globals
        globals.resetIdents()

        self.formulaTree = parseSMTFile(smtFName, verbose)

        self.normalizeFormula()
    
    def normalizeFormula(self):
        (_, replacementDict) = self.formulaTree.normalizeRec()
        self.formulaTree.addReplacements(replacementDict)
    
    def solve(self):
        assert(self.formulaTree != None)

        lowestQuant = self.formulaTree.getLowestQuant()
        self.SimplifyDiv(lowestQuant.children[0])

        done = False
        while not done:
            lowestQuant = self.formulaTree.getLowestQuant()
            if lowestQuant == None:
                result = self.formulaTree
                assert(result.type == "TOP" or result.type == "BOT")
                # result should be TOP or BOT
                return result.type == "TOP"
            
            quantType = lowestQuant.type
            varList = []
            current = lowestQuant
            while(current != None and current.type == quantType):
                varList.append(current.variable)
                current = current.parent
            
            # current is the node above the highest quantifier in the set
            topParent = current

            if quantType == "FORALL":
                # need to use EXISTS instead, so add the NOTs
                notNode = TreeNode("NOT", lowestQuant, lowestQuant.children)
                lowestQuant.children[0].parent = notNode
                lowestQuant.children = [notNode]
                
                # technically not necessary (I think)
                lowestQuant.type = "EXISTS"

                # simplify double-negatives or TOP/BOT
                notNode.simplify()
                
                upperNotNode = TreeNode("NOT", topParent, None)
                if topParent != None:
                    topParent.children = [upperNotNode]
                else:
                    self.formulaTree = upperNotNode

                topParent = upperNotNode

            root = lowestQuant.children[0]
            root.parent = None

            # some branches aren't always deleted, so reset the variable pointers for the variables we are concerned about
            for var in varList:
                var.resetTerms()

            root.setVariablePointers(varList)

            # initialise the work list to be the full formula and varList
            self.workList = []
            self.addToWorkList([(varList, root)])

            self.finishedList = []
            self.addedQuants = []
            while len(self.workList) > 0:
                (varList, root) = self.workList.pop(0)
                if self.hasLinear(varList):
                    linearVar = self.getLinear(varList)
                    self.addToWorkList(self.PresQE(linearVar, varList, root))
                else:
                    self.addToWorkList(self.Linearise(self.SemCover(varList, root)))

            # add in the created quantifiers
            for (quant, _) in self.addedQuants:
                if topParent != None:
                    topParent.children = [quant]
                else:
                    self.fomrulaTree = quant

                quant.parent = topParent
                topParent = quant

            # create the disjunction just below topParent
            orNode = TreeNode("OR", topParent)
            if topParent != None:
                topParent.children = [orNode]
            else:
                self.formulaTree = orNode

            for form in self.finishedList:
                orNode.children.append(form)
                form.parent = orNode

            orNode = orNode.simplifyRec()
            if topParent == None:
                self.formulaTree = orNode
            
            if quantType == "FORALL":
                # simplify the upper not node
                if self.formulaTree == upperNotNode:
                    self.formulaTree = upperNotNode.simplify()
                else:
                    upperNotNode.simplify()

    def addToWorkList(self, toAdd):
        formsToAdd = []
        for (vList, form) in toAdd:
            for variable in vList.copy():
                if variable.numVariables() == 0:
                    vList.remove(variable)

            if vList == []:
                # if form.type == BOT, don't add it to finishedList
                if form.type == "TOP":
                    # short-circuit, entire disjunction will result in TOP
                    self.finishedList = [TreeNode("TOP")]
                    self.workList = []
                    return
                elif form.type != "BOT":
                    # don't add if duplicate
                    foundDup = False
                    for finishedForm in self.finishedList:
                        if finishedForm.equiv(form):
                            foundDup = True
                            break
                    
                    if not foundDup:
                        self.finishedList.append(form)
            else:
                formsToAdd.append((vList, form))

        # add new forms to the start of the workList - traverse in DFS manner
        self.workList = formsToAdd + self.workList

    def hasLinear(self, vList):
        for var in vList:
            if len(var.powerTerms) == 0:
                return True
        
        return False

    def getLinear(self, vList):
        for var in vList:
            if len(var.powerTerms) == 0:
                return var

    def PresQE(self, variable, vList, root):
        T = [] # should be unique w.r.t. equiv
        g = 1
        for term in variable.linearTerms:
            a = term.linearDict[variable]
            (rest, _) = term.clone(varReplace = {("linear", variable): (makeInteger(0), 1)})
            rest.constant = 0
            if a > 0:
                rest.negate()
            else:
                a = -a
            
            # only add (a,t) to T if it isn't already in there
            foundDup = False
            for (a2,t2) in T:
                if a == a2 and rest.equiv(t2):
                    foundDup = True
                    break
            if not foundDup:   
                T.append((a, rest))
                g *= a

        (maxLin, mod) = root.getLinAndMod() # gets ||lin|| and mod of phi

        finished = []

        for (a, t) in T:
            r = a * (2 * maxLin + g * mod)
            for k in range(-r, r+1):
                (t2, _) = t.clone()
                t2.constant += k
                (newVList, varDict) = self.cloneVariableList(vList)
                (newForm, _) = root.clone(varDict = varDict, varReplace={("linear", variable):(t2, a)})

                andNode = TreeNode("AND", children=[newForm])
                newForm.parent = andNode

                divNode = DivisibilityNode(a, parent=andNode)
                (tClone, _) = t2.clone(divNode, varDict)
                divNode.children = [tClone]
                andNode.children.append(divNode)

                newForm = andNode

                newForm = newForm.simplifyRec()
                
                newForm = self.SimplifyDiv(newForm)

                if newForm.type == "TOP":
                    # short-circuit
                    return [([], newForm)]

                if newForm.type != "BOT":
                    finished.append((newVList, newForm))

                # if newForm.type == "BOT", no need to add it in

                # remove t2
                t2.delete()
            
            # remove variable pointers to t
            t.delete()
        
        # remove pointers to root
        root.delete()

        return finished

        

    def SemCover(self, vList, root):
        # find the terms with powers for each of the variables beforehand
        powerTerms = {}
        for variable in vList:
            pTerms = variable.powerTerms.copy()
            powerTerms[variable] = pTerms

        Gamma = []
        Lambdas = []
        for variable in vList:
            ineqs = [] # should be unique w.r.t. equiv()
            H = [] # again should be unique w.r.t. equiv()

            pTerms = powerTerms[variable]
            for term in pTerms:
                parent = term.parent
                if parent.type == "LT" and not parent.inPowCmp():
                    # don't add in duplicates
                    foundDup = False
                    for ineq in ineqs:
                        if ineq.equiv(parent):
                            foundDup = True
                            break
                    
                    if not foundDup:
                        ineqs.append(parent)
                        (n, sig) = term.split(vList)
                        # again don't add duplicates
                        foundDup = False
                        for (n2, sig2) in H:
                            if n.equiv(n2) and sig.equiv(sig2):
                                foundDup = True
                                break
                        
                        if not foundDup:
                            H.append((n, sig))

            (phi, _) = root.clone()
            Gammax = [phi] # unique w.r.t equiv

            for (n, sig) in H:
                # calculate A, g, a, and V
                A = []
                maxConst = 0
                for ineq in ineqs:
                    term = ineq.children[0]
                    if term.match(n, sig):
                        A.append(ineq)
                        if abs(term.constant) > maxConst:
                            maxConst = abs(term.constant)
                
                sumN = n.getSum()
                powG = 128 * (Lambda(sumN + maxConst) ** 2)
                g = int(math.log2(powG))

                a = n.powerDict[variable]
                V = list(n.powerDict.keys())
                V.remove(variable)

                # construct beta
                andNode = TreeNode("AND")

                ltNode = LTNode(parent=andNode)
                andNode.children.append(ltNode)
                term = makePower(variable, ltNode, -1)
                term.constant = powG
                ltNode.children = [term]

                for u in V:
                    ltNode = LTNode(parent=andNode)
                    andNode.children.append(ltNode)
                    termu = makePower(u, ltNode, powG)
                    ltNode.children = [termu]
                    termx = makePower(variable, coef=-1)
                    termu.add(termx)
                
                beta = andNode.simplifyRec()
                
                newGammax = [] # will remove duplicates at the end of the pass
                count = 0
                for gamma in Gammax:
                    count += 1

                    # formulas that care about j
                    for j in range(g+1):
                        # construct the new formulas

                        # 2^|x| = 2^|j| AND ...
                        andNode = TreeNode("AND")

                        eqNode = TreeNode("EQ", andNode)
                        andNode.children.append(eqNode)

                        intNode = makeInteger(2 ** j, eqNode)
                        powNode = makePower(variable, eqNode)
                        eqNode.children = [powNode, intNode]
                        
                        varReplace = {}
                        intNode = makeInteger(2 ** j)
                        varReplace[("power", variable)] = (intNode, 1)

                        formReplace = {}
                        for alpha in A:
                            (aClone, _) = alpha.clone(varReplace = varReplace)
                            formReplace[alpha] = aClone
                            # can remove pointers to aClone now (will be cloned when replacing)
                            aClone.delete()

                        (gClone, _) = gamma.clone(parent=andNode, formReplace = formReplace)
                        andNode.children.append(gClone)

                        (andNode, _) = andNode.normalizeRec()
                        
                        newGammax.append(andNode)
     
                        # 2^|x| = 2^|j| . 2^|v| AND ...
                        for v in V:
                            andNode = TreeNode("AND")
                            ltNode = LTNode(parent=andNode)
                            andNode.children.append(ltNode)
                            negXPow = makePower(variable, ltNode, -1)
                            negXPow.constant += powG
                            ltNode.children = [negXPow]

                            eqNode = TreeNode("EQ", andNode)
                            andNode.children.append(eqNode)
                            vPow = makePower(v, eqNode, 2**j)
                            xPow = makePower(variable, eqNode)
                            eqNode.children = [xPow, vPow]

                            vPow = makePower(v, coef=2**j)
                            varReplace = {}
                            varReplace[("power", variable)] = (vPow, 1)

                            formReplace = {}
                            for alpha in A:
                                (aClone, _) = alpha.clone(varReplace = varReplace)
                                formReplace[alpha] = aClone
                                # can remove pointers to aClone now (will be cloned when replacing)
                                aClone.delete()

                            # remove pointers to vPow
                            vPow.delete()

                            (gClone, _) = gamma.clone(andNode, formReplace = formReplace)
                            andNode.children.append(gClone)

                            (andNode, _) = andNode.normalizeRec()

                            newGammax.append(andNode)
                    
                    # formulas with Lambda(sig)
                    if sig.isInteger():
                        # sig should be 0
                        assert(sig.constant == 0)
                        lambdaTerm = makeInteger(0)
                    else:
                        lambdaTerm = makeLambda(sig)
                        
                        # add sig to Lambdas, checking for duplicates
                        foundDup = False
                        for term in Lambdas:
                            if sig.equiv(term):
                                foundDup = True
                                break
                        
                        if not foundDup:
                            Lambdas.append(sig)

                    lambdaA = Lambda(a)

                    # Lambda(a).2^|x| < Lambda(sig) AND sig < 0 AND ...

                    andNode = TreeNode("AND")

                    (betaClone, _) = beta.clone(andNode)
                    andNode.children.append(betaClone)

                    ltNode = LTNode(parent=andNode)
                    andNode.children.append(ltNode)
                    termNode = makePower(variable, ltNode, lambdaA)
                    ltNode.children.append(termNode)
                    (lambdaClone, _) = lambdaTerm.clone()
                    lambdaClone.negate()
                    termNode.add(lambdaClone)

                    ltNode = LTNode(parent=andNode)
                    andNode.children.append(ltNode)
                    (sigClone, _) = sig.clone(ltNode)
                    ltNode.children.append(sigClone)

                    topNode = TreeNode("TOP")
                    formReplace = {}
                    for alpha in A:
                        formReplace[alpha] = topNode
                    (gClone, _) = gamma.clone(andNode, formReplace=formReplace)
                    andNode.children.append(gClone)

                    andNode = andNode.simplifyRec()
 
                    newGammax.append(andNode)

                    # Lambda(a).2^|x| < Lambda(sig) AND sig >= 0 AND ...

                    andNode = TreeNode("AND")

                    (betaClone, _) = beta.clone(andNode)
                    andNode.children.append(betaClone)

                    ltNode = LTNode(parent=andNode)
                    andNode.children.append(ltNode)
                    termNode = makePower(variable, ltNode, lambdaA)
                    ltNode.children.append(termNode)
                    (lambdaClone, _) = lambdaTerm.clone()
                    lambdaClone.negate()
                    termNode.add(lambdaClone)

                    # sig >= 0 equivalent to not (sig < 0)
                    notNode = TreeNode("NOT", andNode)
                    ltNode = LTNode(parent=notNode)
                    notNode.children = [ltNode]
                    andNode.children.append(ltNode)
                    (sigClone, _) = sig.clone(ltNode)
                    ltNode.children.append(sigClone)

                    botNode = TreeNode("BOT")
                    formReplace = {}
                    for alpha in A:
                        formReplace[alpha] = botNode
                    (gClone, _) = gamma.clone(andNode, formReplace=formReplace)
                    andNode.children.append(gClone)

                    andNode = andNode.simplifyRec()

                    newGammax.append(andNode)

                    # Lambda(a).2^|x| = Lambda(sig) AND ...
                    andNode = TreeNode("AND")

                    (betaClone, _) = beta.clone(andNode)
                    andNode.children.append(betaClone)

                    eqNode = TreeNode("EQ", andNode)
                    andNode.children.append(eqNode)
                    termNode = makePower(variable, eqNode, lambdaA)
                    eqNode.children.append(termNode)
                    (lambdaClone, _) = lambdaTerm.clone(eqNode)
                    eqNode.children.append(lambdaClone)

                    varReplace = {}
                    varReplace[("power", variable)] = (lambdaTerm, lambdaA)

                    formReplace = {}
                    for alpha in A:
                        (aClone, _) = alpha.clone(varReplace = varReplace)
                        formReplace[alpha] = aClone
                        # can remove pointers to aClone now (will be cloned when replacing)
                        aClone.delete()
                        
                    (gClone, _) = gamma.clone(andNode, formReplace=formReplace)
                    andNode.children.append(gClone)
                   
                    (andNode, _) = andNode.normalizeRec()

                    newGammax.append(andNode)

                    # Lambda(a).2^|x| = 2.Lambda(sig) AND ...
                    andNode = TreeNode("AND")

                    (betaClone, _) = beta.clone(andNode)
                    andNode.children.append(betaClone)

                    eqNode = TreeNode("EQ", andNode)
                    andNode.children.append(eqNode)
                    termNode = makePower(variable, eqNode, lambdaA)
                    eqNode.children.append(termNode)
                    (lambdaClone, _) = lambdaTerm.clone(eqNode)
                    lambdaClone.multiply(2)
                    eqNode.children.append(lambdaClone)

                    varReplace = {}
                    (lambdaClone, _) = lambdaTerm.clone()
                    lambdaClone.multiply(2)
                    varReplace[("power", variable)] = (lambdaClone, lambdaA)

                    formReplace = {}
                    for alpha in A:
                        (aClone, _) = alpha.clone(varReplace = varReplace)
                        formReplace[alpha] = aClone
                        # can remove pointers to aClone now (will be cloned when replacing)
                        aClone.delete()
                        
                    (gClone, _) = gamma.clone(andNode, formReplace=formReplace)
                    andNode.children.append(gClone)

                    (andNode, _) = andNode.normalizeRec()

                    newGammax.append(andNode)

                    # Lambda(a).2^|x| > 2.Lambda(sig) AND a < 0 AND ...
                    # Lambda(a).2^|x| > 2.Lambda(sig) AND a > 0 AND ...
                    # a is an integer, we can evaluate a now
                    # a shouldn't be 0
                    assert(a != 0)
                    if (a < 0):
                        nodeToReplace = TreeNode("TOP")
                    else:
                        nodeToReplace = TreeNode("BOT")
                    
                    andNode = TreeNode("AND")

                    (betaClone, _) = beta.clone(andNode)
                    andNode.children.append(betaClone)

                    # Lambda(a).2^|x| > 2.Lambda(sig) equivalent to -(Lambda(a).2^|x|) + 2.Lambda(sig) < 0
                    ltNode = LTNode(parent=andNode)
                    andNode.children.append(ltNode)
                    termNode = makePower(variable, ltNode, lambdaA)
                    ltNode.children.append(termNode)
                    termNode.negate()
                    (lambdaClone, _) = lambdaTerm.clone()
                    lambdaClone.multiply(2)
                    termNode.add(lambdaClone)

                    formReplace = {}
                    for alpha in A:
                        formReplace[alpha] = nodeToReplace
                        
                    (gClone, _) = gamma.clone(andNode, formReplace=formReplace)
                    andNode.children.append(gClone)

                    andNode = andNode.simplifyRec()

                    newGammax.append(andNode)

                    # remove pointers to gamma
                    gamma.delete()

                # Remove BOT nodes from Gammax
                Gammax = []
                for form in newGammax:
                    if form.type != "BOT":
                        Gammax.append(form)
            
            # add the terms in Gammax to Gamma
            for gamma in Gammax:
                # only duplication if gamma is Bottom, as Gammax is unique w.r.t. equiv
                if gamma.type == "BOT":
                    continue

                andNode = TreeNode("AND", children=[gamma])
                gamma.parent = andNode

                for y in vList:
                    # 2^|x| >= 2^|y| equivalent to NOT (2^|y| - 2^|x| < 0)
                    notNode = TreeNode("NOT", andNode)
                    andNode.children.append(notNode)
                    ltNode = LTNode(parent=notNode)
                    notNode.children = [ltNode]
                    yPow = makePower(y, ltNode)
                    ltNode.children.append(yPow)
                    xPow = makePower(variable, coef=-1)
                    yPow.add(xPow)
                
                andNode = andNode.simplifyRec()
                Gamma.append(andNode)
            
        # create new variables
        lambdaVars = {}
        for sig in Lambdas:
            # if sig is 0, we ignore it
            if sig.isInteger():
                continue

            # check if variable already been created
            found = False
            for (quant, qSig) in self.addedQuants:
                if sig.equiv(qSig):
                    lambdaVars[sig] = quant.variable
                    found = True
                    break
            
            if not found:
                varObj = Variable("w")
                quantNode = QuantifierNode("FORALL", varObj)
                self.addedQuants.append((quantNode, sig))
                lambdaVars[sig] = varObj

        """
        helper function for constructing
            2^|wsig| <= |sig| < 2.2^|wsig|
        as we need it a couple of times, and 
        it is a long construction

        This formula is equivalent to:
            (NOT (sig < 0) ==> (NOT (sig - 2^|wsig| < 0) AND sig - 2.2^|wsig| < 0)) 
            AND (sig < 0 ==> (NOT (-sig - 2^|wsig| < 0) AND -sig - 2.2^|wsig| < 0))
        """
        def constructComp(wsig, sig, parent=None):
            upperAnd = TreeNode("AND", parent)

            impNode = TreeNode("IMP", upperAnd)
            upperAnd.children.append(impNode)

            notNode = TreeNode("NOT", impNode)
            impNode.children.append(notNode)
            ltNode = LTNode(parent=notNode)
            notNode.children = [ltNode]
            (sigClone, _) = sig.clone(ltNode)
            ltNode.children = [sigClone]

            lowerAnd = TreeNode("AND", impNode)
            impNode.children.append(lowerAnd)

            notNode = TreeNode("NOT", lowerAnd)
            lowerAnd.children.append(notNode)
            ltNode = LTNode(parent=notNode)
            notNode.children = [ltNode]
            term = makePower(wsig, ltNode, -1)
            ltNode.children = [term]
            (sigClone, _) = sig.clone()
            term.add(sigClone)

            ltNode = LTNode(parent=lowerAnd)
            lowerAnd.children.append(ltNode)
            term = makePower(wsig, ltNode, -2)
            ltNode.children = [term]
            (sigClone, _) = sig.clone()
            term.add(sigClone)

            impNode = TreeNode("IMP", upperAnd)
            upperAnd.children.append(impNode)

            ltNode = LTNode(parent=impNode)
            impNode.children = [ltNode]
            (sigClone, _) = sig.clone(ltNode)
            ltNode.children = [sigClone]

            lowerAnd = TreeNode("AND", impNode)
            impNode.children.append(lowerAnd)

            notNode = TreeNode("NOT", lowerAnd)
            lowerAnd.children.append(notNode)
            ltNode = LTNode(parent=notNode)
            notNode.children = [ltNode]
            term = makePower(wsig, ltNode, -1)
            ltNode.children = [term]
            (sigClone, _) = sig.clone()
            sigClone.negate()
            term.add(sigClone)

            ltNode = LTNode(parent=lowerAnd)
            lowerAnd.children.append(ltNode)
            term = makePower(wsig, ltNode, -2)
            ltNode.children = [term]
            (sigClone, _) = sig.clone()
            sigClone.negate()
            term.add(sigClone)

            (upperAnd, _) = upperAnd.normalizeRec()
            return upperAnd

        Theta = [] # unique w.r.t. equiv
        # initialize Theta
        for sig in lambdaVars.keys():
            andNode = TreeNode("AND")

            neqNode = TreeNode("NEQ", andNode)
            andNode.children.append(neqNode)
            (sigClone, _) = sig.clone(neqNode)
            neqNode.children.append(sigClone)
            zeroNode = makeInteger(0, neqNode)
            neqNode.children.append(zeroNode)

            notNode = TreeNode("NOT", andNode)
            andNode.children.append(notNode)
            wsig = lambdaVars[sig]
            compNode = constructComp(wsig, sig, notNode)
            notNode.children = [compNode]

            (andNode, _) = andNode.normalizeRec()
            Theta.append(andNode)

        for gamma in Gamma:
            # for every possible subset of Epsilon (= lambdaVars.keys())
            # powerset(list) = chain.from_iterable(combinations(list,r) for r in range(len(list)+1))
            lambdas = list(lambdaVars.keys())
            powerset = itertools.chain.from_iterable(itertools.combinations(lambdas,r) for r in range(len(lambdas)+1))
            for subset in powerset:
                rest = []
                for sig in lambdaVars.keys():
                    if sig not in subset:
                        rest.append(sig)

                lambdaReplacements = {}
                for sig in subset:
                    powW = makePower(wsig)
                    # remove variable references to powW
                    powW.delete()
                    lambdaReplacements[("lambda", sig)] = (powW, 1)

                for sig in rest:
                    zeroTerm = makeInteger(0)
                    lambdaReplacements[("lambda", sig)] = (zeroTerm, 1)

                andNode = TreeNode("AND")                    

                (gClone, _) = gamma.clone(andNode, varReplace = lambdaReplacements)
                andNode.children.append(gClone)

                for sig in subset:
                    wsig = lambdaVars[sig]
                    compNode = constructComp(wsig, sig, andNode)
                    andNode.children.append(compNode)

                for sig in rest:
                    eqNode = TreeNode("EQ", andNode)
                    andNode.children.append(eqNode)
                    (sigClone, _) = sig.clone(eqNode)
                    zeroTerm = makeInteger(0, eqNode)
                    eqNode.children = [sigClone, zeroTerm]

                (andNode, _) = andNode.normalizeRec()
                Theta.append(andNode)
            
            # remove pointers to gamma
            gamma.delete()

        finished = []
        for thetaForm in Theta:
            # clone the variable list
            (newVList, varDict) = self.cloneVariableList(vList)
            
            (finForm, _) = thetaForm.clone(varDict = varDict)
            finished.append((newVList, finForm))
            
            # remove pointers to thetaForm
            thetaForm.delete()

        # remove pointers to root
        root.delete()

        return finished

    def Linearise(self, sCover):
        for (vList, root) in sCover:
            for variable in vList:
                isPowCmp = True
                if len(variable.powerTerms) == 0:
                    isPowCmp = False

                for pTerm in variable.powerTerms:
                    constraint = pTerm.parent
                    if constraint.type == "LT" and not constraint.inPowCmp():
                        isPowCmp = False
                        break

                if not isPowCmp:
                    # variable not relevant
                    continue
                    

                # variable x s.t. 2^|x| appears and only appears in PowCmp constraints
                pTerms = list(variable.powerTerms)
                for pTerm in pTerms:
                    constraint = pTerm.parent
                    if constraint.type == "DIV":
                        # q | 2^|x| - r
                        q = constraint.divisor
                        r = -pTerm.constant

                        # find q' (if exists)
                        newQ = None
                        for t in range(1,q):
                            if r * ((2 ** t) - 1) % q == 0:
                                newQ = t
                                break

                        # find r' (if exists)
                        newR = None
                        for s in range(q):
                            if (2**s) - r % q == 0:
                                newR = s
                                break

                        # if r' doesn't exist, replace with bot
                        if newR == None:
                            botNode = TreeNode("BOT")
                            constraint.replace(botNode)
                            constraint.delete()
                            continue

                        # if q' doesn't exist, replace with |x| = r'
                        if newQ == None:
                            # posForm for makeAbs is x = r'
                            posForm = TreeNode("EQ")
                            xNode = makeVariable(variable, posForm)
                            newRNode = makeInteger(newR, posForm)
                            posForm.children = [xNode, newRNode]
                        else:
                            # q' and r' exist, replace with q' | |x| - r'
                            # posForm for makeAbs is q' | x - r'
                            posForm = DivisibilityNode(newQ)
                            termNode = makeVariable(variable, posForm)
                            posForm.children = [termNode]
                            termNode.constant = -newR

                        # make the abs formula
                        absNode = makeAbs([variable], posForm)
                        constraint.replace(absNode)
                        constraint.delete()
                        continue

                    # constraint.type == "LT"

                    if len(pTerm.powerDict) == 1:
                        # a . 2^|x| < b
                        a = pTerm.powerDict[variable]
                        b = -pTerm.constant

                        # if a and b have different signs, should have been simplified
                        assert((a < 0 and b < 0) or (a > 0 and b > 0))
                        
                        # if a > 0 and b > 0, replace with |x| - ceil(log2(b/a)) < 0
                        if a > 0 and b > 0:
                            # posForm for makeAbs is x - ceil(log2(b/a)) < 0
                            posForm = LTNode()
                            termNode = makeVariable(variable, posForm)
                            posForm.children = [termNode]
                            termNode.constant = -math.ceil(math.log2(b/a))
                        else:
                            # a < 0 and b < 0
                            # replace with floor(log2(b/a)) - |x| < 0
                            # posForm for makeAbs is -x + floor(log2(b/a)) < 0
                            posForm = LTNode()
                            termNode = makeVariable(variable, posForm, -1)
                            posForm.children = [termNode]
                            termNode.constant = math.floor(math.log2(b/a))

                        # make the abs formula
                        absNode = makeAbs([variable], posForm)
                        constraint.replace(absNode)
                        constraint.delete()
                        continue
                
                    # a . 2^|x| < b . 2^|y|
                    a = pTerm.powerDict[variable]
                    xy = list(pTerm.powerDict.keys())
                    xy.remove(variable)
                    assert(len(xy) == 1)
                    y = xy[0]
                    b = -pTerm.powerDict[y]

                     # if a and b have different signs, should have been simplified
                    assert((a < 0 and b < 0) or (a > 0 and b > 0))

                    # if a > 0 and b > 0, replace with |x| - |y| - ceil(log2(b/a)) < 0
                    if a > 0 and b > 0:
                        # posForm for makeAbs is x - y - ceil(log2(b/a)) < 0
                        posForm = LTNode()
                        termNode = makeVariable(variable, posForm)
                        posForm.children = [termNode]
                        termNode.constant = -math.ceil(math.log2(b/a))
                        yTerm = makeVariable(y, coef=-1)
                        termNode.add(yTerm)
                    else:
                        # a < 0 and b < 0
                        # replace with -|x| + |y| + floor(log2(b/a)) < 0
                        # posForm for makeAbs is -x + y + floor(log2(b/a)) < 0
                        posForm = LTNode()
                        termNode = makeVariable(variable, posForm, -1)
                        posForm.children = [termNode]
                        termNode.constant = math.floor(math.log2(b/a))
                        yTerm = makeVariable(y)
                        termNode.add(yTerm)
                    
                    # make the abs formula
                    absNode = makeAbs([y, variable], posForm)
                    constraint.replace(absNode)
                    constraint.delete()

            root.simplifyRec()
        
        return sCover


    def SimplifyDiv(self, root):
        G = root.getNonSimple()
        if G == []:
            # no need to do anything
            return root

        lcm = 1
        for div in G:
            lcm = math.lcm(lcm, div.divisor)
        
        d = lcm

        t = set() # python set

        for div in G:
            term = div.children[0]

            for variable in term.linearDict.keys():
                t.add(("linear", variable))

            for variable in term.powerDict.keys():
                t.add(("power", variable))

        numbersSet = set(range(d))
        singleReplacementLists = []
        for var in t:
            singleReplacementLists.append(list(itertools.product([var], numbersSet)))
        
        replacementList = list(itertools.product(*singleReplacementLists))

        # disjunction of the cover
        orNode = TreeNode("OR")

        for replacementTuple in replacementList:
            replacementDict = {}

            # conjunction of divisibility nodes and replaced formula
            andNode = TreeNode("AND", orNode)
            orNode.children.append(andNode)

            for varTuple in list(replacementTuple):
                (tup, rep) = varTuple
                (typ, var) = tup
                replacementDict[tup] = rep

                if typ == "linear":
                    replacementDict[tup] = (makeInteger(rep), 1)
                    node = makeVariable(var)
                    node.constant = -rep
                else:
                    replacementDict[tup] = (makeInteger(2**abs(rep)), 1)
                    node = makePower(var)
                    node.constant = -rep
                divNode = DivisibilityNode(d, parent=andNode, children=[node])
                node.parent = divNode
                andNode.children.append(divNode)

            (replacedFormula, _) = root.clone(andNode, varReplace=replacementDict)
            andNode.children.append(replacedFormula)

        orNode = orNode.simplifyRec()

        root.replace(orNode)
        root.delete()

        return orNode

    def cloneVariableList(self, vList):
        varDict = {}
        newVList = []
        for var in vList:
            newVar = var.clone()
            varDict[var] = newVar
            newVList.append(newVar)
        
        return (newVList, varDict)