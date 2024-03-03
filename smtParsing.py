from pysmt.shortcuts import *
from pysmt.operators import *
from variable import Variable
from formulaTree import *


def parseSMTForm(smtFName):
    form = read_smtlib(smtFName)
    print(serialize(form))

    # assume free variables are existentially quantified at the start of the formula
    varDict = {}

    freeVars = form.get_free_variables()
    
    parent = None
    topNode = None
    for varSym in freeVars:
        varIdent = str(varSym)
        varObj = Variable(varIdent)
        node = QuantifierNode("EXISTS", varObj, parent)
        if parent != None:
            parent.children = [node]
        else:
            topNode = node
        
        varObj.quant = node
        
        varDict[varIdent] = varObj

        parent = node

    form = convertForm(form, varDict, parent)
    if parent != None:
        parent.children = [form]
        return topNode
    
    return form

def convertForm(form, variableDict = {}, parent = None):
    basicConversions = {
        "AND": "AND",
        "OR": "OR",
        "NOT": "NOT",
        "IMPLIES": "IMP",
        "IFF": "DIMP",
        "PLUS": "PLUS",
        "TIMES": "MUL",
        "LE": "LTE",
        "LT": "LT",
        "EQUALS": "EQ",
    }

    formType = op_to_str(form.node_type())
    payload = form._content.payload
    formChildren = form.args()

    newVarDict = variableDict.copy()

    nodeToReturn = None

    if formType == "EXISTS" or formType == "FORALL":
        assert(payload != None and len(payload) > 0)
        for varSym in payload:
            varIdent = str(varSym)
            varObj = Variable(varIdent)
            node = QuantifierNode(formType, varObj, parent)
            varObj.quant = node

            if nodeToReturn == None:
                nodeToReturn = node
            else:
                parent.children = [node]

            newVarDict[varIdent] = varObj

            parent = node
    elif formType == "SYMBOL":
        assert(payload != None)
        (sym, typ) = payload
        ident = str(sym)
        assert(str(typ) == "Int")
        if ident in variableDict.keys():
            return makeVariable(variableDict[ident], parent)
    
        # else something has gone wrong
        raise Exception("Unreachable code.")
    elif formType == "BOOL_CONSTANT":
        assert(payload != None)
        print("payload = " + str(payload))
        if payload:
            return TreeNode("TOP", parent)
        else:
            return TreeNode("BOT", parent)
    elif formType == "INT_CONSTANT":
        assert(payload != None)
        return makeInteger(int(payload), parent)
    elif formType == "MINUS":
        assert(payload == None)
        assert(len(formChildren) > 0 and len(formChildren) <= 2)
        if len(formChildren) == 1:
            node = TreeNode("UMIN", parent)
        else:
            node = TreeNode("MIN", parent)
    elif formType == "POW":
        assert(payload == None)
        node = TreeNode("POW", parent)
        child1 = convertForm(formChildren[0], newVarDict, node)
        child2 = convertForm(formChildren[1])
        assert(child2.type == "TERM")
        assert(child2.isInteger())
        if child2.constant != 2:
            raise Exception("Bad Formula: non-2 exponential: " + str(child2.constant))
        node.children = [child1]
        return node
    elif formType == "ITE":
        assert(payload == None)
        # if a then b else c equivalent to (a -> b) and (¬a -> c)
        ifNode = convertForm(formChildren[0], newVarDict)
        print("ifNode = " + str(ifNode)) 
        thenNode = convertForm(formChildren[1], newVarDict)
        elseNode = convertForm(formChildren[2], newVarDict)

        andNode = TreeNode("AND", parent)

        impNode1 = TreeNode("IMP", andNode)
        thenNode.parent = impNode1
        andNode.children.append(impNode1)

        (ifClone, _) = ifNode.clone(impNode1)
        impNode1.children = [ifClone, thenNode]
        thenNode.parent = impNode1

        impNode2 = TreeNode("IMP", andNode)
        andNode.children.append(impNode2)

        notNode = TreeNode("NOT", impNode2, [ifNode])
        ifNode.parent = notNode
        impNode2.children.append(notNode)
        
        impNode2.children.append(elseNode)
        elseNode.parent = impNode2

        return andNode

    elif formType in basicConversions.keys():
        assert(payload == None)
        node = TreeNode(basicConversions[formType], parent)
    else:
        # bad token
        raise Exception("Unknown operator: " + formType)
    
    children = []
    for child in formChildren:
        children.append(convertForm(child, newVarDict, node))

    node.children = children

    if nodeToReturn != None:
        return nodeToReturn
    else:
        return node

print(parseSMTForm("test.smt2"))