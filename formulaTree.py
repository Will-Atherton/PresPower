from variable import Variable

class TreeNode:
    def __init__(self, type, children):
        self.type = type
        self.children = children

    def clone(self, varDict = {}):
        clonedChildren = []
        for child in self.children:
            clonedChildren.append(child.clone(varDict))
        return TreeNode(self.type, clonedChildren)

    def __repr__(self):
        return self.type + ": " + str(self.children)

    def __repr__(self):
        return self.type + ": " + str(self.children)
    
class QuantifierNode(TreeNode):
    def __init__(self, type, children, variable):
        assert(type == "EXISTS" or type == "FORALL")
        super().__init__(type, children)
        self.variable = variable

    def clone(self, varDict):
        varObj = Variable()
        varDict[self.variable] = varObj
        newChildren = [self.children[0].clone(varDict)]
        quantNode = QuantifierNode(self.type, newChildren, varObj)
        varObj.quant = quantNode
        return quantNode

class VariableNode(TreeNode):
    def __init__(self, type, children, variable):
        assert(children == [] and type == "VAR")
        super().__init__("VAR", [])
        self.variable = variable

    def clone(self, varDict):
        return VariableNode("VAR", [], varDict[self.variable])
    
    def __str__(self):
        return "VAR"
    
    def __repr__(self):
        return "VAR"

class IntegerNode(TreeNode):
    def __init__(self, type, children, int):
        assert(children == [] and type == "INT")
        super().__init__("INT", [])
        self.int = int

    def clone(self, varDict):
        return IntegerNode("INT", self.children, self.int)
    
    def __str__(self):
        return "INT:" + str(self.int)
    
    def __repr__(self):
        return "INT:" + str(self.int)

def convertTokenTree(tokenTree, variableDict = {}):
    print("TOkTree: " + str(tokenTree))
    print("variableDict: " + str(variableDict))
    basicConversions = {
        "POW": ("POW", 1),
        "+": ("PLUS", 2),
        "<": ("LA", 2),
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

    if tokenTree.type == "VAR":
        assert(tokenTree.children == [])
        ident = tokenTree.value
        if ident in variableDict.keys():
            return VariableNode("VAR", [], variableDict[ident])
        raise Exception("Bad Formula - Free Variabe " + ident)
    
    if tokenTree.type == "INT":
        assert(tokenTree.children == [])
        return IntegerNode("INT", [], tokenTree.value)
    
    if tokenTree.type == "EXISTS" or tokenTree.type == "FORALL":
        assert(len(tokenTree.children) == 1)
        varToken = tokenTree.value
        varIdent = varToken.value
        varObj = Variable()
        variableDict[varIdent] = varObj
        children = [convertTokenTree(tokenTree.children[0], variableDict.copy())]
        quantNode = QuantifierNode(tokenTree.type, children, varObj)
        varObj.quant = quantNode
        return quantNode

    if tokenTree.type == "-":
        assert(len(tokenTree.children) == 1 or len(tokenTree.children == 2))
        children = []
        for child in tokenTree.children:
            children.append(convertTokenTree(child, variableDict))
        if len(children) == 1:
            return TreeNode("UMIN", children)
        return TreeNode("MIN", children)
    
    if tokenTree.type == ".":
        assert(len(tokenTree.children) == 2)
        children = []
        intChild = convertTokenTree(tokenTree.children[0], variableDict)
        if intChild.type != "INT" and intChild.type != "UMIN":
            raise Exception("Bad Formula - non-constant multiplication")
        children.append(intChild)
        children.append(convertTokenTree(tokenTree.children[1], variableDict))
        return TreeNode(".", children)
    
    print(tokenTree.type)
    assert(tokenTree.type in basicConversions.keys())
    (nodeType, numChildren) = basicConversions[tokenTree.type]
    assert(len(tokenTree.children) == numChildren)
    children = []
    for child in tokenTree.children:
        children.append(convertTokenTree(child, variableDict))
    return TreeNode(nodeType, children)

formula = "EXISTS x TOP OR 1 | x"
from parsing import getTokenTree
tokenTree = getTokenTree(formula)
print(tokenTree)
formulaTree = convertTokenTree(tokenTree)
print(formulaTree)
print(str(formulaTree))