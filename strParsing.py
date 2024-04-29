import sys
from pyparsing import *
from formulaTree import *

ppc = pyparsing_common

ParserElement.enablePackrat()
sys.setrecursionlimit(3000)

class TokenNode:
    def __init__(self, type, children, value = None):
        self.type = type
        self.value = value
        self.children = children

    def __str__(self):
        if self.type == "VAR" or self.type == "INT":
            return self.type + "-" + str(self.value)
        strRep = self.type
        if self.value != None:
            strRep += "-" + str(self.value)
        return strRep + ": " + str(self.children)
        
    def __repr__(self):
        if self.type == "VAR" or self.type == "INT":
            return self.type + "-" + str(self.value)
        strRep = self.type
        if self.value != None:
            strRep += "-" + str(self.value)
        return strRep + ": " + str(self.children)
    
def parseStr(strFormula):
    tokenTree = getTokenTree(strFormula)
    return convertTokenTree(tokenTree)

def getTokenTree(strFormula):
    def unOpParse(t):
        # all unary operators are right-associative
        tokList = t[0]
        while (len(tokList) > 1):
            tokList = tokList[:-2] + [TokenNode(tokList[-2], [tokList[-1]])]
        return tokList

    def binOpParse(t):
        # most binary operators are left-associative
        tokList = t[0]
        while len(tokList) > 1:
            tokList = [TokenNode(tokList[1], [tokList[0], tokList[2]])] + tokList[3:]
        return tokList
    
    def binOpParseRight(t):
        # for the right-associative binary operators
        tokList = t[0]
        while (len(tokList) > 1):
            tokList = tokList[:-3] + [TokenNode(tokList[-2], [tokList[-3], tokList[-1]])]
        return tokList

    integer = ppc.integer.set_parse_action(lambda t: TokenNode("INT", [], t[0]))
    variable = Word(alphas.lower(),min=1).set_parse_action(lambda t: TokenNode("VAR", [], t[0]))

    atomicTerm = integer | variable

    powOp = Literal("POW")
    uminOp = Literal("-")
    multOp = Literal(".")
    addOp = oneOf("+ -")

    term = infixNotation(
        atomicTerm,
        [
            (powOp, 1, opAssoc.RIGHT, unOpParse),
            (uminOp, 1, opAssoc.RIGHT, unOpParse),
            (multOp, 2, opAssoc.LEFT, binOpParse),
            (addOp, 2, opAssoc.LEFT, binOpParse),
        ]
    )

    def quantNotOpParse(t):
        # the quantifiers / not need special treatment, as they are already in TokenNode objects
        tokList = t[0]
        while (len(tokList) > 1):
            tokList[-2].children.append(tokList[-1])
            tokList = tokList[:-1]
        return tokList

    comparison = (term + oneOf("< > <= >= == !=") + term).set_parse_action(lambda t: TokenNode(t[1], [t[0], t[2]]))
    divisible = (integer + Literal("|") + term).set_parse_action(lambda t: TokenNode("DIV", [t[0], t[2]]))
    top = Literal("TOP").set_parse_action(lambda: TokenNode("TOP", []))
    bottom = Literal("BOT").set_parse_action(lambda: TokenNode("BOTTOM", []))

    atomicFormula = comparison | divisible | top | bottom

    andOp = Literal("AND")
    orOp = Literal("OR")
    implOp = Literal("->")
    doubleImplOp = Literal("<->")
    notOp = Literal("¬").set_parse_action(lambda t: TokenNode("¬", []))
    quantOp = (oneOf("EXISTS FORALL") + variable).set_parse_action(lambda t: TokenNode(t[0], [], t[1]))
    quantNotOp = notOp | quantOp

    formulaParser = infixNotation(
        atomicFormula,
        [
            (quantNotOp, 1, opAssoc.RIGHT, quantNotOpParse),
            (orOp, 2, opAssoc.LEFT, binOpParse),
            (andOp, 2, opAssoc.LEFT, binOpParse),
            (implOp, 2, opAssoc.RIGHT, binOpParseRight),
            (doubleImplOp, 2, opAssoc.RIGHT, binOpParseRight),
        ]
    )

    try:
        tokenTree = formulaParser.parseString(strFormula, parseAll = True)
        return tokenTree[0]
    except Exception as e:
        raise Exception("Cannot Parse Formula: " + str(e))
    
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

        node = QuantifierNode(tokenTree.type, varObj, parent)
        varObj.quant = node
    elif tokenTree.type == "VAR":
        assert(tokenTree.children == [])
        ident = tokenTree.value
        if ident in variableDict.keys():
            return makeVariable(variableDict[ident], parent)
        raise Exception("Bad Formula - Free Variable " + ident)
    elif tokenTree.type == "INT":
        assert(tokenTree.children == [])
        return makeInteger(int(tokenTree.value), parent)
    elif tokenTree.type == "-":
        assert(len(tokenTree.children) == 1 or len(tokenTree.children) == 2)
        if len(tokenTree.children) == 1:
            node = TreeNode("UMIN", parent)
        else:
            node = TreeNode("MIN", parent)
    else:
        assert(tokenTree.type in basicConversions.keys())
        (nodeType, numChildren) = basicConversions[tokenTree.type]
        assert(len(tokenTree.children) == numChildren)
        node = TreeNode(nodeType, parent)

    children = []
    for child in tokenTree.children:
        children.append(convertTokenTree(child, newVarDict, node))

    node.children = children
    
    return node