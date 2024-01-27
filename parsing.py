import sys
from pyparsing import *

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