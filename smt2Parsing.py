from formulaTree import *
from variable import Variable
from exceptions import InputException

class SMTTree:
    def __init__(self, token, value = None, children = None):
        self.token = token
        self.value = value
        self.children = children
    
    def __repr__(self):
        if self.token == "LIST":
            return str(self.children)

        if self.value == None:
            return self.token
        
        return self.token + "(" + str(self.value) + ")"



def parseSMTFile(smtFName, verbose = False):
    # read file into list of lines
    lines = []

    # open and read file (automatically closes file)
    with open(smtFName, "r") as file:
        lines = file.readlines()

    # read lines into list of 'words' = left paren, right paren, or string of characters
    words = []

    # current word
    word = ""

    # read lines character at a time
    for line in lines:
        # don't read if line is a comment
        if line[0] == ";":
            continue

        for char in line:
            if char.isspace() or char == "(" or char == ")":
                # add word to words if it is not empty
                if word != "":
                    words.append(word)
                    word = ""
                
                # if character is a paren, add it to words
                if char == "(" or char == ")":
                    words.append(char)
            else:
                # standard character, add it to current word
                word += char
        
        if word != "":
            words.append(word)
            word = ""
    
    # turn list of words into list of tree of words based on brackets
    (trees, rest) = createTreesFromWords(words)
    if rest != []:
        # extra )
        raise InputException("Incorrect Brackets: found extra ')'")

    # the asserts together make a conjuntion
    andNode = TreeNode("AND")

    # top parent node (will add existentials before the and node)
    parent = andNode

    # define the dictionary of variables
    varDict = {}

    # need to be able to parse boolean varaibles, which will be treated like integer variables, with 1 = true
    boolVars = []

    # trees will always be a "LIST"
    for tree in trees.children:
        # find token and children of the node
        token = ""
        children = []
        if tree.token == "LIST":
            if tree.children == []:
                # node is a blank node
                # we ignore
                continue
            else:
                token = tree.children[0].token
                children = tree.children[1:]
        else:
            token = tree.token

        # only care about declare-fun and assert
        if token != "declare-fun" and token != "assert":
            continue

        if token == "declare-fun":
            # declares an (existential) variable outside of and
            # should have three children
            if len(children) != 3:
                raise InputException("Bad SMT2 file: declare-fun has wrong number of arguments: should have 3, has " + str(len(children)))
            
            ident = children[0]
            if ident.token != "VAR":
                # identifier already a token, or is an integer
                raise InputException("Invalid variable identifier: " + ident.token)
            ident = ident.value
            
            type = children[2]
            if type.token != "Int" and type.token != "Bool":
                # we only parse ints and bools
                raise InputException("Invalid type: " + type.token)
            
            if type.token == "Bool":
                # add the identifier to the boolean variable list
                boolVars.append(ident)

            varObj = Variable(ident)

            node = QuantifierNode("EXISTS", varObj, children=[parent])
            parent.parent = node
            parent = node

            varObj.quant = node

            varDict[ident] = varObj

            continue
        
        # token is assert
        # should only have one child
        if len(children) != 1:
            raise InputException("Bad formula: assert with wrong number of arguments: should have 1, has " + str(len(children)))

        form = convertForm(children[0], varDict, boolVars, andNode)
        andNode.children.append(form)

    if len(andNode.children) == 0:
        raise InputException("Bad formula: no formula defined")

    return parent
    

# list of smt2 tokens
tokens = [
    "set-logic",
    "set-option",
    "declare-fun",
    "assert",
    "check-sat",
    "get-model",
    "+",
    "-",
    "*",
    "pow",
    "exp",
    "forall",
    "exists",
    "<",
    ">",
    "<=",
    ">=",
    "=",
    "!=",
    "not",
    "and",
    "or",
    "=>",
    "<->",
    "let",
    "ite",
    "Int",
    "Bool",
    "true",
    "false",
]

def isInteger(word):
    if word[0] == "+" or word[0] == "-":
        # these are ok
        word = word[1:]
    
    # word.isdecimal() returns true if all characters are numbers 0-9
    return word.isdecimal()

def createTreesFromWords(words):
    # create list of trees from the list of words
    # recurses on brackets
    listOfTrees = []

    while words != []:
        word = words.pop(0)
        if word == ")":
            return (SMTTree("LIST", children=listOfTrees), words)
        
        if word == "(":
            (trees, rest) = createTreesFromWords(words)
            listOfTrees.append(trees)
            words = rest
        elif word in tokens:
            listOfTrees.append(SMTTree(word))
        elif isInteger(word):
            listOfTrees.append(SMTTree("INT", value=int(word)))
        else:
            listOfTrees.append(SMTTree("VAR", value=word))
        
    return (SMTTree("LIST", children=listOfTrees), words)

def convertForm(tree, variableDict = {}, booleanVars = [], parent = None):
    basicConversions = {
        "and": "AND",
        "or": "OR",
        "not": "NOT",
        "=>": "IMP",
        "<->": "DIMP",
        "<": "LT",
        "<=": "LTE",
        ">": "GT",
        ">=": "GTE",
        "=": "EQ",
        "!=": "NEQ",
        "true": "TOP",
        "false": "BOT",
    }

    newVarDict = variableDict.copy()

    newBooleanVars = booleanVars.copy()

    token = tree.token
    children = []
    if token == "LIST":
        if tree.children[0].token == "VAR" or tree.children[0].token == "INT" or tree.children[0].token == "LIST":
            raise InputException("Bad formula - list of operators where there should be one operator: " + str(tree.children))
        
        token = tree.children[0].token
        children = tree.children[1:]

    nodeToReturn = None

    if token == "EXISTS" or token == "FORALL":
        vars = children.pop(0)
        # vars should be a LIST
        if len(vars.children) == 0:
            raise InputException("Quantifier without children.")
        
        for varChild in vars.children:
            # each variable is a list of [varIdent, type]
            if len(varChild.children) != 2:
                raise InputException("Quantifier variable has wrong format")

            if varChild.children[0].type != "VAR":
                raise InputException("Quantifier variable has bad identifier: " + varChild.children[0].type)
            
            varIdent = varChild.children[1].value
            varType = varChild.children[1].type

            if varType != "Int" and varType != "Bool":
                raise InputException("Invalid type: " + varType)
            
            if varType == "Bool":
                newBooleanVars.append(varIdent)
            
            varObj = Variable(varIdent)
            node = QuantifierNode(token, varObj, parent)
            varObj.quant = node

            if nodeToReturn == None:
                nodeToReturn = node
            else:
                parent.children = [node]

            newVarDict[varIdent] = varObj

            parent = node

    elif token == "VAR":
        ident = tree.value

        if ident not in newVarDict.keys():
            raise InputException("Undefined variable: " + ident)
        
        varObj = variableDict[ident]
        varNode = makeVariable(varObj, parent)

        if ident in booleanVars:
            # replace boolean variable x with (x = 1)
            eqNode = TreeNode("EQ", parent, [varNode])
            varNode.parent = eqNode

            intNode = makeInteger(1, eqNode)
            eqNode.children.append(intNode)
            
            return eqNode

        return varNode
    
    elif token == "INT":
        val = tree.value
        return makeInteger(val, parent)
    
    elif token == "-":
        assert(len(children) > 0 and len(children) <= 2)
        if len(children) == 1:
            node = TreeNode("UMIN", parent)
        else:
            node = TreeNode("MIN", parent)

    elif token == "pow" or token == "exp":
        node = TreeNode("POW", parent)
        child1 = convertForm(children[0], newVarDict, newBooleanVars)
        child2 = convertForm(children[1], newVarDict, newBooleanVars, node)
        if child1.type != "TERM" or (not child1.isInteger()) or child1.constant != 2:
            raise InputException("Bad Formula: non-2 exponential: " + str(child1))
        node.children = [child2]
        return node
    
    elif token == "+" or token == "*":
        # need to convert these n-ary versions of + and * to 2-ary + and *
        # as that is how the normalizer expects them
        if token == "+":
            nodeType = "PLUS"
        else:
            nodeType = "MUL"

        if len(children) < 2:
            raise InputException("Operator " + token + " has too few operands.")
        
        newChildren = []
        for child in children:
            newChildren.append(convertForm(child, newVarDict, newBooleanVars))
        
        node = TreeNode(nodeType, parent, [newChildren[0]])
        newChildren[0].parent = node
        nodeToReturn = node
        for child in newChildren[1:-1]:
            newNode = TreeNode(nodeType, node, [child])
            node.children.append(newNode)
            child.parent = newNode
            node = newNode

        node.children.append(newChildren[-1])
        newChildren[-1].parent = node

        return nodeToReturn        

    elif token == "ite":
        # if a then b else c equivalent to (a -> b) and (¬a -> c)
        ifNode = convertForm(children[0], newVarDict, newBooleanVars)
        thenNode = convertForm(children[1], newVarDict, newBooleanVars)
        elseNode = convertForm(children[2], newVarDict, newBooleanVars)

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
    
    elif token == "let":
        # let ((x a)) b is equivalent to:
            # EXISTS x (x = a AND b) for x an integer variable
            # EXISTS y (((y = 1) <-> a) AND b[x / (y = 1)] for x a boolean variable (y is an integer variable)
        # can be extended to let ((x1 a1) (x2 a2) ... (xn an)) b
        if len(children) != 2:
            raise InputException("Let statement has wrong number of arguments.")
        
        reps = children[0]
        if reps.token != "LIST" or len(reps.children) == 0:
            raise InputException("Invalid let statement")
        reps = reps.children

        for rep in reps:
            if rep.token != "LIST" or len(rep.children) != 2:
                raise InputException("Invalid let statement")

            var = rep.children[0]
            if var.token != "VAR":
                raise InputException("Invalid let statement")
            ident = var.value
            varObj = Variable(ident)
            newVarDict[ident] = varObj

            quantNode = QuantifierNode("EXISTS", varObj, parent)
            varObj.quant = quantNode
            if nodeToReturn == None:
                nodeToReturn = quantNode
            else:
                parent.children.append(quantNode)

            andNode = TreeNode("AND", quantNode)
            quantNode.children = [andNode]
            parent = andNode

            formRep = convertForm(rep.children[1], newVarDict, newBooleanVars)

            booleanForms = ["AND", "OR", "NOT", "EQ", "NEQ", "LT", "LTE", "GT", "GTE", "TOP", "BOT"]
            if formRep.type in booleanForms:
                # ident is a boolean variable
                iffNode = TreeNode("DIMP", andNode)
                andNode.children.append(iffNode)

                eqNode = TreeNode("EQ", iffNode)
                iffNode.children.append(eqNode)

                varNode = makeVariable(varObj, eqNode)
                oneNode = makeInteger(1, eqNode)
                eqNode.children = [varNode, oneNode]

                formRep.parent = iffNode
                iffNode.children.append(formRep)

                newBooleanVars.append(ident)
            else:
                # ident is an integer variable
                eqNode = TreeNode("EQ", andNode)
                andNode.children.append(eqNode)

                varNode = makeVariable(varObj, eqNode)
                formRep.parent = eqNode
                eqNode.children = [varNode, formRep]
        
        inNode = convertForm(children[1], newVarDict, newBooleanVars, parent)
        parent.children.append(inNode)

        return nodeToReturn




    elif token in basicConversions.keys():
        node = TreeNode(basicConversions[token], parent)
    
    else:
        # bad token
        raise InputException("Unkown token " + token)
    
    newChildren = []
    for child in children:
        newChildren.append(convertForm(child, newVarDict, newBooleanVars, node))

    node.children = newChildren

    if nodeToReturn != None:
        return nodeToReturn
    
    return node