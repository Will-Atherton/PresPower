identDict = {}

def getNextIdent(ident):
    if ident in identDict:
        identDict[ident] += 1
        return ident + str(identDict[ident])
    
    identDict[ident] = 1
    return ident

def resetIdents():
    identDict.clear()