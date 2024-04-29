import os
from solver import Solver
from exceptions import InputException

relPath = "QF_EIA-master/LoAT/CHC_Comp_22_LIA_Lin/"
nextTest = 4

testFiles = []
print(os.getcwd())
for f in os.listdir(os.getcwd() + "/" + relPath):
    testFiles.append(f)

for fName in testFiles:
    fName = relPath + fName

    solve = Solver()

    badSMT = False

    try:
        solve.makeFormulaFromSmt(fName, False)
    except InputException as e:
        #print("Fail: " + fName)
        #print("Exception: " + str(e))
        badSMT = True

    if badSMT:
        # don't copy over file
        continue

    print("Successful: " + fName)

    os.rename(fName, "tests/test" + str(nextTest) + ".smt2")
    nextTest += 1