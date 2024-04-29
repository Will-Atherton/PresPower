import time, os
import solver

class TestException(Exception):
    pass

def resConvert(res):
    if res:
        return "SAT"

    return "UNSAT"

solve = solver.Solver()

def runTest(formLoc, formType, correctRes, verbose):
    if correctRes == None and verbose:
        print("Result Unknown.")

    # CPU time
    t1 = time.process_time()

    if formType == "str":
        strFormula = formLoc
        if verbose:
            print("formula: " + strFormula)
        solve.makeFormulaFromStr(strFormula)
    elif formType == "smt2":
        fName = formLoc
        solve.makeFormulaFromSmt(fName, verbose)

    res = solve.solve()

    t2 = time.process_time()
    timeTaken = t2 - t1

    if correctRes != None and res != correctRes:
        raise TestException("Incorrect result, wanted: " + resConvert(correctRes) + ", got: " + resConvert(res))
    
    if verbose:
        print("result: " + resConvert(res))
        print("time taken: " + str(timeTaken) + "s")
    
    return  timeTaken

def runTests(tests, verbose):
    assert(tests == "all" or tests == "examples" or tests == "tests")
    if tests == "all" or tests == "examples":
        print("Running examples")
        totalTime = 0
        for (strForm, expected) in examples:
            totalTime += runTest(strForm, "str", expected, verbose)

    if verbose:
        print("Total time taken for examples: " + str(totalTime) + "s")
    
    if tests == "all" or tests == "tests":
        print("Running tests")
        testFiles = []
        for f in os.listdir(os.getcwd() + "/tests/"):
            testFiles.append(f)

        totalTime = 0

        for fName in testFiles:
            fName = "tests/" + fName

            # read first line of file to check comment
            correctRes = None
            f = open(fName, "r")
            firstLine = f.readline()
            f.close()

            if firstLine[0] == ";":
                # first line is a comment
                if "unsat" in firstLine:
                    # result should be UNSAT
                    correctRes = False
                elif "sat" in firstLine:
                    # result should be SAT
                    correctRes = True

            if verbose:
                print("running file: " + fName)

            totalTime += runTest(fName, "smt2", correctRes, verbose)

        print("All tests successful.")
        if verbose:
            print("Total time taken for tests: " + totalTime + "s")

examples = []

# integer arithmetic is not dense
# formula should be UNSAT
examples.append(("FORALL x FORALL z EXISTS y (x < z -> (x < y AND y < z))", False))


# addition is commutative
# formula should be SAT
examples.append(("FORALL x FORALL y (x + y == y + x)", True))

# the POW function is monotonic for non-negatives
# formula should be SAT
examples.append(("FORALL x FORALL y ((x >= 0 AND x < y) -> POW(x) < POW(y))", True))

# this is not the case for general x,y
# formula should be UNSAT
examples.append(("FORALL x FORALL y (x < y -> POW(x) < POW(y))", False))

# at least one integer between POW(x) and POW(y), for 1 <= x < y
# formula should be SAT
examples.append(("FORALL x FORALL y ((x < y AND x >= 1) -> EXISTS z (POW(x) < z AND z < POW(y)))", True))

# this is not the case if x == 0
# formula should be UNSAT
examples.append(("FORALL x FORALL y (x < y -> EXISTS z (POW(x) < z AND z < POW(y)))", False))

testFiles = ["test"]