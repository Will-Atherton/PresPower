import solver, time

class TestException(Exception):
    pass

solve = solver.Solver()

def runExample(strFormula, correctRes):
    print("formula: " + strFormula)
    # CPU time including initial parsing and normalization
    t1 = time.process_time()

    solve.makeFormula(strFormula)

    # CPU time excluding initial parsing and normalization
    t2 = time.process_time()

    res = solve.solve()

    t3 = time.process_time()

    if res != correctRes:
        raise TestException("Incorrect result, wanted: " + str(correctRes) + ", got: " + str(res))
    
    print("result: " + str(res))
    print("time taken, including initial parsing: " + str(t3 - t1))
    print("time taken, excluding initial parsing: " + str(t3 - t2))

# at least one integer between POW(x) and POW(y), for 1 <= x < y
# formula should be SAT
runExample("FORALL x FORALL y ((x < y AND x >= 1) -> EXISTS z (POW(x) < z AND z < POW(y)))", True)

# integer arithmetic is not dense
# formula should be UNSAT
runExample("FORALL x FORALL z EXISTS y (x < z -> (x < y AND y < z))", False)


# addition is commutative
# formula should be SAT
runExample("FORALL x FORALL y (x + y == y + x)", True)

# the POW function is monotonic for non-negatives
# formula should be SAT
runExample("FORALL x FORALL y ((x >= 0 AND x < y) -> POW(x) < POW(y))", True)

# this is not the case for general x,y
# formula should be UNSAT
runExample("FORALL x FORALL y (x < y -> POW(x) < POW(y))", False)

# this is not the case if x == 0
# formula should be UNSAT
runExample("FORALL x FORALL y (x < y -> EXISTS z (POW(x) < z AND z < POW(y)))", False)