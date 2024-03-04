import argparse
import strParsing, smtParsing, solver, test

def main():
    parser = argparse.ArgumentParser(
        prog="PresPower",
        description="Solves SMT for the theory of Presburger Arithmetic extended with power-of-2 exponentiation.",
        epilog="Exactly one of -f, -s, and -t should be used."
    )

    parser.add_argument("-f", "--file_name", help = "file name of an .smt2 file to check SAT")
    parser.add_argument("-s", "--string_formula", help = "string representation of a formula to check SAT")
    parser.add_argument("-t", "--run_tests", choices=["all", "examples", "tests"], nargs="?", const="all", help="run tests")
    parser.add_argument("-v", "--verbose", action="store_true")

    args = parser.parse_args()

    # should only have one of -f, -s, and -t
    numFound = 0
    if args.file_name != None:
        numFound += 1
    if args.string_formula != None:
        numFound += 1
    if args.run_tests != None:
        numFound += 1
    
    if numFound < 1:
        raise Exception("At least one of --file_name, --string_formula, or --run_tests must be used.")
    if numFound > 1:
        raise Exception("At most one of --file_name, --string_formula, or --run_tests may be used.")

    if args.run_tests != None:
        test.runTests(args.run_tests, args.verbose)
        return
    
    solve = solver.Solver()
    if args.string_formula != None:
        solve.makeFormulaFromStr(args.string_formula)
    else:
        solve.makeFormulaFromSmt(args.file_name, args.verbose)

    res = solve.solve()
    print("Finished Solving")
    if res:
        print("Result: SAT")
    else:
        print("Result: UNSAT")

if __name__ == "__main__":
    main()