import sys, getopt

try:
    opts, args = getopt.getopt(sys.argv[1:], "a:bc", ["argument="])
except getopt.GetoptError:
    print("bad argument")
    sys.exit(2)
for opt, arg in opts:
    if opt == "-a":
        print("testing: " + arg)
    elif opt == "-b":
        print("testb")
    elif opt == "-c":
        print("testc" + arg)
    elif opt == "--argument":
        print("testing long " + arg)