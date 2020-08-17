from voqc import *
import sys
import time
def run(a,b):
    print("Input file: %s" % (a))
    print("Output file: %s" % (b))
    a = VOQC(str(a))
    a.optimize()
    a.write(str(b))

run(sys.argv[1], sys.argv[2])

