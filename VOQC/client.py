from voqc import *
import sys
def run(a):
    a = SQIR(str(a))
    a.optimize()
    a.write("py_out.qasm")

run(sys.argv[1])

