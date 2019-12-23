# Run t|ket> on all the benchmarks

# tket includes several optimization passes, but I'm not sure which is/are the
# right one(s) to call. When I tried including more (e.g. CommuteThroughMultis)
# the benchmarks were very slow to compile.

import pytket
from pytket import OpType, Transform
from pytket.qasm import circuit_from_qasm
import os
import re
import sys

def run_on_nam_benchmarks(fname):
    
    f = open(fname, "w")
    d = "nam-benchmarks"
    
    f.write("name, num gates before, num gates after\n")
    
    for fname in os.listdir(d):

        print("Processing %s..." % fname)
        
        # same hack as the one used in run_qiskit.py
        inqasm = open("nam-benchmarks/%s" % fname, "r")
        tmp = open("copy.qasm", "w") # hardcoded filename
        p_ccz = re.compile("ccz (.*), (.*), (.*);")
        p_ccx = re.compile("ccx (.*), (.*), (.*);")
        
        for line in inqasm:
            m1 = p_ccx.match(line)
            m2 = p_ccz.match(line)
            if m1:
                a = m1.group(1)
                b = m1.group(2)
                c = m1.group(3)
                tmp.write("h %s;\n" % (c))
                tmp.write("cx %s, %s;\n" % (b, c))
                tmp.write("tdg %s;\n" % (c))
                tmp.write("cx %s, %s;\n" % (a, c))
                tmp.write("t %s;\n" % (c))
                tmp.write("cx %s, %s;\n" % (b, c))
                tmp.write("tdg %s;\n" % (c))
                tmp.write("cx %s, %s;\n" % (a, c))
                tmp.write("cx %s, %s;\n" % (a, b))
                tmp.write("tdg %s;\n" % (b))
                tmp.write("cx %s, %s;\n" % (a, b))
                tmp.write("t %s;\n" % (a))
                tmp.write("t %s;\n" % (b))
                tmp.write("t %s;\n" % (c))
                tmp.write("h %s;\n" % (c))
            elif m2:
                a = m2.group(1)
                b = m2.group(2)
                c = m2.group(3)
                tmp.write("cx %s, %s;\n" % (b, c))
                tmp.write("tdg %s;\n" % (c))
                tmp.write("cx %s, %s;\n" % (a, c))
                tmp.write("t %s;\n" % (c))
                tmp.write("cx %s, %s;\n" % (b, c))
                tmp.write("tdg %s;\n" % (c))
                tmp.write("cx %s, %s;\n" % (a, c))
                tmp.write("cx %s, %s;\n" % (a, b))
                tmp.write("tdg %s;\n" % (b))
                tmp.write("cx %s, %s;\n" % (a, b))
                tmp.write("t %s;\n" % (a))
                tmp.write("t %s;\n" % (b))
                tmp.write("t %s;\n" % (c))
            else:
                tmp.write(line)
        tmp.close()
        circ = circuit_from_qasm("copy.qasm")
        
        num_gates_before = circ.n_gates
        print("\nORIGINAL: %d gates" % (num_gates_before))
        
        Transform.OptimisePhaseGadgets().apply(circ)
        num_gates_after = circ.n_gates
        print("OPTIMIZED: %d gates\n" % (num_gates_after))

        f.write("%s,%d,%d\n" % (fname, num_gates_before, num_gates_after))

if (len(sys.argv) != 2):
    print("Usage: python3 run_tket.py output_file")
    exit(-1)

run_on_nam_benchmarks(sys.argv[1])
