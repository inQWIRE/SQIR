# Run t|ket> on all the benchmarks

# tket includes several optimization passes, but I'm not sure which is/are the
# right one(s) to call. When I tried including more (e.g. CommuteThroughMultis)
# the benchmarks were very slow to compile.

import pytket
from pytket.qasm import circuit_from_qasm, circuit_to_qasm
from pytket.passes import FullPeepholeOptimise
from pytket.circuit import OpType
import os
import re
import sys
import time

def run(d,fname):
    
    f = open(fname, "w")
    
    f.write("name,Orig. total,Orig. CNOT,tket total,tket CNOT,time\n")
    
    for fname in os.listdir(d):

        print("Processing %s..." % fname)
        
        # same hack as the one used in run_qiskit.py
        inqasm = open(os.path.join(d, fname), "r")
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
        num_CNOTs_before = circ.n_gates_of_type(OpType.CX)
        print("Original:\t Total %d, CNOT %d" % (num_gates_before, num_CNOTs_before))
        
        start = time.perf_counter() # start timer
        FullPeepholeOptimise().apply(circ)
        stop = time.perf_counter() # stop timer
        num_gates_after = circ.n_gates
        num_CNOTs_after = circ.n_gates_of_type(OpType.CX)
        print("Final:\t Total %d, CNOT %d\n" % (num_gates_after, num_CNOTs_after))

        f.write("%s,%d,%d,%d,%d,%f\n" % (fname, num_gates_before, num_CNOTs_before, num_gates_after, num_CNOTs_after, stop - start))
        
    os.remove("copy.qasm")

if (len(sys.argv) != 3):
    print("Usage: python3 run_tket.py <input directory> <output file>")
    exit(-1)

run(sys.argv[1], sys.argv[2])
