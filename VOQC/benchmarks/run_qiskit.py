'''
    We consider the optimizations used up to level 3 with basis {u1, u2, u3, CNOT}
    
    Reference: https://github.com/Qiskit/qiskit-terra/blob/master/qiskit/transpiler/preset_passmanagers/level3.py
'''

import math
import numpy
import os
from qiskit import QuantumCircuit
from qiskit.compiler import transpile
from qiskit.transpiler import PassManager
from qiskit.transpiler.passes import Unroller, Optimize1qGates, CommutationAnalysis, CommutativeCancellation, CXCancellation, Depth, FixedPoint, Collect2qBlocks, ConsolidateBlocks
import sys
import re
import time
import csv
from gmpy2 import mpq, mpfr

def count(d):
    sum = 0
    for k in d.keys():
        sum += d[k]
    return sum

def run(d, fname):
    
    f = open("out.txt", "w")
    
    f.write("name,Orig. total,Orig. CNOT,Qiskit total,Qiskit CNOT,time\n")
    t = open("out.csv", "w")
    csvwriter = csv.writer(t) 
    csvwriter.writerow(["Name", "Before",  "Final", "Before CNOT","Final CNOT","Time"])
    t.close()
    
    for fname in os.listdir(d):

        print("Processing %s..." % fname)
        
        # Some of the benchmarks contain 'ccz' and 'ccx' gates. For consistency, we
        # want to make sure Qiskit uses the same decomposition for these gates as VOQC.
        # Our (hacky) solution for now is to make a copy of the benchmark that contains
        # already-decomposed versions of ccx and ccz.
        
        inqasm = open(os.path.join(d, fname), "r")
        tmp = open("copy.qasm", "w") # hardcoded filename
        p_ccz = re.compile("ccz (.*), (.*), (.*);")
        p_ccx = re.compile("ccx (.*), (.*), (.*);")
        p_rzq = re.compile("rzq\((.*),(.*)\) q\[([0-9]+)\];")
        
        for line in inqasm:
            m1 = p_ccx.match(line)
            m2 = p_ccz.match(line)
            m3 = p_rzq.match(line)
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
            elif m3:
                num1 = int(m3.group(1))
                num2 = int(m3.group(2))
                q = int(m3.group(3))
                t= mpq(int(num1), int(num2))
                y = float(mpfr(t, 53))
                tmp.write("rz(%s*pi) q[%d];\n" % (y, q))
            else:
                tmp.write(line)
        tmp.close()
        circ = QuantumCircuit.from_qasm_file("copy.qasm")

        num_gates_before = count(circ.count_ops())
        cnot_count_before = 0
        for inst, _, _ in circ.data:
            if (inst.name == "cx"):
                cnot_count_before += 1
        print("Original:\t Total %d, CNOT %d" % (num_gates_before, cnot_count_before))
        
        basis_gates = ['u1', 'u2', 'u3', 'cx']
        _unroll = Unroller(basis_gates)
        _depth_check = [Depth(), FixedPoint('depth')]
        def _opt_control(property_set):
            return not property_set['depth_fixed_point']
        _opt = [Collect2qBlocks(), ConsolidateBlocks(),
                Unroller(basis_gates),  # unroll unitaries
                Optimize1qGates(), CommutativeCancellation()]
        pm = PassManager()
        pm.append(_unroll)
        pm.append(_depth_check + _opt, do_while=_opt_control)
        start = time.perf_counter() # start timer
        new_circ = pm.run(circ)
        stop = time.perf_counter() # stop timer
        num_gates_after = count(new_circ.count_ops())
        cnot_count_after = 0
        for inst, _, _ in new_circ.data:
            if (inst.name == "cx"):
                cnot_count_after += 1
        print("Final:\t Total %d, CNOT %d\n" % (num_gates_after, cnot_count_after))
        f = open(fname.split(".")[0] + "_qiskit.qasm", "w")
        f.write(new_circ.qasm())

        f.write("%s,%d,%d,%d,%d,%f\n" % (fname, num_gates_before, cnot_count_before, num_gates_after, cnot_count_after, stop - start))
        t = open("out.csv", "a")
        csvwriter = csv.writer(t) 
        csvwriter.writerow([fname, num_gates_before, num_gates_after, cnot_count_before,cnot_count_after,stop-start])
        t.close()
        
    f.close()

if (len(sys.argv) != 3):
    print("Usage: python3 run_qiskit.py <input directory> <output file>")
    exit(-1)

run(sys.argv[1], sys.argv[2])

