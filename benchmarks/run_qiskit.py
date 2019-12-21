'''
    We consider running Qiskit with two different settings:
    - A: the optimizations used up to level 2 with basis {u1, H, X, CNOT}
    - B: the optimizations used up to level 3 with basis {u1, u2, u3, CNOT}
    
    References:
    - https://github.com/Qiskit/qiskit-terra/blob/master/qiskit/transpiler/preset_passmanagers/level2.py
    - https://github.com/Qiskit/qiskit-terra/blob/master/qiskit/transpiler/preset_passmanagers/level3.py
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

def count(d):
    sum = 0
    for k in d.keys():
        sum += d[k]
    return sum
    
def get_closest_multiple_of_pi(theta):
    l = [x * (math.pi/4) for x in range(-7,8)]
    l1 = [abs(x - theta) for x in l]
    return(range(-7,8)[l1.index(min(l1))])

def run_on_nam_benchmarks(fname):
    
    f = open(fname, "w")
    
    f.write("name, num gates before, t-count before, num gates after (A), t-count after (A), num gates after (B)\n")
    
    for fname in os.listdir("nam-benchmarks"):

        print("Processing %s..." % fname)
        
        # Some of the benchmarks contain 'ccz' and 'ccx' gates. For consistency, we
        # want to make sure Qiskit uses the same decomposition for these gates as VOQC.
        # Our (hacky) solution for now is to make a copy of the benchmark that contains
        # already-decomposed versions of ccx and ccz.
        
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
        circ = QuantumCircuit.from_qasm_file("copy.qasm")

        num_gates_before = count(circ.count_ops())
        # getting a t-count only makes sense for the current benchmarks, which only 
        # contain rotations by PI/4
        t_count_before = 0
        for inst, _, _ in circ.data:
            if (inst.name == "t" or inst.name == "tdg"):
                t_count_before += 1
        print("\nORIGINAL: %d gates, %d T-gates" % (num_gates_before, t_count_before))

        # A
        basis_gates = ['u1', 'h', 'x', 'cx']
        _unroll = Unroller(basis_gates)
        _depth_check = [Depth(), FixedPoint('depth')]
        def _opt_control(property_set):
           return not property_set['depth_fixed_point']
        _opt = [Optimize1qGates(), CommutativeCancellation()]
        pmA = PassManager()
        pmA.append(_unroll)
        pmA.append([CommutationAnalysis()])
        pmA.append(_depth_check + _opt, do_while=_opt_control)
        circA = pmA.run(circ)
        num_gates_afterA = count(circA.count_ops())
        t_count_afterA = 0
        for inst, _, _ in circA.data:
            if (inst.name == "u1"):
                if (get_closest_multiple_of_pi(inst.params[0]) % 2 == 1):
                    t_count_afterA += 1
        print("OPTIMIZED (A): %d gates, %d T-gates" % (num_gates_afterA, t_count_afterA))
        
        # B
        basis_gates = ['u1', 'u2', 'u3', 'cx']
        _unroll = Unroller(basis_gates)
        _depth_check = [Depth(), FixedPoint('depth')]
        def _opt_control(property_set):
            return not property_set['depth_fixed_point']
        _opt = [Collect2qBlocks(), ConsolidateBlocks(),
                Unroller(basis_gates),  # unroll unitaries
                Optimize1qGates(), CommutativeCancellation()]
        pmB = PassManager()
        pmB.append(_unroll)
        pmB.append(_depth_check + _opt, do_while=_opt_control)
        circB = pmB.run(circ)
        num_gates_afterB = count(circB.count_ops())
        # not sure how to get the t-gate count for the {u1, u2, u3, CX} gate set
        print("OPTIMIZED (B): %d gates\n" % (num_gates_afterB))

        f.write("%s,%d,%d,%d,%d,%d\n" % (fname, num_gates_before, t_count_before, num_gates_afterA, t_count_afterA, num_gates_afterB))
        
    f.close()

if (len(sys.argv) != 2):
    print("Usage: python3 run_qiskit.py output_file")
    exit(-1)

run_on_nam_benchmarks(sys.argv[1])

