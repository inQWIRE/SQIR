import math
import numpy
import os
from qiskit import QuantumCircuit
from qiskit.transpiler import PassManager
from qiskit.transpiler.passes import Unroller, Optimize1qGates, CommutationAnalysis, CommutativeCancellation, CXCancellation, Depth, FixedPoint, Collect2qBlocks, ConsolidateBlocks
import sys
import re
import time
from interop.format_from_qasm import format_from_qasm
from interop.div_pi import div_pi
from interop.rzq_to_rz import rzq_to_rz
from voqc import SQIR
import csv
from qiskit.circuit.gate import Gate
from qiskit.circuit.quantumregister import QuantumRegister
from qiskit.qasm import pi
from gmpy2 import *

def count(d):
    sum = 0
    for k in d.keys():
        sum += d[k]
    return sum    
def run(d, l):
    t = open(l, "w")
    csvwriter = csv.writer(t) 
    csvwriter.writerow(["Name", "Before", "After VOQC", "Final", "Before CNOT","VOQC CNOT","Final CNOT","Time"])
    t.close()
    for fname in os.listdir(d):
        print("Processing %s..." % fname)
        inqasm = open(os.path.join(d, fname), "r")
        format_from_qasm(os.path.join(d, fname))
        circ = QuantumCircuit.from_qasm_file("copy.qasm")
                
        num_gates_before = count(circ.count_ops())
        cnot_count_before = 0
        for inst, _, _ in circ.data:
            if (inst.name == "cx"):
                cnot_count_before += 1
        print("Original:\t Total %d, CNOT %d" % (num_gates_before, cnot_count_before))
        pm = PassManager()
        pm.append(VOQC(["optimize"]))
        start = time.perf_counter()
        new_circ = pm.run(circ)
        stop = time.perf_counter()
        first = stop-start

        voqc_gates = count(new_circ.count_ops())
        cnot_voqc = 0
        for inst, _, _ in new_circ.data:
            if (inst.name == "cx"):
                cnot_voqc += 1
        print("After VOQC:\t Total %d, CNOT %d" % (voqc_gates, cnot_voqc))
                
        basis_gates = ['u1','u2','u3','cx']
        _unroll = Unroller(basis_gates)
        _depth_check = [Depth(), FixedPoint('depth')]
        def _opt_control(property_set):
            return not property_set['depth_fixed_point']
        _opt = [Collect2qBlocks(), ConsolidateBlocks(), Unroller(basis_gates),
                Optimize1qGates(), CommutativeCancellation()]
        pm1 = PassManager()
        pm1.append(_unroll)
        pm1.append(_depth_check + _opt, do_while=_opt_control)
        start = time.perf_counter() # start timer
        new_circ = pm1.run(new_circ)
        stop = time.perf_counter() # stop timer
        second = stop-start
    
        num_gates_after = count(new_circ.count_ops())
        cnot_count_after = 0
        for inst, _, _ in new_circ.data:
            if (inst.name == "cx"):
                cnot_count_after += 1
        print("Final:\t Total %d, CNOT %d\n" % (num_gates_after, cnot_count_after))

        cwd = os.getcwd()
        f = open(os.path.join((os.path.join(cwd, "voqc_build")), fname.split(".")[0]) + "_qiskit.qasm", "w")
        f.write(new_circ.qasm())

        t = open(l, "a")
        csvwriter = csv.writer(t) 
        csvwriter.writerow([fname, num_gates_before, voqc_gates, num_gates_after, cnot_count_before,cnot_voqc,cnot_count_after,first+second])
        t.close()
    f.close()
    
if (len(sys.argv) != 3):
    print("Usage: python3 run_qiskit.py <input directory> <output file>")
    exit(-1)

run(sys.argv[1], sys.argv[2])

