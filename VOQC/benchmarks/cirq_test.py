import math
import numpy
import os
import sys
import re
import time
from interop.cirq.voqc_optimization import VOQC
from interop.format_from_qasm import format_from_qasm
import csv
from cirq import circuits, ops, protocols
import cirq
from cirq.contrib.qasm_import import circuit_from_qasm, qasm
from cirq.circuits import Circuit
from interop.formatting.format_from_qasm import format_from_qasm

def count(d):
    sum = 0
    for k in d.keys():
        sum += d[k]
    return sum    
def run(d, l):
    for fname in os.listdir(d):
        print(fname)
        format_from_qasm(os.path.join(d, fname))
        c = open('copy.qasm').read()
        circ = circuit_from_qasm(c)
        print(len(list(circ.all_operations())))
        l =  VOQC().optimize_circuit(circ)
        print(len(list(l.all_operations())))


    
if (len(sys.argv) != 3):
    print("Usage: python3 run_qiskit.py <input directory> <output file>")
    exit(-1)

run(sys.argv[1], sys.argv[2])

