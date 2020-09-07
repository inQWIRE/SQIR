import math
import numpy
import os
import sys
import re
import time
import csv
from cirq import circuits, ops, protocols
import cirq
from cirq.optimizers import MergeInteractions,MergeSingleQubitGates, EjectPhasedPaulis, EjectZ, DropNegligible, ConvertToCzAndSingleGates
from cirq.contrib.qasm_import import circuit_from_qasm, qasm
from cirq.circuits import Circuit
from interop.formatting.format_from_qasm import format_from_qasm
from interop.cirq.voqc_optimization import VOQC
import time
   
def run(d,l):
    t = open(l, "w")
    csvwriter = csv.writer(t) 
    csvwriter.writerow(["Name", "Before", "Cirq",  "Time"])
    t.close()
    for fname in os.listdir(d):
        print(fname)
        format_from_qasm(os.path.join(d, fname))
        c = open('copy.qasm').read()
        circ = circuit_from_qasm(c)
        before = len(list(circ.all_operations()))
        print("Original:\t Total %d" % (len(list(circ.all_operations()))))
        #start = time.time()
        #circ =  VOQC().optimize_circuit(circ)
        #end = time.time()
        #first = end-start
        #after_voqc = len(list(circ.all_operations()))
        #print("After VOQC:\t Total %d" % (len(list(circ.all_operations()))))
        
        start = time.time()
        ConvertToCzAndSingleGates().optimize_circuit(circ)
        MergeInteractions().optimize_circuit(circ)
        MergeSingleQubitGates().optimize_circuit(circ)
        EjectPhasedPaulis().optimize_circuit(circ)
        EjectZ().optimize_circuit(circ)
        DropNegligible().optimize_circuit(circ)
        end = time.time()
        
        second = end-start
        final_1 = len(list(circ.all_operations()))
        print("Final:\t Total %d" % (final_1))
        t = open(l, "a")
        csvwriter = csv.writer(t) 
        csvwriter.writerow([fname, before,final_1,second])
        t.close()


    
if (len(sys.argv) != 3):
    print("Usage: python3 run_qiskit.py <input directory> <output file>")
    exit(-1)

run(sys.argv[1], sys.argv[2])

