#!/usr/bin/env python

import os
import random
import sys

def gen_qubit(num_qubits):
    return str(random.randint(0,num_qubits-1))

def gen_gate(num_qubits):
    g = random.randint(0, 7)
    if g < 7:
        q = gen_qubit(num_qubits)
        return [g, q]
    else:
        q1 = gen_qubit(num_qubits)
        q2 = q1
        while (q2 == q1):
            q2 = gen_qubit(num_qubits)
        return [g, q1, q2]

def gate_to_qasm(l):
    g = l[0]
    if g == 0:
        return ("h q[" + l[1] + "]")
    elif g == 1:
        return ("x q[" + l[1] + "]")
    elif g == 2:
        return ("z q[" + l[1] + "]")
    elif g == 3:
        return ("s q[" + l[1] + "]")
    elif g == 4:
        return ("sdg q[" + l[1] + "]")
    elif g == 5:
        return ("t q[" + l[1] + "]")
    elif g == 6:
        return ("tdg q[" + l[1] + "]")
    elif g == 7:
        return ("cx q[" + l[1] + "]" + ", q[" + l[2] + "]")

''' 
  Super simple function for generating a random (well-typed) QASM circuit. 
  Uses a uniform distribution (or whatever the distribution of randint is) 
  over gates & arguments.
'''
def gen_programs(num_qubits, num_gates, num_progs):
    progs = []
    for x in range(num_progs):
        prog = []
        for g in range(num_gates):
            prog.append(gen_gate(num_qubits))
        progs.append(prog)
    return progs

def write_qasm_prog(f, prog, num_qubits): # f should be an open file
    f.write("OPENQASM 2.0;\ninclude \"qelib1.inc\";\n\n")
    f.write("qreg q[" + str(num_qubits) + "];\n")
    f.write("\n")
    for g in prog:
        f.write("%s;\n" % gate_to_qasm(g))

if (len(sys.argv) < 5):
    print "Usage: ./generate_random_programs.py <output directory> <NUM_PROGS> <NUM_QUBITS> <NUM_GATES>"
    exit(-1)
    
dir = sys.argv[1]
NUM_PROGS = int(sys.argv[2])
NUM_QUBITS = int(sys.argv[3])
NUM_GATES = int(sys.argv[4])

print "Generating %d programs with %d qubits and %d gates in the %s directory." % (NUM_PROGS, NUM_QUBITS, NUM_GATES, dir)

progs = gen_programs(NUM_QUBITS, NUM_GATES, NUM_PROGS)

# write QASM programs to multiple files
i = 0
os.mkdir(dir)
for p in progs:
    qasm_fname = os.path.join(dir, "benchmark%d.qasm" % i)
    qasm_f = open(qasm_fname, "w")
    write_qasm_prog(qasm_f, p, NUM_QUBITS)
    qasm_f.close()
    i += 1
 
 
 

        