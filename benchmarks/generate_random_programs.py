#!/usr/bin/env python

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
        return ("h q" + l[1])
    elif g == 1:
        return ("x q" + l[1])
    elif g == 2:
        return ("z q" + l[1])
    elif g == 3:
        return ("s q" + l[1])
    elif g == 4:
        return ("sdg q" + l[1])
    elif g == 5:
        return ("t q" + l[1])
    elif g == 6:
        return ("tdg q" + l[1])
    elif g == 7:
        return ("cx q" + l[1] + ", q" + l[2])

def gate_to_sqire(l):
    g = l[0]
    if g == 0:
        return ("_H " + l[1])
    elif g == 1:
        return ("_X " + l[1])
    elif g == 2:
        return ("_Z " + l[1])
    elif g == 3:
        return ("_P " + l[1])
    elif g == 4:
        return ("_PDAG " + l[1])
    elif g == 5:
        return ("_T " + l[1])
    elif g == 6:
        return ("_TDAG " + l[1])
    elif g == 7:
        return ("_CNOT " + l[1] + " " + l[2])

''' 
  Super simple function for generating a random (well-typed) SQIRE program and
  QASM circuit. Uses a uniform distribution (or whatever the distribution of  
  randint is) over gates & arguments.
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
    for q in range(num_qubits):
        f.write("qreg q" + str(q) + "[1];\n")
    f.write("\n")
    for g in prog:
        f.write("%s;\n" % gate_to_qasm(g))

def write_sqire_prog(f, prog, n): # f should be an open file
    f.write("let prog%d = [\n" % n)
    for g in prog:
        f.write("%s; " % gate_to_sqire(g))
    f.write("\n]\n\n")


NUM_QUBITS = 15
NUM_GATES = 5000
NUM_PROGS = 20
progs = gen_programs(NUM_QUBITS, NUM_GATES, NUM_PROGS)

# write SQIRE programs to one large file
sqire_fname = "random_sqire_progs.ml"
sqire_f = open(sqire_fname, "w")
sqire_f.write("open Extracted_code\n\n")
i = 0
for p in progs:
    write_sqire_prog(sqire_f, p, i)
    i += 1
sqire_f.write("let progs = [")
for x in range(i):
    sqire_f.write("prog%d; " % x)
sqire_f.write("]")
sqire_f.close()

# write QASM programs to multiple files
i = 0
for p in progs:
    qasm_fname = "benchmark%d.qasm" % i
    qasm_f = open(qasm_fname, "w")
    write_qasm_prog(qasm_f, p, NUM_QUBITS)
    qasm_f.close()
    i += 1
 
 
 

        