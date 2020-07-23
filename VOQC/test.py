from qiskit.transpiler.passes import Optimize1qGates
from qiskit import QuantumCircuit
from qiskit.compiler import transpile
from qiskit.transpiler import PassManager
from qiskit.converters import circuit_to_dag
from voqc_pass import VOQC
from qiskit.transpiler import basepasses
import math
import numpy
import os
from qiskit import QuantumCircuit
from qiskit.compiler import transpile
from qiskit.transpiler import PassManager
import sys
import re
import time

inqasm = open("/home/ag/Documents/SQIR/VOQC/benchmarks/Arithmetic_and_Toffoli/gf2^9_mult.qasm", "r")
tmp = open("copy.qasm", "w") # hardcoded filename
p_ccz = re.compile("ccz (.*), (.*), (.*);")
p_ccx = re.compile("ccx (.*), (.*), (.*);")
p_rzq = re.compile("rzq (.*), (.*);")
        
for line in inqasm:
    m1 = p_ccx.match(line)
    m2 = p_ccz.match(line)
    m3 = line.startswith('rzq')
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
        a = (re.findall('\d+', line))[0]
        b = (re.findall('\d+', line))[1]
        t= mpq(int(a), int(b))
        q = line.index('q[')
        t = line.index(']')
        fin = line[q:t+1]
        y = float(mpfr(t, 53))
        tmp.write("rz(%f) %s;\n" % (y))
        
    else:
        tmp.write(line)
tmp.close()
def count(d):
    sum = 0
    for k in d.keys():
        sum += d[k]
    return sum
circ = QuantumCircuit.from_qasm_file("copy.qasm")
pass_ = VOQC(["optimize"])
first = count(circ.count_ops())
print(first)
pm = PassManager(pass_)
new_circ=pm.run(circ)
print(count(new_circ.count_ops()))
