import sys

'''
Simulate a circuit for 1000 trials. Useful to check that (small) circuits are
doing the right thing.
'''

if len (sys.argv) != 2:
    print("Missing input file.")
    exit(-1)

from qiskit import *
from jkq import ddsim
provider = ddsim.JKQProvider()
backend = provider.get_backend('qasm_simulator')
circ = QuantumCircuit.from_qasm_file(sys.argv[1])
job = execute(circ, backend, shots=1000)
result = job.result()
print(result.get_counts(circ))
