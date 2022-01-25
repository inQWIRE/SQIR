import random
import sys

'''
Run shor.qasm for NUM_SHOTS shots and write out a file listing the observed 
probability of each measurement outcome.

It is also be possible to write the output state vector for more accurate 
probabilities, but I wanted to avoid doing any complex arithmetic. -KH
'''
NUM_SHOTS = 10000

if len(sys.argv) == 2:
    from qiskit import *
    from jkq import ddsim
    
    # read circuit from shor.qasm
    circ = QuantumCircuit.from_qasm_file(sys.argv[1])

    # run the circuit with ddsim
    provider = ddsim.JKQProvider()
    backend = provider.get_backend('qasm_simulator')
    job = execute(circ, backend, shots=NUM_SHOTS) # shots = number of trials
    result = job.result()
    counts = result.get_counts(circ)

    # choose a measurement outcome
    outcomes = list(counts.keys())
    weights = list(counts.values())
    result = random.choices(outcomes, weights)[0]
    result = int(result[::-1], 2) # result is a (reversed) binary string
    print(result)
    
else:
    print("Usage: python run_circuit.py <input file>")

