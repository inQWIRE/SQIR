from os import path
import random
import sys

# we support a "-c" option to use the output cached in meas_outcomes.txt for re-runs

if len(sys.argv) == 1:
    from qiskit import *
    from jkq import ddsim
    
    # read circuit from shor.qasm
    circ = QuantumCircuit.from_qasm_file("shor.qasm")

    # run the circuit with ddsim
    provider = ddsim.JKQProvider()
    backend = provider.get_backend('qasm_simulator')
    job = execute(circ, backend, shots=10000) # shots = number of trials
    result = job.result()
    counts = result.get_counts(circ)

    # choose a measurement outcome
    outcomes = list(counts.keys())
    weights = list(counts.values())
    result = random.choices(outcomes, weights)[0]
    result = int(result[::-1], 2) # result is a (reversed) binary string
    print(result)

    # write outcomes to the file out.txt
    f = open("meas_outcomes.txt", "w")
    for k,v in counts.items():
        f.write("%d,%d\n" % (int(k[::-1], 2), v))
    f.close()
    
elif len(sys.argv) == 2 and sys.argv[1] == "-c":
    if not (path.exists("meas_outcomes.txt")):
        print("Cache file (meas_outcomes.txt) does not exist.")
    else:
        f = open("meas_outcomes.txt", "r")
        outcomes = []
        weights = []
        for line in f:
            line = line.split(",")
            outcomes.append(int(line[0]))
            weights.append(int(line[1]))
        
        result = random.choices(outcomes, weights)[0]
        print(result)

else:
    print("Usage: python run_circuit.py [-c]")

