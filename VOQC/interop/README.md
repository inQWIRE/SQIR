# VOQC Interoperability

## Overview

This README contains instructions for using the VOQC optimizer with widely used quantum frameworks.

VOQC is currently compatible with the following frameworks:
* Cirq (Version 0.8.2)
* Qiskit (Version 0.19.6)

The VOQC transpiler pass currently supports the following gates:
* t, tdg
* s, sdg
* z
* rz(f * pi)
* h
* x
* cnot
* ccz, ccx
* u1, u2, u3



## Compilation

Dependencies:
  * OCaml version 4.08.1 
  * dune (`opam install dune`)
  * menhir (`opam install menhir`)
  * batteries (`opam install batteries`)
  * OCaml OpenQASM parser (`opam install openQASM`)

**Library**: Run `dune build extraction/libvoqc.so` in the VOQC directory. This will produce `libvoqc.so` in _build/default/extraction/.

## Using VOQC Transpiler Pass in Qiskit

To pass a qiskit circuit to the VOQC optimizer, append `VOQC([list of optimizations])` to a pass manager. The argument `list of optimizations` is an optional argument that allows custom optimizations to be run. Appending `VOQC()` to a pass manager without a list will run the main optimize function in VOQC. The client file must be run from the VOQC directory.

*Example*: The following is a transpiler pass to VOQC using a circuit built in qiskit. 
```
from qiskit.transpiler import PassManager
from interop.qiskit.voqc_optimization import VOQC
from qiskit import QuantumCircuit

 #Build Quantum Circuit
 circ = QuantumCircuit(2)
 circ.cx(0, 1)
 circ.cx(0, 1)
 circ.h(0)
 
 #Pass to VOQC
 pm = PassManager().
 #Call cancel_two_qubit_gates
 pm.append(VOQC(["cancel_two_qubit_gates"]))
 new_circ = pm.run(circ)
 
```
*Example*: The following is a transpiler pass to VOQC using a qasm file as an input. 

```
from qiskit.transpiler import PassManager
from interop.qiskit.voqc_optimization import VOQC
from qiskit.circuit import QuantumCircuit
import os.path

rel = os.path.dirname(os.path.abspath(__file__))
#Decompose gates not supported in qiskit such as rzq, ccx, ccz
#Only necessary if input file has ccx, ccz, rzq gates
format_from_qasm(os.path.join(rel, "benchmarks/Arithmetic_and_Toffoli/tof_3.qasm"))
circ = QuantumCircuit.from_qasm_file("copy.qasm")

pm = PassManager()
#Pass no args to run optimize function
pm.append(VOQC())
new_circ = pm.run(circ)
```


## Running Benchmarks using VOQC and Qiskit

The run_qiskit_voqc.py file in test/run_benchmarks provides the ability to run VOQC optimizations, followed by Qiskit optimizations to optimize a qasm file, and see total gate improvements. Copy this file into the VOQC directory. The file writes out the optimized gate counts to a csv file.

*Example*: The following is an example of running run_qiskit_voqc.py. Only the first output in the directory is shown for simplicity.
```
$ python run_qiskit_voqc.py benchmarks/Arithmetic_and_Toffoli out.csv
Processing gf2^9_mult.qasm...
Original:	 Total 1095, CNOT 494
After VOQC:	 Total 885, CNOT 494
Final:	 Total 882, CNOT 494
```

## Using VOQC optimization pass in Cirq

Similarly to Qiskit, the VOQC optimizations can be called in Cirq by calling the optimize circuit function that is implement in the VOQC optimization class. By passing`VOQC([list of optimizations])` to the optimize circuit funcion, VOQC will return an optimized Cirq circuit. The argument `list of optimizations` is an optional argument that allows custom optimizations to be run. Calling `VOQC()` without a list will run the main optimize function in VOQC. The client file must be run from the VOQC directory.
*Example*: The following is an optimization pass to VOQC using a circuit built in Cirq. 
```
from interop.cirq.voqc_optimization import VOQC
import cirq

a = cirq.NamedQubit("a")
b = cirq.NamedQubit("b")
c = cirq.NamedQubit("c")

# Circuit being passed to VOQC
circuit = cirq.Circuit([cirq.X.on(a), cirq.H.on(b), cirq.S.on(c)])
new_circ = VOQC(["optimize"]).optimize_circuit(circuit)
```


## Running Benchmarks using VOQC and Cirq

The run_cirq_voqc.py file in test/run_benchmarks provides the ability to run VOQC optimizations, followed by Cirq optimizations to optimize a qasm file, and see total gate improvements. Copy this file into the VOQC directory. The file writes out the optimized gate counts to a csv file. The Product Formula benchmarks will produce an error due to the miniscule rotations around the z-axis.

*Example*: The following is an example of running run_cirq_voqc.py. Only the first output in the directory is shown for simplicity.
```
$ python run_cirq_voqc.py benchmarks/Arithmetic_and_Toffoli out.csv
gf2^9_mult.qasm
Original:	 Total 1095
After VOQC:	 Total 885
Final:	 Total 1034
```
