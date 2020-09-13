import os
import cirq
from interop.formatting.format_from_qasm import format_from_qasm
from interop.voqc import SQIR
from cirq.contrib.qasm_import import circuit_from_qasm, qasm
from cirq.circuits import Circuit
from interop.exceptions import InvalidVOQCFunction, InvalidVOQCGate
from interop.cirq.voqc_optimization import VOQC
import unittest
from interop.cirq.decompose_cirq_gates import *
from cirq.circuits.qasm_output import QasmUGate
import numpy as np
from cirq import decompose
rel = os.path.join(os.path.dirname(os.path.abspath(__file__)), "benchmarks")
class TestQiskitInterop(unittest.TestCase):

    
    def test_AT(self):
        
        before = format_from_qasm(os.path.join(rel, "Arithmetic_and_Toffoli/tof_10.qasm"))
        with open("copy.qasm", "r") as f:
            c = f.read()
        before = circuit_from_qasm(c)
        #c.close()
        f = open(os.path.join((os.path.dirname(os.path.abspath(__file__))), "interop/tests/optimized_qasm_files/optim_tof_10.qasm"))
        t = f.read()
        f.close()
        after = circuit_from_qasm(t)
        #f.close()
        a = cirq.qasm(after)
        after = circuit_from_qasm(a)
        run = self.run_voqc(before)
        run = cirq.qasm(run)
        run = circuit_from_qasm(run)
        self.assertEqual(run, after)

    

    def test_not_propagation(self):
        q_0 = cirq.NamedQubit("q_0")
        q_1 = cirq.NamedQubit("q_1")

        before = cirq.Circuit([cirq.X.on(q_1),
                                cirq.CNOT.on(q_0,q_1)])
        after = cirq.Circuit([cirq.CNOT.on(q_0,q_1),
                                cirq.X.on(q_1)])
        self.assertEqual(cirq.qasm(self.run_voqc(before, ["not_propagation"])), cirq.qasm(after))

    def test_cancel_single_qubit_gates(self):
        q_0 = cirq.NamedQubit("q_0")
        before = cirq.Circuit([cirq.rz(np.pi/2).on(q_0), cirq.H.on(q_0), cirq.H.on(q_0)])
        after = cirq.Circuit([cirq.S.on(q_0)])
        self.assertEqual(self.run_voqc(before, ["cancel_single_qubit_gates"]), after)
    
    def test_cancel_two_qubit_gates(self):
        q_0 = cirq.NamedQubit("q_0")
        q_1 = cirq.NamedQubit("q_1")
        before = cirq.Circuit([cirq.CNOT.on(q_0,q_1), cirq.CNOT.on(q_0, q_1), cirq.H.on(q_0)])
        after = cirq.Circuit([cirq.H.on(q_0)])
        self.assertEqual(self.run_voqc(before, ["cancel_two_qubit_gates"]), after)
        
    def test_merge_rotations(self):
        q_0 = cirq.NamedQubit("q_0")
        before = cirq.Circuit([cirq.rz(np.pi/4).on(q_0), cirq.rz(np.pi/4).on(q_0)])
        after = cirq.Circuit([cirq.S.on(q_0)])
        self.assertEqual(self.run_voqc(before, ["merge_rotations"]), after)
    
    def test_hadamard_reduction(self):
        q_0 = cirq.NamedQubit("q_0")
        before = cirq.Circuit([cirq.H.on(q_0), cirq.rz(np.pi/2).on(q_0), cirq.H.on(q_0)])
        after = cirq.Circuit([cirq.S.on(q_0)**-1, cirq.H.on(q_0), cirq.S.on(q_0)**-1])
        self.assertEqual(self.run_voqc(before, ["hadamard_reduction"]), after)

    
    def test_u3_decomposition(self):
        q_0 = cirq.NamedQubit("q_0")
        before = cirq.Circuit([QasmUGate(3/2, 1/2, 1).on(q_0)])
        after = cirq.Circuit([cirq.rz(np.pi).on(q_0), cirq.H.on(q_0), cirq.rz((3*np.pi)/2).on(q_0), cirq.H.on(q_0), cirq.rz(np.pi/2).on(q_0)])
        circuit = Circuit(decompose(before, intercepting_decomposer=decompose_library,keep=need_to_keep))
        self.assertEqual(circuit, after)
 
    def test_invalid_function(self):
        q_0 = cirq.NamedQubit("q_0")
        before = cirq.Circuit([cirq.H.on(q_0)])
        with self.assertRaises(InvalidVOQCFunction):
            self.run_voqc(before, ["me"])
            
    def test_invalid_gate(self):
        q_0 = cirq.NamedQubit("q_0")
        q_1 = cirq.NamedQubit("q_1")
        q_2 = cirq.NamedQubit("q_2")
        before = cirq.Circuit([cirq.CSWAP.on(q_0,q_1,q_2)])
        with self.assertRaises(ValueError):
            self.run_voqc(before)
    def run_voqc(self, before, list_opt=None):
        new_circ = VOQC(list_opt).optimize_circuit(before)
        return new_circ
     
if __name__ == "__main__":
    unittest.main()
