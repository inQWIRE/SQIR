from qiskit import QuantumCircuit
import os
from qiskit.qasm import pi
import warnings
from interop.formatting.format_from_qasm import format_from_qasm
from interop.voqc import SQIR
from qiskit.transpiler.passes.basis import BasisTranslator

from interop.exceptions import InvalidVOQCFunction, InvalidVOQCGate
from qiskit.transpiler import PassManager
from interop.qiskit.voqc_optimization import VOQC
from interop.qiskit.voqc_equivalence_library import eq_lib
from qiskit.converters import circuit_to_dag
import unittest
rel = os.path.join(os.path.dirname(os.path.abspath(__file__)), "benchmarks")
class TestQiskitInterop(unittest.TestCase):

    
    def test_AT(self):
        before = format_from_qasm(os.path.join(rel, "Arithmetic_and_Toffoli/tof_10.qasm"))
        before = QuantumCircuit.from_qasm_file("copy.qasm")
        after = QuantumCircuit.from_qasm_file(os.path.join((os.path.dirname(os.path.abspath(__file__))), "interop/tests/optimized_qasm_files/optim_tof_10.qasm"))
        self.assertEqual(self.run_voqc(before), after)

    def test_PF(self):
        before = format_from_qasm(os.path.join(rel, "PF/pf2_100.qasm"))
        before = QuantumCircuit.from_qasm_file("copy.qasm")
        after = QuantumCircuit.from_qasm_file(os.path.join((os.path.dirname(os.path.abspath(__file__))), "interop/tests/optimized_qasm_files/optim_pf2_100.qasm"))
        self.assertEqual(self.run_voqc(before), after)

    def test_QFT(self):
        before = format_from_qasm(os.path.join(rel, "QFT_and_Adders/QFTAdd64.qasm"))
        before = QuantumCircuit.from_qasm_file("copy.qasm")
        after = QuantumCircuit.from_qasm_file(os.path.join((os.path.dirname(os.path.abspath(__file__))), "interop/tests/optimized_qasm_files/optim_QFTAdd64.qasm"))
        self.assertEqual(self.run_voqc(before), after)

    def test_not_propagation(self):
        before = QuantumCircuit(2)
        before.x(1)
        before.cx(0, 1)
        after = QuantumCircuit(2)
        after.cx(0, 1)
        after.x(1)
        self.assertEqual(self.run_voqc(before, ["not_propagation"]), after)

    def test_cancel_single_qubit_gates(self):
        before = QuantumCircuit(1)
        before.rz(pi/2, 0)
        before.h(0)
        before.h(0)
        after = QuantumCircuit(1)
        after.s(0)
        self.assertEqual(self.run_voqc(before, ["cancel_single_qubit_gates"]), after)

    def test_cancel_two_qubit_gates(self):
        before = QuantumCircuit(2)
        before.cx(0, 1)
        before.cx(0, 1)
        before.h(0)
        after = QuantumCircuit(2)
        after.h(0)
        self.assertEqual(self.run_voqc(before, ["cancel_two_qubit_gates"]), after)

    def test_merge_rotations(self):
        before = QuantumCircuit(1)
        before.rz(pi/4, 0)
        before.rz(pi/4, 0)
        after = QuantumCircuit(1)
        after.s(0)
        self.assertEqual(self.run_voqc(before, ["merge_rotations"]), after)

    def test_hadamard_reduction(self):
        before = QuantumCircuit(1)
        before.h(0)
        before.rz(pi/2, 0)
        before.h(0)
        after = QuantumCircuit(1)
        after.sdg(0)
        after.h(0)
        after.sdg(0)
        self.assertEqual(self.run_voqc(before, ["hadamard_reduction"]), after)

    def test_rzq_decomposition(self):
        qasm_str = 'OPENQASM 2.0;\n include "qelib1.inc";\n qreg q[1];\n rz(.375*pi) q[0];'
        before = QuantumCircuit.from_qasm_str(qasm_str)
        after = QuantumCircuit(1)
        after.rz(.375*pi, 0)
        self.assertEqual(before, after)

    def test_u1_decomposition(self):
        before = QuantumCircuit(1)
        before.u1(pi/8, 0)
        after = QuantumCircuit(1)
        after.rz(pi/8, 0)
        dag = (BasisTranslator(eq_lib, ['x', 'h','cx','rz','tdg','sdg','s','t','z'])).run(circuit_to_dag(before))
        self.assertEqual(circuit_to_dag(after),dag)

    def test_u2_decomposition(self):
        before = QuantumCircuit(1)
        before.u2(pi, pi, 0)
        after = QuantumCircuit(1)
        after.rz(3*pi/2, 0)
        after.h(0)
        after.rz(pi/2, 0)
        after.h(0)
        after.rz(pi/2, 0)
        dag = (BasisTranslator(eq_lib, ['h','rz'])).run(circuit_to_dag(before))
        self.assertEqual(circuit_to_dag(after),dag)

    def test_u3_decomposition(self):
        before = QuantumCircuit(1)
        before.u3(3*pi/2, pi/2, pi, 0)
        after = QuantumCircuit(1)
        after.rz(pi, 0)
        after.h(0)
        after.rz(3*pi/2, 0)
        after.h(0)
        after.rz(pi/2, 0)
        dag = (BasisTranslator(eq_lib, ['x', 'h','cx','rz','tdg','sdg','s','t','z'])).run(circuit_to_dag(before))
        self.assertEqual(circuit_to_dag(after),dag)


    def test_invalid_function(self):
        before = QuantumCircuit(1)
        before.x(0)
        with self.assertRaises(InvalidVOQCFunction):
            self.run_voqc(before, ["me"])
            
    def test_invalid_gate(self):
        before = QuantumCircuit(2)
        before.ch(0,1)
        with self.assertRaises(InvalidVOQCGate):
            self.run_voqc(before)

    def run_voqc(self, before, list_opt=None):
        pm = PassManager()
        pm.append(VOQC(list_opt))
        new_circ = pm.run(before)
        return new_circ

if __name__ == "__main__":
    unittest.main()
