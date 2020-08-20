from qiskit.transpiler.basepasses import TransformationPass
from qiskit import QuantumCircuit
import re
import os
from qiskit.qasm import pi

from interop.formatting.format_from_qasm import format_from_qasm
from interop.formatting.rzq_to_rz import rzq_to_rz
from interop.voqc import SQIR

from interop.exceptions import InvalidVOQCFunction
from qiskit.transpiler import PassManager
from interop.qiskit.voqc_optimization import VOQC
rel = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "benchmarks")

def assert_equality_circuit(before, after, list_opt=None):
    pm = PassManager()
    pm.append(VOQC())
    pm.append(VOQC(list_opt))
    new_circ = pm.run(before)
    assert (new_circ == after)

def test_AT():
    before = format_from_qasm(os.path.join(rel, "Arithmetic_and_Toffoli/tof_10.qasm"))
    before = QuantumCircuit.from_qasm_file("copy.qasm")
    rzq_to_rz(os.path.join((os.path.dirname(os.path.abspath(__file__))), "optimized_qasm_files/optim_tof_10.qasm"))
    after = QuantumCircuit.from_qasm_file(os.path.join((os.path.dirname(os.path.abspath(__file__))), "optimized_qasm_files/optim_tof_10.qasm"))
    assert_equality_circuit(before, after)
    
def test_PF():
    before = format_from_qasm(os.path.join(rel, "PF/pf2_100.qasm"))
    before = QuantumCircuit.from_qasm_file("copy.qasm")
    rzq_to_rz(os.path.join((os.path.dirname(os.path.abspath(__file__))), "optimized_qasm_files/optim_pf2_100.qasm"))
    after = QuantumCircuit.from_qasm_file(os.path.join((os.path.dirname(os.path.abspath(__file__))), "optimized_qasm_files/optim_pf2_100.qasm"))
    assert_equality_circuit(before, after)
    
def test_QFT():
    before = format_from_qasm(os.path.join(rel, "QFT_and_Adders/QFTAdd64.qasm"))
    before = QuantumCircuit.from_qasm_file("copy.qasm")
    rzq_to_rz(os.path.join((os.path.dirname(os.path.abspath(__file__))), "optimized_qasm_files/optim_QFTAdd64.qasm"))
    after = QuantumCircuit.from_qasm_file(os.path.join((os.path.dirname(os.path.abspath(__file__))), "optimized_qasm_files/optim_QFTAdd64.qasm"))
    assert_equality_circuit(before, after)
    
def test_not_propagation():
    before = QuantumCircuit(2)
    before.x(1)
    before.cx(0, 1)
    after = QuantumCircuit(2)
    after.cx(0, 1)
    after.x(1)
    assert_equality_circuit(before, after, ["not_propagation"])

def test_cancel_single_qubit_gates():
    before = QuantumCircuit(1)
    before.rz(pi/2, 0)
    before.h(0)
    before.h(0)
    after = QuantumCircuit(1)
    after.s(0)
    assert_equality_circuit(before, after, ["cancel_single_qubit_gates"])

def test_cancel_two_qubit_gates():
    before = QuantumCircuit(2)
    before.cx(0, 1)
    before.cx(0, 1)
    before.h(0)
    after = QuantumCircuit(2)
    after.h(0)
    assert_equality_circuit(before, after, ["cancel_two_qubit_gates"])

def test_merge_rotations():
    before = QuantumCircuit(1)
    before.rz(pi/4, 0)
    before.rz(pi/4, 0)
    after = QuantumCircuit(1)
    after.s(0)
    assert_equality_circuit(before, after, ["merge_rotations"])

def test_hadamard_reduction():
    before = QuantumCircuit(1)
    before.h(0)
    before.rz(pi/2, 0)
    before.h(0)
    after = QuantumCircuit(1)
    after.sdg(0)
    after.h(0)
    after.sdg(0)
    assert_equality_circuit(before, after, ["hadamard_reduction"])
