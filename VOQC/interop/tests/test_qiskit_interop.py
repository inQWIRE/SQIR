from qiskit.converters import circuit_to_dag, dag_to_circuit
from qiskit.transpiler.basepasses import TransformationPass
from qiskit import QuantumCircuit
import re
import os
from interop.formatting.format_from_qasm import format_from_qasm
from interop.formatting.div_pi import div_pi
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
