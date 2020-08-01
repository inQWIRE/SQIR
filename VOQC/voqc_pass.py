from qiskit.converters import circuit_to_dag
from qiskit.converters import dag_to_circuit
from qiskit.transpiler.basepasses import TransformationPass
from voqc import SQIR
from qiskit import QuantumCircuit
import re
import os
from gmpy2 import *
from qiskit.transpiler import PassManager
import ast
from format_voqc import *
import os.path

class VOQC(TransformationPass):
    def __init__(self, func = None, out = None):
        super().__init__()
        self.func = func if func else ["optimize"]
    def run(self, dag):
        circ1 = dag_to_circuit(dag)
        circ1.qasm(formatted=False, filename="temp.qasm")
        format_from_qasm("temp.qasm")
        div_pi("copy.qasm")
        t = self.function_call(self.func, "copy.qasm")
        rzq_to_rz("temp2.qasm")
        to_circ = QuantumCircuit.from_qasm_file("temp2.qasm")
        to_dag = circuit_to_dag(to_circ)
        os.remove("temp.qasm")
        os.remove("temp2.qasm")
        return to_dag
    
    def function_call(self,func_list, fname_in):
        a = SQIR(fname_in)
        function_dict={"not_propagation": "not_propagation",
                       "cancel_single_qubit_gates": "cancel_single_qubit_gates",
                       "cancel_two_qubit_gates" : "cancel_two_qubit_gates",
                       "merge_rotations": "merge_rotations",
                       "hadamard_reduction": "hadamard_reduction",
                       "optimize" : "optimize"}
        for i in range(len(func_list)):
            call = getattr(a,function_dict[func_list[i]])
            call(False)
        a.write("temp2.qasm", False)
