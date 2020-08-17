from qiskit.converters import circuit_to_dag, dag_to_circuit
from qiskit.transpiler.basepasses import TransformationPass
from qiskit import QuantumCircuit
import re
import os
from interop.format_from_qasm import format_from_qasm
from interop.div_pi import div_pi
from interop.rzq_to_rz import rzq_to_rz
from voqc import SQIR


class VOQC(TransformationPass):
    def __init__(self, func = None):
        super().__init__()
        self.func = func if func else ["optimize"]
    def run(self, dag):
        circ1 = dag_to_circuit(dag)
        circ1.qasm(formatted=False, filename="temp.qasm")
        format_from_qasm("temp.qasm")
        t = self.function_call(self.func, "copy.qasm")
        rzq_to_rz("temp2.qasm")
        to_circ = QuantumCircuit.from_qasm_file("temp2.qasm")
        to_dag = circuit_to_dag(to_circ)
        #os.remove("temp.qasm")
        #os.remove("temp2.qasm")
        #os.remove("copy.qasm")
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
