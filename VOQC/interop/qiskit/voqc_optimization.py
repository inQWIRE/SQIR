from qiskit.converters import circuit_to_dag, dag_to_circuit
from qiskit.transpiler.basepasses import TransformationPass
from qiskit import QuantumCircuit
import re
import os
from interop.formatting.format_from_qasm import format_from_qasm
from interop.formatting.div_pi import div_pi
from interop.formatting.rzq_to_rz import rzq_to_rz
from interop.voqc import SQIR


class VOQC(TransformationPass):
    def __init__(self, func = None):
        super().__init__()
        self.optimizations =  ["optimize", "not_propagation", "cancel_single_qubit_gates", "cancel_two_qubit_gates", "hadamard_reduction", "merge_rotations"]
        self.func = func if func else ["optimize"]
        for i in range(len(self.func)):
            if (i in self.optimizations == False):
                raise ValueError(i+ "is not a valid VOQC optimization function. These are the 6 valid optimizers:"+ self.optimizations)
    def run(self, dag):
        #Write qasm file for VOQC input
        circ = dag_to_circuit(dag)
        circ.qasm(formatted=False, filename="temp.qasm")
        
        #Decompose gates such as u1, u2, u3, ccz, ccx, rzq
        format_from_qasm("temp.qasm")
        
        #Apply Optimization list
        t = self.function_call(self.func, "copy.qasm")
        
        #Transform rzq(num, den) to rz((num/den)*pi)
        rzq_to_rz("temp2.qasm")
        to_dag = circuit_to_dag(QuantumCircuit.from_qasm_file("temp2.qasm"))
        
        os.remove("temp.qasm")
        os.remove("temp2.qasm")
        os.remove("copy.qasm")
        return to_dag
    
    def function_call(self,func_list, fname_in):
        a = SQIR(fname_in, False)
        function_dict={"not_propagation": "not_propagation",
                       "cancel_single_qubit_gates": "cancel_single_qubit_gates",
                       "cancel_two_qubit_gates" : "cancel_two_qubit_gates",
                       "merge_rotations": "merge_rotations",
                       "hadamard_reduction": "hadamard_reduction",
                       "optimize" : "optimize"}
        for i in range(len(func_list)):
            call = getattr(a,function_dict[func_list[i]])
            call()
        a.write("temp2.qasm")
