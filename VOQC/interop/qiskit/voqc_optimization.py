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


class VOQC(TransformationPass):
    def __init__(self, func = None):
        super().__init__()
        self.functions = ["optimize", "not_propagation", "cancel_single_qubit_gates", "cancel_two_qubit_gates", "hadamard_reduction", "merge_rotations"]
        self.func = func if func else ["optimize"]
        for i in range(len(self.func)):
            if ((self.func[i] in self.functions) == False):
                raise InvalidVOQCFunction(str(self.func[i]), self.functions)
    def run(self, dag):
        """Run the VOQC optimizations in passed list on `dag`.
        Args:
            dag (DAGCircuit): the DAG to be optimized.
        Returns:
            DAGCircuit: the optimized DAG after list of VOQC optimizations.
        Raises:
            InvalidVOQCGate: if gate in circuit is not currently supported by VOQC
        """
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
        for i in range(len(self.func)):
            call = getattr(a,self.func[i])
            call()
        a.write("temp2.qasm")  
