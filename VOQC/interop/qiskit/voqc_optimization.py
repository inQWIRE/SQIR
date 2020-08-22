from qiskit.converters import circuit_to_dag, dag_to_circuit
from qiskit.transpiler.basepasses import TransformationPass
from qiskit.transpiler.passes import Unroller
from qiskit import QuantumCircuit
from qiskit.transpiler.passes.basis import BasisTranslator
import os
from qiskit.transpiler import PassManager
from interop.qiskit.voqc_equivalence_library import eq_lib
from interop.formatting.format_from_qasm import format_from_qasm
from interop.formatting.rzq_to_rz import rzq_to_rz
from interop.voqc import SQIR
from interop.exceptions import InvalidVOQCFunction
from qiskit.qasm import pi
import collections
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

        #Unroll input gates to the gates supported by VOQC
        dag = (BasisTranslator(eq_lib, ['x', 'h','cx','rz','tdg','sdg','s','t','z'])).run(dag)

        circ = dag_to_circuit(dag)

        #Remove rz(0) gates to pass to VOQC
        i = 0
        while i < len(circ.data):
            if (circ.data[i][0]).name == "rz":
                if (circ.data[i][0].params)[0] == 0:
                    circ.data.pop(i)
                else:
                    i+=1
            else:
                i+=1
        circ.qasm(formatted=False, filename="temp.qasm")
        
        
        #Apply Optimization list
        t = self.function_call(self.func, "temp.qasm")
        
        #Transform rzq(num, den) to rz((num/den)*pi)
        rzq_to_rz("temp2.qasm")
        to_dag = circuit_to_dag(QuantumCircuit.from_qasm_file("temp2.qasm"))
        
        os.remove("temp.qasm")
        os.remove("temp2.qasm")
        return to_dag
    
    def function_call(self,func_list, fname):
        
        a = SQIR(fname, False)
        for i in range(len(self.func)):
            call = getattr(a,self.func[i])
            call()
        a.write("temp2.qasm")  
