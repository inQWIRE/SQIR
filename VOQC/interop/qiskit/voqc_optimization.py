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
from interop.exceptions import InvalidVOQCFunction, InvalidVOQCGate
from qiskit.qasm import pi
from qiskit.transpiler.exceptions import TranspilerError
import collections
import re
class VOQC(TransformationPass):
    def __init__(self, func = None):
        
        super().__init__()
        self.functions = ["optimize", "not_propagation", "cancel_single_qubit_gates", "cancel_two_qubit_gates", "hadamard_reduction", "merge_rotations"]
        
        self.voqc_gates = ['x', 'h','cx','rz','tdg','sdg','s','t','z']
        
        self.func = func if func else ["optimize"]
        
        for i in range(len(self.func)):
            if ((self.func[i] in self.functions) == False):
                raise InvalidVOQCFunction(str(self.func[i]), self.functions)
            
    def run(self, dag):
        
        #Unroll input gates to the gates supported by VOQC and check if gates are supported in VOQC
        try:
            after_dag = (BasisTranslator(eq_lib, self.voqc_gates)).run(dag)
        except TranspilerError as e:
            source_basis = {(node.op.name, node.op.num_qubits)
                    for node in dag.op_nodes()}
            for x in source_basis:
                if (x[0] in self.voqc_gates) ==False:
                    raise InvalidVOQCGate(str(x[0]))

        #Remove rz(0) gates to pass to VOQC
        circ = dag_to_circuit(after_dag)
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
        qasm_str = self.function_call("temp.qasm")
        after_circ = QuantumCircuit.from_qasm_str(qasm_str)
        #Apply Optimization list
        pm = PassManager()
        pm.append(Unroller(['x','h','cx','rz','tdg','sdg','s','t','z']))
        after_circ = pm.run(after_circ)
        to_dag = circuit_to_dag(after_circ)
        return to_dag
    
    def function_call(self,fname):
        a = SQIR(fname, False)
        for i in range(len(self.func)):
            call = getattr(a,self.func[i])
            call()
        return (a.write_str())  
