from cirq import circuits, ops, protocols
import cirq
from cirq.contrib.qasm_import import circuit_from_qasm, qasm
import re
import os

from cirq.circuits import Circuit
from interop.formatting.format_from_qasm import format_from_qasm
from interop.formatting.rzq_to_rz import rzq_to_rz
from interop.voqc import SQIR

class VOQC:
    def __init__(self, func = None):
        self.functions = ["optimize", "not_propagation", "cancel_single_qubit_gates", "cancel_two_qubit_gates", "hadamard_reduction", "merge_rotations"]
        self.func = func if func else ["optimize"]
        for i in range(len(self.func)):
            if ((self.func[i] in self.functions) == False):
                raise InvalidVOQCFunction(str(self.func[i]), self.functions)
    def optimize_circuit(self, circuit: circuits.Circuit):
        
        #Write qasm file from circuit
        qasm_str = cirq.qasm(circuit)
        f = open("temp.qasm", "w")
        f.write(qasm_str)
        f.close()
        
        #Decompose gates such as ccz, ccx, u1, u2, u3
        format_from_qasm("temp.qasm")
        #Call VOQC optimizations from input list and go from rzq to rz
        t = self.function_call("copy.qasm")
        rzq_to_rz("temp2.qasm")
        #Get Cirq Circuit from qasm file
        c = open("temp2.qasm").read()
        circ = circuit_from_qasm(c)
    
        #Remove temporary files
        #os.remove("temp.qasm")
        #os.remove("copy.qasm")
        
        return circ
    
    def function_call(self,fname_in):
        a = SQIR(fname_in, False)
        for i in range(len(self.func)):
            call = getattr(a,self.func[i])
            call()
        a.write("temp2.qasm")     
    
