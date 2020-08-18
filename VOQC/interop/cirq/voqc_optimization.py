from cirq import circuits, ops, protocols
import cirq
from cirq.contrib.qasm_import import circuit_from_qasm, qasm
import re
import os
from cirq.circuits import Circuit
from interop.format_qasm.format_from_qasm import format_from_qasm
from interop.format_qasm.div_pi import div_pi
from interop.format_qasm.rzq_to_rz import rzq_to_rz
from interop.voqc import SQIR

class VOQC:
    def __init__(self, func = None):
        super().__init__()
        self.optimizations =  ["optimize", "not_propagation", "cancel_single_qubit_gates", "cancel_two_qubit_gates", "hadamard_reduction", "merge_rotations"]
        self.func = func if func else ["optimize"]
        for i range(len(self.func)):
            if (i in self.optimizations == False):
                print("%s is not a valid VOQC optimization function. These are the 6 valid optimizers: %s" (i, self.optimizations))
    def optimize_circuit(self, circuit: circuits.Circuit):
        
        #Write qasm file from circuit
        qasm_str = cirq.qasm(circuit)
        f = open("temp.qasm", "w")
        f.write(qasm_str)
        f.close()
        
        #Decompose gates such as ccz, ccx, u1, u2, u3
        format_from_qasm("temp.qasm")
        
        #Call VOQC optimizations from input list
        t = self.function_call(self.func, "copy.qasm")
        rzq_to_rz("temp.qasm")
        
        #Get Cirq Circuit from qasm file
        c = open("temp.qasm").read()
        circ = circuit_from_qasm(c)
        os.remove("temp.qasm")
        os.remove("copy.qasm")
        return circ
    
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
        a.write("temp.qasm", False)     
    
