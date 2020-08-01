from cirq import circuits, ops, protocols
import cirq
from cirq.contrib.qasm_import import circuit_from_qasm, qasm
import re
from cirq.optimizers import *
from cirq.circuits import *

if TYPE_CHECKING:
    import cirq
class VOQC:
    def __init__(self, func = None):
        super().__init__()
        self.func = func if func else ["optimize"]
    def optimize_circuit(self, circuit: circuits.Circuit):
        qasm_str = cirq.qasm(circuit)
        f = open("temp.qasm", "w")
        f.write(qasm_str)
        f.close()
        format_from_qasm("temp.qasm")
        t = self.function_call(self.func, "copy.qasm")
        rzq_to_rz("temp2.qasm")
        circ = circuit_from_qasm("temp2.qasm")
        os.remove("temp.qasm")
        os.remove("temp2.qasm")
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
        a.write("temp2.qasm", False)     
    
