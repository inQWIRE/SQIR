from qiskit.converters import circuit_to_dag
from qiskit.converters import dag_to_circuit
from qiskit.transpiler.basepasses import TransformationPass
from voqc import SQIR, load
from qiskit import QuantumCircuit
import re
import os
from gmpy2 import *


class VOQC(TransformationPass):
    def __init__(self, func = None, out = None):
        super().__init__()
        self.func = func if func else ["optimize"]
    def run(self, dag):
        circ = dag_to_circuit(dag)
        y =circ.qasm(formatted=False, filename="temp.qasm")
        t = self.function_call(self.func, "temp.qasm")
        os.remove("temp.qasm")
        u = self.rzq("temp2.qasm")
        to_circ = QuantumCircuit.from_qasm_file(str("temp2.qasm"))
        #os.remove("temp2.qasm")
        to_dag = circuit_to_dag(to_circ)
        return to_dag
    def function_call(self,func_list, fname_in):
        a = load(str(fname_in))
        function_dict={"not_propagation": "not_propagation",
                       "cancel_single_qubit_gates": "cancel_single_qubit_gates",
                       "cancel_two_qubit_gates" : "cancel_two_qubit_gates",
                       "merge_rotations": "merge_rotations",
                       "hadamard_reduction": "hadamard_reduction",
                       "optimize" : "optimize"}
        for i in range(len(func_list)):
            call = getattr(a, str(function_dict[func_list[i]]))
            call()
        a.write(str("temp2.qasm"))
    def rzq(self, fname_in):
        print("HIIIIIIIIIIIIIIIIIIIIIII)")
        line1 = []
        count = 0
        with open(str(fname_in), 'r') as f:
            data = f.readlines()
            for line in data:
                if line.startswith("rzq"):
                    line1.append(count)
                count = count+1
            print(line1)
        for i in range(len(line1)):
            a = (re.findall('\d+', data[line1[i]]))[0]
            b = (re.findall('\d+', data[line1[i]]))[1]
            print(data[i])
            t= mpq(int(a), int(b))
            q = data[line1[i]].index('q[')
            w = data[line1[i]].index(']')
            fin = (data[line1[i]])[q:w+1]
            y = float(mpfr(t, 53))
            data[line1[i]] = "rz(%f*pi) %s;\n" % (y, fin)
        with open(str(fname_in), 'w') as f:
            f.writelines(data)
