from voqc import *


a = load("/home/ag/Documents/SQIR/VOQC/benchmarks/Arithmetic_and_Toffoli/tof_10.qasm")
a.optimize()
a.write("/home/ag/Documents/VOQC_PythonBindings/SQIR/VOQC/extraction/_build/with_qopt10.qasm")



