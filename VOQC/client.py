from voqc import *

a = load("benchmarks/Arithmetic_and_Toffoli/tof_3.qasm")
a.optimize()
a.write("extraction/tof.qasm")



