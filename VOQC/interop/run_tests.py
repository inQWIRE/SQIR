import os.path
from interop.tests.test_qiskit_interop import *

#Test entire benchmarks
test_PF()
test_QFT()
test_AT()

#Test individual functions
test_not_propagation()
test_cancel_single_qubit_gates()
test_cancel_two_qubit_gates()
test_merge_rotations()
test_hadamard_reduction()
