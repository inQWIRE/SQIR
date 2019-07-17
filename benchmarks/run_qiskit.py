# MUST BE RUN USING PYTHON 3

import numpy
from qiskit import QuantumCircuit
from qiskit.compiler import transpile
from qiskit.transpiler import PassManager
from qiskit.transpiler.passes import Unroller, Optimize1qGates, CommutativeCancellation, CXCancellation, Depth, FixedPoint, Collect2qBlocks, ConsolidateBlocks

H_reduction = []
X_reduction = []
U1_reduction = []
CNOT_reduction = []

for i in range(20):
#for i in range(30):
    print("Processing benchmark %d..." % i)
    circ = QuantumCircuit.from_qasm_file("random_qasm_benchmarks/benchmark%d.qasm" % i)
    #circ = QuantumCircuit.from_qasm_file("qasm_benchmarks/benchmark%d.qasm" % i)
    
    initial_counts = circ.count_ops()
    initial_h = initial_counts['h']
    initial_x = initial_counts.get('x', 0)
    initial_u1 = initial_counts.get('z', 0) + initial_counts.get('t', 0) + initial_counts.get('tdg', 0) + initial_counts.get('s', 0) + initial_counts.get('sdg', 0)
    initial_cnot = initial_counts['cx']
    
    # level 2
    #_unroll = Unroller(['u1', 'h', 'x', 'cx'])
    #_depth_check = [Depth(), FixedPoint('depth')]
    #def _opt_control(property_set):
    #    return not property_set['depth_fixed_point']
    #pm = PassManager(_unroll)
    #_opt = [Optimize1qGates(), CommutativeCancellation(), CXCancellation()]
    #pm.append(_depth_check + _opt, do_while=_opt_control)
    #newc = pm.run(circ)
    
    # level 3
    basis_gates = ['u1', 'h', 'x', 'cx']
    _unroll = Unroller(basis_gates)
    _depth_check = [Depth(), FixedPoint('depth')]
    def _opt_control(property_set):
        return not property_set['depth_fixed_point']
    _opt = [Collect2qBlocks(), ConsolidateBlocks(),
            Unroller(basis_gates),  # unroll unitaries
            Optimize1qGates(), CommutativeCancellation()]
    pm = PassManager()
    pm.append(_unroll)
    pm.append(_depth_check + _opt, do_while=_opt_control)
    newc = pm.run(circ)
    
    final_counts = newc.count_ops()
    final_h = final_counts['h']
    final_x = final_counts.get('x',0)
    final_u1 = final_counts['u1']
    final_cnot = final_counts['cx']
    
    #H_reduction.append((float(initial_h - final_h) / initial_h))
    #X_reduction.append((float(initial_x - final_x) / initial_x))
    #U1_reduction.append((float(initial_u1 - final_u1) / initial_u1))
    #CNOT_reduction.append((float(initial_cnot - final_cnot) / initial_cnot))
    
    #print("H: %d -> %d (%f)" % (initial_h, final_h, float(initial_h - final_h) / initial_h))
    #print("X: %d -> %d (%f)" % (initial_x, final_x, float(initial_x - final_x) / initial_x))
    print("U: %d -> %d (%f)" % (initial_u1,final_u1, float(initial_u1 - final_u1) / initial_u1))
    #print("CX: %d -> %d (%f)" % (initial_cnot, final_cnot, float(initial_cnot - final_cnot) / initial_cnot))
    print("Final total: %d" % (final_h + final_x + final_u1 + final_cnot))
    
#print("H: average = %f, std. = %f" % (numpy.average(H_reduction), numpy.std(H_reduction)))
#print("X: average = %f, std. = %f" % (numpy.average(X_reduction), numpy.std(X_reduction)))
#print("U1: average = %f, std. = %f" % (numpy.average(U1_reduction), numpy.std(U1_reduction)))
#print("CNOT: average = %f, std. = %f" % (numpy.average(CNOT_reduction), numpy.std(CNOT_reduction)))
    