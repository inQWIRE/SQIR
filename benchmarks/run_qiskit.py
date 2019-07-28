# MUST BE RUN USING PYTHON 3

'''
    We consider running Qiskit with two different settings:
    - A: the optimizations used at level 2 with basis {u1, H, X, CNOT}
    - B: the optimizations used at level 2 with basis {u1, u2, u3, CNOT}
    
    TODO: add the following (the code commented out below gives an error??)
    - C: the optimizations used at level 3 with basis {u1, u2, u3, CNOT}
'''

import numpy
import os
from qiskit import QuantumCircuit
from qiskit.compiler import transpile
from qiskit.transpiler import PassManager
from qiskit.transpiler.passes import Unroller, Optimize1qGates, CommutativeCancellation, CXCancellation, Depth, FixedPoint, Collect2qBlocks, ConsolidateBlocks
import sys

def run_on_random_benchmarks(dir):

    # A
    print("Running Qiskit on setting A")
    reductions = {'u1': [], 'h': [], 'x': [], 'cx': []}
    for fname in os.listdir(dir):
        
        print("\tProcessing %s..." % fname)
        circ = QuantumCircuit.from_qasm_file(os.path.join(dir, fname))
        
        counts = circ.count_ops()
        initial = {}
        initial['h'] = counts.get('h', 0)
        initial['x'] = counts.get('x', 0)
        initial['u1'] = counts.get('z', 0) + counts.get('t', 0) + counts.get('tdg', 0) + counts.get('s', 0) + counts.get('sdg', 0)
        initial['cx'] = counts.get('cx', 0)
        
        _unroll = Unroller(['u1', 'h', 'x', 'cx'])
        _depth_check = [Depth(), FixedPoint('depth')]
        def _opt_control(property_set):
           return not property_set['depth_fixed_point']
        _opt = [Optimize1qGates(), CommutativeCancellation()]
        pmA = PassManager()
        pmA.append(_unroll)
        pmA.append(_depth_check + _opt, do_while=_opt_control)
        circA = pmA.run(circ)
        
        counts = circA.count_ops()
        final = {}
        final['h'] = counts.get('h', 0)
        final['x'] = counts.get('x', 0)
        final['u1'] = counts.get('u1', 0)
        final['cx'] = counts.get('cx', 0)
        
        for k in reductions.keys():
            if initial[k] != 0:
                reductions[k].append(float(initial[k] - final[k]) / initial[k])
    for k in reductions.keys():
        print("Gate %s: average reduction = %f, std. = %f" % (k, numpy.average(reductions[k]), numpy.std(reductions[k])))

    # B
    print("\nRunning Qiskit on setting B")
    reductions = {'u1': [], 'u2': [], 'u3': [], 'cx': []}
    for fname in os.listdir(dir):
        
        print("\tProcessing %s..." % fname)
        circ = QuantumCircuit.from_qasm_file(os.path.join(dir, fname))
        
        counts = circ.count_ops()
        initial = {}
        initial['u1'] = counts.get('z', 0) + counts.get('t', 0) + counts.get('tdg', 0) + counts.get('s', 0) + counts.get('sdg', 0)
        initial['u2'] = counts.get('h', 0)
        initial['u3'] = counts.get('x', 0)
        initial['cx'] = counts.get('cx', 0)
        
        _unroll = Unroller(['u1', 'u2', 'u3', 'cx'])
        _depth_check = [Depth(), FixedPoint('depth')]
        def _opt_control(property_set):
           return not property_set['depth_fixed_point']
        _opt = [Optimize1qGates(), CommutativeCancellation()]
        pmB = PassManager()
        pmB.append(_unroll)
        pmB.append(_depth_check + _opt, do_while=_opt_control)
        circB = pmB.run(circ)
        
        counts = circB.count_ops()
        final = {}
        final['u1'] = counts.get('u1', 0)
        final['u2'] = counts.get('u2', 0)
        final['u3'] = counts.get('u3', 0)
        final['cx'] = counts.get('cx', 0)
        
        for k in reductions.keys():
            if initial[k] != 0:
                reductions[k].append(float(initial[k] - final[k]) / initial[k])
    for k in reductions.keys():
        print("Gate %s: average reduction = %f, std. = %f" % (k, numpy.average(reductions[k]), numpy.std(reductions[k])))


def count(d):
    sum = 0
    for k in d.keys():
        sum += d[k]
    return sum
    
def run_on_nam_benchmarks(fname):
    
    f = open(fname, "w")
    
    for fname in os.listdir("nam-benchmarks"):
        
        print("Processing %s..." % fname)
        circ = QuantumCircuit.from_qasm_file("nam-benchmarks/%s" % fname)
        
        # A
        _unroll = Unroller(['u1', 'h', 'x', 'cx'])
        _depth_check = [Depth(), FixedPoint('depth')]
        def _opt_control(property_set):
           return not property_set['depth_fixed_point']
        _opt = [Optimize1qGates(), CommutativeCancellation()]
        pmA = PassManager()
        pmA.append(_unroll)
        pmA.append(_depth_check + _opt, do_while=_opt_control)
        circA = pmA.run(circ)
        countA = count(circA.count_ops())
        
        # B
        _unroll = Unroller(['u1', 'u2', 'u3', 'cx'])
        _depth_check = [Depth(), FixedPoint('depth')]
        def _opt_control(property_set):
           return not property_set['depth_fixed_point']
        _opt = [Optimize1qGates(), CommutativeCancellation()]
        pmB = PassManager()
        pmB.append(_unroll)
        pmB.append(_depth_check + _opt, do_while=_opt_control)
        circB = pmB.run(circ)
        countB = count(circB.count_ops())
        
        # C
        # basis_gates = ['u1', 'u2', 'u3', 'cx']
        # _unroll = Unroller(basis_gates)
        # _depth_check = [Depth(), FixedPoint('depth')]
        # def _opt_control(property_set):
        #     return not property_set['depth_fixed_point']
        # _opt = [Collect2qBlocks(), ConsolidateBlocks(),
        #         Unroller(basis_gates),  # unroll unitaries
        #         Optimize1qGates(), CommutativeCancellation()]
        # pmC = PassManager()
        # pmC.append(_unroll)
        # pmC.append(_depth_check + _opt, do_while=_opt_control)
        # circC = pmC.run(circ)
        # countC = count(circC.count_ops())
        
        f.write("%s,%d,%d\n" % (fname, countA, countB))
        
    f.close()


if (len(sys.argv) != 3):
    print("Usage: python3 run_qiskit.py [-rand input_dir] [-nam output_file]")
    exit(-1)

if sys.argv[1] == "-rand":
    run_on_random_benchmarks(sys.argv[2])
elif sys.argv[1] == "-nam":
    run_on_nam_benchmarks(sys.argv[2])
else:
    print("Usage: python3 run_qiskit.py [-rand input_dir] [-nam output_file]")
    exit(-1)
