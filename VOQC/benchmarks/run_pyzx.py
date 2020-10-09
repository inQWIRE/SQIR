# Run PyZX on all the benchmarks
# You will need to run this from the directory where PyZX is installed

import pyzx as zx
import os
import sys
import time

def run(d, fname):
    
    f = open(fname, "w")
        
    f.write("name,Orig. total,Orig. CNOT,Orig. T,PyZX total,PyZX CNOT,PyZX T,time\n")
    
    for fname in os.listdir(d):

        print("Processing %s..." % fname)
        
        circ = zx.Circuit.load(os.path.join(d, fname)).to_basic_gates()
        num_gates_before = len(circ.gates)
        cnot_count_before = circ.twoqubitcount()
        t_count_before = zx.tcount(circ)
        print("Original:\t Total %d, CNOT %d, T %d" % (num_gates_before, cnot_count_before, t_count_before))
        
        start = time.perf_counter() # start timer
        g = circ.to_graph()
        zx.full_reduce(g,quiet=False)
        g.normalize()
        new_circ = zx.extract_circuit(g).to_basic_gates()
        stop = time.perf_counter() # stop timer
        num_gates_after = len(new_circ.gates)
        cnot_count_after = new_circ.twoqubitcount()
        t_count_after = zx.tcount(new_circ)
        print("Final:\t Total %d, CNOT %d, T %d\n" % (num_gates_after, cnot_count_after, t_count_after))

        f.write("%s,%d,%d,%d,%d,%d,%d,%f\n" % (fname, num_gates_before, cnot_count_before, t_count_before, num_gates_after, cnot_count_after, t_count_after, stop - start))

if (len(sys.argv) != 3):
    print("Usage: python3 run_pyzx.py <input directory> <output file>")
    exit(-1)

run(sys.argv[1], sys.argv[2])
