# Run PyZX on all the benchmarks
# You will need to run this from the directory where PyZX is installed

import pyzx as zx
import os
import sys

def run_on_nam_benchmarks(fname):
    
    f = open(fname, "w")
    d = "nam-benchmarks" # This may need to be changed depending on where the script is run from!
    
    f.write("name, num gates before, t-count before, num gates after, t-count after\n")
    
    for fname in os.listdir(d):

        print("Processing %s..." % fname)
        
        circ = zx.Circuit.load(os.path.join(d, fname)).to_basic_gates()
        num_gates_before = len(circ.gates)
        t_count_before = zx.tcount(circ)
        print("\nORIGINAL: %d gates, %d T-gates" % (num_gates_before, t_count_before))
        
        g = circ.to_graph()
        zx.simplify.full_reduce(g,quiet=False)
        g.normalise()
        new_circ = zx.extract.streaming_extract(g).to_basic_gates()
        num_gates_after = len(new_circ.gates)
        t_count_after = zx.tcount(new_circ)
        print("OPTIMIZED: %d gates, %d T-gates\n" % (num_gates_after, t_count_after))

        f.write("%s,%d,%d,%d,%d\n" % (fname, num_gates_before, t_count_before, num_gates_after, t_count_after))

if (len(sys.argv) != 2):
    print("Usage: python3 run_pyzx.py output_file")
    exit(-1)

run_on_nam_benchmarks(sys.argv[1])
