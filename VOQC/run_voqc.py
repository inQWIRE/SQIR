from voqc import *
import argparse
import time
import os.path
from pathlib import Path
def run(a,b):
    print("Input file: %s" % (a))
    print("Output file: %s" % (b))
    a = VOQC(str(a))
    a.optimize()
    a.write(str(b))

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description= "Run all optimizations,usage: python run_voqc.py <input rel. directory> <output qasm file>")
    parser.add_argument("-i", type=str, help="The input directory of the file. Ex. benchmarks/Arithmetic_and_Toffoli/tof_3.qasm")
    parser.add_argument("-o", type=str, help="Name of the output qasm file")
    args = parser.parse_args()
    print(len(args))
    if (Path(os.path.join(os.getcwd()), args.i)).exists():
        run(args.i, args.o)
    else:
        print("The directory %s is not a valid directory" % (os.path.join(os.getcwd(),args.i)))
        exit(-1)

