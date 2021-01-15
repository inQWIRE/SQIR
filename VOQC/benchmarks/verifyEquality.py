import pyzx as zx                                                                                                                    
import sys

'''
This script runs PyZX's verify_equality function on two input programs, indicating
whether it succeeded with an exit code of 0 (success) or 1 (failure). 
'''

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: verifyEquality.py <input prog 1> <input prog 2>")
        sys.exit(1)
    f1 = sys.argv[1]
    f2 = sys.argv[2]
    
    failed = 0
    try:
        circ = zx.Circuit.from_qasm_file(f1)
        circ_opt = zx.Circuit.from_qasm_file(f2)
        if (circ.verify_equality(circ_opt)):
            pass
        else:
            failed = 1
    except:
        print("Invalid inputs: %s, %s" % (f1, f2))
        sys.exit(1)
    
    sys.exit(failed)