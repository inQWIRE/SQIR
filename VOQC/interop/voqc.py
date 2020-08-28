from ctypes import *
import os.path
import time
    
def print_gates(lib, circ, orig):
        
    lib.x_count.argtypes =[c_void_p]
    lib.x_count.restype =c_int
        
    lib.h_count.argtypes =[c_void_p]
    lib.h_count.restype =c_int
        
    lib.cnot_count.argtypes =[c_void_p]
    lib.cnot_count.restype =c_int
        
    lib.rz_count.argtypes =[c_void_p]
    lib.rz_count.restype =c_int

    lib.total_count.argtypes =[c_void_p]
    lib.total_count.restype =c_int

    lib.c_count.argtypes =[c_void_p]
    lib.c_count.restype =c_int
        
    lib.t_count.argtypes =[c_void_p]
    lib.t_count.restype =c_int

    fin_counts = [lib.total_count(circ), lib.rz_count(circ), lib.c_count(circ), 
                 lib.t_count(circ), lib.h_count(circ), lib.x_count(circ), lib.cnot_count(circ)]
    if orig==True:
        
        print("Original:\t Total %d, Rz %d, Clifford %d, T %d, H %d, X %d, CNOT %d" % (fin_counts[0], fin_counts[1], fin_counts[2], fin_counts[3],
                                                                                         fin_counts[4], fin_counts[5], fin_counts[6]))
    else:
        print("Final:\t Total %d, Rz %d, Clifford %d, T %d, H %d, X %d, CNOT %d" % (fin_counts[0], fin_counts[1], fin_counts[2], fin_counts[3],
                                                                                         fin_counts[4], fin_counts[5], fin_counts[6]))
        
class SQIR:
    def __init__(self, fname, c=True):
        
        #Whether to print gates and optimization time
        self.print_c = c
        self.optim = 0
        
        #Set path and lib
        self.rel = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        self.lib = CDLL(os.path.join(self.rel,'_build/default/extraction/libvoqc.so'))

        #Initialize OCaml code
        self.lib.init.argtypes = None
        self.lib.init.restype= None
        self.lib.init()

        #Call read_qasm_file function and return pointer to SQIR circuit 
        self.lib.read_qasm_file.argtypes = [c_char_p]
        self.lib.read_qasm_file.restype= c_void_p        
        start = time.time()
        final_file = (os.path.join(self.rel, fname)).encode('utf-8')
        self.circ = self.lib.read_qasm_file(final_file)
        end = time.time()

        #Print time to parse and gate counts if not Cirq/Qiskit pass
        if c:
            print("Time to parse: %fs" % (end-start))
            print_gates(self.lib, self.circ,True)
        
    def optimize(self):
        
        #Define argtype/restype for optimize
        self.lib.optimize.argtypes =[c_void_p]
        self.lib.optimize.restype = c_void_p

        #Call optimizer function
        start1 = time.time()
        self.circ = self.lib.optimize(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self
    
    def merge_rotations(self):
        
        #Define argtype/restype for merge_rotations
        self.lib.merge_rotations.argtypes =[c_void_p]
        self.lib.merge_rotations.restype = c_void_p

        #Call merge_rotations function
        start1 = time.time()
        self.circ = self.lib.merge_rotations(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self

    def cancel_single_qubit_gates(self):
        
        #Define argtype/restype for cancel_single_qubit_gates
        self.lib.cancel_single_qubit_gates.argtypes =[c_void_p]
        self.lib.cancel_single_qubit_gates.restype = c_void_p

        #Call cancel_single_qubit_gates function
        start1 = time.time()
        self.circ = self.lib.cancel_single_qubit_gates(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self
    
    def cancel_two_qubit_gates(self):
        
        #Define argtype/restype for cancel_two_qubit_gates
        self.lib.cancel_two_qubit_gates.argtypes =[c_void_p]
        self.lib.cancel_two_qubit_gates.restype = c_void_p

        #Call cancel_two_qubit_gates function
        start1 = time.time()
        self.circ = self.lib.cancel_two_qubit_gates(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self

    def not_propagation(self):
        
        #Define argtype/restype for not_propagation
        self.lib.not_propagation.argtypes =[c_void_p]
        self.lib.not_propagation.restype = c_void_p

        #Call not_propagation function
        start1 = time.time()
        self.circ = self.lib.not_propagation(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self
    
    def hadamard_reduction(self):
        
        #Define argtype/restype for hadamard_reduction
        self.lib.hadamard_reduction.argtypes =[c_void_p]
        self.lib.hadamard_reduction.restype = c_void_p

        #Call hadamard_reduction function
        start1 = time.time()
        self.circ = self.lib.hadamard_reduction(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self

    def write(self, fname):

        #Define function argtype/restype to match C
        self.lib.write_qasm_file.argtypes = [c_char_p, c_void_p]
        self.lib.write_qasm_file.restype = None
                
        #Write qasm file
        start2 = time.time()
        out_file = (os.path.join(self.rel,fname)).encode('utf-8')
        self.lib.write_qasm_file(out_file, self.circ)
        end2 = time.time()
       
        #Print time if not through external compiler
        if self.print_c:
            print("Time to optimize: %fs" % (self.optim))
            print_gates(self.lib, self.circ, False)
            print("Time to write: %fs" % (end2-start2))
        
        #Free OCaml Root after written to qasm
        self.lib.destroy.argtypes = [c_void_p]
        self.lib.destroy.restype = None
        self.lib.destroy(self.circ)

    def write_str(self):

        #Define function argtype/restype to match C
        self.lib.write_qasm_file_str.argtypes = [c_void_p]
        self.lib.write_qasm_file_str.restype = c_char_p
        t = (self.lib.write_qasm_file_str(self.circ)).decode('utf-8') 
        #Free OCaml Root after written to qasm
        self.lib.destroy.argtypes = [c_void_p]
        self.lib.destroy.restype = None
        self.lib.destroy(self.circ)
        return t
