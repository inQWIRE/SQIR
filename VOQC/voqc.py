from ctypes import *
import os.path
import time
import re
    
def print_gates(lib, circ, orig):
        
    lib.x_c.argtypes =[c_void_p]
    lib.x_c.restype =c_int
        
    lib.h_c.argtypes =[c_void_p]
    lib.h_c.restype =c_int
        
    lib.cnot_c.argtypes =[c_void_p]
    lib.cnot_c.restype =c_int
        
    lib.rz_c.argtypes =[c_void_p]
    lib.rz_c.restype =c_int

                
    lib.c_c.argtypes =[c_void_p]
    lib.c_c.restype =c_int

    lib.tot.argtypes =[c_void_p]
    lib.tot.restype =c_int

    lib.c_c.argtypes =[c_void_p]
    lib.c_c.restype =c_int
        
        
    lib.t_c.argtypes =[c_void_p]
    lib.t_c.restype =c_char_p

    fin_counts = [lib.tot(circ), lib.rz_c(circ), lib.c_c(circ), (lib.t_c(circ)).decode('utf-8'), lib.h_c(circ),
                      lib.x_c(circ), lib.cnot_c(circ)]
    if orig==True:
        print("Original:\t Total %d, Rz %d, Clifford %d, T %s, H %d, X %d, CNOT %d" % (fin_counts[0], fin_counts[1], fin_counts[2], fin_counts[3],
                                                                                         fin_counts[4], fin_counts[5], fin_counts[6]))
    else:
        print("Final:\t Total %d, Rz %d, Clifford %d, T %s, H %d, X %d, CNOT %d" % (fin_counts[0], fin_counts[1], fin_counts[2], fin_counts[3],
                                                                                         fin_counts[4], fin_counts[5], fin_counts[6]))
        
        
class SQIR:
    def __init__(self, fname, c=True):
        self.print_c = c
        self.optim = 0
        
        #Set path and lib
        self.rel = os.path.dirname(os.path.abspath(__file__))
        self.lib = CDLL(os.path.join(self.rel,'_build/default/extraction/libvoqc.so'))

        #Initialize OCaml code
        self.lib.init_lib.argtypes = None
        self.lib.init_lib.restype= None
        self.lib.init_lib()

        #Call get_gate_list function and return pointer to SQIR circuit 
        self.lib.get_gate.argtypes = [c_char_p]
        self.lib.get_gate.restype= c_void_p        
        start = time.time()
        final_file = str(os.path.join(self.rel, fname)).encode('utf-8')
        self.circ = self.lib.get_gate(final_file)
        end = time.time()

        #Print time to parse and gate counts if not Cirq/Qiskit pass
        if c:
            print("Time to parse: %fs" % (end-start))
            print_gates(self.lib, self.circ,True)

        
    def optimize(self):
        
        #Define argtype/restype for optimize
        self.lib.optimizer.argtypes =[c_void_p]
        self.lib.optimizer.restype = c_void_p

        #Call optimizer function
        start1 = time.time()
        self.circ = self.lib.optimizer(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self
    def not_propagation(self):
        #Define argtype/restype for optimize
        self.lib.not_p.argtypes =[c_void_p]
        self.lib.not_p.restype = c_void_p

        #Call optimizer function
        start1 = time.time()
        self.circ = self.lib.not_p(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self

    def hadamard_reduction(self):
        #Define argtype/restype for optimize
        self.lib.hadamard.argtypes =[c_void_p]
        self.lib.hadamrd.restype = c_void_p

        #Call optimizer function
        start1 = time.time()
        self.circ = self.lib.hadamard(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self

    def cancel_single_qubit_gates(self):
        #Define argtype/restype for optimize
        self.lib.single.argtypes =[c_void_p]
        self.lib.single.restype = c_void_p

        #Call optimizer function
        start1 = time.time()
        self.circ = self.lib.single(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self

    def merge_rotations(self):
        #Define argtype/restype for optimize
        self.lib.merge.argtypes =[c_void_p]
        self.lib.merge.restype = c_void_p

        #Call optimizer function
        start1 = time.time()
        self.circ = self.lib.merge(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self      
    
    def cancel_two_qubit_gates(self):
        #Define argtype/restype for optimize
        self.lib.two.argtypes =[c_void_p]
        self.lib.two.restype = c_void_p

        #Call optimizer function
        start1 = time.time()
        self.circ = self.lib.two(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self

    def write(self, fname):

        #Define function argtype/restype to match C
        self.lib.write_qasm.argtypes =[c_char_p, c_void_p]
        self.lib.write_qasm.restype =None
        
        
        #Write qasm file
        start2 = time.time()
        out_file = (os.path.join(self.rel,fname)).encode('utf-8')
        self.lib.write_qasm(out_file, self.circ)
        end2 = time.time()

               
        #Print time if not through external compiler
        if self.print_c:
            print("Time to optimize: %fs" % (self.optim))
            print_gates(self.lib, self.circ, False)
            print("Time to write: %fs" % (end2-start2))
        
        #Free OCaml Root after written to qasm
        self.lib.free_root.argtypes = [c_void_p]
        self.lib.free_root.restype = None
        self.lib.free_root(self.circ)
 

    

        
