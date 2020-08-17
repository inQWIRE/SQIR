from ctypes import *
import os.path
import time
import re
    
   
class Opaque(Structure):
    pass
class temp(Structure):
    _fields_ = [('z', c_int)]

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
        self.lib.get_gate.restype= POINTER(Opaque)
        
        final_file = str(os.path.join(self.rel, fname)).encode('utf-8')
        start = time.time()
        self.circ = self.lib.get_gate(final_file)
        end = time.time()
        
        #Print time to parse and gate counts if not Cirq/Qiskit pass
        if self.print_c:
            print("Time to parse: %fs" % (end-start))

           
    
    def optimize(self):
        
        #Define argtype/restype for optimize
        self.lib.optimizer.argtypes =[POINTER(Opaque)]
        self.lib.optimizer.restype = POINTER(Opaque)

        self.lib.tot.argtypes = [POINTER(Opaque)]
        self.lib.tot.restype = c_int
            
        self.lib.x_c.argtypes = [POINTER(Opaque)]
        self.lib.x_c.restype = c_int
            
        self.lib.rz_c.argtypes = [POINTER(Opaque)]
        self.lib.rz_c.restype = c_int
            
        self.lib.cnot_c.argtypes = [POINTER(Opaque)]
        self.lib.cnot_c.restype = c_int
            
        self.lib.t_c.argtypes = [POINTER(Opaque)]
        self.lib.t_c.restype = c_char_p
            
        self.lib.c_c.argtypes = [POINTER(Opaque)]
        self.lib.c_c.restype = c_int

        self.lib.h_c.argtypes = [POINTER(Opaque)]
        self.lib.h_c.restype = c_int
        print(self.lib.tot(self.circ), self.lib.t_c(self.circ),self.lib.x_c(self.circ), self.lib.h_c(self.circ),
              self.lib.rz_c(self.circ), self.lib.cnot_c(self.circ), self.lib.c_c(self.circ))

        #Call optimizer function
        start1 = time.time()
        self.circ = self.lib.optimizer(self.circ)
        end1 = time.time()
        t = self.circ
        print(self.lib.tot(t),self.lib.x_c(self.circ), self.lib.h_c(self.circ),
              self.lib.rz_c(self.circ), self.lib.cnot_c(self.circ), self.lib.c_c(self.circ))
        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self
    def not_propagation(self):
        #Define argtype/restype for not_propagation
        self.lib.not_p.argtypes =[c_void_p]
        self.lib.not_p.restype = c_void_p

        #Call not_propagation function
        start1 = time.time()
        self.circ = self.lib.not_p(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self

    def hadamard_reduction(self):
        #Define argtype/restype for hadamard_reduction
        self.lib.hadamard.argtypes =[c_void_p]
        self.lib.hadamard.restype = c_void_p

        #Call hadamard_reduction function
        start1 = time.time()
        self.circ = self.lib.hadamard(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self

    def cancel_single_qubit_gates(self):
        #Define argtype/restype for cancel_single_qubit_gates
        self.lib.single.argtypes =[c_void_p]
        self.lib.single.restype = c_void_p

        #Call cancel_single_qubit_gates function
        start1 = time.time()
        self.circ = self.lib.single(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self

    def merge_rotations(self):
        #Define argtype/restype for merge_rotations
        self.lib.merge.argtypes =[c_void_p]
        self.lib.merge.restype = c_void_p

        #Call merge_rotations function
        start1 = time.time()
        self.circ = self.lib.merge(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
            
        return self      
    
    def cancel_two_qubit_gates(self):
        #Define argtype/restype for cancel_two_qubit_gates
        self.lib.two.argtypes =[c_void_p]
        self.lib.two.restype = c_void_p

        #Call cancel_two_qubit_gates function
        start1 = time.time()
        self.circ = self.lib.two(self.circ)
        end1 = time.time()

        #Print time taken to optimize if not a Cirq/Qiskit pass
        if self.print_c:
            self.optim+=(end1-start1)
        return self

    def write(self, fname):

        #Define function argtype/restype to match C
        self.lib.write_qasm.argtypes =[c_char_p, POINTER(Opaque)]
        self.lib.write_qasm.restype =None
        if self.print_c:
            print("Time to optimize: %fs" % (self.optim))
                                                                                           
           
        
        #Write qasm file
        start2 = time.time()
        out_file = (os.path.join(self.rel,fname)).encode('utf-8')
        self.lib.write_qasm(out_file, self.circ)
        end2 = time.time()
     
        #Print time if not through external compiler
        if self.print_c:
            print("Time to write: %fs" % (end2-start2))
        

        
        #Free OCaml Root after written to qasm
        self.lib.free_root.argtypes = [POINTER(Opaque)]
        self.lib.free_root.restype = None
        self.lib.free_root(self.circ)        
