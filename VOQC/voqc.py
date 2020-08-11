from ctypes import *
import ast
import os.path
from gmpy2 import *
import time


    


    
def print_gates(fin_counts, orig):
    if orig == True:
        print("Original:\t Total %d, Rz %d, Clifford %d, T %s, H %d, X %d, CNOT %d" % (fin_counts[0], fin_counts[1], fin_counts[2], fin_counts[3],
                                                                                         fin_counts[4], fin_counts[5],fin_counts[6]))
    else:
        print("Final:\t Total %d, Rz %d, Clifford %d, T %s, H %d, X %d, CNOT %d" % (fin_counts[0], fin_counts[1], fin_counts[2], fin_counts[3],
                                                                                         fin_counts[4], fin_counts[5],fin_counts[6]))
        
class SQIR:
    def __init__(self, fname, c=True):
        self.print_c = c
        rel = os.path.dirname(os.path.abspath(__file__))
        self.lib = CDLL(os.path.join(rel,'_build/default/extraction/libvoqc.so'))
        self.lib.init_lib.argtypes = None
        self.lib.init_lib.restype= None
        self.lib.init_lib()
        self.lib.get_gate.argtypes = [c_char_p]
        self.lib.get_gate.restype= c_void_p
        
        self.lib.tot.argtypes = [c_void_p]
        self.lib.tot.restype= c_int
        
        self.lib.x_c.argtypes = [c_void_p]
        self.lib.x_c.restype= c_int
        
        self.lib.h_c.argtypes = [c_void_p]
        self.lib.h_c.restype= c_int
        
        self.lib.cnot_c.argtypes = [c_void_p]
        self.lib.cnot_c.restype= c_int
        
        self.lib.rz_c.argtypes = [c_void_p]
        self.lib.rz_c.restype= c_int
        
        self.lib.t_c.argtypes = [c_void_p]
        self.lib.t_c.restype= c_char_p

                
        final_file =str(os.path.join(rel, fname)).encode('utf-8')
        start = time.time()
        self.circ = self.lib.get_gate(final_file)
        end = time.time()
        self.lib.cliff_c.argtypes = [c_void_p]
        self.lib.cliff_c.restype = c_int
        
        
        self.gates = [self.lib.tot(self.circ), self.lib.rz_c(self.circ), self.lib.cliff_c(self.circ), (self.lib.t_c(self.circ)).decode('utf-8')
                     ,self.lib.h_c(self.circ), self.lib.x_c(self.circ), self.lib.cnot_c(self.circ)]
        
        print("Time to parse: %fs" % (end-start))

        
    def optimize(self):
        self.lib.optimizer.argtypes =[c_void_p]
        self.lib.optimizer.restype = c_void_p
        print(self.format_counts(True))
        start1 = time.time()
        self.circ = self.lib.optimizer(self.circ)
        end1 = time.time()
        if self.print_c:
            print("Time to optimize: %fs" % (end1-start1))
        return self
    def not_propagation(self):
        self.lib.not_propagation.argtypes =[POINTER(with_qubits)]
        self.lib.not_propagation.restype =POINTER(with_qubits)
        t = format_from_c(self.circ)
        self.circ = self.lib.not_propagation(byref(t))
        return self

    def hadamard_reduction(self):
        self.lib.hadamard.argtypes =[POINTER(with_qubits)]
        self.lib.hadamard.restype =POINTER(with_qubits)
        t = format_from_c(self.circ)
        self.circ = self.lib.hadamard(byref(t))
        return self

    def cancel_two_qubit_gates(self):
        self.lib.cancel_two_qubit_gates.argtypes =[POINTER(with_qubits)]
        self.lib.cancel_two_qubit_gates.restype =POINTER(with_qubits)
        t = format_from_c(self.circ)
        self.circ = self.lib.cancel_two_qubit_gates(byref(t))
        return self

    def merge_rotations(self):
        self.lib.merge_rotations.argtypes =[POINTER(with_qubits)]
        self.lib.merge_rotations.restype =POINTER(with_qubits)
        t = format_from_c(self.circ)
        self.circ = self.lib.merge_rotations(byref(t))
        return self      
    
    def cancel_single_qubit_gates(self):
        self.lib.cancel_single_qubit_gates.argtypes =[POINTER(with_qubits)]
        self.lib.cancel_single_qubit_gates.restype =POINTER(with_qubits)
        t = format_from_c(self.circ)
        self.circ = self.lib.cancel_single_qubit_gates(byref(t))
        return self


    def write(self, fname):
        self.lib.write_qasm.argtypes =[c_char_p, c_void_p]
        self.lib.write_qasm.restype =None
        rel = os.path.dirname(os.path.abspath(__file__))
        out_file = str(os.path.join(rel,fname)).encode('utf-8')
        self.gates = [self.lib.tot(self.circ), self.lib.rz_c(self.circ),self.lib.cliff_c(self.circ), (self.lib.t_c(self.circ)).decode('utf-8')
                      ,self.lib.h_c(self.circ), self.lib.x_c(self.circ), self.lib.cnot_c(self.circ)]
        if self.print_c:
            print(self.format_counts(False))
        start2 = time.time()
        self.lib.write_qasm(out_file,self.circ)
        end2 = time.time()
        print("Time to write: %fs" % (end2-start2))

    def format_counts(self, orig):
        fin_counts = self.gates
        if orig == True:
            return ("Original:\t Total %d, Rz %d, Clifford %d T %s, H %d, X %d, CNOT %d" % (fin_counts[0], fin_counts[1], fin_counts[2], fin_counts[3],
                                                                                             fin_counts[4], fin_counts[5], fin_counts[6
                                                                                             ]))
        else:
            return ("Final:\t Total %d, Rz %d, Clifford %d, T %s, H %d, X %d, CNOT %d" % (fin_counts[0], fin_counts[1], fin_counts[2], fin_counts[3],
                                                                                          fin_counts[4], fin_counts[5], fin_counts[6]))
