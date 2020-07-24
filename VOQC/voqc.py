from ctypes import *
import argparse
import ast
import os.path
from gmpy2 import *

class final_gates(Structure):
    _fields_ = [('gates', c_int), ('type1', c_void_p)]



class tuples(Structure):
    _fields_ = [('gate', final_gates), ('x', c_int)]


class triples(Structure):
    _fields_ = [('gate1', final_gates), ('a', c_int), ('b', c_int)]


class quad(Structure):
    _fields_ = [('gate2', final_gates), ('c', c_int), ('f', c_int), ('e', c_int)]


class gate_app1(Structure):
    _fields_ = [('App1', tuples), ('App2', triples), ('App3', quad),('ans', c_int)]
    

GATE_APP = gate_app1*250000
class with_qubits(Structure):
    _fields_ = [('length', c_int), ('contents2', GATE_APP), ('qubits', c_int)]

    
def format_from_c(y):
    deref = y.contents
    tot_length = deref.length
    num_q = deref.qubits
    struct_app = gate_app1()
    struct_return = GATE_APP()
    struct_ret = GATE_APP()
    temp_app = tuples()
    temp_app1 = triples()
    temp_app2 = quad()
    for i in range(tot_length):
        val = deref.contents2[i]
        if val.App2.gate1.gates == 0 and val.App3.gate2.gates ==0:
            struct_app = gate_app1(App1 = val.App1, ans = 1)
        elif val.App3.gate2.gates ==0 and val.App1.gate.gates==0:
            struct_app = gate_app1(App2 = val.App2, ans = 2)            
        else:
            struct_app = gate_app1(App3 = val.App3, ans = 3)  
        struct_return[i] = struct_app
    return with_qubits(tot_length, struct_return, num_q)

def get_counts(circ):
    tot_length = circ.length
    rz_count = 0
    cnot_count = 0
    x_count = 0
    h_count = 0
    for i in range(tot_length):
        val = circ.contents2[i]
        if val.ans == 1:
            if val.App1.gate.gates == 1:
                x_count+=1
            elif val.App1.gate.gates ==2:
                h_count+=1
            elif val.App1.gate.gates ==3:
                cnot_count+=1
            else:
                rz_count+=1
        elif val.ans == 2:
            if val.App2.gate1.gates == 1:
                x_count+=1
            elif val.App2.gate1.gates ==2:
                h_count+=1
            elif val.App2.gate1.gates ==3:
                cnot_count+=1
            else:
                rz_count+=1
        else:
            if val.App3.gate2.gates == 1:
                x_count+=1
            elif val.App3.gate2.gates ==2:
                h_count+=1
            elif val.App3.gate2.gates ==3:
                cnot_count+=1
            else:
                rz_count+=1
    return (x_count, h_count, cnot_count, rz_count, tot_length)         
        
    
def cliff(q):
    rel = os.path.dirname(os.path.abspath(__file__))
    testlib = CDLL(os.path.join(rel,'_build/default/extraction/libvoqc.so'))
    testlib.cliff.argtypes =[POINTER(with_qubits)]
    testlib.cliff.restype =c_int
    l = testlib.cliff(byref(q))
    return l
def t_count(q):
    rel = os.path.dirname(os.path.abspath(__file__))
    testlib = CDLL(os.path.join(rel,'_build/default/extraction/libvoqc.so'))
    testlib.t_count.argtypes =[POINTER(with_qubits)]
    testlib.t_count.restype =c_char_p
    l = testlib.t_count(byref(q))
    return (l.decode('utf-8')) 

def voqc(fname, out):
    testlib = CDLL('./libvoqc.so')
    testlib.get_gate_list.argtypes = [c_char_p, c_char_p]
    testlib.get_gate_list.restype = None
    in_file =str(fname).encode('utf-8')
    out_file = str(out).encode('utf-8')
    testlib.voqc(in_file, out_file)
    

def print_gates(fin_counts, t_c, c_c, orig):
    if orig == False:
        print("Original:\t Total %d, Rz %d, Clifford %d, T %s, H %d, X %d, CNOT %d\n" % (fin_counts[4], fin_counts[3], c_c, t_c,
                                                                                         fin_counts[1], fin_counts[0],fin_counts[2]))
    else:
        print("Final:\t Total %d, Rz %d, Clifford %d, T %s, H %d, X %d, CNOT %d\n" % (fin_counts[4], fin_counts[3], c_c, t_c,
                                                                                      fin_counts[1], fin_counts[0],fin_counts[2]))
        
    
class SQIR:
    def __init__(self, fname):
        rel = os.path.dirname(os.path.abspath(__file__))
        self.lib = CDLL(os.path.join(rel,'_build/default/extraction/libvoqc.so'))
        self.lib.get_gate_list.argtypes = [c_char_p]
        self.lib.get_gate_list.restype = POINTER(with_qubits)
        final_file =str(fname).encode('utf-8')
        rel = os.path.dirname(os.path.abspath(__file__))
        final_file =str(os.path.join(rel, fname)).encode('utf-8')
        self.circ = self.lib.get_gate_list(final_file)  

    def optimize(self):
        self.lib.optimizer.argtypes =[POINTER(with_qubits)]
        self.lib.optimizer.restype =POINTER(with_qubits)
        t = format_from_c(self.circ)
        t = format_from_c(self.circ)
        fin_counts = get_counts(t)
        t_c = t_count(t)
        c_c = cliff(t)
        print_gates(fin_counts, t_c, c_c, False)
        self.circ = self.lib.optimizer(byref(t))
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
        self.lib.write_qasm_file.argtypes =[c_char_p, POINTER(with_qubits)]
        self.lib.write_qasm_file.restype =None
        rel = os.path.dirname(os.path.abspath(__file__))
        out_file = str(os.path.join(rel,fname)).encode('utf-8')
        t = format_from_c(self.circ)
        fin_counts = get_counts(t)
        t_c = t_count(t)
        c_c = cliff(t)
        print_gates(fin_counts, t_c, c_c, True)
        self.lib.write_qasm_file(out_file,byref(t))
