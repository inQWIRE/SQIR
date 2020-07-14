from ctypes import *
import argparse
import ast
from gmpy2 import mpq
import os.path

class rational(Structure):
    _fields_ = [('num', c_int), ('den', c_int)]

class final_gates(Structure):
    _fields_ = [('gates', c_int), ('type1', rational)]



class tuples(Structure):
    _fields_ = [('gate', final_gates), ('x', c_int)]


class triples(Structure):
    _fields_ = [('gate1', final_gates), ('a', c_int), ('b', c_int)]


class quad(Structure):
    _fields_ = [('gate2', final_gates), ('c', c_int), ('f', c_int), ('e', c_int)]


class gate_app1(Structure):
    _fields_ = [('App1', tuples), ('App2', triples), ('App3', quad),('ans', c_int)]
    
GATE_APP = gate_app1 *1000

class with_qubits(Structure):
    _fields_ = [('length', c_int), ('contents2', GATE_APP), ('qubits', c_int)]
def convert_gates(x):
    y = 0
    num = 0
    den = 0
    if x == 'X':
        y = 1
    elif x == 'H':
        y =2
    elif x == 'CNOT':
        y =3
    else:
        y=4
        num = int(x[3])
        den = int(x[5])
    return y, num, den
def format_to_c(py_list, q):
    struct_return = GATE_APP()
    struct_app = gate_app1()
    tot_length = len(py_list)
    for i in range(tot_length):
        sub_len = len(py_list[i])
        conv = (convert_gates(py_list[i][0]))
        int_val = conv[0]
        numer = conv[1]
        denom = conv[2]
        rat = rational(numer, denom)
        temp = final_gates(int_val, rat)
        if sub_len == 2:
            tup = tuples(temp, int(py_list[i][1]))
            struct_app=gate_app1(App1=tup, ans =1)
        elif sub_len == 3:
            tup = triples(temp, int(py_list[i][1]),int(py_list[i][2]))
            struct_app=gate_app1(App2=tup, ans=2)
        else:
             tup = quad(temp, int(py_list[i][1]),int(py_list[i][2]),int(py_list[i][3]))
             struct_app=gate_app1(App3=tup, ans =3)
        struct_return[i] = struct_app
    with_q = with_qubits(tot_length, struct_return,int(q))
    return with_q
def get_text(x,y,z):
    gate_get = {1:'X', 2: 'H', 3:'CNOT', 4: 'Rz'+ ' ' +str(y) + '/' + str(z)}
    return gate_get.get(x)
def format_from_c(y):
    return_list = []
    val = gate_app1()
    deref = y.contents
    for i in range(deref.length):
        val = deref.contents2[i]
        if val.App2.gate1.gates == 0 and val.App3.gate2.gates ==0:
            sub_list = []
            sub_list.append(get_text(val.App1.gate.gates,val.App1.gate.type1.num, val.App1.gate.type1.den))
            sub_list.append(val.App1.x)
            return_list.append(sub_list)
        elif val.App3.gate2.gates ==0 and val.App1.gate.gates==0:
            sub_list =[]
            sub_list.append(get_text(val.App2.gate1.gates,val.App2.gate1.type1.num, val.App2.gate1.type1.den))
            sub_list.append(val.App2.a)
            sub_list.append(val.App2.b)
            return_list.append(sub_list)
        else:
            sub_list = []
            sub_list.append(get_text(val.App3.gate2.gates,val.App3.gate2.type1.num, val.App3.gate2.type1.den))
            sub_list.append(val.App3.c)
            sub_list.append(val.App3.f)
            sub_list.append(val.App3.e)
            return_list.append(sub_list)
        
    return return_list


def voqc(fname, out):
    testlib = CDLL('./libvoqc.so')
    testlib.get_gate_list.argtypes = [c_char_p, c_char_p]
    testlib.get_gate_list.restype = None
    in_file =str(fname).encode('utf-8')
    out_file = str(out).encode('utf-8')
    testlib.voqc(in_file, out_file)
    

def path():
    return os.path.dirname(os.path.abspath(__file__)) + "/extraction/_build/generated/" + "libvoqc.so"
class SQIR:
    def __init__(self, circ):
        self.circ = circ
    def optimize(self):
        testlib =  CDLL(path())
        testlib.optimizer.argtypes =[POINTER(with_qubits)]
        testlib.optimizer.restype =POINTER(with_qubits)
        t = format_from_c(self.circ)
        y = format_to_c(t, self.circ.contents.qubits)
        self.circ = testlib.optimizer(byref(y))
        return self

    def not_propagation(self):
        testlib = CDLL(path())
        testlib.not_propagation.argtypes =[POINTER(with_qubits)]
        testlib.not_propagation.restype =POINTER(with_qubits)
        t = format_from_c(self.circ)
        y = format_to_c(t, self.circ.contents.qubits)
        self.circ =testlib.not_propagation(byref(y))
        return self

    def hadamard_reduction(self):
        testlib = CDLL(path())
        testlib.hadamard.argtypes =[POINTER(with_qubits)]
        testlib.hadamard.restype =POINTER(with_qubits)
        t = format_from_c(self.circ)
        y = format_to_c(t, self.circ.contents.qubits)
        self.circ =testlib.hadamard(byref(y))
        return self

    def cancel_two_qubit_gates(self):
        testlib = CDLL(path())
        testlib.cancel_two_qubit_gates.argtypes =[POINTER(with_qubits)]
        testlib.cancel_two_qubit_gates.restype =POINTER(with_qubits)
        t = format_from_c(self.circ)
        y = format_to_c(t, self.circ.contents.qubits)
        self.circ =testlib.cancel_two_qubit_gates(byref(y))
        return self

    def merge_rotations(self):
        testlib = CDLL(path())
        testlib.merge_rotations.argtypes =[POINTER(with_qubits)]
        testlib.merge_rotations.restype =POINTER(with_qubits)
        t = format_from_c(self.circ)
        y = format_to_c(t, self.circ.contents.qubits)
        self.circ =testlib.merge_rotation(byref(y))
        return self
    
    def cancel_single_qubit_gates(fname):
        testlib = CDLL(path())
        testlib.cancel_single_qubit_gates.argtypes =[POINTER(with_qubits)]
        testlib.cancel_single_qubit_gates.restype =POINTER(with_qubits)
        t = format_from_c(self.circ)
        y = format_to_c(t, self.circ.contents.qubits)
        self.circ =testlib.cancel_single_qubit_gates(byref(y))
        return self
    
    def write(self, fname):
        testlib = CDLL(path())
        testlib.write_qasm_file.argtypes =[c_char_p, POINTER(with_qubits)]
        testlib.write_qasm_file.restype =None
        rel = os.path.dirname(os.path.abspath(__file__))
        out_file = str(os.path.join(rel,fname)).encode('utf-8')
        t = format_from_c(self.circ)
        q = self.circ.contents.qubits
        y = format_to_c(t, q)
        testlib.write_qasm_file(out_file,byref(y))

def load(fname): 
    testlib = CDLL(path())
    testlib.get_gate_list.argtypes = [c_char_p]
    testlib.get_gate_list.restype = POINTER(with_qubits)
    rel = os.path.dirname(os.path.abspath(__file__))
    final_file =str(os.path.join(rel, fname)).encode('utf-8')
    circ = testlib.get_gate_list(final_file)
    return SQIR(circ)


    

