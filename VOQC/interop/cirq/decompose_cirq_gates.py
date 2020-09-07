import cirq
import numpy as np
from cirq.ops.common_gates import ZPowGate
from cirq.circuits.qasm_output import QasmUGate

#Got flags from:  https://github.com/alexandrupaler/fondq
def is_op_with_decomposed_flag(op, gate_type):
    if op == gate_type:
        return hasattr(op, "decomposed")
    return False

def reset_decomposition_flags(circuit, gate_type):
    for op in circuit.all_operations():
        if is_op_with_decomposed_flag(op, gate_type):
            op.decomposed = False

def add_decomposition_flags(circuit, gate_type):
    for op in circuit.all_operations():
        if not is_op_with_decomposed_flag(op, gate_type):
            setattr(op, "decomposed", True)

def remove_decomposition_flags(circuit, gate_type):
    for op in circuit.all_operations():
        if is_op_with_decomposed_flag(op, gate_type):
            delattr(op, "decomposed")

            
def decompose_library(op):
            
    if isinstance(op, cirq.GateOperation) and (op.gate == cirq.CCZ):
        a = op.qubits[0]
        b = op.qubits[1]
        c = op.qubits[2]

        decomp = [cirq.CNOT.on(b, c),
                  cirq.T.on(c)**-1,
                  cirq.CNOT.on(a, c),
                  cirq.T.on(c),
                  cirq.CNOT.on(b, c),
                  cirq.T.on(c)**-1,
                  cirq.CNOT.on(a, c),
                  cirq.CNOT.on(a, b),
                  cirq.T.on(b)**-1,
                  cirq.CNOT.on(a, b),
                  cirq.T.on(a),
                  cirq.T.on(b),
                  cirq.T.on(c),]
                  

        if not is_op_with_decomposed_flag(cirq.CCZ, op.gate):
            setattr(cirq.CCZ, "decomposed", True)
        return decomp
            
    if isinstance(op, cirq.GateOperation) and (op.gate == cirq.CCX):
        a = op.qubits[0]
        b = op.qubits[1]
        c = op.qubits[2]
        
        decomp = [cirq.H.on(c),
                  cirq.CNOT.on(b, c),
                  cirq.T.on(c)**-1,
                  cirq.CNOT.on(a, c),
                  cirq.T.on(c),
                  cirq.CNOT.on(b, c),
                  cirq.T.on(c)**-1,
                  cirq.CNOT.on(a, c),
                  cirq.CNOT.on(a, b),
                  cirq.T.on(b)**-1,
                  cirq.CNOT.on(a, b),
                  cirq.T.on(a),
                  cirq.T.on(b),
                  cirq.T.on(c),
                  cirq.H.on(c),]
                  

        if not is_op_with_decomposed_flag(cirq.CCX, op.gate):
            setattr(cirq.CCX, "decomposed", True)
    if isinstance(op.gate, QasmUGate):
        a = op.qubits[0]
        theta = op.gate.theta*np.pi
        phi = op.gate.phi*np.pi
        lam = op.gate.lmda*np.pi
        decomp = [cirq.rz(phi+(np.pi/2)).on(a),
                  cirq.H.on(a),
                  cirq.rz(theta).on(a),
                  cirq.H.on(a),
                  cirq.rz(lam-(np.pi/2)).on(a),]
        if not is_op_with_decomposed_flag(cirq.CCX, op.gate):
            setattr(QasmUGate, "decomposed", True)
        
        return decomp

def need_to_keep(op):
    voqc_gates = [cirq.H, cirq.X, cirq.rz, cirq.T, cirq.S, cirq.T**-1,cirq.S**-1, cirq.CNOT, cirq.Z]
    if (op.gate in voqc_gates) or (isinstance(op.gate, ZPowGate)):
        return True
    if is_op_with_decomposed_flag(op, op.gate):
        return op.decomposed
    return False
