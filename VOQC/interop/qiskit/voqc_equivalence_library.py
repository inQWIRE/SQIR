from qiskit.circuit import EquivalenceLibrary, Parameter, QuantumCircuit, QuantumRegister
from qiskit.circuit.library.standard_gates import U2Gate, U3Gate, HGate, U1Gate, CCXGate, TdgGate, TGate, RZGate, CXGate
from qiskit.qasm import pi

eq_lib = EquivalenceLibrary()

theta = Parameter('theta')
phi = Parameter('phi')
lamda = Parameter('lamda')

u3 = U3Gate(theta, phi, lamda)
u2 = U2Gate(theta, phi)
u1 = U1Gate(theta)
ccx = CCXGate()
        
q = QuantumRegister(1, 'q')
equiv_u3 = QuantumCircuit(q)
equiv_u3.append(RZGate(phi+(pi/2)), [q[0]], [])
equiv_u3.append(HGate(),[q[0]], [] )
equiv_u3.append(RZGate(theta),[q[0]], [])
equiv_u3.append(HGate(), [q[0]], [])
equiv_u3.append(RZGate(lamda-(pi/2)),[q[0]], 0)
eq_lib.add_equivalence(u3, equiv_u3)


q = QuantumRegister(1, 'q')
equiv_u2 = QuantumCircuit(q)
equiv_u2.append(RZGate(theta+(pi/2)), [q[0]], [])
equiv_u2.append(HGate(),[q[0]], [] )
equiv_u2.append(RZGate(pi/2),[q[0]], [])
equiv_u2.append(HGate(), [q[0]], [])
equiv_u2.append(RZGate(phi-(pi/2)),[q[0]], 0)
eq_lib.add_equivalence(u2, equiv_u2)

q = QuantumRegister(1, 'q')
equiv_u1 = QuantumCircuit(q)
equiv_u1.append(RZGate(pi/2), [q[0]], [])
equiv_u1.append(HGate(),[q[0]], [] )
equiv_u1.append(RZGate(0),[q[0]], [])
equiv_u1.append(HGate(), [q[0]], [])
equiv_u1.append(RZGate(theta-(pi/2)),[q[0]], 0)
eq_lib.add_equivalence(u1, equiv_u1)

q = QuantumRegister(3, 'q')
equiv_ccx = QuantumCircuit(q)
for inst, qargs, cargs in [
    (HGate(), [q[2]], []),
    (CXGate(), [q[1], q[2]],[]),
    (TdgGate(), [q[2]], []),
    (CXGate(), [q[0],q[2]], []),
    (TGate(), [q[2]], []),
    (CXGate(), [q[1],q[2]], []),
    (TdgGate(), [q[2]], []),
    (CXGate(), [q[0],q[2]], []),
    (CXGate(), [q[0],q[1]], []),
    (TdgGate(), [q[1]], []),
    (CXGate(), [q[0],q[1]], []),
    (TGate(), [q[0]], []),
    (TGate(), [q[1]], []),
    (TGate(), [q[2]], []),
    (HGate(), [q[2]], [])

]:
    equiv_ccx.append(inst, qargs, cargs)
    
eq_lib.add_equivalence(ccx, equiv_ccx)
