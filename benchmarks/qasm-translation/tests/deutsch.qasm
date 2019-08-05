OPENQASM 2.0;
qreg q[2];
creg c[1];
x q[1];
h q[0];
h q[1];
CX q[0],q[1];
h q[0];
measure q[0] -> c[0];
