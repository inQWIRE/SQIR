qreg q[2];
creg c[1];
X q[1];
H q[0];
H q[1];
CX q[0],q[1];
H q[0];
measure q[0] -> c[0];

