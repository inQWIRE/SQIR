OPENQASM 2.0;
//include "qelib1.inc";

qreg q[2];
qreg r[2];

CX q[0], r[0];
CX q, r;
CX q,r[0];
CX q[0],r;

//cx q[0], r[0];
//cx q, r;
//cx q,r[0];
//cx q[0],r;

