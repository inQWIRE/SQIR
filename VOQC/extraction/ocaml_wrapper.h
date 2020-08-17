#include <caml/mlvalues.h>

void init();
void destroy(value*);

value* read_qasm_file(char* fname);
value* optimize(value* circ);
value* not_propagation(value* circ);
value* hadamard_reduction(value* circ);
value* merge_rotations(value* circ);
value* cancel_single_qubit_gates(value* circ);
value* cancel_two_qubit_gates(value* circ);
void write_qasm_file(char* outf, value* circ);
int x_count (value* circ);
int h_count (value* circ);
int rz_count (value* circ);
int cnot_count (value* circ);
int c_count(value* circ);
int t_count (value* circ);
int total_count (value* circ);
