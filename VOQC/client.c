#include <stdio.h>
#include <caml/callback.h>
#include "extraction/ocaml_wrapper.h"

// 1. copy libvoqc.so to extraction directory
// 2. compile with gcc -I/usr/local/lib/ocaml/ -I./extraction -L./extraction/ client.c -lvoqc

void init(void);

int main(int argc, char** argv) {
  if(argc != 3) {
      printf("usage: %s <input file> <output file>\n", argv[0]);
      exit(-1);
  }
  init();
  value x  = read_qasm_file(argv[1]);
  printf("Original:\t Total %d, Rz %d, Clifford %d, T %d, H %d, X %d, CNOT %d\n",
         // (will seg fault with c_count or t_count included)
         //total_count(x), rz_count(x), c_count(x), t_count(x), h_count(x), x_count(x), cnot_count(x));
         total_count(x), rz_count(x), -1, -1, h_count(x), x_count(x), cnot_count(x));
  x = optimize(x);
  printf("Final:\t Total %d, Rz %d, Clifford %d, T %d, H %d, X %d, CNOT %d\n", 
          //total_count(x), rz_count(x), c_count(x), t_count(x), h_count(x), x_count(x), cnot_count(x));
          total_count(x), rz_count(x), -1, -1, h_count(x), x_count(x), cnot_count(x));
  write_qasm_file(argv[2], x);
  return 0;
}