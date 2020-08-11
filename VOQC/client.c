#include <stdio.h>
#include <caml/callback.h>
extern value get_gate(char const *x);
extern value optimizer(value x);
extern value not_p(value x);
extern value cancel_single(value x);
extern value cancel_two(value x);
extern value merge(value x);
extern value hadamard(value x);
extern value write_qasm(char const *x, value y);
void init_lib(void);
int main(int argc, char** argv) {
  init_lib();
  value x  = get_gate("/home/ag/Documents/SQIR/VOQC/benchmarks/PF/pf1_100.qasm");
  x = optimizer(x);
  write_qasm("out.qasm", x);
  return 0;
}
