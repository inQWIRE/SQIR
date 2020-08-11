#include <caml/mlvalues.h>
value get_gate(char *x);
value optimizer(value x);
value not_p(value x);
value cancel_single(value x);
value cancel_two(value x);
value merge(value x);
value hadamard(value x);
value write_qasm(char *x, value y);
void init_lib(void);
