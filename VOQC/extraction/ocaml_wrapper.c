#include <stdio.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/fail.h>
#include <caml/callback.h>
#include <caml/custom.h>
#include <caml/threads.h>

static int init_done = 0;

void init_lib(void){
  char *start[1];
  start[0] = NULL;
  if (!init_done){
	caml_startup(start);
	init_done = 1;
  }
}

value get_gate (char *x){
   CAMLparam0();
   int nargs;
   nargs = 1;
   CAMLlocalN(locals, nargs);
   locals[0] = caml_copy_string(x);
   static const value * gate_closure = NULL;
   if (gate_closure == NULL) gate_closure = caml_named_value("get_gate");
   value circ = caml_callbackN(*gate_closure, nargs, locals);
   CAMLreturn(circ);

}

value optimizer (value x){
   CAMLparam1(x);
   int nargs;
   nargs = 1;
   CAMLlocalN(locals, nargs);
   locals[0] = x;
   static const value * fib_closure = NULL;
   if (fib_closure == NULL) fib_closure = caml_named_value("optimizer");
   value x51 = caml_callbackN(*fib_closure, nargs, locals);
   caml_local_roots = caml__frame;;
   CAMLreturn(x51);
}

value not_p (value x){
   CAMLparam1(x);
   int nargs;
   nargs = 1;
   CAMLlocalN(locals, nargs);
   locals[0] = x;
   static const value * fib_closure = NULL;
   if (fib_closure == NULL) fib_closure = caml_named_value("not_p");
   value x51 = caml_callbackN(*fib_closure, nargs, locals);
   /*caml_local_roots = caml__frame;;*/
   CAMLreturn(x51);
}

value hadamard (value x){
   CAMLparam1(x);
   int nargs;
   nargs = 1;
   CAMLlocalN(locals, nargs);
   locals[0] = x;
   static const value * fib_closure = NULL;
   if (fib_closure == NULL) fib_closure = caml_named_value("hadamard");
   value x51 = caml_callbackN(*fib_closure, nargs, locals);
   /*caml_local_roots = caml__frame;;*/
   CAMLreturn(x51);
}

value merge (value x){
   CAMLparam1(x);
   int nargs;
   nargs = 1;
   CAMLlocalN(locals, nargs);
   locals[0] = x;
   static const value * fib_closure = NULL;
   if (fib_closure == NULL) fib_closure = caml_named_value("merge");
   value x51 = caml_callbackN(*fib_closure, nargs, locals);
   /*caml_local_roots = caml__frame;;*/
   CAMLreturn(x51);
}

value cancel_single (value x){
   CAMLparam1(x);
   int nargs;
   nargs = 1;
   CAMLlocalN(locals, nargs);
   locals[0] = x;
   static const value * fib_closure = NULL;
   if (fib_closure == NULL) fib_closure = caml_named_value("cancel_single");
   value x51 = caml_callbackN(*fib_closure, nargs, locals);
   /*caml_local_roots = caml__frame;;*/
   CAMLreturn(x51);
}

value cancel_two (value x){
   CAMLparam1(x);
   int nargs;
   nargs = 1;
   CAMLlocalN(locals, nargs);
   locals[0] = x;
   static const value * fib_closure = NULL;
   if (fib_closure == NULL) fib_closure = caml_named_value("cancel_two");
   value x51 = caml_callbackN(*fib_closure, nargs, locals);
   /*caml_local_roots = caml__frame;;*/
   CAMLreturn(x51);
}

value write_qasm (char * x, value y){
   CAMLparam1(y);
   int nargs;
   nargs = 2;
   CAMLlocalN(locals, nargs);
   locals[0] = caml_copy_string(x);
   locals[1] = y;
   static const value * fib_closure = NULL;
   if (fib_closure == NULL) fib_closure = caml_named_value("write_qasm");
   value x51 = caml_callbackN(*fib_closure, nargs, locals);
   /*caml_local_roots = caml__frame;;*/
   CAMLreturn(x51);
}

int x_c (value x){
   CAMLparam1(x);
   int nargs;
   nargs = 1;
   CAMLlocalN(locals, nargs);
   locals[0] = x;
   static const value * fib_closure = NULL;
   if (fib_closure == NULL) fib_closure = caml_named_value("x_c");
   int y = Int_val(caml_callbackN(*fib_closure, nargs, locals));
   CAMLreturn(y);
}


int h_c (value x){
   CAMLparam1(x);
   int nargs;
   nargs = 1;
   CAMLlocalN(locals, nargs);
   locals[0] = x;
   static const value * fib_closure = NULL;
   if (fib_closure == NULL) fib_closure = caml_named_value("h_c");
   int y = Int_val(caml_callbackN(*fib_closure, nargs, locals));
   CAMLreturn(y);
}


int rz_c (value x){
   CAMLparam1(x);
   int nargs;
   nargs = 1;
   CAMLlocalN(locals, nargs);
   locals[0] = x;
   static const value * fib_closure = NULL;
   if (fib_closure == NULL) fib_closure = caml_named_value("rz_c");
   int y = Int_val(caml_callbackN(*fib_closure, nargs, locals));
   CAMLreturn(y);
}


int cnot_c (value x){
   CAMLparam1(x);
   int nargs;
   nargs = 1;
   CAMLlocalN(locals, nargs);
   locals[0] = x;
   static const value * fib_closure = NULL;
   if (fib_closure == NULL) fib_closure = caml_named_value("cnot_c");
   int y = Int_val(caml_callbackN(*fib_closure, nargs, locals));
   CAMLreturn(y);
}


int cliff_c (value x){
   CAMLparam1(x);
   int nargs;
   nargs = 1;
   CAMLlocalN(locals, nargs);
   locals[0] = x;
   static const value * fib_closure = NULL;
   if (fib_closure == NULL) fib_closure = caml_named_value("cliff_c");
   int y = Int_val(caml_callbackN(*fib_closure, nargs, locals));
   CAMLreturn(y);
}

char* t_c (value x){
   CAMLparam1(x);
   int nargs;
   nargs = 1;
   CAMLlocalN(locals, nargs);
   locals[0] = x;
   static const value * fib_closure = NULL;
   if (fib_closure == NULL) fib_closure = caml_named_value("t_c");
   char* y = String_val(caml_callbackN(*fib_closure, nargs, locals));
   CAMLreturnT(char *, y);
}

int tot (value x){
   CAMLparam1(x);
   int nargs;
   nargs = 1;
   CAMLlocalN(locals, nargs);
   locals[0] = x;
   static const value * fib_closure = NULL;
   if (fib_closure == NULL) fib_closure = caml_named_value("tot");
   int y = Int_val(caml_callbackN(*fib_closure, nargs, locals));
   CAMLreturn(y);
}
