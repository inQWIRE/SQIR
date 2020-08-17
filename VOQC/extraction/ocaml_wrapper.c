#include <stdio.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/fail.h>
#include <caml/callback.h>

#include "ocaml_wrapper.h"

// CLOSURE taken from https://github.com/xoolive/facile
#define CLOSURE(A)\
  static const value * closure = NULL;\
  if (closure == NULL) {\
    closure = caml_named_value(A);\
  }

void init () {
    static char* dummy_argv[2] = { "", NULL };
    caml_startup(dummy_argv);
}

void cleanup(value circ) {
    caml_remove_global_root(&circ);
}

value read_qasm_file (char* fname) {
   CAMLparam0();
   CAMLlocal2(local, circ);
   local = caml_copy_string(fname);
   CLOSURE("read_qasm_file");
   caml_register_global_root(&circ);
   circ = caml_callback(*closure, local);
   caml_register_global_root(&circ);
   CAMLreturn(circ);
}

value optimize (value circ) {
   CAMLparam1(circ);
   CAMLlocal1(res);
   CLOSURE("optimize");
   caml_register_global_root(&res);
   res = caml_callback(*closure, circ);
   caml_register_global_root(&res);
   caml_remove_global_root(&circ);
   CAMLreturn(res);
}

void write_qasm_file (char* outf, value circ) {
   CAMLparam1(circ);
   CAMLlocal2(fname, res);
   fname = caml_copy_string(outf);
   CLOSURE("write_qasm_file");
   res = caml_callback2(*closure, fname, circ);
   CAMLreturn0;
}

int x_count (value circ) {
    CAMLparam1(circ);
    CLOSURE("x_count");
    CAMLreturn(Int_val(caml_callback(*closure, circ)));
}

int h_count (value circ) {
    CAMLparam1(circ);
    CLOSURE("h_count");
    CAMLreturn(Int_val(caml_callback(*closure, circ)));
}

int rz_count (value circ) {
    CAMLparam1(circ);
    CLOSURE("rz_count");
    CAMLreturn(Int_val(caml_callback(*closure, circ)));
}

int cnot_count (value circ) {
    CAMLparam1(circ);
    CLOSURE("cnot_count");
    CAMLreturn(Int_val(caml_callback(*closure, circ)));
}

int c_count (value circ) {
    CAMLparam1(circ);
    CLOSURE("c_count");
    CAMLreturn(Int_val(caml_callback(*closure, circ)));
}

int t_count (value circ) {
    CAMLparam1(circ);
    CLOSURE("t_count");
    CAMLreturn(Int_val(caml_callback(*closure, circ)));
}

int total_count (value circ) {
    CAMLparam1(circ);
    CLOSURE("total_count");
    CAMLreturn(Int_val(caml_callback(*closure, circ)));
}


