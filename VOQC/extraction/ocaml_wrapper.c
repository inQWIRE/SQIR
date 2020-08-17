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

value* wrap(value v) {
    value* res = (value*) malloc(sizeof(value));
    *res = v;
    caml_register_global_root(res);
    return res;
}

void destroy(value* v) {
    caml_remove_global_root(v);
    free(v);
}

void init () {
    static char* dummy_argv[2] = { "", NULL };
    caml_startup(dummy_argv);
}

value* read_qasm_file (char* fname) {
   value local, circ;
   local = caml_copy_string(fname);
   CLOSURE("read_qasm_file");
   circ = caml_callback(*closure, local);
   return wrap(circ);
}

value* optimize (value* circ) {
   value res;
   CLOSURE("optimize");
   res = caml_callback(*closure, *circ);
   destroy(circ);
   return wrap(res);
}

void write_qasm_file (char* outf, value* circ) {
   value fname, res;
   fname = caml_copy_string(outf);
   CLOSURE("write_qasm_file");
   res = caml_callback2(*closure, fname, *circ);
}

int x_count (value* circ) {
    CLOSURE("x_count");
    return Int_val(caml_callback(*closure, *circ));
}

int h_count (value* circ) {
    CLOSURE("h_count");
    return Int_val(caml_callback(*closure, *circ));
}

int rz_count (value* circ) {
    CLOSURE("rz_count");
    return Int_val(caml_callback(*closure, *circ));
}

int cnot_count (value* circ) {
    CLOSURE("cnot_count");
    return Int_val(caml_callback(*closure, *circ));
}

int c_count (value* circ) {
    CLOSURE("c_count");
    return Int_val(caml_callback(*closure, *circ));
}

int t_count (value* circ) {
    CLOSURE("t_count");
    return Int_val(caml_callback(*closure, *circ));
}

int total_count (value* circ) {
    CLOSURE("total_count");
    return Int_val(caml_callback(*closure, *circ));
}


