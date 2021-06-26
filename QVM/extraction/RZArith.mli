open Nat
open VSQIR

val rz_adder' : var -> int -> int -> (int -> bool) -> exp

val rz_adder : var -> int -> (int -> bool) -> exp

val rz_sub' : var -> int -> int -> (int -> bool) -> exp

val rz_sub : var -> int -> (int -> bool) -> exp

val qft_cu : var -> posi -> pexp

val qft_acu : var -> posi -> pexp

val one_cu_adder : var -> int -> posi -> (int -> bool) -> exp

val mod_adder_half :
  var -> int -> posi -> (int -> bool) -> (int -> bool) -> pexp

val clean_hbit : var -> int -> posi -> (int -> bool) -> pexp

val mod_adder : var -> int -> posi -> (int -> bool) -> (int -> bool) -> pexp

val rz_modmult' : var -> var -> int -> int -> posi -> int -> int -> pexp

val rz_modmult_half : var -> var -> int -> posi -> int -> int -> pexp

val rz_modmult_full : var -> var -> int -> posi -> int -> int -> int -> pexp
