open Summation

(** val coq_R_is_monoid : float coq_Monoid **)

let coq_R_is_monoid =
  { coq_Gzero = (Z.to_float Z.zero); coq_Gplus = ( +. ) }
