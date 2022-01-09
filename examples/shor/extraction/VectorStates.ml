open BinNums
open Complex
open Matrix

(** val basis_vector : int -> int -> coq_Matrix **)

let basis_vector _ k i j =
  if (&&) ((=) i k) ((=) j 0)
  then coq_RtoC (Float.of_int (Zpos Coq_xH))
  else coq_RtoC (Float.of_int Z0)
