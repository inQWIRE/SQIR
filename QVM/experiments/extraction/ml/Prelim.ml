open Bool
open PeanoNat

(** val beq_reflect : int -> int -> reflect **)

let beq_reflect x y =
  iff_reflect ((=) x y)

(** val blt_reflect : int -> int -> reflect **)

let blt_reflect x y =
  iff_reflect (Nat.ltb x y)
