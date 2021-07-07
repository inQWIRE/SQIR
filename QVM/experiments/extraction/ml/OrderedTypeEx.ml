open Datatypes
open PeanoNat

module Nat_as_OT =
 struct
  type t = int

  (** val compare : int -> int -> int OrderedType.coq_Compare **)

  let compare x y =
    match Nat.compare x y with
    | Eq -> OrderedType.EQ
    | Lt -> OrderedType.LT
    | Gt -> OrderedType.GT

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    (=)
 end
