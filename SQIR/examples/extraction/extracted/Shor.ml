open PeanoNat
open ShorAux

(** val coq_OF_post_step : int -> int -> int -> int **)

let coq_OF_post_step step o m =
  snd
    (coq_ContinuedFraction step o
      (Nat.pow (Pervasives.succ (Pervasives.succ 0)) m))
