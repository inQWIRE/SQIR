open ModMult
open Nat
open RCIR
open SQIR
open ShorAux

(** val coq_OF_post_step : int -> int -> int -> int **)

let coq_OF_post_step step o m =
  snd
    (coq_ContinuedFraction step o
      (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) m))

(** val modmult_circuit : int -> int -> int -> int -> base_ucom **)

let modmult_circuit a ainv n n0 =
  bc2ucom (add n0 (modmult_rev_anc n0))
    (csplit (bcelim (modmult_rev n a ainv n0)))
