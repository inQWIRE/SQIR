open Datatypes
open Nat
open ShorAux

(** val coq_OF_post_step : int -> int -> int -> int **)

let coq_OF_post_step step o m =
  snd
    (coq_ContinuedFraction step o
      (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) m))

(** val modexp : int -> int -> int -> int **)

let modexp a x n =
  PeanoNat.Nat.modulo (PeanoNat.Nat.pow a x) n

(** val coq_OF_post' : int -> int -> int -> int -> int -> int **)

let rec coq_OF_post' step a n o m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun step' ->
    let pre = coq_OF_post' step' a n o m in
    if (=) pre 0
    then if (=) (modexp a (coq_OF_post_step step' o m) n) (Pervasives.succ 0)
         then coq_OF_post_step step' o m
         else 0
    else pre)
    step

(** val coq_OF_post : int -> int -> int -> int -> int **)

let coq_OF_post a n o m =
  coq_OF_post'
    (add (mul (Pervasives.succ (Pervasives.succ 0)) m) (Pervasives.succ
      (Pervasives.succ 0))) a n o m
