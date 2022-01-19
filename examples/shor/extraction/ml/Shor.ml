open ContFrac
open Datatypes
open Nat

(** val coq_OF_post_step : Z.t -> Z.t -> Z.t -> Z.t **)

let coq_OF_post_step step o m =
  snd
    (coq_ContinuedFraction step o
      (PeanoNat.Nat.pow (Z.succ (Z.succ Z.zero)) m))

(** val coq_OF_post' : Z.t -> Z.t -> Z.t -> Z.t -> Z.t -> Z.t **)

let rec coq_OF_post' step a n o m =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> Z.zero)
    (fun step' ->
    let pre = coq_OF_post' step' a n o m in
    if Z.equal pre Z.zero
    then if Z.equal (Z.powm a (coq_OF_post_step step' o m) n) (Z.succ Z.zero)
         then coq_OF_post_step step' o m
         else Z.zero
    else pre)
    step

(** val coq_OF_post : Z.t -> Z.t -> Z.t -> Z.t -> Z.t **)

let coq_OF_post a n o m =
  coq_OF_post'
    (add (mul (Z.succ (Z.succ Z.zero)) m) (Z.succ (Z.succ Z.zero))) a n o m
