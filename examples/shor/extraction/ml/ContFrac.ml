open Nat

(** val coq_CF_ite :
    Z.t -> Z.t -> Z.t -> Z.t -> Z.t -> Z.t -> Z.t -> Z.t * Z.t **)

let rec coq_CF_ite n a b p1 q1 p2 q2 =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> (p1, q1))
    (fun n0 ->
    if Z.equal a Z.zero
    then (p1, q1)
    else let c = Z.div b a in
         coq_CF_ite n0 (Z.rem b a) a (add (mul c p1) p2) (add (mul c q1) q2)
           p1 q1)
    n

(** val coq_ContinuedFraction : Z.t -> Z.t -> Z.t -> Z.t * Z.t **)

let coq_ContinuedFraction step a b =
  coq_CF_ite step a b Z.zero (Z.succ Z.zero) (Z.succ Z.zero) Z.zero
