open Nat

(** val coq_CF_ite :
    int -> int -> int -> int -> int -> int -> int -> int * int **)

let rec coq_CF_ite n a b p1 q1 p2 q2 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (p1, q1))
    (fun n0 ->
    if (=) a 0
    then (p1, q1)
    else let c = PeanoNat.Nat.div b a in
         coq_CF_ite n0 (PeanoNat.Nat.modulo b a) a (add (mul c p1) p2)
           (add (mul c q1) q2) p1 q1)
    n

(** val coq_ContinuedFraction : int -> int -> int -> int * int **)

let coq_ContinuedFraction step a b =
  coq_CF_ite step a b 0 (Pervasives.succ 0) (Pervasives.succ 0) 0
