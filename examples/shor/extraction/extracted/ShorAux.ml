open BinInt
open BinNums
open Nat

(** val exteuc : int -> int -> coq_Z * coq_Z **)

let rec exteuc a b =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (Z0, (Zpos Coq_xH)))
    (fun a' ->
    let (p, q) =
      exteuc (PeanoNat.Nat.modulo b (Pervasives.succ a')) (Pervasives.succ a')
    in
    ((Z.sub q (Z.mul (Z.div (Z.of_nat b) (Z.of_nat a)) p)), p))
    a

(** val modinv : int -> int -> int **)

let modinv a n =
  let (n0, _) = exteuc a n in Z.to_nat (Z.modulo n0 (Z.of_nat n))

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
