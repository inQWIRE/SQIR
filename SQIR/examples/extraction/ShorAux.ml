open BinInt
open BinNums
open PeanoNat

(** val exteuc : int -> int -> coq_Z * coq_Z **)

let rec exteuc a b =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (Z0, (Zpos Coq_xH)))
    (fun a' ->
    let (p, q) =
      exteuc (Nat.modulo b (Pervasives.succ a')) (Pervasives.succ a')
    in
    ((Z.sub q (Z.mul (Z.div (Z.of_nat b) (Z.of_nat a)) p)), p))
    a

(** val modinv : int -> int -> int **)

let modinv a n =
  let (n0, _) = exteuc a n in Z.to_nat (Z.modulo n0 (Z.of_nat n))
