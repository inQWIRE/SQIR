open AltGateSet
open AltShor
open Nat
open Shor

(** val shor_circuit : int -> int -> (coq_U ucom * int) * int **)

let shor_circuit a n =
  let m =
    PeanoNat.Nat.log2
      (mul (Pervasives.succ (Pervasives.succ 0))
        (PeanoNat.Nat.pow n (Pervasives.succ (Pervasives.succ 0))))
  in
  let n0 = PeanoNat.Nat.log2 (mul (Pervasives.succ (Pervasives.succ 0)) n) in
  let numq = num_qubits n0 in (((shor_circuit a n), (add m numq)), m)

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

(** val post_process : int -> int -> int -> int **)

let post_process a n o =
  let m =
    PeanoNat.Nat.log2
      (mul (Pervasives.succ (Pervasives.succ 0))
        (PeanoNat.Nat.pow n (Pervasives.succ (Pervasives.succ 0))))
  in
  coq_OF_post a n o m
