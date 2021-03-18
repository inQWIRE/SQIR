open Nat
open QPE
open RCIRplus
open SQIR
open Shor
open ShorAux

(** val modexp : int -> int -> int -> int **)

let modexp = fun a x n -> Z.to_int (Z.powm (Z.of_int a) (Z.of_int x) (Z.of_int n))

(** val modmult_circuit : int -> int -> int -> int -> int -> base_ucom **)

let modmult_circuit a ainv n n0 i =
  fst
    (rz_mod_sqir n
      (modexp a (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) n)
      (modexp ainv (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) i)
        n) n0)

(** val num_qubits : int -> int **)

let num_qubits n =
  get_dim (rz_mod_vars n)

(** val shor_circuit : int -> int -> (base_Unitary ucom * int) * int **)

let shor_circuit a n =
  let m =
    PeanoNat.Nat.log2
      (mul (Pervasives.succ (Pervasives.succ 0))
        (PeanoNat.Nat.pow n (Pervasives.succ (Pervasives.succ 0))))
  in
  let n0 = PeanoNat.Nat.log2 (mul (Pervasives.succ (Pervasives.succ 0)) n) in
  let ainv = modinv a n in
  let numq = num_qubits n0 in
  let f = fun i -> modmult_circuit a ainv n n0 i in
  (((Coq_useq ((coq_X (sub (add m n0) (Pervasives.succ 0))),
  (coq_QPE_var m numq f))), (add m numq)), m)

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
