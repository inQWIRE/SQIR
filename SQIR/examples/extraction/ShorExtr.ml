open ModMult
open Nat
open QPE
open RCIR
open SQIR
open ShorAux

(** val modexp : int -> int -> int -> int **)

let modexp = fun a i n -> Z.to_int (Z.powm (Z.of_int a) (Z.pow (Z.of_int 2) i) (Z.of_int n))

(** val shor_circuit : int -> int -> base_ucom * int **)

let shor_circuit a n =
  let m =
    PeanoNat.Nat.log2
      (mul (Pervasives.succ (Pervasives.succ 0))
        (PeanoNat.Nat.pow n (Pervasives.succ (Pervasives.succ 0))))
  in
  let n0 = PeanoNat.Nat.log2_up n in
  let anc = modmult_rev_anc n0 in
  let ainv = modinv a n in
  let f = fun i ->
    bc2ucom (add n0 anc)
      (bcelim (modmult_rev n (modexp a i n) (modexp ainv i n) n0))
  in
  ((coq_QPE_var m (add n0 anc) f), (add m (add n0 anc)))

(** val post_process : int -> int -> int -> unit **)

let post_process _ _ _ =
  ()
