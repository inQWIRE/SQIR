open BinNums
open ModMult
open Nat
open QPE
open Rdefinitions
open SQIR
open Shor
open ShorAux

(** val modexp : int -> int -> int -> int **)

let modexp = fun a x n -> Z.to_int (Z.powm (Z.of_int a) (Z.of_int x) (Z.of_int n))

(** val shor_circuit : int -> int -> (base_Unitary ucom * int) * int **)

let shor_circuit a n =
  let m =
    PeanoNat.Nat.log2
      (mul (Pervasives.succ (Pervasives.succ 0))
        (PeanoNat.Nat.pow n (Pervasives.succ (Pervasives.succ 0))))
  in
  let n0 = PeanoNat.Nat.log2 (mul (Pervasives.succ (Pervasives.succ 0)) n) in
  let anc = modmult_rev_anc n0 in
  let ainv = modinv a n in
  let f = fun i ->
    modmult_circuit
      (modexp a (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) n)
      (modexp ainv (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) i)
        n) n n0
  in
  (((Coq_useq ((coq_X (sub (add m n0) (Pervasives.succ 0))),
  (coq_QPE_var m (add n0 anc) f))), (add m (add n0 anc))), m)

(** val remove_skips : base_ucom -> base_Unitary ucom **)

let rec remove_skips u = match u with
| Coq_useq (u1, u2) ->
  (match remove_skips u1 with
   | Coq_uapp1 (g, q) ->
     (match g with
      | U_R (_UU03b8_, _UU03d5_, _UU03bb_) ->
        if (&&)
             ((&&) (( = ) _UU03b8_ (coq_IZR Z0))
               (( = ) _UU03d5_ (coq_IZR Z0))) (( = ) _UU03bb_ (coq_IZR Z0))
        then remove_skips u2
        else Coq_useq ((Coq_uapp1 (g, q)), (remove_skips u2))
      | U_CNOT -> Coq_useq ((Coq_uapp1 (g, q)), (remove_skips u2)))
   | x ->
     (match remove_skips u2 with
      | Coq_uapp1 (g, q) ->
        (match g with
         | U_R (_UU03b8_, _UU03d5_, _UU03bb_) ->
           if (&&)
                ((&&) (( = ) _UU03b8_ (coq_IZR Z0))
                  (( = ) _UU03d5_ (coq_IZR Z0))) (( = ) _UU03bb_ (coq_IZR Z0))
           then x
           else Coq_useq (x, (Coq_uapp1 (g, q)))
         | U_CNOT -> Coq_useq (x, (Coq_uapp1 (g, q))))
      | x0 -> Coq_useq (x, x0)))
| _ -> u

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
