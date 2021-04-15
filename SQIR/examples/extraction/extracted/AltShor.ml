open AltGateSet
open BinNums
open ModMult
open Nat
open RCIR
open Rdefinitions
open Rpow_def
open Rtrigo1
open ShorAux

(** val controlled_rotations : int -> coq_U ucom **)

let rec controlled_rotations n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_SKIP)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        coq_CU1
          (coq_Rdiv (coq_Rmult (coq_IZR (Zpos (Coq_xO Coq_xH))) coq_PI)
            (pow (coq_IZR (Zpos (Coq_xO Coq_xH))) n)) (Pervasives.succ 0) 0)
        (fun _ -> Coq_useq ((controlled_rotations n'),
        (coq_CU1
          (coq_Rdiv (coq_Rmult (coq_IZR (Zpos (Coq_xO Coq_xH))) coq_PI)
            (pow (coq_IZR (Zpos (Coq_xO Coq_xH))) n)) n' 0)))
        n0)
      n')
    n

(** val coq_QFT : int -> coq_U ucom **)

let rec coq_QFT n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_H 0)
      (fun _ -> Coq_useq ((Coq_useq ((coq_H 0), (controlled_rotations n))),
      (map_qubits (fun x -> Pervasives.succ x) (coq_QFT n'))))
      n')
    n

(** val reverse_qubits' : int -> int -> coq_U ucom **)

let rec reverse_qubits' dim n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_SWAP 0 (sub dim (Pervasives.succ 0)))
      (fun _ -> Coq_useq ((reverse_qubits' dim n'),
      (coq_SWAP n' (sub (sub dim n') (Pervasives.succ 0)))))
      n')
    n

(** val reverse_qubits : int -> coq_U ucom **)

let reverse_qubits n =
  reverse_qubits' n (PeanoNat.Nat.div n (Pervasives.succ (Pervasives.succ 0)))

(** val coq_QFT_w_reverse : int -> coq_U ucom **)

let coq_QFT_w_reverse n =
  Coq_useq ((coq_QFT n), (reverse_qubits n))

(** val controlled_powers_var' : (int -> bccom) -> int -> int -> bccom **)

let rec controlled_powers_var' f k kmax =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Coq_bcskip)
    (fun k' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Coq_bccont ((sub kmax (Pervasives.succ 0)), (f 0)))
      (fun _ -> Coq_bcseq ((controlled_powers_var' f k' kmax), (Coq_bccont
      ((sub (sub kmax k') (Pervasives.succ 0)), (f k')))))
      k')
    k

(** val controlled_powers_var : (int -> bccom) -> int -> coq_U ucom **)

let controlled_powers_var f k =
  bc2ucom (controlled_powers_var' f k k)

(** val map_bccom : (int -> int) -> bccom -> bccom **)

let rec map_bccom f = function
| Coq_bcskip -> Coq_bcskip
| Coq_bcx a -> Coq_bcx (f a)
| Coq_bcswap (a, b) -> Coq_bcswap ((f a), (f b))
| Coq_bccont (a, bc1) -> Coq_bccont ((f a), (map_bccom f bc1))
| Coq_bcseq (bc1, bc2) -> Coq_bcseq ((map_bccom f bc1), (map_bccom f bc2))

(** val coq_QPE_var : int -> (int -> bccom) -> coq_U ucom **)

let coq_QPE_var k f =
  Coq_useq ((Coq_useq ((npar k U_H),
    (controlled_powers_var (fun x -> map_bccom (fun q -> add k q) (f x)) k))),
    (invert (coq_QFT_w_reverse k)))

(** val modexp : int -> int -> int -> int **)

let modexp = fun a x n -> Z.to_int (Z.powm (Z.of_int a) (Z.of_int x) (Z.of_int n))

(** val modmult_circuit : int -> int -> int -> int -> int -> bccom **)

let modmult_circuit a ainv n n0 i =
  bcelim
    (modmult_rev n
      (modexp a (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) n)
      (modexp ainv (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) i)
        n) n0)

(** val num_qubits : int -> int **)

let num_qubits n =
  add n (modmult_rev_anc n)

(** val shor_circuit : int -> int -> (coq_U ucom * int) * int **)

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
  (coq_QPE_var m f))), (add m numq)), m)
