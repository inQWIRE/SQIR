open AltGateSet
open ModMult
open Nat
open NumTheory
open RCIR

(** val controlled_rotations : int -> coq_U ucom **)

let rec controlled_rotations n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_SKIP)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        coq_CU1
          (( /. ) (( *. ) 2.0 Float.pi)
            ((fun a b -> a ** Float.of_int b) 2.0 n0)) (Pervasives.succ 0) 0)
        (fun _ -> Coq_useq ((controlled_rotations n'),
        (coq_CU1
          (( /. ) (( *. ) 2.0 Float.pi)
            ((fun a b -> a ** Float.of_int b) 2.0 n0)) n' 0)))
        n1)
      n')
    n0

(** val coq_QFT : int -> coq_U ucom **)

let rec coq_QFT n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_H 0)
      (fun _ -> Coq_useq ((Coq_useq ((coq_H 0), (controlled_rotations n0))),
      (map_qubits (fun x -> Pervasives.succ x) (coq_QFT n'))))
      n')
    n0

(** val reverse_qubits' : int -> int -> coq_U ucom **)

let rec reverse_qubits' dim n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_SWAP 0 (sub dim (Pervasives.succ 0)))
      (fun _ -> Coq_useq ((reverse_qubits' dim n'),
      (coq_SWAP n' (sub (sub dim n') (Pervasives.succ 0)))))
      n')
    n0

(** val reverse_qubits : int -> coq_U ucom **)

let reverse_qubits n0 =
  reverse_qubits' n0
    (PeanoNat.Nat.div n0 (Pervasives.succ (Pervasives.succ 0)))

(** val coq_QFT_w_reverse : int -> coq_U ucom **)

let coq_QFT_w_reverse n0 =
  Coq_useq ((coq_QFT n0), (reverse_qubits n0))

(** val bc2ucom : bccom -> coq_U ucom **)

let rec bc2ucom = function
| Coq_bcskip -> coq_SKIP
| Coq_bcx a -> coq_X a
| Coq_bcswap (a, b) -> coq_SWAP a b
| Coq_bccont (a, bc1) -> control a (bc2ucom bc1)
| Coq_bcseq (bc1, bc2) -> Coq_useq ((bc2ucom bc1), (bc2ucom bc2))

(** val controlled_powers' : (int -> bccom) -> int -> int -> bccom **)

let rec controlled_powers' f k0 kmax =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Coq_bcskip)
    (fun k' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> bygatectrl (sub kmax (Pervasives.succ 0)) (f 0))
      (fun _ -> Coq_bcseq ((controlled_powers' f k' kmax),
      (bygatectrl (sub (sub kmax k') (Pervasives.succ 0)) (f k'))))
      k')
    k0

(** val controlled_powers : (int -> bccom) -> int -> coq_U ucom **)

let controlled_powers f k0 =
  bc2ucom (controlled_powers' f k0 k0)

(** val coq_QPE : int -> (int -> bccom) -> coq_U ucom **)

let coq_QPE k0 f =
  Coq_useq ((Coq_useq ((npar k0 U_H),
    (controlled_powers (fun x -> map_bccom (fun q -> add k0 q) (f x)) k0))),
    (invert (coq_QFT_w_reverse k0)))

(** val modexp : int -> int -> int -> int **)

let modexp = fun a x n -> Z.to_int (Z.powm (Z.of_int a) (Z.of_int x) (Z.of_int n))

(** val modmult_circuit : int -> int -> int -> int -> int -> bccom **)

let modmult_circuit a ainv n0 n1 i =
  bcelim
    (modmult_rev n0
      (modexp a (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) n0)
      (modexp ainv (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) i)
        n0) n1)

(** val num_qubits : int -> int **)

let num_qubits n0 =
  add n0 (modmult_rev_anc n0)

(** val shor_circuit : int -> int -> coq_U ucom **)

let shor_circuit a n0 =
  let m =
    PeanoNat.Nat.log2
      (mul (Pervasives.succ (Pervasives.succ 0))
        (PeanoNat.Nat.pow n0 (Pervasives.succ (Pervasives.succ 0))))
  in
  let n1 = PeanoNat.Nat.log2 (mul (Pervasives.succ (Pervasives.succ 0)) n0) in
  let ainv = modinv a n0 in
  let f = fun i -> modmult_circuit a ainv n0 n1 i in
  Coq_useq ((coq_X (sub (add m n1) (Pervasives.succ 0))), (coq_QPE m f))

(** val n : int -> int **)

let n n0 =
  PeanoNat.Nat.log2
    (mul (Pervasives.succ (Pervasives.succ 0))
      (PeanoNat.Nat.pow n0 (Pervasives.succ (Pervasives.succ 0))))

(** val k : int -> int **)

let k n0 =
  num_qubits
    (PeanoNat.Nat.log2 (mul (Pervasives.succ (Pervasives.succ 0)) n0))
