open AltGateSet
open ModMult
open Nat
open RCIR

(** val controlled_rotations : Z.t -> coq_U ucom **)

let rec controlled_rotations n =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> coq_SKIP)
    (fun n' ->
    (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
      (fun _ -> coq_SKIP)
      (fun n0 ->
      (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
        (fun _ ->
        coq_CU1
          (( /. ) (( *. ) 2.0 Float.pi)
            ((fun a b -> a ** Z.to_float b) 2.0 n)) (Z.succ Z.zero) Z.zero)
        (fun _ -> Coq_useq ((controlled_rotations n'),
        (coq_CU1
          (( /. ) (( *. ) 2.0 Float.pi)
            ((fun a b -> a ** Z.to_float b) 2.0 n)) n' Z.zero)))
        n0)
      n')
    n

(** val coq_QFT : Z.t -> coq_U ucom **)

let rec coq_QFT n =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> coq_SKIP)
    (fun n' ->
    (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
      (fun _ -> coq_H Z.zero)
      (fun _ -> Coq_useq ((Coq_useq ((coq_H Z.zero),
      (controlled_rotations n))),
      (map_qubits (fun x -> Z.succ x) (coq_QFT n'))))
      n')
    n

(** val reverse_qubits' : Z.t -> Z.t -> coq_U ucom **)

let rec reverse_qubits' dim n =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> coq_SKIP)
    (fun n' ->
    (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
      (fun _ -> coq_SWAP Z.zero (sub dim (Z.succ Z.zero)))
      (fun _ -> Coq_useq ((reverse_qubits' dim n'),
      (coq_SWAP n' (sub (sub dim n') (Z.succ Z.zero)))))
      n')
    n

(** val reverse_qubits : Z.t -> coq_U ucom **)

let reverse_qubits n =
  reverse_qubits' n (Z.div n (Z.succ (Z.succ Z.zero)))

(** val coq_QFT_w_reverse : Z.t -> coq_U ucom **)

let coq_QFT_w_reverse n =
  Coq_useq ((coq_QFT n), (reverse_qubits n))

(** val bc2ucom : bccom -> coq_U ucom **)

let rec bc2ucom = function
| Coq_bcskip -> coq_SKIP
| Coq_bcx a -> coq_X a
| Coq_bcswap (a, b) -> coq_SWAP a b
| Coq_bccont (a, bc1) -> control a (bc2ucom bc1)
| Coq_bcseq (bc1, bc2) -> Coq_useq ((bc2ucom bc1), (bc2ucom bc2))

(** val controlled_powers' : (Z.t -> bccom) -> Z.t -> Z.t -> bccom **)

let rec controlled_powers' f k kmax =
  (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
    (fun _ -> Coq_bcskip)
    (fun k' ->
    (fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))
      (fun _ -> bygatectrl (sub kmax (Z.succ Z.zero)) (f Z.zero))
      (fun _ -> Coq_bcseq ((controlled_powers' f k' kmax),
      (bygatectrl (sub (sub kmax k') (Z.succ Z.zero)) (f k'))))
      k')
    k

(** val controlled_powers : (Z.t -> bccom) -> Z.t -> coq_U ucom **)

let controlled_powers f k =
  bc2ucom (controlled_powers' f k k)

(** val coq_QPE : Z.t -> (Z.t -> bccom) -> coq_U ucom **)

let coq_QPE k f =
  Coq_useq ((Coq_useq ((npar k U_H),
    (controlled_powers (fun x -> map_bccom (fun q -> add k q) (f x)) k))),
    (invert (coq_QFT_w_reverse k)))

(** val modexp : Z.t -> Z.t -> Z.t -> Z.t **)

let modexp a x n =
  Z.rem (PeanoNat.Nat.pow a x) n

(** val modmult_circuit : Z.t -> Z.t -> Z.t -> Z.t -> Z.t -> bccom **)

let modmult_circuit a ainv n n0 i =
  bcelim
    (modmult_rev n (modexp a (PeanoNat.Nat.pow (Z.succ (Z.succ Z.zero)) i) n)
      (modexp ainv (PeanoNat.Nat.pow (Z.succ (Z.succ Z.zero)) i) n) n0)

(** val shor_circuit : Z.t -> Z.t -> coq_U ucom **)

let shor_circuit a n =
  let m =
    PeanoNat.Nat.log2
      (mul (Z.succ (Z.succ Z.zero))
        (PeanoNat.Nat.pow n (Z.succ (Z.succ Z.zero))))
  in
  let n0 = PeanoNat.Nat.log2 (mul (Z.succ (Z.succ Z.zero)) n) in
  let ainv = Z.invert a n in
  let f = fun i -> modmult_circuit a ainv n n0 i in
  Coq_useq ((coq_X (sub (add m n0) (Z.succ Z.zero))), (coq_QPE m f))

(** val shor_output_nqs : Z.t -> Z.t **)

let shor_output_nqs n =
  PeanoNat.Nat.log2
    (mul (Z.succ (Z.succ Z.zero))
      (PeanoNat.Nat.pow n (Z.succ (Z.succ Z.zero))))

(** val modmult_data_nqs : Z.t -> Z.t **)

let modmult_data_nqs n =
  PeanoNat.Nat.log2 (mul (Z.succ (Z.succ Z.zero)) n)

(** val modmult_anc_nqs : Z.t -> Z.t **)

let modmult_anc_nqs n =
  modmult_rev_anc (PeanoNat.Nat.log2 (mul (Z.succ (Z.succ Z.zero)) n))

(** val modmult_nqs : Z.t -> Z.t **)

let modmult_nqs n =
  add (modmult_data_nqs n) (modmult_anc_nqs n)

(** val shor_nqs : Z.t -> Z.t **)

let shor_nqs n =
  add (shor_output_nqs n) (modmult_nqs n)
