open BinNums
open Nat
open Rdefinitions
open Rpow_def
open Rtrigo1
open SQIR
open UnitaryOps

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val controlled_rotations : int -> base_ucom **)

let rec controlled_rotations n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP __)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_SKIP __)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        control n (Pervasives.succ 0)
          (coq_Rz
            (coq_Rdiv (coq_Rmult (coq_IZR (Zpos (Coq_xO Coq_xH))) coq_PI)
              (pow (coq_IZR (Zpos (Coq_xO Coq_xH))) n)) 0))
        (fun _ -> Coq_useq ((cast n' (controlled_rotations n') n),
        (control n n'
          (coq_Rz
            (coq_Rdiv (coq_Rmult (coq_IZR (Zpos (Coq_xO Coq_xH))) coq_PI)
              (pow (coq_IZR (Zpos (Coq_xO Coq_xH))) n)) 0))))
        n0)
      n')
    n

(** val coq_QFT : int -> base_ucom **)

let rec coq_QFT n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP __)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_H 0)
      (fun _ -> Coq_useq ((Coq_useq ((coq_H 0), (controlled_rotations n))),
      (cast n' (map_qubits n' (fun x -> Pervasives.succ x) (coq_QFT n')) n)))
      n')
    n

(** val reverse_qubits' : int -> int -> base_ucom **)

let rec reverse_qubits' dim n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP __)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_SWAP 0 (sub dim (Pervasives.succ 0)))
      (fun _ -> Coq_useq ((reverse_qubits' dim n'),
      (coq_SWAP n' (sub (sub dim n') (Pervasives.succ 0)))))
      n')
    n

(** val reverse_qubits : int -> base_ucom **)

let reverse_qubits n =
  reverse_qubits' n (PeanoNat.Nat.div n (Pervasives.succ (Pervasives.succ 0)))

(** val coq_QFT_w_reverse : int -> base_Unitary ucom **)

let coq_QFT_w_reverse n =
  Coq_useq ((coq_QFT n), (reverse_qubits n))

(** val controlled_powers_var' :
    int -> (int -> base_ucom) -> int -> int -> base_ucom **)

let rec controlled_powers_var' n f k kmax =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP __)
    (fun k' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      cast n (control n (sub kmax (Pervasives.succ 0)) (f 0)) (add kmax n))
      (fun _ -> Coq_useq ((controlled_powers_var' n f k' kmax),
      (cast n (control n (sub (sub kmax k') (Pervasives.succ 0)) (f k'))
        (add kmax n))))
      k')
    k

(** val controlled_powers_var :
    int -> (int -> base_ucom) -> int -> base_ucom **)

let controlled_powers_var n f k =
  controlled_powers_var' n f k k

(** val coq_QPE_var : int -> int -> (int -> base_ucom) -> base_ucom **)

let coq_QPE_var k n f =
  Coq_useq ((Coq_useq ((cast k (npar k coq_U_H) (add k n)),
    (controlled_powers_var n (fun x -> map_qubits n (fun q -> add k q) (f x))
      k))), (cast k (invert k (coq_QFT_w_reverse k)) (add k n)))
