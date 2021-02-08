open BinNums
open Rdefinitions
open Rtrigo1

type __ = Obj.t

type 'u ucom =
| Coq_useq of 'u ucom * 'u ucom
| Coq_uapp1 of 'u * int
| Coq_uapp2 of 'u * int * int
| Coq_uapp3 of 'u * int * int * int

type base_Unitary =
| U_R of coq_R * coq_R * coq_R
| U_CNOT

type base_ucom = base_Unitary ucom

(** val coq_U_H : base_Unitary **)

let coq_U_H =
  U_R ((coq_Rdiv coq_PI (coq_IZR (Zpos (Coq_xO Coq_xH)))), (coq_IZR Z0),
    coq_PI)

(** val coq_U_X : base_Unitary **)

let coq_U_X =
  U_R (coq_PI, (coq_IZR Z0), coq_PI)

(** val coq_H : int -> base_ucom **)

let coq_H n =
  Coq_uapp1 (coq_U_H, n)

(** val coq_X : int -> base_ucom **)

let coq_X n =
  Coq_uapp1 (coq_U_X, n)

(** val coq_ID : int -> base_ucom **)

let coq_ID n =
  Coq_uapp1 ((U_R ((coq_IZR Z0), (coq_IZR Z0), (coq_IZR Z0))), n)

(** val coq_SKIP : __ -> base_ucom **)

let coq_SKIP _ =
  coq_ID 0

(** val coq_Rz : coq_R -> int -> base_ucom **)

let coq_Rz _UU03bb_ n =
  Coq_uapp1 ((U_R ((coq_IZR Z0), (coq_IZR Z0), _UU03bb_)), n)

(** val coq_T : int -> base_ucom **)

let coq_T n =
  coq_Rz (coq_Rdiv coq_PI (coq_IZR (Zpos (Coq_xO (Coq_xO Coq_xH))))) n

(** val coq_TDAG : int -> base_ucom **)

let coq_TDAG n =
  coq_Rz
    (coq_Ropp (coq_Rdiv coq_PI (coq_IZR (Zpos (Coq_xO (Coq_xO Coq_xH)))))) n

(** val coq_CNOT : int -> int -> base_ucom **)

let coq_CNOT m n =
  Coq_uapp2 (U_CNOT, m, n)

(** val coq_SWAP : int -> int -> base_ucom **)

let coq_SWAP m n =
  Coq_useq ((Coq_useq ((coq_CNOT m n), (coq_CNOT n m))), (coq_CNOT m n))
