open BinNums

type 'u ucom =
| Coq_useq of 'u ucom * 'u ucom
| Coq_uapp1 of 'u * int
| Coq_uapp2 of 'u * int * int
| Coq_uapp3 of 'u * int * int * int

type base_Unitary =
| U_R of float * float * float
| U_CNOT

type base_ucom = base_Unitary ucom

(** val coq_U_H : base_Unitary **)

let coq_U_H =
  U_R ((( /. ) Float.pi (Float.of_int (Zpos (Coq_xO Coq_xH)))),
    (Float.of_int Z0), Float.pi)

(** val coq_U_X : base_Unitary **)

let coq_U_X =
  U_R (Float.pi, (Float.of_int Z0), Float.pi)

(** val coq_H : int -> int -> base_ucom **)

let coq_H _ n =
  Coq_uapp1 (coq_U_H, n)

(** val coq_X : int -> int -> base_ucom **)

let coq_X _ n =
  Coq_uapp1 (coq_U_X, n)

(** val coq_ID : int -> int -> base_ucom **)

let coq_ID _ n =
  Coq_uapp1 ((U_R ((Float.of_int Z0), (Float.of_int Z0), (Float.of_int Z0))),
    n)

(** val coq_SKIP : int -> base_ucom **)

let coq_SKIP dim =
  coq_ID dim 0

(** val coq_Rz : int -> float -> int -> base_ucom **)

let coq_Rz _ _UU03bb_ n =
  Coq_uapp1 ((U_R ((Float.of_int Z0), (Float.of_int Z0), _UU03bb_)), n)

(** val coq_T : int -> int -> base_ucom **)

let coq_T dim n =
  coq_Rz dim (( /. ) Float.pi (Float.of_int (Zpos (Coq_xO (Coq_xO Coq_xH)))))
    n

(** val coq_TDAG : int -> int -> base_ucom **)

let coq_TDAG dim n =
  coq_Rz dim
    (((-.) 0.0)
      (( /. ) Float.pi (Float.of_int (Zpos (Coq_xO (Coq_xO Coq_xH)))))) n

(** val coq_CNOT : int -> int -> int -> base_ucom **)

let coq_CNOT _ m n =
  Coq_uapp2 (U_CNOT, m, n)

(** val coq_SWAP : int -> int -> int -> base_ucom **)

let coq_SWAP dim m n =
  Coq_useq ((Coq_useq ((coq_CNOT dim m n), (coq_CNOT dim n m))),
    (coq_CNOT dim m n))

(** val coq_U1 : int -> float -> int -> base_ucom **)

let coq_U1 _ a n =
  Coq_uapp1 ((U_R ((Float.of_int Z0), (Float.of_int Z0), a)), n)

(** val coq_U2 : int -> float -> float -> int -> base_ucom **)

let coq_U2 _ a b n =
  Coq_uapp1 ((U_R ((( /. ) Float.pi (Float.of_int (Zpos (Coq_xO Coq_xH)))),
    a, b)), n)

(** val coq_U3 : int -> float -> float -> float -> int -> base_ucom **)

let coq_U3 _ a b c n =
  Coq_uapp1 ((U_R (a, b, c)), n)

(** val coq_CCX : int -> int -> int -> int -> base_ucom **)

let coq_CCX dim a b c =
  Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((Coq_useq ((coq_H dim c), (coq_CNOT dim b c))), (coq_TDAG dim c))),
    (coq_CNOT dim a c))), (coq_T dim c))), (coq_CNOT dim b c))),
    (coq_TDAG dim c))), (coq_CNOT dim a c))), (coq_CNOT dim a b))),
    (coq_TDAG dim b))), (coq_CNOT dim a b))), (coq_T dim a))),
    (coq_T dim b))), (coq_T dim c))), (coq_H dim c))
