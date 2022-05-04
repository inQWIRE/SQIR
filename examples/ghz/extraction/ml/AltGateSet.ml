
type 'u ucom =
| Coq_useq of 'u ucom * 'u ucom
| Coq_uapp of int * 'u * int list

type coq_U =
| U_X
| U_H
| U_U1 of float
| U_U2 of float * float
| U_U3 of float * float * float
| U_CX
| U_CU1 of float
| U_SWAP
| U_CCX
| U_CSWAP
| U_C3X
| U_C4X

(** val coq_H : int -> coq_U ucom **)

let coq_H q =
  Coq_uapp ((Pervasives.succ 0), U_H, (q :: []))

(** val coq_U1 : float -> int -> coq_U ucom **)

let coq_U1 r1 q =
  Coq_uapp ((Pervasives.succ 0), (U_U1 r1), (q :: []))

(** val coq_ID : int -> coq_U ucom **)

let coq_ID q =
  coq_U1 0.0 q

(** val coq_SKIP : coq_U ucom **)

let coq_SKIP =
  coq_ID 0

(** val coq_CX : int -> int -> coq_U ucom **)

let coq_CX q1 q2 =
  Coq_uapp ((Pervasives.succ (Pervasives.succ 0)), U_CX, (q1 :: (q2 :: [])))
