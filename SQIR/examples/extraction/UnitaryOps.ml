open BinNums
open Rdefinitions
open SQIR

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val invert : int -> base_ucom -> base_ucom **)

let rec invert dim = function
| Coq_useq (c1, c2) -> Coq_useq ((invert dim c2), (invert dim c1))
| Coq_uapp1 (b, n) ->
  (match b with
   | U_R (_UU03b8_, _UU03d5_, _UU03bb_) ->
     Coq_uapp1 ((U_R ((coq_Ropp _UU03b8_), (coq_Ropp _UU03bb_),
       (coq_Ropp _UU03d5_))), n)
   | U_CNOT -> coq_SKIP __)
| Coq_uapp2 (b, m, n) ->
  (match b with
   | U_R (_, _, _) -> coq_SKIP __
   | U_CNOT -> Coq_uapp2 (U_CNOT, m, n))
| Coq_uapp3 (_, _, _, _) -> coq_SKIP __

(** val coq_CU : int -> coq_R -> coq_R -> coq_R -> int -> int -> base_ucom **)

let coq_CU _ _UU03b8_ _UU03d5_ _UU03bb_ c t =
  Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((coq_Rz
       (coq_Rdiv (coq_Rplus _UU03bb_ _UU03d5_)
         (coq_IZR (Zpos (Coq_xO Coq_xH)))) c),
    (coq_Rz
      (coq_Rdiv (coq_Rminus _UU03bb_ _UU03d5_)
        (coq_IZR (Zpos (Coq_xO Coq_xH)))) t))), (coq_CNOT c t))), (Coq_uapp1
    ((U_R ((coq_Rdiv (coq_Ropp _UU03b8_) (coq_IZR (Zpos (Coq_xO Coq_xH)))),
    (coq_IZR Z0),
    (coq_Rdiv (coq_Ropp (coq_Rplus _UU03d5_ _UU03bb_))
      (coq_IZR (Zpos (Coq_xO Coq_xH)))))), t)))), (coq_CNOT c t))),
    (Coq_uapp1 ((U_R ((coq_Rdiv _UU03b8_ (coq_IZR (Zpos (Coq_xO Coq_xH)))),
    _UU03d5_, (coq_IZR Z0))), t)))

(** val coq_CCX : int -> int -> int -> int -> base_ucom **)

let coq_CCX _ a b c =
  Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((Coq_useq ((coq_H c), (coq_CNOT b c))), (coq_TDAG c))),
    (coq_CNOT a c))), (coq_T c))), (coq_CNOT b c))), (coq_TDAG c))),
    (coq_CNOT a c))), (coq_CNOT a b))), (coq_TDAG b))), (coq_CNOT a b))),
    (coq_T a))), (coq_T b))), (coq_T c))), (coq_H c))

(** val control : int -> int -> base_ucom -> base_ucom **)

let rec control dim q = function
| Coq_useq (c1, c2) -> Coq_useq ((control dim q c1), (control dim q c2))
| Coq_uapp1 (b, n) ->
  (match b with
   | U_R (_UU03b8_, _UU03d5_, _UU03bb_) ->
     coq_CU dim _UU03b8_ _UU03d5_ _UU03bb_ q n
   | U_CNOT -> coq_SKIP __)
| Coq_uapp2 (b, m, n) ->
  (match b with
   | U_R (_, _, _) -> coq_SKIP __
   | U_CNOT -> coq_CCX dim q m n)
| Coq_uapp3 (_, _, _, _) -> coq_SKIP __

(** val map_qubits : int -> (int -> int) -> 'a1 ucom -> 'a1 ucom **)

let rec map_qubits dim f = function
| Coq_useq (c1, c2) -> Coq_useq ((map_qubits dim f c1), (map_qubits dim f c2))
| Coq_uapp1 (u, n) -> Coq_uapp1 (u, (f n))
| Coq_uapp2 (u, m, n) -> Coq_uapp2 (u, (f m), (f n))
| Coq_uapp3 (u, m, n, p) -> Coq_uapp3 (u, (f m), (f n), (f p))

(** val cast : int -> 'a1 ucom -> int -> 'a1 ucom **)

let rec cast dim c dim' =
  match c with
  | Coq_useq (c1, c2) -> Coq_useq ((cast dim c1 dim'), (cast dim c2 dim'))
  | x -> x

(** val npar' : int -> int -> base_Unitary -> base_ucom **)

let rec npar' dim n u =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP __)
    (fun n' -> Coq_useq ((npar' dim n' u), (Coq_uapp1 (u, n'))))
    n

(** val npar : int -> base_Unitary -> base_ucom **)

let npar n u =
  npar' n n u
