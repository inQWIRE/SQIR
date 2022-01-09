open BinNums
open SQIR

(** val coq_CU :
    int -> float -> float -> float -> int -> int -> base_ucom **)

let coq_CU dim _UU03b8_ _UU03d5_ _UU03bb_ c t =
  Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((coq_Rz dim
       (( /. ) (( +. ) _UU03bb_ _UU03d5_)
         (Float.of_int (Zpos (Coq_xO Coq_xH)))) c),
    (coq_Rz dim
      (( /. ) (( -. ) _UU03bb_ _UU03d5_)
        (Float.of_int (Zpos (Coq_xO Coq_xH)))) t))), (coq_CNOT dim c t))),
    (Coq_uapp1 ((U_R
    ((( /. ) (((-.) 0.0) _UU03b8_) (Float.of_int (Zpos (Coq_xO Coq_xH)))),
    (Float.of_int Z0),
    (( /. ) (((-.) 0.0) (( +. ) _UU03d5_ _UU03bb_))
      (Float.of_int (Zpos (Coq_xO Coq_xH)))))), t)))), (coq_CNOT dim c t))),
    (Coq_uapp1 ((U_R
    ((( /. ) _UU03b8_ (Float.of_int (Zpos (Coq_xO Coq_xH)))), _UU03d5_,
    (Float.of_int Z0))), t)))

(** val control : int -> int -> base_ucom -> base_ucom **)

let rec control dim q = function
| Coq_useq (c1, c2) -> Coq_useq ((control dim q c1), (control dim q c2))
| Coq_uapp1 (b, n) ->
  (match b with
   | U_R (_UU03b8_, _UU03d5_, _UU03bb_) ->
     coq_CU dim _UU03b8_ _UU03d5_ _UU03bb_ q n
   | U_CNOT -> coq_SKIP dim)
| Coq_uapp2 (b, m, n) ->
  (match b with
   | U_R (_, _, _) -> coq_SKIP dim
   | U_CNOT -> coq_CCX dim q m n)
| Coq_uapp3 (_, _, _, _) -> coq_SKIP dim
