
type comparison =
| Eq
| Lt
| Gt

type coq_CompareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val coq_CompareSpec2Type : comparison -> coq_CompareSpecT **)

let coq_CompareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a coq_CompSpecT = coq_CompareSpecT

(** val coq_CompSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 coq_CompSpecT **)

let coq_CompSpec2Type _ _ =
  coq_CompareSpec2Type
