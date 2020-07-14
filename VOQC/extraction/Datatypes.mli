type comparison = Eq | Lt | Gt
val coq_CompOpp : comparison -> comparison
type coq_CompareSpecT = CompEqT | CompLtT | CompGtT
val coq_CompareSpec2Type : comparison -> coq_CompareSpecT
type 'a coq_CompSpecT = coq_CompareSpecT
val coq_CompSpec2Type : 'a -> 'b -> comparison -> coq_CompareSpecT
