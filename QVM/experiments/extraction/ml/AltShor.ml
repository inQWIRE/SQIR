open AltGateSet
open RCIR

(** val bc2ucom : bccom -> coq_U ucom **)

let rec bc2ucom = function
| Coq_bcskip -> coq_SKIP
| Coq_bcx a -> coq_X a
| Coq_bcswap (a, b) -> coq_SWAP a b
| Coq_bccont (a, bc1) -> control a (bc2ucom bc1)
| Coq_bcseq (bc1, bc2) -> Coq_useq ((bc2ucom bc1), (bc2ucom bc2))
