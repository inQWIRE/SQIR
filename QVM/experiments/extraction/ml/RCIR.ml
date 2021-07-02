
type bccom =
| Coq_bcskip
| Coq_bcx of int
| Coq_bcswap of int * int
| Coq_bccont of int * bccom
| Coq_bcseq of bccom * bccom

(** val bccnot : int -> int -> bccom **)

let bccnot x y =
  Coq_bccont (x, (Coq_bcx y))

(** val bcccnot : int -> int -> int -> bccom **)

let bcccnot x y z =
  Coq_bccont (x, (bccnot y z))

(** val bcinv : bccom -> bccom **)

let rec bcinv p = match p with
| Coq_bccont (n, p0) -> Coq_bccont (n, (bcinv p0))
| Coq_bcseq (p1, p2) -> Coq_bcseq ((bcinv p2), (bcinv p1))
| _ -> p

(** val bygatectrl : int -> bccom -> bccom **)

let rec bygatectrl n c = match c with
| Coq_bcseq (c1, c2) -> Coq_bcseq ((bygatectrl n c1), (bygatectrl n c2))
| _ -> Coq_bccont (n, c)
