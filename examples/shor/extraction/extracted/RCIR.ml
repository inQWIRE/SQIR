
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

(** val bcelim : bccom -> bccom **)

let rec bcelim p = match p with
| Coq_bccont (q, p0) ->
  (match bcelim p0 with
   | Coq_bcskip -> Coq_bcskip
   | x -> Coq_bccont (q, x))
| Coq_bcseq (p1, p2) ->
  (match bcelim p1 with
   | Coq_bcskip -> bcelim p2
   | x -> (match bcelim p2 with
           | Coq_bcskip -> x
           | x0 -> Coq_bcseq (x, x0)))
| _ -> p

(** val bcinv : bccom -> bccom **)

let rec bcinv p = match p with
| Coq_bccont (n, p0) -> Coq_bccont (n, (bcinv p0))
| Coq_bcseq (p1, p2) -> Coq_bcseq ((bcinv p2), (bcinv p1))
| _ -> p
