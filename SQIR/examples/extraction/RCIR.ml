open SQIR
open UnitaryOps

let __ = let rec f _ = Obj.repr f in Obj.repr f

type bccom =
| Coq_bcskip
| Coq_bcx of int
| Coq_bccont of int * bccom
| Coq_bcseq of bccom * bccom

(** val bccnot : int -> int -> bccom **)

let bccnot x y =
  Coq_bccont (x, (Coq_bcx y))

(** val bcswap : int -> int -> bccom **)

let bcswap x y =
  if (=) x y
  then Coq_bcskip
  else Coq_bcseq ((Coq_bcseq ((bccnot x y), (bccnot y x))), (bccnot x y))

(** val bcccnot : int -> int -> int -> bccom **)

let bcccnot x y z =
  Coq_bccont (x, (bccnot y z))

(** val bc2ucom : int -> bccom -> base_ucom **)

let rec bc2ucom dim = function
| Coq_bcskip -> coq_SKIP __
| Coq_bcx n -> coq_X n
| Coq_bccont (n, p0) -> control dim n (bc2ucom dim p0)
| Coq_bcseq (p1, p2) -> Coq_useq ((bc2ucom dim p1), (bc2ucom dim p2))

(** val bcelim : bccom -> bccom **)

let rec bcelim = function
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
| x -> x

(** val bcinv : bccom -> bccom **)

let rec bcinv = function
| Coq_bccont (n, p0) -> Coq_bccont (n, (bcinv p0))
| Coq_bcseq (p1, p2) -> Coq_bcseq ((bcinv p2), (bcinv p1))
| x -> x
