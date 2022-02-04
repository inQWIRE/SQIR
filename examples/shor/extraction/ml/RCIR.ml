
type bccom =
| Coq_bcskip
| Coq_bcx of Z.t
| Coq_bcswap of Z.t * Z.t
| Coq_bccont of Z.t * bccom
| Coq_bcseq of bccom * bccom

(** val bccnot : Z.t -> Z.t -> bccom **)

let bccnot x y =
  Coq_bccont (x, (Coq_bcx y))

(** val bcccnot : Z.t -> Z.t -> Z.t -> bccom **)

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

(** val bygatectrl : Z.t -> bccom -> bccom **)

let rec bygatectrl n c = match c with
| Coq_bcseq (c1, c2) -> Coq_bcseq ((bygatectrl n c1), (bygatectrl n c2))
| _ -> Coq_bccont (n, c)

(** val map_bccom : (Z.t -> Z.t) -> bccom -> bccom **)

let rec map_bccom f = function
| Coq_bcskip -> Coq_bcskip
| Coq_bcx a -> Coq_bcx (f a)
| Coq_bcswap (a, b) -> Coq_bcswap ((f a), (f b))
| Coq_bccont (a, bc1) -> Coq_bccont ((f a), (map_bccom f bc1))
| Coq_bcseq (bc1, bc2) -> Coq_bcseq ((map_bccom f bc1), (map_bccom f bc2))
