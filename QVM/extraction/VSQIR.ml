open BinNat
open BinNums

type var = int

type posi = var * int

type exp =
| SKIP of posi
| X of posi
| CU of posi * exp
| RZ of int * posi
| RRZ of int * posi
| SR of int * var
| SRR of int * var
| HCNOT of posi * posi
| Lshift of var
| Rshift of var
| Rev of var
| Seq of exp * exp

type pexp =
| Exp of exp
| QFT of var
| RQFT of var
| H of var
| PCU of posi * pexp
| PSeq of pexp * pexp

(** val inv_exp : exp -> exp **)

let rec inv_exp = function
| CU (n, p0) -> CU (n, (inv_exp p0))
| RZ (q, p1) -> RRZ (q, p1)
| RRZ (q, p1) -> RZ (q, p1)
| SR (n, x) -> SRR (n, x)
| SRR (n, x) -> SR (n, x)
| Lshift x -> Rshift x
| Rshift x -> Lshift x
| Seq (p1, p2) -> Seq ((inv_exp p2), (inv_exp p1))
| x -> x

(** val inv_pexp : pexp -> pexp **)

let rec inv_pexp = function
| Exp s -> Exp (inv_exp s)
| QFT x -> RQFT x
| RQFT x -> QFT x
| H x -> H x
| PCU (n, p0) -> PCU (n, (inv_pexp p0))
| PSeq (p1, p2) -> PSeq ((inv_pexp p2), (inv_pexp p1))

(** val allfalse : int -> bool **)

let allfalse _ =
  false

(** val fb_push : bool -> (int -> bool) -> int -> bool **)

let fb_push b f x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> b)
    (fun n -> f n)
    x

(** val pos2fb : positive -> int -> bool **)

let rec pos2fb = function
| Coq_xI p' -> fb_push true (pos2fb p')
| Coq_xO p' -> fb_push false (pos2fb p')
| Coq_xH -> fb_push true allfalse

(** val coq_N2fb : coq_N -> int -> bool **)

let coq_N2fb = function
| N0 -> allfalse
| Npos p -> pos2fb p

(** val nat2fb : int -> int -> bool **)

let nat2fb n =
  coq_N2fb (N.of_nat n)

(** val coq_CNOT : posi -> posi -> exp **)

let coq_CNOT x y =
  CU (x, (X y))
