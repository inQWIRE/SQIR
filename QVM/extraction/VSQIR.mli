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

val inv_exp : exp -> exp

val inv_pexp : pexp -> pexp

val allfalse : int -> bool

val fb_push : bool -> (int -> bool) -> int -> bool

val pos2fb : positive -> int -> bool

val coq_N2fb : coq_N -> int -> bool

val nat2fb : int -> int -> bool

val coq_CNOT : posi -> posi -> exp
