open Nat
open VSQIR

(** val rz_adder' : var -> int -> int -> (int -> bool) -> exp **)

let rec rz_adder' x n size m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m0 -> Seq ((rz_adder' x m0 size m),
    (if m m0 then SR ((sub size n), x) else SKIP (x, m0))))
    n

(** val rz_adder : var -> int -> (int -> bool) -> exp **)

let rz_adder x n m =
  rz_adder' x n n m

(** val rz_sub' : var -> int -> int -> (int -> bool) -> exp **)

let rec rz_sub' x n size m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m0 -> Seq ((rz_sub' x m0 size m),
    (if m m0 then SRR ((sub size n), x) else SKIP (x, m0))))
    n

(** val rz_sub : var -> int -> (int -> bool) -> exp **)

let rz_sub x n m =
  rz_sub' x n n m

(** val qft_cu : var -> posi -> pexp **)

let qft_cu x c =
  PSeq ((PSeq ((RQFT x), (Exp (coq_CNOT (x, 0) c)))), (QFT x))

(** val qft_acu : var -> posi -> pexp **)

let qft_acu x c =
  PSeq ((PSeq ((RQFT x), (Exp (Seq ((Seq ((X (x, 0)), (coq_CNOT (x, 0) c))),
    (X (x, 0))))))), (QFT x))

(** val one_cu_adder : var -> int -> posi -> (int -> bool) -> exp **)

let one_cu_adder x n c m =
  CU (c, (rz_adder x n m))

(** val mod_adder_half :
    var -> int -> posi -> (int -> bool) -> (int -> bool) -> pexp **)

let mod_adder_half x n c a m =
  PSeq ((PSeq ((Exp (Seq ((rz_adder x n a), (rz_sub x n m)))),
    (qft_cu x c))), (Exp (one_cu_adder x n c m)))

(** val clean_hbit : var -> int -> posi -> (int -> bool) -> pexp **)

let clean_hbit x n c m =
  PSeq ((PSeq ((Exp (rz_sub x n m)), (qft_acu x c))), (Exp
    (inv_exp (rz_sub x n m))))

(** val mod_adder :
    var -> int -> posi -> (int -> bool) -> (int -> bool) -> pexp **)

let mod_adder x n c a m =
  PSeq ((mod_adder_half x n c a m), (clean_hbit x n c a))

(** val rz_modmult' :
    var -> var -> int -> int -> posi -> int -> int -> pexp **)

let rec rz_modmult' y x n size c a m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Exp (SKIP (y, 0)))
    (fun m0 -> PSeq ((rz_modmult' y x m0 size c a m), (PCU ((x,
    (sub size n)),
    (mod_adder y size c
      (nat2fb
        (PeanoNat.Nat.modulo
          (mul (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) m0) a)
          m)) (nat2fb m))))))
    n

(** val rz_modmult_half : var -> var -> int -> posi -> int -> int -> pexp **)

let rz_modmult_half y x size c a m =
  PSeq ((PSeq ((QFT y), (rz_modmult' y x size size c a m))), (RQFT y))

(** val rz_modmult_full :
    var -> var -> int -> posi -> int -> int -> int -> pexp **)

let rz_modmult_full y x n c a ainv n0 =
  PSeq ((rz_modmult_half y x n c a n0),
    (inv_pexp (rz_modmult_half x y n c ainv n0)))
