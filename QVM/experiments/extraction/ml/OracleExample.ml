open PQASM
open QIMP

(** val hash_qr : qvar -> qvar -> qexp **)

let hash_qr b0 a0 =
  Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_nadd ((Nor (Var b0)), (Nor (Var
    a0)))), (Coq_qxor ((Nor (Var a0)), (Nor (Var b0)))))), (Coq_nadd ((Nor
    (Var b0)), (Nor (Var a0)))))), (Coq_qxor ((Nor (Var a0)), (Nor (Var
    b0)))))

(** val g : var **)

let g =
  Pervasives.succ 0

(** val x : var **)

let x =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))

(** val a : var **)

let a =
  Pervasives.succ (Pervasives.succ (Pervasives.succ 0))

(** val b : var **)

let b =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))

(** val c : var **)

let c =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))

(** val d : var **)

let d =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val f : var **)

let f =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))

(** val result : var **)

let result =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))

(** val hash_oracle : int -> int -> func **)

let hash_oracle key sndk =
  (((f, (((TNor (Q, Bl)), g) :: (((TNor (C, Nat)), x) :: (((TNor (Q, Nat)),
    a) :: (((TNor (Q, Nat)), b) :: (((TNor (Q, Nat)), c) :: (((TNor (Q,
    Nat)), d) :: []))))))), (Coq_qseq ((Coq_init ((Nor (Var (L d))), (Nor
    (Num (nat2fb (Pervasives.succ 0)))))), (Coq_qfor (x, (Nor (Num
    (nat2fb (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))),
    (Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq ((hash_qr (L a) (L c)),
    (hash_qr (L b) (L d)))), (hash_qr (L a) (L d)))),
    (hash_qr (L b) (L c)))), (Coq_qif ((Coq_ceq (Nat, (Nor (Var (L c))), (Nor
    (Num (nat2fb key))))), (Coq_qif ((Coq_ceq (Nat, (Nor (Var (L d))), (Nor
    (Num (nat2fb sndk))))), (Coq_init ((Nor (Var (L g))), (Nor (Num
    (nat2fb (Pervasives.succ 0)))))), Coq_skip)), Coq_skip))))))))), (Nor
    (Var (L g))))

(** val hash_prog : int -> int -> int -> prog **)

let hash_prog size key sndk =
  ((((size, (((TNor (Q, Bl)), result) :: [])),
    ((hash_oracle key sndk) :: [])), f), result)

(** val x2 : int **)

let x2 =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))

(** val x3 : int **)

let x3 =
  0

(** val n : var **)

let n =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))

(** val e : var **)

let e =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))

(** val rc : var **)

let rc =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))

(** val re : var **)

let re =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))))))

(** val fac : var **)

let fac =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))

(** val xc : var **)

let xc =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))

(** val taylor_sin : func **)

let taylor_sin =
  (((f, (((TArray (Q, FixedP, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
    x3) :: (((TNor (Q, FixedP)), x2) :: (((TNor (Q, FixedP)), e) :: (((TNor
    (C, Nat)), g) :: (((TNor (C, Nat)), n) :: (((TNor (C, Nat)),
    xc) :: (((TNor (C, Nat)), fac) :: (((TNor (C, FixedP)), rc) :: (((TNor
    (Q, FixedP)), re) :: [])))))))))), (Coq_qseq ((Coq_qseq ((Coq_qseq
    ((Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq
    ((Coq_init ((Nor (Var (L re))), (Nor (Var (G x))))), (Coq_fmul ((Nor (Var
    (L x2))), (Nor (Var (G x))), (Nor (Var (L re))))))), (Coq_fmul ((Index
    ((L x3), (Num (nat2fb 0)))), (Nor (Var (L x2))), (Nor (Var (G x))))))),
    (Coq_fmul ((Index ((L x3), (Num (nat2fb (Pervasives.succ 0))))), (Index
    ((L x3), (Num (nat2fb 0)))), (Nor (Var (L x2))))))), (Coq_fmul ((Index
    ((L x3), (Num (nat2fb (Pervasives.succ (Pervasives.succ 0)))))), (Index
    ((L x3), (Num (nat2fb (Pervasives.succ 0))))), (Nor (Var (L x2))))))),
    (Coq_fmul ((Index ((L x3), (Num
    (nat2fb (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
    (Index ((L x3), (Num (nat2fb (Pervasives.succ (Pervasives.succ 0)))))),
    (Nor (Var (L x2))))))), (Coq_fmul ((Index ((L x3), (Num
    (nat2fb (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))))))), (Index ((L x3), (Num
    (nat2fb (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Nor
    (Var (L x2))))))), (Coq_ncadd ((Nor (Var (L n))), (Nor (Num
    (nat2fb (Pervasives.succ 0)))), (Nor (Var (L n))))))), (Coq_ncadd ((Nor
    (Var (L xc))), (Nor (Num (nat2fb (Pervasives.succ 0)))), (Nor (Var (L
    xc))))))), (Coq_qfor (g, (Nor (Num
    (nat2fb (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0)))))))), (Coq_qif ((Coq_iseven (Nor
    (Var (L g)))), (Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_qseq
    ((Coq_qseq ((Coq_ncadd ((Nor (Var (L n))), (Nor (Var (L n))), (Nor (Num
    (nat2fb (Pervasives.succ (Pervasives.succ 0))))))), (Coq_nfac ((Nor (Var
    (L fac))), (Nor (Var (L n))))))), (Coq_ncmul ((Nor (Var (L xc))), (Nor
    (Num
    (nat2fb (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))), (Nor (Var (L xc))))))), (Coq_fndiv ((Nor
    (Var (L rc))), (Nor (Var (L xc))), (Nor (Var (L fac))))))), (Coq_fmul
    ((Nor (Var (L e))), (Nor (Var (L rc))), (Index ((L x3), (Var (L
    g)))))))), (Coq_fsub ((Nor (Var (L re))), (Nor (Var (L e))))))),
    (Coq_qinv (Nor (Var (L e)))))), (Coq_qseq ((Coq_qseq ((Coq_qseq
    ((Coq_qseq ((Coq_qseq ((Coq_qseq ((Coq_ncadd ((Nor (Var (L n))), (Nor
    (Num (nat2fb (Pervasives.succ (Pervasives.succ 0))))), (Nor (Var (L
    n))))), (Coq_nfac ((Nor (Var (L fac))), (Nor (Var (L n))))))), (Coq_ncmul
    ((Nor (Var (L xc))), (Nor (Num
    (nat2fb (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))), (Nor (Var (L xc))))))), (Coq_fndiv ((Nor
    (Var (L rc))), (Nor (Var (L xc))), (Nor (Var (L fac))))))), (Coq_fmul
    ((Nor (Var (L e))), (Nor (Var (L rc))), (Index ((L x3), (Var (L
    g)))))))), (Coq_fadd ((Nor (Var (L re))), (Nor (Var (L e))))))),
    (Coq_qinv (Nor (Var (L e))))))))))))), (Nor (Var (L re))))

(** val sin_prog : int -> prog **)

let sin_prog size =
  ((((size, (((TNor (Q, FixedP)), x) :: (((TNor (Q, FixedP)),
    result) :: []))), (taylor_sin :: [])), f), result)
