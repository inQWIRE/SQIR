open PQASM
open QIMP

(** val g : var **)

let g =
  Pervasives.succ 0

(** val x : var **)

let x =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))

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
    (Q, FixedP)), re) :: [])))))))))), (Coq_ncadd ((Nor (Var (L n))), (Nor
    (Num (nat2fb (Pervasives.succ 0)))), (Nor (Var (L n)))))), (Nor (Var (L
    re))))

(** val sin_prog : int -> prog **)

let sin_prog size =
  ((((size, (((TNor (Q, FixedP)), x) :: (((TNor (Q, FixedP)),
    result) :: []))), (taylor_sin :: [])), f), result)
