open Nat
open PQASM

(** val coq_MAJ : posi -> posi -> posi -> exp **)

let coq_MAJ a b c =
  Seq ((Seq ((coq_CNOT c b), (coq_CNOT c a))), (coq_CCX a b c))

(** val coq_UMA : posi -> posi -> posi -> exp **)

let coq_UMA a b c =
  Seq ((Seq ((coq_CCX a b c), (coq_CNOT c a))), (coq_CNOT a b))

(** val coq_MAJseq' : int -> var -> var -> posi -> exp **)

let rec coq_MAJseq' n x y c =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_MAJ c (y, 0) (x, 0))
    (fun m -> Seq ((coq_MAJseq' m x y c), (coq_MAJ (x, m) (y, n) (x, n))))
    n

(** val coq_MAJseq : int -> var -> var -> posi -> exp **)

let coq_MAJseq n x y c =
  coq_MAJseq' (sub n (Pervasives.succ 0)) x y c

(** val coq_UMAseq' : int -> var -> var -> posi -> exp **)

let rec coq_UMAseq' n x y c =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_UMA c (y, 0) (x, 0))
    (fun m -> Seq ((coq_UMA (x, m) (y, n) (x, n)), (coq_UMAseq' m x y c)))
    n

(** val coq_UMAseq : int -> var -> var -> posi -> exp **)

let coq_UMAseq n x y c =
  coq_UMAseq' (sub n (Pervasives.succ 0)) x y c

(** val adder01 : int -> var -> var -> posi -> exp **)

let adder01 n x y c =
  Seq ((coq_MAJseq n x y c), (coq_UMAseq n x y c))

(** val highbit : int -> var -> posi -> exp **)

let highbit n x c2 =
  Seq ((Seq ((Seq ((Seq ((X (x, (sub n (Pervasives.succ 0)))), (X c2))),
    (coq_CNOT (x, (sub n (Pervasives.succ 0))) c2))), (X c2))), (X (x,
    (sub n (Pervasives.succ 0)))))

(** val highb01 : int -> var -> var -> posi -> posi -> exp **)

let highb01 n x y c1 c2 =
  Seq ((Seq ((coq_MAJseq n x y c1), (highbit n x c2))),
    (inv_exp (coq_MAJseq n x y c1)))

(** val negator0 : int -> var -> exp **)

let rec negator0 i x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun i' -> Seq ((negator0 i' x), (X (x, i'))))
    i

(** val comparator01 : int -> var -> var -> posi -> posi -> exp **)

let comparator01 n x y c1 c2 =
  Seq ((Seq ((Seq ((X c1), (negator0 n x))), (highb01 n x y c1 c2))),
    (inv_exp (Seq ((X c1), (negator0 n x)))))

(** val subtractor01 : int -> var -> var -> posi -> exp **)

let subtractor01 n x y c1 =
  Seq ((Seq ((Seq ((X c1), (negator0 n x))), (adder01 n x y c1))),
    (inv_exp (Seq ((X c1), (negator0 n x)))))

(** val modadder21 : int -> var -> var -> var -> posi -> posi -> exp **)

let modadder21 n x y m c1 c2 =
  Seq ((Seq ((Seq ((Seq ((adder01 n y x c1), (comparator01 n m x c1 c2))), (X
    c2))), (CU (c2, (subtractor01 n m x c1))))),
    (inv_exp (comparator01 n y x c1 c2)))

(** val doubler1 : var -> exp **)

let doubler1 y =
  Rshift y

(** val moddoubler01 : int -> var -> var -> posi -> posi -> exp **)

let moddoubler01 n x m c1 c2 =
  Seq ((doubler1 x), (Seq ((comparator01 n x m c1 c2), (CU (c2,
    (subtractor01 n m x c1))))))

(** val modsummer' :
    int -> int -> var -> var -> var -> posi -> posi -> var -> (int -> bool)
    -> exp **)

let rec modsummer' i n m x y c1 c2 s fC =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> if fC 0 then adder01 n x y c1 else SKIP (x, 0))
    (fun i' -> Seq ((Seq ((Seq ((modsummer' i' n m x y c1 c2 s fC),
    (moddoubler01 n x m c1 c2))), (coq_SWAP c2 (s, i)))),
    (if fC i then modadder21 n y x m c1 c2 else SKIP (x, i))))
    i

(** val modsummer :
    int -> var -> var -> var -> posi -> posi -> var -> int -> exp **)

let modsummer n m x y c1 c2 s c =
  modsummer' (sub n (Pervasives.succ 0)) n m x y c1 c2 s (nat2fb c)

(** val modmult_half :
    int -> var -> var -> var -> posi -> posi -> var -> int -> exp **)

let modmult_half n m x y c1 c2 s c =
  Seq ((modsummer n m x y c1 c2 s c), (inv_exp (modsummer n m x y c1 c2 s 0)))

(** val modmult_full :
    int -> int -> int -> var -> var -> var -> posi -> posi -> var -> exp **)

let modmult_full c cinv n m x y c1 c2 s =
  Seq ((modmult_half n m x y c1 c2 s c),
    (inv_exp (modmult_half n m x y c1 c2 s cinv)))

(** val modmult :
    (int -> bool) -> int -> int -> int -> var -> var -> var -> var -> posi ->
    posi -> exp **)

let modmult m c cinv n x y z s c1 c2 =
  Seq ((Seq ((init_v n z m), (modmult_full c cinv n z x y c1 c2 s))),
    (inv_exp (init_v n z m)))

(** val modmult_rev :
    (int -> bool) -> int -> int -> int -> var -> var -> var -> var -> posi ->
    posi -> pexp **)

let modmult_rev m c cinv n x y z s c1 c2 =
  PSeq ((PSeq ((Exp (Rev x)), (Exp (modmult m c cinv n x y z s c1 c2)))),
    (Exp (Rev x)))

(** val x_var : int **)

let x_var =
  0

(** val y_var : int **)

let y_var =
  Pervasives.succ 0

(** val z_var : int **)

let z_var =
  Pervasives.succ (Pervasives.succ 0)

(** val s_var : int **)

let s_var =
  Pervasives.succ (Pervasives.succ (Pervasives.succ 0))

(** val c_var : int **)

let c_var =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))

(** val vars_for_cl' :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_cl' size =
  gen_vars size (x_var :: (y_var :: (z_var :: (s_var :: []))))

(** val vars_for_cl :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_cl size x =
  if (=) x c_var
  then ((((mul size (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0))))), (Pervasives.succ (Pervasives.succ 0))),
         id_nat), id_nat)
  else vars_for_cl' size x

(** val real_modmult_rev : int -> int -> int -> int -> pexp **)

let real_modmult_rev m c cinv size =
  modmult_rev (nat2fb m) c cinv size x_var y_var z_var s_var (c_var, 0)
    (c_var, (Pervasives.succ 0))

(** val vars_for_adder01' :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_adder01' size =
  gen_vars size (x_var :: (y_var :: []))

(** val vars_for_adder01 :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_adder01 size x =
  if (=) x z_var
  then ((((mul size (Pervasives.succ (Pervasives.succ 0))), (Pervasives.succ
         0)), id_nat), id_nat)
  else vars_for_adder01' size x

(** val adder01_out : int -> exp **)

let adder01_out size =
  adder01 size x_var y_var (z_var, 0)

(** val one_cl_cu_adder :
    posi -> var -> var -> int -> posi -> (int -> bool) -> exp **)

let one_cl_cu_adder c2 ex re n c1 m =
  CU (c2, (Seq ((Seq ((init_v n ex m), (adder01 n ex re c1))),
    (init_v n ex m))))

(** val cl_nat_mult' :
    int -> int -> var -> var -> var -> posi -> (int -> bool) -> exp **)

let rec cl_nat_mult' n size x ex re c m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m0 -> Seq ((one_cl_cu_adder (x, m0) ex re size c m),
    (cl_nat_mult' m0 size x ex re c (cut_n (times_two_spec m) size))))
    n

(** val cl_nat_mult :
    int -> var -> var -> var -> posi -> (int -> bool) -> exp **)

let cl_nat_mult size x re ex c m =
  cl_nat_mult' size size x ex re c m

(** val vars_for_cl_nat_m' :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_cl_nat_m' size =
  gen_vars size (x_var :: (y_var :: (z_var :: [])))

(** val vars_for_cl_nat_m :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_cl_nat_m size x =
  if (=) x s_var
  then ((((mul size (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))),
         (Pervasives.succ 0)), id_nat), id_nat)
  else vars_for_cl_nat_m' size x

(** val cl_nat_mult_out : int -> (int -> bool) -> exp **)

let cl_nat_mult_out size m =
  cl_nat_mult size x_var y_var z_var (s_var, 0) m

(** val one_cu_cl_full_adder : posi -> var -> var -> posi -> int -> exp **)

let one_cu_cl_full_adder c2 y x c1 n =
  CU (c2, (adder01 n x y c1))

(** val cl_full_mult' :
    int -> int -> var -> var -> var -> var -> posi -> exp **)

let rec cl_full_mult' n size x y re ex c =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m -> Seq ((Seq ((Seq ((cl_full_mult' m size x y re ex c),
    (one_cu_cl_full_adder (x, m) re y c size))),
    (coq_SWAP (y, (sub size (Pervasives.succ 0))) (ex, m)))), (Lshift y)))
    n

(** val cl_full_mult_quar : int -> var -> var -> var -> var -> posi -> exp **)

let cl_full_mult_quar size x y re ex c =
  cl_full_mult' size size x y re ex c

(** val clean_high : int -> int -> var -> var -> exp **)

let rec clean_high n size y ex =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (y, 0))
    (fun m -> Seq ((Seq ((clean_high m size y ex),
    (coq_SWAP (y, (sub size (Pervasives.succ 0))) (ex, m)))), (Lshift y)))
    n

(** val cl_full_mult : int -> var -> var -> var -> var -> posi -> pexp **)

let cl_full_mult size x y re ex c =
  Exp (Seq ((cl_full_mult_quar size x y re ex c),
    (inv_exp (clean_high size size y ex))))

(** val vars_for_cl_nat_full_m' :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_cl_nat_full_m' size =
  gen_vars size (x_var :: (y_var :: (z_var :: (s_var :: []))))

(** val vars_for_cl_nat_full_m :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_cl_nat_full_m size x =
  if (=) x c_var
  then ((((mul size (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0))))), (Pervasives.succ 0)), id_nat), id_nat)
  else vars_for_cl_nat_full_m' size x

(** val cl_full_mult_out : int -> pexp **)

let cl_full_mult_out size =
  cl_full_mult size x_var y_var z_var s_var (c_var, 0)
