open BasicUtility
open MathSpec
open Nat0
open PQASM
open PeanoNat

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
  Lshift y

(** val moddoubler01 : int -> var -> var -> posi -> posi -> exp **)

let moddoubler01 n x m c1 c2 =
  Seq ((doubler1 x), (Seq ((Seq ((comparator01 n m x c1 c2), (X c2))), (CU
    (c2, (subtractor01 n m x c1))))))

(** val modsummer' :
    int -> int -> var -> var -> var -> posi -> var -> (int -> bool) -> exp **)

let rec modsummer' i n m x y c1 s fC =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    if fC 0 then modadder21 n y x m c1 (s, 0) else SKIP (x, 0))
    (fun i' -> Seq ((Seq ((modsummer' i' n m x y c1 s fC),
    (moddoubler01 n x m c1 (s, i')))),
    (if fC i then modadder21 n y x m c1 (s, i) else SKIP (x, i))))
    i

(** val modsummer : int -> var -> var -> var -> posi -> var -> int -> exp **)

let modsummer n m x y c1 s c =
  modsummer' (sub n (Pervasives.succ 0)) n m x y c1 s (nat2fb c)

(** val modmult_half :
    int -> var -> var -> var -> posi -> var -> int -> exp **)

let modmult_half n m x y c1 s c =
  Seq ((modsummer n m x y c1 s c), (inv_exp (modsummer n m x y c1 s 0)))

(** val modmult_full :
    int -> int -> int -> var -> var -> var -> posi -> var -> exp **)

let modmult_full c cinv n m x y c1 s =
  Seq ((modmult_half n m x y c1 s c),
    (inv_exp (modmult_half n m y x c1 s cinv)))

(** val modmult :
    (int -> bool) -> int -> int -> int -> var -> var -> var -> var -> posi ->
    exp **)

let modmult m c cinv n x y z s c1 =
  Seq ((Seq ((init_v n z m), (modmult_full c cinv n z x y c1 s))),
    (inv_exp (init_v n z m)))

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
            (Pervasives.succ 0))))), (Pervasives.succ 0)), id_nat), id_nat)
  else vars_for_cl' size x

(** val real_modmult_rev : int -> int -> int -> int -> exp **)

let real_modmult_rev m c cinv size =
  modmult (nat2fb m) c cinv size x_var y_var z_var s_var (c_var, 0)

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

(** val coq_MAJseq'_i : int -> var -> var -> posi -> int -> exp **)

let rec coq_MAJseq'_i n x y c i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_MAJ c (y, i) (x, 0))
    (fun m -> Seq ((coq_MAJseq'_i m x y c i),
    (coq_MAJ (x, m) (y, (add n i)) (x, n))))
    n

(** val coq_MAJseq_i : int -> var -> var -> posi -> int -> exp **)

let coq_MAJseq_i n x y c i =
  coq_MAJseq'_i (sub n (Pervasives.succ 0)) x y c i

(** val coq_UMAseq'_i : int -> var -> var -> posi -> int -> exp **)

let rec coq_UMAseq'_i n x y c i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_UMA c (y, i) (x, 0))
    (fun m -> Seq ((coq_UMA (x, m) (y, (add n i)) (x, n)),
    (coq_UMAseq'_i m x y c i)))
    n

(** val coq_UMAseq_i : int -> var -> var -> posi -> int -> exp **)

let coq_UMAseq_i n x y c i =
  coq_UMAseq'_i (sub n (Pervasives.succ 0)) x y c i

(** val adder_i : int -> var -> var -> posi -> int -> exp **)

let adder_i n x y c i =
  Seq ((coq_MAJseq_i n x y c i), (coq_UMAseq_i n x y c i))

(** val cl_nat_mult' :
    int -> int -> var -> var -> posi -> (int -> bool) -> exp **)

let rec cl_nat_mult' n size x re c m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (re, 0))
    (fun m0 -> Seq ((cl_nat_mult' m0 size x re c m),
    (if m m0 then adder_i (sub size m0) x re c m0 else SKIP (re, 0))))
    n

(** val cl_nat_mult : int -> var -> var -> posi -> (int -> bool) -> exp **)

let cl_nat_mult size x re c m =
  cl_nat_mult' size size x re c m

(** val vars_for_cl_nat_m' :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_cl_nat_m' size =
  gen_vars size (x_var :: (y_var :: []))

(** val vars_for_cl_nat_m :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_cl_nat_m size x =
  if (=) x z_var
  then ((((mul size (Pervasives.succ (Pervasives.succ 0))), (Pervasives.succ
         0)), id_nat), id_nat)
  else vars_for_cl_nat_m' size x

(** val cl_nat_mult_out : int -> (int -> bool) -> exp **)

let cl_nat_mult_out size m =
  cl_nat_mult size x_var y_var (z_var, 0) m

(** val cl_flt_mult' :
    int -> int -> var -> var -> var -> posi -> (int -> bool) -> exp **)

let rec cl_flt_mult' n size x ex re c m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m0 -> Seq ((one_cl_cu_adder (x, (sub size n)) ex re size c m),
    (cl_flt_mult' m0 size x ex re c (cut_n (div_two_spec m) size))))
    n

(** val cl_flt_mult :
    int -> var -> var -> var -> posi -> (int -> bool) -> exp **)

let cl_flt_mult size x re ex c m =
  cl_flt_mult' size size x ex re c m

(** val one_cu_cl_full_adder_i :
    posi -> var -> var -> posi -> int -> int -> exp **)

let one_cu_cl_full_adder_i c2 x re c1 n i =
  CU (c2, (adder_i n x re c1 i))

(** val cl_full_mult' : int -> int -> var -> var -> var -> posi -> exp **)

let rec cl_full_mult' n size x y re c =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (re, 0))
    (fun m -> Seq ((cl_full_mult' m size x y re c),
    (one_cu_cl_full_adder_i (y, m) x re c (sub size m) m)))
    n

(** val cl_full_mult : int -> var -> var -> var -> posi -> exp **)

let cl_full_mult size x y re c =
  cl_full_mult' size size x y re c

(** val vars_for_cl_nat_full_m' :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_cl_nat_full_m' size =
  gen_vars size (x_var :: (y_var :: (z_var :: [])))

(** val vars_for_cl_nat_full_m :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_cl_nat_full_m size x =
  if (=) x s_var
  then ((((mul size (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))),
         (Pervasives.succ 0)), id_nat), id_nat)
  else vars_for_cl_nat_full_m' size x

(** val cl_full_mult_out : int -> exp **)

let cl_full_mult_out size =
  cl_full_mult size x_var y_var z_var (s_var, 0)

(** val one_cu_cl_full_adder : posi -> var -> var -> posi -> int -> exp **)

let one_cu_cl_full_adder c2 y x c1 n =
  CU (c2, (adder01 n x y c1))

(** val clf_full_mult' :
    int -> int -> var -> var -> var -> var -> posi -> exp **)

let rec clf_full_mult' n size x y re ex c =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun m -> Seq ((Seq ((Seq ((clf_full_mult' m size x y re ex c),
    (one_cu_cl_full_adder (x, m) re y c size))), (coq_SWAP (y, 0) (ex, m)))),
    (Rshift y)))
    n

(** val clf_full_mult_quar :
    int -> var -> var -> var -> var -> posi -> exp **)

let clf_full_mult_quar size x y re ex c =
  clf_full_mult' size size x y re ex c

(** val clean_high_flt : int -> int -> var -> var -> exp **)

let rec clean_high_flt n size y ex =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (y, 0))
    (fun m -> Seq ((Seq ((clean_high_flt m size y ex),
    (coq_SWAP (y, 0) (ex, m)))), (Rshift y)))
    n

(** val clf_full_mult : int -> var -> var -> var -> var -> posi -> exp **)

let clf_full_mult size x y re ex c =
  Seq ((clf_full_mult_quar size x y re ex c),
    (inv_exp (clean_high_flt size size y ex)))

(** val cl_moder' :
    int -> int -> var -> var -> var -> posi -> (int -> bool) -> exp **)

let rec cl_moder' i n x y ex c1 m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> SKIP (x, 0))
    (fun j -> Seq ((Seq ((Seq ((Seq ((Seq ((init_v n y m), (X (ex, j)))),
    (comparator01 n y x c1 (ex, j)))), (CU ((ex, j),
    (subtractor01 n y x c1))))), (init_v n y m))),
    (cl_moder' j n x y ex c1 (cut_n (div_two_spec m) n))))
    i

(** val cl_moder : int -> var -> var -> var -> var -> posi -> int -> exp **)

let cl_moder n x re y ex c1 m =
  let i = findnum m n in
  Seq ((Seq
  ((cl_moder' (Pervasives.succ i) n x y ex c1
     (nat2fb (mul (Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) m))),
  (copyto x re n))),
  (inv_exp
    (cl_moder' (Pervasives.succ i) n x y ex c1
      (nat2fb (mul (Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) m)))))

(** val vars_for_cl_moder' :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_cl_moder' size =
  gen_vars size (x_var :: (y_var :: (z_var :: (s_var :: []))))

(** val vars_for_cl_moder :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_cl_moder size x =
  if (=) x c_var
  then ((((mul size (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0))))), (Pervasives.succ 0)), id_nat), id_nat)
  else vars_for_cl_moder' size x

(** val cl_moder_out : int -> int -> exp **)

let cl_moder_out size =
  cl_moder size x_var y_var z_var s_var (c_var, 0)

(** val cl_div : int -> var -> var -> var -> var -> posi -> int -> exp **)

let cl_div n x re y ex c1 m =
  let i = findnum m n in
  Seq ((Seq
  ((cl_moder' (Pervasives.succ i) n x y ex c1
     (nat2fb (mul (Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) m))),
  (copyto ex re n))),
  (inv_exp
    (cl_moder' (Pervasives.succ i) n x y ex c1
      (nat2fb (mul (Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) m)))))

(** val vars_for_cl_div' :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_cl_div' size =
  gen_vars size (x_var :: (y_var :: (z_var :: (s_var :: []))))

(** val vars_for_cl_div :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_cl_div size x =
  if (=) x c_var
  then ((((mul size (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ 0))))), (Pervasives.succ 0)), id_nat), id_nat)
  else vars_for_cl_div' size x

(** val cl_div_out : int -> int -> exp **)

let cl_div_out size =
  cl_div size x_var y_var z_var s_var (c_var, 0)

(** val cl_div_mod : int -> var -> var -> var -> posi -> int -> exp **)

let cl_div_mod n x y ex c1 m =
  let i = findnum m n in
  cl_moder' (Pervasives.succ i) n x y ex c1
    (nat2fb (mul (Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) m))

(** val vars_for_cl_div_mod' :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_cl_div_mod' size =
  gen_vars size (x_var :: (y_var :: (z_var :: [])))

(** val vars_for_cl_div_mod :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_cl_div_mod size x =
  if (=) x s_var
  then ((((mul size (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))),
         (Pervasives.succ 0)), id_nat), id_nat)
  else vars_for_cl_div_mod' size x

(** val cl_div_mod_out : int -> int -> exp **)

let cl_div_mod_out size =
  cl_div_mod size x_var y_var z_var (s_var, 0)
