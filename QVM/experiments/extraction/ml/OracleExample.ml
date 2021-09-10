open BasicUtility
open CLArith
open MathSpec
open Nat0
open PQASM
open QIMP

(** val test_fun : qexp **)

let test_fun =
  Coq_qseq ((Coq_binapp ((Nor (Var (L x_var))), Coq_ndiv, (Nor (Var (L
    y_var))), (Nor (Var (L z_var))))), (Coq_binapp ((Nor (Var (L s_var))),
    Coq_nmul, (Nor (Var (L x_var))), (Nor (Var (L c_var))))))

(** val temp_var : int **)

let temp_var =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))

(** val temp1_var : int **)

let temp1_var =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))

(** val stack_var : int **)

let stack_var =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))

(** val var_list : (typ * int) list **)

let var_list =
  ((TNor (C, Nat)), x_var) :: (((TNor (C, Nat)), y_var) :: (((TNor (C, Nat)),
    z_var) :: (((TNor (Q, Nat)), s_var) :: (((TNor (Q, Nat)), c_var) :: []))))

(** val dmc_benv : benv **)

let dmc_benv =
  match gen_env var_list empty_benv with
  | Some bv -> bv
  | None -> empty_benv

(** val dmc_vmap' : (typ * var) list -> int -> (qvar * int) -> int **)

let rec dmc_vmap' l n =
  match l with
  | [] ->
    (fun _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ
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
      (Pervasives.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  | p :: xl ->
    let (t0, x) = p in
    if is_q t0
    then (fun i ->
           if qdty_eq i ((L x), 0)
           then n
           else dmc_vmap' xl (Pervasives.succ n) i)
    else dmc_vmap' xl (Pervasives.succ n)

(** val dmc_vmap : (qvar * int) -> int **)

let dmc_vmap =
  dmc_vmap' var_list 0

(** val dmc_estore : estore **)

let dmc_estore =
  init_estore empty_estore var_list

(** val dmc_cstore : (int -> bool) Store.t **)

let dmc_cstore =
  Store.add ((L z_var), 0)
    (nat2fb (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))))
    (Store.add ((L y_var), 0)
      (nat2fb (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))
      (init_cstore empty_cstore var_list))

(** val compile_dm_qft :
    int -> (((exp option * int) * cstore) * estore) value option **)

let compile_dm_qft size =
  trans_qexp size (fun _ -> Pervasives.succ 0) dmc_vmap dmc_benv QFTA
    dmc_cstore temp_var temp1_var stack_var 0 [] dmc_estore dmc_estore
    test_fun

(** val compile_dm_classic :
    int -> (((exp option * int) * cstore) * estore) value option **)

let compile_dm_classic size =
  trans_qexp size (fun _ -> Pervasives.succ 0) dmc_vmap dmc_benv Classic
    dmc_cstore temp_var temp1_var stack_var 0 [] dmc_estore dmc_estore
    test_fun

(** val vars_for_dm_c' :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_dm_c' size =
  gen_vars size (0 :: ((Pervasives.succ 0) :: []))

(** val vars_for_dm_c :
    int -> int -> ((int * int) * (int -> int)) * (int -> int) **)

let vars_for_dm_c size x =
  if (=) x stack_var
  then ((((mul size (Pervasives.succ (Pervasives.succ 0))), (Pervasives.succ
         0)), id_nat), id_nat)
  else vars_for_dm_c' size x

(** val var_list_q : (typ * int) list **)

let var_list_q =
  ((TNor (Q, Nat)), x_var) :: (((TNor (Q, Nat)), y_var) :: (((TNor (C, Nat)),
    z_var) :: (((TNor (Q, Nat)), s_var) :: (((TNor (Q, Nat)), c_var) :: []))))

(** val dmq_benv : benv **)

let dmq_benv =
  match gen_env var_list_q empty_benv with
  | Some bv -> bv
  | None -> empty_benv

(** val dmq_vmap : (qvar * int) -> int **)

let dmq_vmap =
  dmc_vmap' var_list_q 0

(** val dmq_estore : estore **)

let dmq_estore =
  init_estore empty_estore var_list_q

(** val dmq_cstore : (int -> bool) Store.t **)

let dmq_cstore =
  Store.add ((L z_var), 0)
    (nat2fb (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))))
    (init_cstore empty_cstore var_list_q)

(** val compile_dmq_qft :
    int -> (((exp option * int) * cstore) * estore) value option **)

let compile_dmq_qft size =
  trans_qexp size (fun _ -> Pervasives.succ 0) dmq_vmap dmq_benv QFTA
    dmq_cstore temp_var temp1_var stack_var 0 [] dmq_estore dmq_estore
    test_fun

(** val compile_dmq_classic :
    int -> (((exp option * int) * cstore) * estore) value option **)

let compile_dmq_classic size =
  trans_qexp size (fun _ -> Pervasives.succ 0) dmq_vmap dmq_benv Classic
    dmq_cstore temp_var temp1_var stack_var 0 [] dmq_estore dmq_estore
    test_fun
