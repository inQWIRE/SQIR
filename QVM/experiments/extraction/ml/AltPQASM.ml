open AltGateSet2
open CLArith
open Datatypes
open Nat
open PQASM
open QIMP
open RCIR
open RZArith

(** val rz_ang : int -> float **)

let rz_ang n =
  ( /. ) (( *. ) 2.0 Float.pi) ((fun a b -> a ** Float.of_int b) 2.0 n)

(** val rrz_ang : int -> float **)

let rrz_ang n =
  ( -. ) (( *. ) 2.0 Float.pi)
    (( /. ) (( *. ) 2.0 Float.pi) ((fun a b -> a ** Float.of_int b) 2.0 n))

(** val gen_sr_gate' : vars -> var -> int -> int -> coq_U ucom **)

let rec gen_sr_gate' f x n size =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_ID (find_pos f (x, 0)))
    (fun m -> Coq_useq ((gen_sr_gate' f x m size),
    (coq_U1 (rz_ang (sub size m)) (find_pos f (x, m)))))
    n

(** val gen_sr_gate : vars -> var -> int -> coq_U ucom **)

let gen_sr_gate f x n =
  gen_sr_gate' f x (Pervasives.succ n) (Pervasives.succ n)

(** val gen_srr_gate' : vars -> var -> int -> int -> coq_U ucom **)

let rec gen_srr_gate' f x n size =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_ID (find_pos f (x, 0)))
    (fun m -> Coq_useq ((gen_srr_gate' f x m size),
    (coq_U1 (rrz_ang (sub size m)) (find_pos f (x, m)))))
    n

(** val gen_srr_gate : vars -> var -> int -> coq_U ucom **)

let gen_srr_gate f x n =
  gen_srr_gate' f x (Pervasives.succ n) (Pervasives.succ n)

(** val trans_exp :
    vars -> int -> exp -> (int -> posi) -> (coq_U ucom * vars) * (int -> posi) **)

let rec trans_exp f dim exp0 avs =
  match exp0 with
  | SKIP p -> (((coq_ID (find_pos f p)), f), avs)
  | X p -> (((coq_X (find_pos f p)), f), avs)
  | CU (p, e1) ->
    let (p0, _) = trans_exp f dim e1 avs in
    let (e1', _) = p0 in (((control (find_pos f p) e1'), f), avs)
  | RZ (q, p) -> (((coq_U1 (rz_ang q) (find_pos f p)), f), avs)
  | RRZ (q, p) -> (((coq_U1 (rrz_ang q) (find_pos f p)), f), avs)
  | SR (n, x) -> (((gen_sr_gate f x n), f), avs)
  | SRR (n, x) -> (((gen_srr_gate f x n), f), avs)
  | HCNOT (p1, p2) -> (((coq_CX (find_pos f p1) (find_pos f p2)), f), avs)
  | Lshift x ->
    (((coq_ID (find_pos f (x, 0))), (trans_lshift f x)),
      (lshift_avs dim f avs x))
  | Rshift x ->
    (((coq_ID (find_pos f (x, 0))), (trans_rshift f x)),
      (rshift_avs dim f avs x))
  | Rev x ->
    (((coq_ID (find_pos f (x, 0))), (trans_rev f x)), (rev_avs dim f avs x))
  | Seq (e1, e2) ->
    let (p, avs') = trans_exp f dim e1 avs in
    let (e1', f') = p in
    let (p0, avs'') = trans_exp f' dim e2 avs' in
    let (e2', f'') = p0 in (((Coq_useq (e1', e2')), f''), avs'')

(** val controlled_rotations_gen : vars -> var -> int -> int -> coq_U ucom **)

let rec controlled_rotations_gen f x n i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_ID (find_pos f (x, i)))
    (fun m ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_ID (find_pos f (x, i)))
      (fun _ -> Coq_useq ((controlled_rotations_gen f x m i),
      (control (find_pos f (x, (add m i)))
        (coq_U1 (rz_ang n) (find_pos f (x, i))))))
      m)
    n

(** val coq_QFT_gen : vars -> var -> int -> int -> coq_U ucom **)

let rec coq_QFT_gen f x n size =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_ID (find_pos f (x, 0)))
    (fun m -> Coq_useq ((coq_QFT_gen f x m size), (Coq_useq
    ((coq_H (find_pos f (x, m))),
    (controlled_rotations_gen f x (sub size m) m)))))
    n

(** val trans_qft : vars -> var -> coq_U ucom **)

let trans_qft f x =
  coq_QFT_gen f x (vsize f x) (vsize f x)

(** val trans_rqft : vars -> var -> coq_U ucom **)

let trans_rqft f x =
  invert (coq_QFT_gen f x (vsize f x) (vsize f x))

(** val nH : vars -> var -> int -> coq_U ucom **)

let rec nH f x n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_ID (find_pos f (x, 0)))
    (fun m -> Coq_useq ((coq_H (find_pos f (x, m))), (nH f x m)))
    n

(** val trans_h : vars -> var -> coq_U ucom **)

let trans_h f x =
  nH f x (vsize f x)

(** val trans_pexp' :
    vars -> int -> pexp -> (int -> posi) -> (coq_U ucom * vars) * (int ->
    posi) **)

let rec trans_pexp' vs dim exp0 avs =
  match exp0 with
  | Exp s -> trans_exp vs dim s avs
  | QFT x -> (((trans_qft vs x), vs), avs)
  | RQFT x -> (((trans_rqft vs x), vs), avs)
  | H x -> (((trans_h vs x), vs), avs)
  | PCU (p, e1) ->
    let (p0, _) = trans_pexp' vs dim e1 avs in
    let (e1', _) = p0 in (((control (find_pos vs p) e1'), vs), avs)
  | PSeq (e1, e2) ->
    let (p, avs') = trans_pexp' vs dim e1 avs in
    let (e1', vs') = p in
    let (p0, avs'') = trans_pexp' vs' dim e2 avs' in
    let (e2', vs'') = p0 in (((Coq_useq (e1', e2')), vs''), avs'')

(** val trans_pexp :
    vars -> int -> pexp -> (int -> posi) -> (coq_U ucom * vars) * (int ->
    posi) **)

let trans_pexp vs dim exp0 avs =
  trans_pexp' vs dim (pexp_elim exp0) avs

(** val trans_cl_adder : int -> (coq_U ucom * vars) * (int -> posi) **)

let trans_cl_adder size =
  trans_pexp (vars_for_adder01 size)
    (add (mul (Pervasives.succ (Pervasives.succ 0)) size) (Pervasives.succ 0))
    (Exp (adder01_out size)) (avs_for_arith size)

(** val trans_cl_const_mul :
    int -> int -> (coq_U ucom * vars) * (int -> posi) **)

let trans_cl_const_mul size m =
  trans_pexp (vars_for_cl_nat_m size)
    (add (mul (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))) size)
      (Pervasives.succ 0)) (Exp (cl_nat_mult_out size (nat2fb m)))
    (avs_for_arith size)

(** val trans_cl_mul : int -> (coq_U ucom * vars) * (int -> posi) **)

let trans_cl_mul size =
  trans_pexp (vars_for_cl_nat_full_m size)
    (add
      (mul (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) size) (Pervasives.succ 0))
    (cl_full_mult_out size) (avs_for_arith size)

(** val trans_rz_const_adder :
    int -> int -> (coq_U ucom * vars) * (int -> posi) **)

let trans_rz_const_adder size m =
  trans_pexp (vars_for_rz_adder size) size (rz_adder_out size (nat2fb m))
    (avs_for_arith size)

(** val trans_rz_adder : int -> (coq_U ucom * vars) * (int -> posi) **)

let trans_rz_adder size =
  trans_pexp (vars_for_rz_full_add size)
    (mul (Pervasives.succ (Pervasives.succ 0)) size) (rz_full_adder_out size)
    (avs_for_arith size)

(** val trans_rz_const_mul :
    int -> int -> (coq_U ucom * vars) * (int -> posi) **)

let trans_rz_const_mul size m =
  trans_pexp (vars_for_rz_nat_m size)
    (mul (Pervasives.succ (Pervasives.succ 0)) size)
    (nat_mult_out size (nat2fb m)) (avs_for_arith size)

(** val trans_rz_mul : int -> (coq_U ucom * vars) * (int -> posi) **)

let trans_rz_mul size =
  trans_pexp (vars_for_rz_nat_full_m size)
    (mul (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))) size) (nat_full_mult_out size) (avs_for_arith size)

(** val trans_cl_mod : int -> int -> (coq_U ucom * vars) * (int -> posi) **)

let trans_cl_mod size m =
  trans_pexp (vars_for_cl_moder size)
    (add
      (mul (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) size) (Pervasives.succ (Pervasives.succ 0)))
    (Exp (cl_moder_out size m)) (avs_for_arith size)

(** val trans_cl_div : int -> int -> (coq_U ucom * vars) * (int -> posi) **)

let trans_cl_div size m =
  trans_pexp (vars_for_cl_div size)
    (add
      (mul (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) size) (Pervasives.succ (Pervasives.succ 0)))
    (Exp (cl_div_out size m)) (avs_for_arith size)

(** val trans_cl_div_mod :
    int -> int -> (coq_U ucom * vars) * (int -> posi) **)

let trans_cl_div_mod size m =
  trans_pexp (vars_for_cl_div_mod size)
    (add (mul (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))) size)
      (Pervasives.succ (Pervasives.succ 0))) (Exp (cl_div_mod_out size m))
    (avs_for_arith size)

(** val trans_rz_mod : int -> int -> (coq_U ucom * vars) * (int -> posi) **)

let trans_rz_mod size m =
  trans_pexp (vars_for_rz_moder size)
    (add
      (mul (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
        (Pervasives.succ size)) (Pervasives.succ 0)) (rz_moder_out size m)
    (avs_for_rz_moder size)

(** val trans_rz_div : int -> int -> (coq_U ucom * vars) * (int -> posi) **)

let trans_rz_div size m =
  trans_pexp (vars_for_rz_div size)
    (add
      (mul (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
        (Pervasives.succ size)) (Pervasives.succ 0)) (rz_div_out size m)
    (avs_for_rz_div size)

(** val trans_rz_div_mod :
    int -> int -> (coq_U ucom * vars) * (int -> posi) **)

let trans_rz_div_mod size m =
  trans_pexp (vars_for_rz_div_mod size)
    (add (mul (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ size))
      (Pervasives.succ 0)) (rz_div_mod_out size m) (avs_for_rz_div_mod size)

(** val prog_to_sqir_real : prog -> flag -> coq_U ucom **)

let prog_to_sqir_real p f =
  match prog_to_sqir p f with
  | Some p0 ->
    let (p1, avs) = p0 in
    let (p2, vars0) = p1 in
    let (p3, p4) = p2 in
    let (d, _) = p3 in fst (fst (trans_pexp vars0 d p4 avs))
  | None -> coq_SKIP

(** val trans_rz_modmult_rev :
    int -> int -> int -> int -> (coq_U ucom * vars) * (int -> posi) **)

let trans_rz_modmult_rev m c cinv size =
  trans_pexp (vars_for_rz size)
    (add (mul (Pervasives.succ (Pervasives.succ 0)) size) (Pervasives.succ 0))
    (real_rz_modmult_rev m c cinv size) (avs_for_arith size)

(** val trans_modmult_rev :
    int -> int -> int -> int -> (coq_U ucom * vars) * (int -> posi) **)

let trans_modmult_rev m c cinv size =
  trans_pexp (vars_for_cl size)
    (add
      (mul (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))) size) (Pervasives.succ (Pervasives.succ 0)))
    (real_modmult_rev m c cinv size) (avs_for_arith size)

(** val bc2ucom : bccom -> coq_U ucom **)

let rec bc2ucom = function
| Coq_bcskip -> coq_SKIP
| Coq_bcx a -> coq_X a
| Coq_bcswap (a, b) ->
  Coq_useq ((Coq_useq ((coq_CX a b), (coq_CX b a))), (coq_CX a b))
| Coq_bccont (a, bc1) -> control a (bc2ucom bc1)
| Coq_bcseq (bc1, bc2) -> Coq_useq ((bc2ucom bc1), (bc2ucom bc2))
