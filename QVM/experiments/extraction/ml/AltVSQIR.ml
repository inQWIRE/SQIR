open AltGateSet
open Nat
open VSQIR

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
    (fun _ -> coq_SKIP)
    (fun m -> Coq_useq ((gen_sr_gate' f x m size),
    (coq_U1 (rz_ang (sub size m)) (find_pos f (x, m)))))
    n

(** val gen_sr_gate : vars -> var -> int -> coq_U ucom **)

let gen_sr_gate f x n =
  gen_sr_gate' f x (Pervasives.succ n) (Pervasives.succ n)

(** val gen_srr_gate' : vars -> var -> int -> int -> coq_U ucom **)

let rec gen_srr_gate' f x n size =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
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
  | SKIP _ -> ((coq_SKIP, f), avs)
  | X p -> (((coq_X (find_pos f p)), f), avs)
  | CU (p, e1) ->
    (match e1 with
     | X p2 -> (((coq_CX (find_pos f p) (find_pos f p2)), f), avs)
     | _ ->
       let (p0, _) = trans_exp f dim e1 avs in
       let (e1', _) = p0 in (((control (find_pos f p) e1'), f), avs))
  | RZ (q, p) -> (((coq_U1 (rz_ang q) (find_pos f p)), f), avs)
  | RRZ (q, p) -> (((coq_U1 (rrz_ang q) (find_pos f p)), f), avs)
  | SR (n, x) -> (((gen_sr_gate f x n), f), avs)
  | SRR (n, x) -> (((gen_srr_gate f x n), f), avs)
  | HCNOT (p1, p2) -> (((coq_CX (find_pos f p1) (find_pos f p2)), f), avs)
  | Lshift x -> ((coq_SKIP, (trans_lshift f x)), (lshift_avs dim f avs x))
  | Rshift x -> ((coq_SKIP, (trans_rshift f x)), (rshift_avs dim f avs x))
  | Rev x -> ((coq_SKIP, (trans_rev f x)), (rev_avs dim f avs x))
  | Seq (e1, e2) ->
    let (p, avs') = trans_exp f dim e1 avs in
    let (e1', f') = p in
    let (p0, avs'') = trans_exp f' dim e2 avs' in
    let (e2', f'') = p0 in (((Coq_useq (e1', e2')), f''), avs'')

(** val controlled_rotations_gen : vars -> var -> int -> int -> coq_U ucom **)

let rec controlled_rotations_gen f x n i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun m ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_SKIP)
      (fun _ -> Coq_useq ((controlled_rotations_gen f x m i),
      (control (find_pos f (x, (add m i)))
        (coq_U1 (rz_ang n) (find_pos f (x, i))))))
      m)
    n

(** val coq_QFT_gen : vars -> var -> int -> int -> coq_U ucom **)

let rec coq_QFT_gen f x n size =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun m -> Coq_useq ((coq_H (find_pos f (x, m))), (Coq_useq
    ((controlled_rotations_gen f x (sub size m) m),
    (coq_QFT_gen f x m size)))))
    n

(** val trans_qft : vars -> var -> coq_U ucom **)

let trans_qft f x =
  coq_QFT_gen f x (vsize f x) (vsize f x)

(** val controlled_rotations_gen_r :
    vars -> var -> int -> int -> coq_U ucom **)

let rec controlled_rotations_gen_r f x n i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun m ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_SKIP)
      (fun _ -> Coq_useq
      ((control (find_pos f (x, (add m i)))
         (coq_U1 (rrz_ang n) (find_pos f (x, i)))),
      (controlled_rotations_gen_r f x m i)))
      m)
    n

(** val coq_QFT_gen_r : vars -> var -> int -> int -> coq_U ucom **)

let rec coq_QFT_gen_r f x n size =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun m -> Coq_useq ((controlled_rotations_gen_r f x (sub size m) m),
    (Coq_useq ((coq_H (find_pos f (x, m))), (coq_QFT_gen_r f x m size)))))
    n

(** val trans_rqft : vars -> var -> coq_U ucom **)

let trans_rqft f x =
  coq_QFT_gen_r f x (vsize f x) (vsize f x)

(** val nH : vars -> var -> int -> coq_U ucom **)

let rec nH f x n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun m -> Coq_useq ((coq_H (find_pos f (x, m))), (nH f x m)))
    n

(** val trans_h : vars -> var -> coq_U ucom **)

let trans_h f x =
  nH f x (vsize f x)

(** val trans_pexp :
    vars -> int -> pexp -> (int -> posi) -> (coq_U ucom * vars) * (int ->
    posi) **)

let rec trans_pexp vs dim exp0 avs =
  match exp0 with
  | Exp s -> trans_exp vs dim s avs
  | QFT x -> (((trans_qft vs x), vs), avs)
  | RQFT x -> (((trans_rqft vs x), vs), avs)
  | H x -> (((trans_h vs x), vs), avs)
  | PCU (p, e1) ->
    let (p0, _) = trans_pexp vs dim e1 avs in
    let (e1', _) = p0 in (((control (find_pos vs p) e1'), vs), avs)
  | PSeq (e1, e2) ->
    let (p, avs') = trans_pexp vs dim e1 avs in
    let (e1', vs') = p in
    let (p0, avs'') = trans_pexp vs' dim e2 avs' in
    let (e2', vs'') = p0 in (((Coq_useq (e1', e2')), vs''), avs'')
