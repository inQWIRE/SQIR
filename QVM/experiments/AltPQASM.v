(* We need to redefine trans_pexp to output SQIR programs using the
   alternate gate set & prove that this new definition is equivalent
   to the old (see utilities/AltGateSet.v and examples/shor/AltShor.v
   for examples). *)

Require Import Prelim.
Require Import RCIR.
Require Import AltGateSet.
Require Import MathSpec BasicUtility PQASM.
Require Import RZArith.
Require Import CLArith.
Require Import QIMP.
Require Import OracleExample.
(*Require Import QIMP.*)

Definition rz_ang (n:nat) : R := ((R2 * PI)%R / R2^n). (* redefined using R2 *)

Definition rrz_ang (n:nat) : R := ((R2 * PI)%R - ((R2 * PI)%R / R2^n)).

Definition ID q := AltGateSet.U1 R0 q.

Fixpoint gen_sr_gate' (f:vars) (x:var) (n:nat) (size:nat) : ucom U := 
    match n with 
    | 0 => ID (find_pos f (x,0))
    | S m => (gen_sr_gate' f x m size) >> (U1 (rz_ang (size - m)) (find_pos f (x,m)))
    end.
Definition gen_sr_gate (f:vars) (x:var) (n:nat) := gen_sr_gate' f x (S n) (S n).

Fixpoint gen_srr_gate' (f:vars) (x:var) (n:nat) (size:nat) : ucom U := 
    match n with 
    | 0 => ID (find_pos f (x,0))
    | S m => (gen_srr_gate' f x m size) >> (U1 (rrz_ang (size - m)) (find_pos f (x,m)))
    end.
Definition gen_srr_gate (f:vars) (x:var) (n:nat) := gen_srr_gate' f x (S n) (S n).

Fixpoint controlled_rotations_gen (f : vars) (x:var) (n : nat) (i:nat) : ucom U :=
    match n with
    | 0 | 1 => ID (find_pos f (x,i))
    | S m => (controlled_rotations_gen f x m i) >>
              (control (find_pos f (x,(m+i)%nat)) (U1 (rz_ang n) (find_pos f (x,i))))
    end.

Fixpoint QFT_gen (f : vars) (x:var) (n : nat) (size:nat) : ucom U :=
    match n with
    | 0 => ID (find_pos f (x,0))
    | S m => (QFT_gen f x m size) >>
             ((AltGateSet.H (find_pos f (x,m))) >> 
             (controlled_rotations_gen f x (size-m) m))
    end.

Definition trans_qft (f:vars) (x:var) : ucom U := 
    QFT_gen f x (vsize f x) (vsize f x).

Definition trans_rqft (f:vars) (x:var) : ucom U :=
          invert (QFT_gen f x (vsize f x) (vsize f x)).

Fixpoint nH (f : vars) (x:var) (n:nat) : ucom U :=
    match n with 
    | 0 => ID (find_pos f (x,0))
    | S m => (nH f x m) >> (AltGateSet.H (find_pos f (x,m)))
    end.

Definition trans_h (f : vars) (x:var) : ucom U := nH f x (vsize f x).

Fixpoint trans_exp' (f : vars) (dim:nat) (exp:exp) (avs: nat -> posi) : (ucom U * vars * (nat -> posi)) :=
    match exp with
    | SKIP p => (ID (find_pos f p), f, avs)
    | X p => (AltGateSet.X (find_pos f p), f, avs)
    | RZ q p => (U1 (rz_ang q) (find_pos f p), f, avs)
    | RRZ q p => (U1 (rrz_ang q) (find_pos f p), f, avs)
    | SR n x => (gen_sr_gate f x n, f, avs)
    | SRR n x => (gen_srr_gate f x n, f, avs)
    | Lshift x => (ID (find_pos f (x,0)), trans_lshift f x, lshift_avs dim f avs x)
    | Rshift x => (ID (find_pos f (x,0)), trans_rshift f x, rshift_avs dim f avs x)
    | Rev x => (ID (find_pos f (x,0)), trans_rev f x, rev_avs dim f avs x)
    | HCNOT p1 p2 => (AltGateSet.CX (find_pos f p1) (find_pos f p2), f, avs)
    | CU p e1 => match trans_exp' f dim e1 avs with 
                 | (e1', f',avs') => (control (find_pos f p) e1', f, avs) end
    | QFT x => (trans_qft f x, f, avs)
    | RQFT x => (trans_rqft f x, f, avs)
    | H x => (trans_h f x, f, avs)
    | (e1 ; e2)%exp => match trans_exp' f dim e1 avs with 
                 | (e1', f', avs') => 
                        match trans_exp' f' dim e2 avs' with 
                        | (e2',f'',avs'') => (e1' >> e2', f'', avs'') end
                  end
    end.

(* In the final result, we can throw away the vars and avs. 
   -> also call decompose_CU1_and_C3X to decompose gates for later optimization *)
Definition trans_exp f dim exp avs := 
  decompose_CU1_and_C3X (fst (fst (trans_exp' f dim exp avs))).

(* z = x + y (TOFF-based) *)
Definition trans_cl_adder (size:nat) :=
  trans_exp (CLArith.vars_for_adder01 size) (2 * size + 1) (CLArith.adder01_out size) (PQASM.avs_for_arith size).

(* z = M * x (TOFF-based) *)
Definition trans_cl_const_mul (size M:nat) :=
  trans_exp (CLArith.vars_for_cl_nat_m size) (2 * size + 1) (CLArith.cl_nat_mult_out size (nat2fb M)) (PQASM.avs_for_arith size).

(* z = x * y (TOFF-based) *)
Definition trans_cl_mul (size:nat) :=
  trans_exp (CLArith.vars_for_cl_nat_full_m size) (3 * size + 1) (CLArith.cl_full_mult_out size) (PQASM.avs_for_arith size).

(* z = M + x (QFT-based) *)
Definition trans_rz_const_adder (size M:nat) :=
  trans_exp (RZArith.vars_for_rz_adder size) size (RZArith.rz_adder_out size (nat2fb M)) (PQASM.avs_for_arith size).

(* z = x + y (QFT-based) *)
Definition trans_rz_adder (size:nat) :=
  trans_exp (RZArith.vars_for_rz_full_add size) (2 * size) (RZArith.rz_full_adder_out size) (PQASM.avs_for_arith size).

(* z = M * x (QFT-based) *)
Definition trans_rz_const_mul (size M:nat) :=
  trans_exp (RZArith.vars_for_rz_nat_m size) (2 * size) (RZArith.nat_mult_out size (nat2fb M)) (PQASM.avs_for_arith size).

(* z = x * y (QFT-based) *)
Definition trans_rz_mul (size:nat) :=
  trans_exp (RZArith.vars_for_rz_nat_full_m size) (3 * size) (RZArith.nat_full_mult_out size) (PQASM.avs_for_arith size). 

(* z = x mod y (TOFF-based) *)
Definition trans_cl_mod (size M:nat) :=
  trans_exp (CLArith.vars_for_cl_moder size) (4 * size + 1) (CLArith.cl_moder_out size M) (PQASM.avs_for_arith size). 

(* z = x / y (TOFF-based) *)
Definition trans_cl_div (size M:nat) :=
  trans_exp (CLArith.vars_for_cl_div size) (4 * size + 1) (CLArith.cl_div_out size M) (PQASM.avs_for_arith size). 

(* z = x mod y,x/y (TOFF-based) *)
Definition trans_cl_div_mod (size M:nat) :=
  trans_exp (CLArith.vars_for_cl_div_mod size) (3 * size + 1) (CLArith.cl_div_mod_out size M) (PQASM.avs_for_arith size). 

(* z = x mod y (QFT-based) *)
Definition trans_rz_mod (size M:nat) :=
  trans_exp (RZArith.vars_for_rz_moder size) (3 * (S size) ) (RZArith.rz_moder_out size M) (RZArith.avs_for_rz_moder size). 

(* z = x / y (QFT-based) *)
Definition trans_rz_div (size M:nat) :=
  trans_exp (RZArith.vars_for_rz_div size) (3 * (S size)) (RZArith.rz_div_out size M) (RZArith.avs_for_rz_div size). 

(* z = x mod y, x / y (QFT-based) *)
Definition trans_rz_div_mod (size M:nat) :=
  trans_exp (RZArith.vars_for_rz_div_mod size) (2 * (S size)) (RZArith.rz_div_mod_out size M) (RZArith.avs_for_rz_div_mod size). 

(* Redefine funcs in RZArith and CLArith to use the new trans_exp *)
Definition trans_rz_modmult_rev (M C Cinv size:nat) :=
        trans_exp (vars_for_rz size) (2*size+1) (real_rz_modmult_rev M C Cinv size) (avs_for_arith size).
Definition trans_rz_modmult_rev_alt (M C Cinv size:nat) :=
        trans_exp (vars_for_rz size) (2*size+1) (real_rz_modmult_rev_alt M C Cinv size) (avs_for_arith size).
Definition trans_modmult_rev (M C Cinv size:nat) :=
        trans_exp (vars_for_cl (S (size))) (4*(S (size))+1)
              (real_modmult_rev M C Cinv (S (size))) (avs_for_arith (S (size))).

(* Trans QIMP examples. *)
Definition trans_dmc_qft (size:nat) :=
   match compile_dm_qft size with Some (Value (Some p,n,a,b)) => 
             Some (trans_exp (vars_for_dm_c size) (2*size + 1) p (avs_for_arith size))
        | _ => None
   end.

Definition trans_dmc_cl (size:nat) :=
   match compile_dm_classic size with Some (Value (Some p,n,a,b)) => 
             Some (trans_exp (vars_for_dm_c size) (2*size + 1) p (avs_for_arith size))
        | _ => None
   end.

Definition trans_dmq_qft (size:nat) :=
   match compile_dmq_qft size with Some (Value (Some p,n,a,b)) => 
             Some (trans_exp (vars_for_dm_c size) (6*size + 1) p (avs_for_arith size))
        | _ => None
   end.

Definition trans_dmq_cl (size:nat) :=
   match compile_dmq_classic size with Some (Value (Some p,n,a,b)) => 
             Some (trans_exp (vars_for_dm_c size) (6*size + 1) p (avs_for_arith size))
        | _ => None
   end.
    
(* Also want bc2ucom for comparison's sake *)
Fixpoint bc2ucom (bc : bccom) : ucom U :=
  match bc with
  | bcskip => ID 0
  | bcx a => AltGateSet.X a
  | bcswap a b => AltGateSet.SWAP a b
  | bccont a bc1 => control a (bc2ucom bc1)
  | bcseq bc1 bc2 => (bc2ucom bc1) >> (bc2ucom bc2)
  end.


(** Proof that these new definitions match the ones in PQASM **)


Lemma gen_sr_gate_same : forall dim f x n,
  to_base_ucom dim (gen_sr_gate f x n) = PQASM.gen_sr_gate f dim x n.
Proof.
  intros dim f x n.
  unfold gen_sr_gate, PQASM.gen_sr_gate.
  assert (forall a b, 
          to_base_ucom dim (gen_sr_gate' f x a b) 
            = PQASM.gen_sr_gate' f dim x a b).
  { intros. induction a. reflexivity.
    simpl. rewrite IHa. reflexivity. }
  apply H.
Qed.

Lemma gen_srr_gate_same : forall dim f x n,
  to_base_ucom dim (gen_srr_gate f x n) = PQASM.gen_srr_gate f dim x n.
Proof.
  intros dim f x n.
  unfold gen_srr_gate, PQASM.gen_srr_gate.
  assert (forall a b, 
          to_base_ucom dim (gen_srr_gate' f x a b) 
            = PQASM.gen_srr_gate' f dim x a b).
  { intros. induction a. reflexivity.
    simpl. rewrite IHa. reflexivity. }
  apply H.
Qed.

Lemma controlled_rotations_gen_same : forall dim f x n i, 
  to_base_ucom dim (controlled_rotations_gen f x n i)
    = PQASM.controlled_rotations_gen f dim x n i.
Proof.
  intros.
  destruct n; try reflexivity.
  induction n; try reflexivity.
  simpl in *.
  rewrite IHn.
  reflexivity.
Qed.

Lemma controlled_rotations_WF : forall f x n i,
  well_formed (controlled_rotations_gen f x n i).
Proof.
  intros.
  destruct n.
  simpl. constructor. auto.
  induction n.
  simpl. constructor. auto.
  remember (S n) as m.
  simpl.
  destruct m.
  lia.
  constructor.
  apply IHn.
  apply control'_WF.
  constructor. auto.
Qed.

Lemma QFT_gen_same : forall dim f x n size, 
  to_base_ucom dim (QFT_gen f x n size) = PQASM.QFT_gen f dim x n size.
Proof.
  intros.
  induction n; try reflexivity.
  simpl.
  rewrite IHn.
  rewrite <- controlled_rotations_gen_same.
  reflexivity.
Qed.

Lemma QFT_gen_WF : forall f x n size, well_formed (QFT_gen f x n size).
Proof.
  intros.
  induction n; simpl. 
  constructor. auto.
  repeat constructor. 
  apply IHn.
  apply controlled_rotations_WF.
Qed.

Lemma trans_qft_same : forall dim f x,
  to_base_ucom dim (trans_qft f x) = PQASM.trans_qft f dim x.
Proof. intros. apply QFT_gen_same. Qed.

Lemma trans_rqft_same : forall dim f x,
  uc_eval dim (trans_rqft f x) = UnitarySem.uc_eval (PQASM.trans_rqft f dim x).
Proof. 
  intros. 
  unfold trans_rqft, PQASM.trans_rqft.
  unfold uc_eval.
  rewrite <- QFT_gen_same.
  apply invert_same.
  apply QFT_gen_WF.
Qed.

Lemma trans_h_same : forall dim f x,
  to_base_ucom dim (trans_h f x) = PQASM.trans_h f dim x.
Proof.
  intros.
  unfold trans_h, PQASM.trans_h.
  assert (forall n, to_base_ucom dim (nH f x n) = PQASM.nH f dim x n).
  { induction n. reflexivity.
    simpl. rewrite IHn. reflexivity. }
  apply H.
Qed.

Lemma trans_exp_same : forall f dim exp avs,
  uc_eval dim (trans_exp f dim exp avs) 
    = UnitarySem.uc_eval (fst (fst (PQASM.trans_exp f dim exp avs))).
Proof.
  intros.
  unfold trans_exp.
  rewrite decompose_CU1_and_C3X_preserves_semantics.
  assert (forall u1 u2 f1 f2 avs1 avs2,
          trans_exp' f dim exp avs = (u1, f1, avs1) ->
          PQASM.trans_exp f dim exp avs = (u2, f2, avs2) ->
          uc_eval dim u1 =  UnitarySem.uc_eval u2 /\ f1 = f2 /\ avs1 = avs2).
  { generalize dependent avs.
    generalize dependent dim.
    generalize dependent f.
    induction exp; intros f dim avs u1 u2 f1 f2 avs1 avs2 H1 H2.
    
    (* simple cases *)
    all: try (inversion H1; inversion H2; subst;
              repeat split; reflexivity). 
    
    (* CU p exp *)
    simpl in H1, H2.
    destruct (trans_exp' f dim exp avs) eqn:transexp'.
    destruct p0.
    destruct (PQASM.trans_exp f dim exp avs) eqn:transexp.
    destruct p0.
    eapply IHexp in transexp' as [? [? ?]].
    2: apply transexp.
    inversion H1; inversion H2; subst.
    repeat split; try reflexivity.
    admit. (* annoying... *)

    (* SR q x *)
    simpl in H1, H2.
    unfold uc_eval.
    inversion H1; inversion H2; subst.
    rewrite gen_sr_gate_same.
    auto.

    (* SRR q x *)
    simpl in H1, H2.
    unfold uc_eval.
    inversion H1; inversion H2; subst.
    rewrite gen_srr_gate_same.
    auto.

    (* QFT x *)
    simpl in H1, H2.
    unfold uc_eval.
    inversion H1; inversion H2; subst.
    rewrite trans_qft_same.
    auto.

    (* RQFT x *)
    simpl in H1, H2.
    inversion H1; inversion H2; subst.
    rewrite trans_rqft_same.
    auto.

    (* H x *)
    simpl in H1, H2.
    unfold uc_eval.
    inversion H1; inversion H2; subst.
    rewrite trans_h_same.
    auto.

    (* exp1 ; exp2 *)
    simpl in H1, H2.
    destruct (trans_exp' f dim exp1 avs) eqn:transexp1.
    destruct p.
    destruct (PQASM.trans_exp f dim exp1 avs) eqn:transexp2.
    destruct p.
    eapply IHexp1 in transexp1 as [? [? ?]].
    2: apply transexp2.
    subst.
    destruct (trans_exp' v0 dim exp2 p1) eqn:transexp3.
    destruct p.
    destruct (PQASM.trans_exp v0 dim exp2 p1) eqn:transexp4.
    destruct p.
    eapply IHexp2 in transexp3 as [? [? ?]].
    2: apply transexp4.
    inversion H1; inversion H2; subst.

    repeat split; try reflexivity.
    unfold uc_eval in *.
    simpl.
    rewrite H, H0.
    reflexivity. }
Admitted.

(** Taken from examples/shor/AltShor.v **)

Lemma bc2ucom_WF : forall bc, well_formed (bc2ucom bc).
Proof.
  induction bc; repeat constructor; auto.
  simpl. unfold control. apply control'_WF.
  assumption.
Qed.

Lemma bc2ucom_fresh : forall dim q bc,
  UnitaryOps.is_fresh q (to_base_ucom dim (bc2ucom bc)) <->
  @UnitaryOps.is_fresh _ dim q (RCIR.bc2ucom bc).
Proof.
  intros dim q bc.
  induction bc; try reflexivity.
  simpl.
  destruct bc; try reflexivity.
  rewrite <- UnitaryOps.fresh_control.
  unfold control.
  rewrite <- fresh_control'.
  rewrite IHbc.
  reflexivity.
  lia.
  apply bc2ucom_WF.
  rewrite <- UnitaryOps.fresh_control.
  unfold control.
  rewrite <- fresh_control'.
  rewrite IHbc.
  reflexivity.
  lia.
  apply bc2ucom_WF.
  split; intro H; inversion H; subst; simpl.
  constructor.
  apply IHbc1; auto.
  apply IHbc2; auto.
  constructor.
  apply IHbc1; auto.
  apply IHbc2; auto.
Qed.

Lemma bc2ucom_correct : forall dim (bc : bccom),
  uc_eval dim (bc2ucom bc) = UnitarySem.uc_eval (RCIR.bc2ucom bc).
Proof.
  intros dim bc.
  induction bc; try reflexivity.
  simpl.
  rewrite control_correct.
  destruct bc; try reflexivity.
  apply UnitaryOps.control_ucom_X.
  apply UnitaryOps.control_cong.
  apply IHbc.
  apply bc2ucom_fresh. 
  apply UnitaryOps.control_cong.
  apply IHbc.
  apply bc2ucom_fresh. 
  apply bc2ucom_WF. 
  unfold uc_eval in *. simpl.
  rewrite IHbc1, IHbc2.
  reflexivity.  
Qed.
