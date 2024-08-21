Require Export QuantumLib.VectorStates.
Require Export UnitaryOps.
Require Export SQIR.

Local Open Scope ucom_scope.
Local Close Scope C_scope.
Local Close Scope R_scope.

(** Some useful equivalences over unitary circuits. **)

Lemma ID_equiv_SKIP : forall dim n, n < dim -> @ID dim n ≡ SKIP.
Proof.
  intros dim n WT. 
  unfold uc_equiv.
  autorewrite with eval_db; [|lia].
  bdestruct_all.
  rewrite 2!id_kron; f_equal; unify_pows_two.
Qed.

Lemma SKIP_id_l : forall {dim} (c : base_ucom dim), SKIP; c ≡ c.
Proof.
  intros dim c. 
  unfold uc_equiv.
  simpl. 
  destruct (uc_well_typed_b c) eqn:WT.
  - apply uc_well_typed_b_equiv in WT.
    apply uc_well_typed_implies_dim_nonzero in WT.
    autorewrite with eval_db; try assumption.
    Msimpl_light; reflexivity.
  - apply not_true_iff_false in WT. 
    rewrite uc_well_typed_b_equiv in WT.
    apply uc_eval_zero_iff in WT.
    rewrite WT.
    Msimpl_light; reflexivity.
Qed.

Lemma SKIP_id_r : forall {dim} (c : base_ucom dim), c; SKIP ≡ c.
Proof.
  intros dim c. 
  unfold uc_equiv.
  simpl. 
  destruct (uc_well_typed_b c) eqn:WT.
  - apply uc_well_typed_b_equiv in WT.
    apply uc_well_typed_implies_dim_nonzero in WT.
    autorewrite with eval_db; try assumption.
    Msimpl_light; reflexivity.
  - apply not_true_iff_false in WT. 
    rewrite uc_well_typed_b_equiv in WT.
    apply uc_eval_zero_iff in WT.
    rewrite WT.
    Msimpl_light; reflexivity.
Qed.

Lemma SKIP_id_l_cong : forall {dim} (c : base_ucom dim), SKIP; c ≅ c.
Proof.
  intros. 
  apply uc_equiv_cong.
  apply SKIP_id_l.
Qed.

Lemma SKIP_id_r_cong : forall {dim} (c : base_ucom dim), c; SKIP ≅ c.
Proof.
  intros. 
  apply uc_equiv_cong.
  apply SKIP_id_r.
Qed.

Lemma X_X_id : forall {dim} q, X q; X q ≡ @ID dim q.
Proof. 
  intros dim q. 
  unfold uc_equiv.
  simpl; autorewrite with eval_db. 
  gridify.
  rewrite MmultXX.
  reflexivity.
Qed.

Lemma H_H_id : forall {dim} q, H q; H q ≡ @ID dim q.
Proof. 
  intros dim q. 
  unfold uc_equiv.
  simpl; autorewrite with eval_db.
  gridify.
  rewrite MmultHH.
  reflexivity.
Qed.

Lemma Rz_Rz_add : forall {dim} q θ θ', @Rz dim θ q; Rz θ' q ≡ Rz (θ + θ') q.
Proof.
  intros.
  unfold uc_equiv.
  simpl; autorewrite with eval_db. 
  gridify. 
  rewrite phase_mul.
  rewrite Rplus_comm. 
  reflexivity.
Qed.

Lemma Rz_0_id : forall {dim} q, Rz 0 q ≡ @ID dim q.
Proof.
  intros. 
  unfold uc_equiv.
  autorewrite with eval_db; simpl. 
  gridify.
  Qsimpl.
  reflexivity.
Qed.

Lemma CNOT_CNOT_id : forall {dim} m n, 
  m < dim -> n < dim -> m <> n -> (* easier to state with restrictions on m, n *)
  CNOT m n; CNOT m n ≡ @SKIP dim.
Proof. 
  intros dim m n Hm Hn Hneq. 
  unfold uc_equiv.
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  simpl.
  rewrite denote_SKIP by lia.
  rewrite Mmult_1_l by auto_wf.
  rewrite Mmult_assoc.
  rewrite 2!f_to_vec_CNOT by easy.
  rewrite update_index_eq, update_index_neq, update_twice_eq by easy.
  rewrite xorb_assoc, xorb_nilpotent, xorb_false_r.
  now rewrite update_same by easy.
Qed.

Lemma U_V_comm : forall {dim} (m n : nat) (U V : base_Unitary 1),
  m <> n ->
  @uapp1 _ dim U m; uapp1 V n ≡ uapp1 V n ; uapp1 U m. 
Proof.
  intros.
  unfold uc_equiv; simpl.
  dependent destruction U; dependent destruction V.
  unfold ueval_r.
  apply pad_A_B_commutes; auto with wf_db.
Qed.

Lemma U_CNOT_comm : forall {dim} (q n1 n2 : nat) (U : base_Unitary 1),
  q <> n1 ->
  q <> n2 ->
  @uapp1 _ dim U q ; CNOT n1 n2 ≡ CNOT n1 n2 ; uapp1 U q. 
Proof.
  intros.
  unfold uc_equiv; simpl.
  dependent destruction U.
  rewrite denote_cnot.
  unfold ueval_cnot, ueval_r.
  rewrite pad_A_ctrl_commutes; auto with wf_db.
Qed.

Lemma CNOT_CNOT_comm : forall {dim} (n1 n2 n1' n2' : nat),
  n1' <> n1 -> n1' <> n2 -> n2' <> n1 -> n2' <> n2 ->
  @CNOT dim n1 n2 ; CNOT n1' n2' ≡ CNOT n1' n2' ; CNOT n1 n2. 
Proof.
  intros.
  unfold uc_equiv; simpl.
  rewrite 2 denote_cnot.
  unfold ueval_cnot.
  rewrite pad_ctrl_ctrl_commutes; auto with wf_db.
Qed.

(* FIXME: Move *)

Lemma H_comm_Z : forall {dim} q, @H dim q; SQIR.Z q ≡ X q; H q.
Proof.
  intros.
  unfold uc_equiv.
  simpl.
  bdestruct (q <? dim); [|rewrite H_ill_typed by lia; now Msimpl].
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  simpl.
  rewrite !Mmult_assoc.
  f_to_vec_simpl.
  prep_matrix_equivalence.
  unfold scale, Mplus.
  intros i j Hi Hj.
  cbn [Nat.b2n Cpow].
  destruct (f q); cbn; rewrite ?Rmult_0_l, ?Rmult_1_l, ?Cexp_0, ?Cexp_PI;
  lca.
Qed.

(* FIXME: Move *)

Lemma X_comm_Rz : forall {dim} q a,
  @X dim q; Rz a q ≅ invert (Rz a q); X q.
Proof.
  intros.
  exists a.
  cbn.
  bdestruct (q <? dim); [|rewrite X_ill_typed by lia; now Msimpl].
  rewrite invert_Rz.
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  distribute_scale.
  rewrite !Mmult_assoc.
  f_to_vec_simpl.
  rewrite <- Cexp_add.
  f_equal.
  f_equal.
  destruct (f q); cbn; lra.
Qed.

Lemma X_comm_CNOT_control : forall {dim} m n,
  @X dim m; CNOT m n ≡ CNOT m n; X m; X n.
Proof.
  intros dim m n.
  unfold uc_equiv.
  simpl.
  bdestruct (n <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (m <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (n =? m); [rewrite CNOT_ill_typed by lia; now Msimpl|].
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  rewrite !Mmult_assoc.
  rewrite f_to_vec_CNOT by easy.
  rewrite !f_to_vec_X by easy.
  rewrite !update_index_neq, update_twice_neq, update_twice_eq by easy.
  rewrite update_index_eq.
  rewrite f_to_vec_CNOT by easy.
  rewrite update_index_eq, update_index_neq by lia.
  rewrite update_twice_neq by easy.
  now rewrite negb_xorb_r.
Qed.

Lemma X_comm_CNOT_target : forall {dim} m n,
  @X dim n; CNOT m n ≡ CNOT m n; X n.
Proof.
  intros dim m n.
  unfold uc_equiv.
  simpl.
  bdestruct (n <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (m <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (n =? m); [rewrite CNOT_ill_typed by lia; now Msimpl|].
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  rewrite !Mmult_assoc.
  rewrite f_to_vec_CNOT by easy.
  rewrite !f_to_vec_X, f_to_vec_CNOT by easy.
  rewrite !update_index_eq, update_index_neq by easy.
  now rewrite !update_twice_eq, negb_xorb_l.
Qed.

Lemma Rz_comm_H_CNOT_H : forall {dim} a q1 q2,
  @Rz dim a q2; H q2; CNOT q1 q2; H q2 ≡ H q2; CNOT q1 q2; H q2; Rz a q2.
Proof.
  intros dim a q1 q2.
  unfold uc_equiv. 
  simpl.
  bdestruct (q1 <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (q2 <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (q1 =? q2); [rewrite CNOT_ill_typed by lia; now Msimpl|].
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  rewrite !Mmult_assoc.
  rewrite f_to_vec_Rz, f_to_vec_H by easy.
  distribute_scale; distribute_plus; distribute_scale.
  rewrite f_to_vec_CNOT, f_to_vec_H by easy.
  rewrite update_index_eq, update_index_neq, xorb_false_l by easy.
  rewrite update_twice_eq.
  distribute_scale; distribute_plus; distribute_scale.
  rewrite 2!f_to_vec_CNOT, 3!f_to_vec_H by easy.
  rewrite !update_index_eq, !update_index_neq, !update_twice_eq by easy.
  rewrite xorb_false_l, xorb_true_l.
  distribute_scale; distribute_plus; distribute_scale.
  rewrite !f_to_vec_Rz, !update_index_eq by easy.
  prep_matrix_equivalence.
  cbn [b2R].
  unfold scale, Mplus.
  intros i j Hi Hj.
  C_field.
  destruct (f q1), (f q2); cbn [b2R];
  rewrite ?Rmult_0_l, ?Rmult_1_l, ?Cexp_0, ?Cexp_PI;
  lca.
Qed.

Lemma Rz_comm_CNOT_Rz_CNOT : forall {dim} a a' q1 q2,
  @Rz dim a q2; CNOT q1 q2; Rz a' q2; CNOT q1 q2 ≡ CNOT q1 q2; Rz a' q2; CNOT q1 q2; Rz a q2.
Proof.
  intros dim a a' q1 q2.
  unfold uc_equiv.
  simpl.
  bdestruct (q1 <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (q2 <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (q1 =? q2); [rewrite CNOT_ill_typed by lia; now Msimpl|].
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  rewrite !Mmult_assoc.
  f_to_vec_simpl.
  f_equal.
  rewrite <- 2!Cexp_add.
  f_equal.
  destruct (f q1), (f q2); cbn; lra.
Qed.

Lemma Rz_comm_CNOT : forall {dim} a q1 q2,
  @Rz dim a q1; CNOT q1 q2 ≡ CNOT q1 q2; Rz a q1.
Proof.
  intros dim a q1 q2.
  unfold uc_equiv. 
  simpl.
  bdestruct (q1 <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (q2 <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (q1 =? q2); [rewrite CNOT_ill_typed by lia; now Msimpl|].
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  rewrite !Mmult_assoc.
  f_to_vec_simpl.
  easy.
Qed.

Lemma CNOT_comm_CNOT_sharing_target : forall {dim} q1 q2 q3,
  @CNOT dim q1 q3; CNOT q2 q3 ≡ CNOT q2 q3; CNOT q1 q3.
Proof.
  intros dim q1 q2 q3.
  unfold uc_equiv. 
  simpl.
  bdestruct (q1 =? q2); [now subst|].
  bdestruct (q1 <? dim); [|rewrite (CNOT_ill_typed q1) by lia; now Msimpl].
  bdestruct (q2 <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (q3 <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (q1 =? q3); [rewrite (CNOT_ill_typed q1) by lia; now Msimpl|].
  bdestruct (q2 =? q3); [rewrite (CNOT_ill_typed q2) by lia; now Msimpl|].
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  rewrite !Mmult_assoc.
  f_to_vec_simpl.
  now rewrite 2!xorb_assoc, (xorb_comm (f q1)).
Qed.

Lemma CNOT_comm_CNOT_sharing_control : forall {dim} q1 q2 q3,
  @CNOT dim q1 q3; CNOT q1 q2 ≡ CNOT q1 q2; CNOT q1 q3.
Proof.
  intros dim q1 q2 q3.
  unfold uc_equiv. 
  simpl.
  bdestruct (q2 =? q3); [now subst|].
  bdestruct (q1 <? dim); [|rewrite (CNOT_ill_typed q1) by lia; now Msimpl].
  bdestruct (q2 <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (q3 <? dim); [|rewrite (CNOT_ill_typed _ q3) by lia; now Msimpl].
  bdestruct (q1 =? q3); [rewrite (CNOT_ill_typed q1 q3) by lia; now Msimpl|].
  bdestruct (q1 =? q2); [rewrite (CNOT_ill_typed q1 q2) by lia; now Msimpl|].
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  rewrite !Mmult_assoc.
  f_to_vec_simpl.
  now rewrite update_twice_neq by easy.
Qed.

Lemma CNOT_comm_H_CNOT_H : forall {dim} q1 q2 q3,
  q1 <> q3 ->
  @CNOT dim q1 q2; H q2; CNOT q2 q3; H q2 ≡ H q2; CNOT q2 q3; H q2; CNOT q1 q2.
Proof.
  intros dim q1 q2 q3 H13.
  unfold uc_equiv. 
  simpl.
  bdestruct (q1 <? dim); [|rewrite (CNOT_ill_typed q1) by lia; now Msimpl].
  bdestruct (q2 <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (q3 <? dim); [|rewrite (CNOT_ill_typed _ q3) by lia; now Msimpl].
  bdestruct (q1 =? q2); [rewrite (CNOT_ill_typed q1 q2) by lia; now Msimpl|].
  bdestruct (q2 =? q3); [rewrite (CNOT_ill_typed q2 q3) by lia; now Msimpl|].
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  rewrite !Mmult_assoc.
  f_to_vec_simpl.
  rewrite xorb_false_l, xorb_false_r, xorb_true_l, xorb_true_r.
  prep_matrix_equivalence.
  intros i j Hi Hj.
  unfold scale, Mplus.
  destruct (f q1), (f q2); cbn;
  rewrite Rmult_0_l, Rmult_1_l, Cexp_0, Cexp_PI;
  lca.
Qed.

Lemma H_swaps_CNOT : forall {dim} m n,
  @H dim m; H n; CNOT n m; H m; H n ≡ CNOT m n.
Proof.
  intros.
  unfold uc_equiv; simpl.
  bdestruct (n <? dim); [|rewrite !CNOT_ill_typed by lia; now Msimpl].
  bdestruct (m <? dim); [|rewrite !CNOT_ill_typed by lia; now Msimpl].
  bdestruct (n =? m); [rewrite !CNOT_ill_typed by lia; now Msimpl|].
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  rewrite !Mmult_assoc.
  rewrite f_to_vec_H by easy.
  distribute_scale; distribute_plus; distribute_scale.
  rewrite 2!f_to_vec_H by easy.
  rewrite 2!update_index_neq by easy.
  distribute_scale; distribute_plus; distribute_scale.
  rewrite 4!f_to_vec_CNOT by easy.
  rewrite update_index_neq, 5!update_index_eq,
    update_index_neq, update_index_eq,
    update_index_neq, update_index_eq,
    update_index_neq, update_index_eq by easy.
  cbn [xorb].
  rewrite 4!f_to_vec_H by easy.
  distribute_scale; distribute_plus; distribute_scale.
  rewrite !update_index_eq.
  rewrite !(update_twice_neq _ n m), !update_twice_eq by easy.
  cbn [b2R].
  rewrite Rmult_1_l, Rmult_0_l, Cexp_0, 2!Mscale_1_l.
  rewrite 4!f_to_vec_H by easy.
  rewrite !update_index_eq, !update_twice_eq.
  cbn [b2R].
  rewrite Rmult_1_l, Rmult_0_l, Cexp_0, 2!Mscale_1_l.
  rewrite f_to_vec_CNOT by easy.
  prep_matrix_equivalence.
  destruct (f n) eqn:efn, (f m) eqn:efm;
  cbn [b2R xorb];
  rewrite ?Rmult_1_l, ?Rmult_0_l, ?Cexp_0, ?Cexp_PI, ?Mscale_1_l;
  distribute_scale;
  rewrite (update_same _ _ _ (eq_sym efm)), !(update_twice_neq _ m n),
    (update_same _ _ _ (eq_sym efn)) by easy;
  intros i j Hi Hj;
  unfold scale, Mplus; cbn;
  C_field;
  lca.
Qed.

Lemma SWAP_extends_CNOT : forall {dim} a b c,
  a < dim -> b < dim -> c < dim ->
  a <> b -> b <> c -> a <> c ->
  @SWAP dim a b ; CNOT b c ; SWAP a b ≡ CNOT a c.
Proof.
  intros.
  eapply equal_on_basis_states_implies_equal; auto with wf_db.
  intro f.
  simpl uc_eval.
  rewrite !Mmult_assoc.
  rewrite f_to_vec_SWAP by auto.
  rewrite 2 f_to_vec_CNOT by auto.
  rewrite f_to_vec_SWAP by auto.
  rewrite fswap_simpl2.
  rewrite fswap_neq by auto.
  apply f_to_vec_eq.
  intros i Hi.
  bdestruct (i =? c); subst.
  rewrite update_index_eq.
  rewrite fswap_neq by auto.
  rewrite update_index_eq.
  reflexivity.
  rewrite update_index_neq by auto.
  bdestructΩ (i =? a); bdestructΩ (i =? b); subst.
  rewrite fswap_simpl1, update_index_neq by auto. 
  apply fswap_simpl2. 
  rewrite fswap_simpl2, update_index_neq by auto. 
  apply fswap_simpl1. 
  rewrite fswap_neq, update_index_neq by auto. 
  apply fswap_neq; auto.
Qed.


Lemma SWAP_symmetric : forall {dim} a b,
  @SWAP dim a b ≡ SWAP b a.
Proof.
  intros.
  unfold uc_equiv.
  bdestruct (a <? dim); [|rewrite !SWAP_ill_typed by lia; easy].
  bdestruct (b <? dim); [|rewrite !SWAP_ill_typed by lia; easy].
  bdestruct (a =? b); [rewrite !SWAP_ill_typed by lia; easy|].
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  rewrite 2!f_to_vec_SWAP by auto.
  apply f_to_vec_eq.
  intros i Hi.
  unfold fswap.
  bdestruct_all; reflexivity + lia.
Qed.

Lemma proj_Rz_comm : forall dim q n b k,
  proj q dim b × uc_eval (SQIR.Rz k n) = uc_eval (SQIR.Rz k n) × proj q dim b. 
Proof.
  intros dim q n b k.
  bdestruct (n <? dim); [|rewrite Rz_ill_typed by lia; now Msimpl].
  bdestruct (q <? dim); [|rewrite proj_ill_typed by lia; now Msimpl].
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  rewrite 2!Mmult_assoc.
  rewrite f_to_vec_Rz by auto.
  distribute_scale.
  destruct (bool_dec b (f q)).
  - rewrite f_to_vec_proj_eq by easy.
    now rewrite f_to_vec_Rz.
  - rewrite f_to_vec_proj_neq by easy.
    now Msimpl.
Qed.

Lemma proj_Rz : forall dim q b θ,
  uc_eval (SQIR.Rz θ q) × proj q dim b = Cexp (b2R b * θ) .* proj q dim b. 
Proof.
  intros dim q b θ.
  bdestruct (q <? dim); [|rewrite proj_ill_typed by lia; now Msimpl].
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros f.
  rewrite Mmult_assoc.
  distribute_scale.
  destruct (bool_dec b (f q)).
  - rewrite f_to_vec_proj_eq by easy.
    rewrite f_to_vec_Rz by easy.
    now subst.
  - rewrite f_to_vec_proj_neq by easy.
    now Msimpl.
Qed.

Lemma proj_CNOT_control : forall dim q m n b,
  (q <> n \/ m = n) ->
  proj q dim b × uc_eval (SQIR.CNOT m n) = uc_eval (SQIR.CNOT m n) × proj q dim b.
Proof.
  intros dim q m n b H.
  bdestruct (m =? n); [rewrite CNOT_ill_typed by lia; now Msimpl|].
  bdestruct (n <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (m <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (q =? m).
  - (* q = control *)
    subst. 
    apply equal_on_basis_states_implies_equal; [auto_wf..|].
    intros f.
    rewrite 2!Mmult_assoc.
    rewrite f_to_vec_CNOT by easy.
    destruct (bool_dec b (f m)).
    + rewrite 2!f_to_vec_proj_eq by (rewrite ?update_index_neq; easy).
      now rewrite f_to_vec_CNOT by easy.
    + rewrite 2!(f_to_vec_proj_neq) by (rewrite ?update_index_neq; easy).
      now Msimpl.
  - (* disjoint qubits *)
    bdestructΩ (q =? n).
    apply proj_commutes_2q_gate; assumption.
Qed.

Lemma proj_CNOT_target : forall dim f q n,
  proj q dim ((f q) ⊕ (f n)) × proj n dim (f n) × uc_eval (SQIR.CNOT n q) = proj n dim (f n) × uc_eval (SQIR.CNOT n q) × proj q dim (f q).
Proof.
  intros dim f q n.
  bdestruct (n =? q); [rewrite CNOT_ill_typed by lia; now Msimpl|].
  bdestruct (n <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  bdestruct (q <? dim); [|rewrite CNOT_ill_typed by lia; now Msimpl].
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros g.
  rewrite !Mmult_assoc.
  rewrite f_to_vec_CNOT by easy.
  destruct (bool_dec (f n) (g n)), (bool_dec (f q) (g q)).
  - rewrite f_to_vec_proj_eq, (f_to_vec_proj_eq g)
      by (rewrite ?update_index_neq; easy).
    rewrite f_to_vec_CNOT by easy.
    rewrite 2!f_to_vec_proj_eq; 
    rewrite ?update_index_eq, ?update_index_neq; try easy.
    now f_equal.
  - rewrite (f_to_vec_proj_neq g) by easy.
    Msimpl.
    rewrite f_to_vec_proj_eq by (rewrite ?update_index_neq; easy).
    apply f_to_vec_proj_neq; [easy|].
    rewrite update_index_eq.
    replace -> (f n).
    now destruct (f q), (g q), (g n).
  - rewrite (f_to_vec_proj_neq) by (rewrite ?update_index_neq; easy).
    rewrite (f_to_vec_proj_eq) by easy.
    rewrite f_to_vec_CNOT by easy.
    rewrite f_to_vec_proj_neq by (rewrite ?update_index_neq; easy).
    now Msimpl.
  - rewrite 2!f_to_vec_proj_neq by (rewrite ?update_index_neq; easy).
    now Msimpl.
Qed.
