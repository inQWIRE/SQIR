Require Import Setoid.
Require Import QuantumLib.Pad.
Require Export QuantumLib.Proportional.
Require Export SQIR.

Local Open Scope matrix_scope.
Local Open Scope ucom_scope.

(* Note: all the definitions in this file are restricted to the base_ucom
   type. To define the semantics using other gate sets, you must define a
   conversion function. See VOQC/RzQGateSet.v for an example. *)

(** Denotation of Unitaries **)

Definition ueval_r (dim n : nat) (U : base_Unitary 1) : Square (2^dim) :=
  match U with
  | U_R θ ϕ λ => pad_u dim n (rotation θ ϕ λ)
  end.

Definition ueval_cnot (dim m n: nat) : Square (2^dim) := pad_ctrl dim m n σx.

(** Denotation of ucoms **)

Fixpoint uc_eval {dim} (c : base_ucom dim) : Matrix (2^dim) (2^dim) :=
  match c with
  | c1 ; c2      => uc_eval c2 × uc_eval c1 
  | uapp1 U n    => ueval_r dim n U
  | uapp2 _ m n  => ueval_cnot dim m n
  | _            => Zero (* no 3-qubit gates in our denotation function *) 
  end.

(** Well-formedness **)

Lemma WF_ueval_r : forall dim n U, WF_Matrix (ueval_r dim n U).
Proof. intros. dependent destruction U. apply WF_pad. apply WF_rotation. Qed.  
  
Lemma WF_ueval_cnot : forall dim m n, WF_Matrix (ueval_cnot dim m n). 
Proof. intros dim m n. apply WF_pad_ctrl. apply WF_σx. Qed.  

Lemma WF_uc_eval : forall {dim} (c : base_ucom dim), WF_Matrix (uc_eval c).
Proof.
  intros dim c.
  induction c; simpl; auto with wf_db.
  apply WF_ueval_r.
  apply WF_ueval_cnot.
Qed.

#[export] Hint Resolve WF_ueval_r WF_ueval_cnot WF_uc_eval : wf_db.

(** Equivalence and Structural Rules **)

Definition uc_equiv {dim} (c1 c2 : base_ucom dim) := 
  uc_eval c1 = uc_eval c2.

Infix "≡" := uc_equiv : ucom_scope.

Lemma uc_equiv_refl : forall {dim} (c1 : base_ucom dim), 
  c1 ≡ c1. 
Proof. easy. Qed.

Lemma uc_equiv_sym : forall {dim} (c1 c2 : base_ucom dim), 
  c1 ≡ c2 -> c2 ≡ c1. 
Proof. easy. Qed.

Lemma uc_equiv_trans : forall {dim} (c1 c2 c3 : base_ucom dim), 
  c1 ≡ c2 -> c2 ≡ c3 -> c1 ≡ c3. 
Proof. intros dim c1 c2 c3 H12 H23. unfold uc_equiv. rewrite H12. easy. Qed.

Lemma useq_assoc : forall {dim} (c1 c2 c3 : base_ucom dim), 
  ((c1 ; c2) ; c3) ≡ (c1 ; (c2 ; c3)).
Proof.
  intros dim c1 c2 c3. 
  unfold uc_equiv. unfold uc_eval. simpl.
  rewrite Mmult_assoc. 
  reflexivity.
Qed.

Lemma useq_congruence : forall {dim} (c1 c1' c2 c2' : base_ucom dim),
    c1 ≡ c1' ->
    c2 ≡ c2' ->
    c1 ; c2 ≡ c1' ; c2'.
Proof.
  intros dim c1 c1' c2 c2' Ec1 Ec2.
  unfold uc_equiv; simpl.
  rewrite Ec1, Ec2.
  reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (base_ucom dim) (@uc_equiv dim)
  reflexivity proved by uc_equiv_refl
  symmetry proved by uc_equiv_sym
  transitivity proved by uc_equiv_trans
  as uc_equiv_rel.

Add Parametric Morphism (dim : nat) : (@useq base_Unitary dim)
  with signature (@uc_equiv dim) ==> (@uc_equiv dim) ==> (@uc_equiv dim) as useq_mor.
Proof. intros x y H x0 y0 H0. apply useq_congruence; easy. Qed.

Lemma test_rel : forall (dim : nat) (c1 c2 : base_ucom dim), c1 ≡ c2 -> c2 ≡ c1.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma test_mor : forall (dim : nat) (c1 c2 : base_ucom dim), c1 ≡ c2 -> c2 ; c1 ≡ c1 ; c1.
Proof. intros. rewrite H. reflexivity. Qed.

(* Equivalence up to a phase. *)

Definition uc_cong {dim : nat} (c1 c2 : base_ucom dim) :=
  uc_eval c1 ∝ uc_eval c2.
Infix "≅" := uc_cong (at level 70).

Lemma uc_cong_refl : forall {dim : nat} (c1 : base_ucom dim), 
  c1 ≅ c1.
Proof. intros. exists 0%R. rewrite Cexp_0. rewrite Mscale_1_l. reflexivity. Qed.

Lemma uc_cong_sym : forall {dim : nat} (c1 c2 : base_ucom dim), 
  c1 ≅ c2 -> c2 ≅ c1.
Proof.
  intros. inversion H.
  exists (Ropp x). rewrite H0. rewrite Mscale_assoc. rewrite <- Cexp_add.
  rewrite Rplus_comm.
  rewrite Rplus_opp_r. rewrite Cexp_0. rewrite Mscale_1_l. reflexivity.
Qed.

Lemma uc_cong_trans : forall {dim : nat} (c1 c2 c3 : base_ucom dim), 
  c1 ≅ c2 -> c2 ≅ c3 -> c1 ≅ c3.
Proof.
  intros. inversion H. inversion H0.
  exists (x + x0)%R. rewrite H1. rewrite H2.
  rewrite Mscale_assoc.
  rewrite Cexp_add. reflexivity.
Qed.

Lemma uc_seq_cong : forall {dim : nat} (c1 c1' c2 c2' : base_ucom dim),
    c1 ≅ c1' -> c2 ≅ c2' -> c1; c2 ≅ c1'; c2'.
Proof.
  intros dim c1 c1' c2 c2' Ec1 Ec2.
  inversion Ec1. inversion Ec2.
  exists (x + x0)%R. simpl.
  rewrite H. rewrite H0.
  rewrite Mscale_mult_dist_r.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_assoc.
  rewrite Cexp_add.
  reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (base_ucom dim) (@uc_cong dim)
  reflexivity proved by uc_cong_refl
  symmetry proved by uc_cong_sym
  transitivity proved by uc_cong_trans
  as uc_cong_rel.

Add Parametric Morphism (dim : nat) : (@useq base_Unitary dim) 
  with signature (@uc_cong dim) ==> (@uc_cong dim) ==> (@uc_cong dim) as useq_cong_mor.
Proof. intros. apply uc_seq_cong; assumption. Qed.

Lemma uc_equiv_cong : forall {dim : nat} (c c' : base_ucom dim), 
  (c ≡ c')%ucom -> c ≅ c'.
Proof.
  intros.
  exists 0. rewrite Cexp_0, Mscale_1_l. 
  apply H.
Qed.

Lemma uc_cong_assoc : forall {dim} (c1 c2 c3 : base_ucom dim), 
  ((c1 ; c2) ; c3) ≅ (c1 ; (c2 ; c3)).
Proof.
  intros. 
  apply uc_equiv_cong.
  apply useq_assoc.
Qed.

(** uc_eval is unitary iff well-typed **)
  
Lemma ueval_r_unitary : forall dim n U,
    (n < dim)%nat ->
    WF_Unitary (ueval_r dim n U).
Proof. 
  intros. dependent destruction U. apply pad_u_unitary. auto. apply rotation_unitary.
Qed.

Lemma ueval_cnot_unitary : forall dim m n,
    m <> n ->
    (m < dim)%nat ->
    (n < dim)%nat ->
    WF_Unitary (ueval_cnot dim m n).
Proof. intros. apply pad_ctrl_unitary; auto. apply σx_unitary. Qed.     

Lemma uc_eval_unitary : forall (dim : nat) (c : base_ucom dim),
    uc_well_typed c -> WF_Unitary (uc_eval c).
Proof.
  intros dim c H.
  unfold WF_Unitary.
  split. apply WF_uc_eval.
  induction c; try dependent destruction u.
  - inversion H; subst.
    simpl. Msimpl. rewrite <- Mmult_assoc. rewrite (Mmult_assoc (_)†).
    rewrite IHc2; trivial. Msimpl.
    rewrite IHc1; easy.
  - inversion H; subst.
    simpl. destruct (ueval_r_unitary dim n (U_R r r0 r1) H1) as [_ UU].
    assumption.
  - inversion H; subst.
    simpl. destruct (ueval_cnot_unitary dim n n0 H5 H3 H4) as [_ UU].
    assumption.
Qed.

Lemma WT_if_nonzero : forall (dim : nat) (c : base_ucom dim),
  uc_eval c <> Zero -> uc_well_typed c.
Proof.
  intros dim u.
  induction u; intros H; try dependent destruction u.
  - simpl in *.
    constructor.
    + apply IHu1.
      intros F. rewrite F in *.
      rewrite Mmult_0_r in H.
      contradiction.
    + apply IHu2.
      intros F. rewrite F in *.
      rewrite Mmult_0_l in H.
      contradiction.
  - simpl in *.
    unfold pad_u, pad in H.
    bdestruct (n + 1 <=? dim); try contradiction. 
    constructor; lia.
  - simpl in *. 
    unfold ueval_cnot, pad_ctrl, pad in H.
    bdestruct (n <? n0). 
    + bdestruct (n + (1 + (n0 - n - 1) + 1) <=? dim); try contradiction.
      constructor; lia.
    + bdestruct (n0 <? n); try contradiction.
      bdestruct (n0 + (1 + (n - n0 - 1) + 1) <=? dim); try contradiction.
      constructor; lia.
Qed.

(* Now we get bidirectionality for free! *)

Lemma uc_eval_unitary_iff : forall (dim : nat) (c : base_ucom dim),
    uc_well_typed c <-> WF_Unitary (uc_eval c).
Proof.
  split.
  - apply uc_eval_unitary.
  - intros H.
    apply WT_if_nonzero.
    intros F.
    rewrite F in H.
    apply zero_not_unitary in H.
    easy.
Qed.

Lemma uc_eval_nonzero_iff : forall (dim : nat) (c : base_ucom dim),
  uc_eval c <> Zero <-> uc_well_typed c.
Proof.
  split.
  - apply WT_if_nonzero.
  - intros H.
    intros F.
    apply uc_eval_unitary in H.
    rewrite F in H.
    apply zero_not_unitary in H.
    easy.
Qed.

(* This alternate form is also useful. *)
Lemma uc_eval_zero_iff : forall (dim : nat) (c : base_ucom dim),
  uc_eval c = Zero <-> not (uc_well_typed c).
Proof.
  split; intros H.
  - (* easy direction, implied by previous lemma *)
    rewrite <- uc_eval_nonzero_iff. 
    intros contra. 
    contradict contra. 
    assumption.
  - (* slightly more annoying direction, not implied by the previous lemma *)
    induction c. 
    assert (HWT: not ((uc_well_typed c1) /\ (uc_well_typed c2))).
    { intro contra.
      destruct contra.
      assert (uc_well_typed (c1; c2)) by (constructor; assumption).
      contradict H. assumption. }
    apply Classical_Prop.not_and_or in HWT.
    simpl; destruct HWT as [HWT | HWT]. 
    apply IHc1 in HWT. rewrite HWT. Msimpl_light; reflexivity.
    apply IHc2 in HWT. rewrite HWT. Msimpl_light; reflexivity.
    assert (HWT: (not (n < dim)%nat)). 
    { intro contra.
      assert (@uc_well_typed _ dim (uapp1 u n)) by (constructor; assumption).
      contradict H. assumption. }
    dependent destruction u.
    simpl; unfold pad_u, pad.
    bdestructΩ (n + 1 <=? dim); reflexivity.
    assert (HWT: (not ((n < dim) /\ (n0 < dim) /\ (n <> n0)))%nat). 
    { intro contra.
      destruct contra. destruct H1.
      assert (@uc_well_typed _ dim (uapp2 u n n0)) by (constructor; assumption).
      contradict H. assumption. }
    dependent destruction u.
    simpl; unfold ueval_cnot, pad_ctrl, pad;
    bdestruct (n <? n0); bdestruct (n0 <? n); try lia; try reflexivity.
    apply Classical_Prop.not_and_or in HWT.
    destruct HWT as [HWT | HWT].
    bdestructΩ (n + (1 + (n0 - n - 1) + 1) <=? dim); reflexivity.
    apply Classical_Prop.not_and_or in HWT.
    destruct HWT as [HWT | HWT].
    bdestructΩ (n + (1 + (n0 - n - 1) + 1) <=? dim); reflexivity.
    bdestructΩ (n + (1 + (n0 - n - 1) + 1) <=? dim); reflexivity.
    bdestructΩ (n0 + (1 + (n - n0 - 1) + 1) <=? dim); reflexivity.
    inversion u.
Qed.

(** Proofs About Standard Gates **)

Local Close Scope R_scope.

Lemma uc_well_typed_H : forall dim n, n < dim <-> uc_well_typed (@H dim n).
Proof. 
  intros. split; intros H.
  constructor; assumption. 
  inversion H; subst; assumption. 
Qed.

Lemma uc_well_typed_X : forall dim n, n < dim <-> uc_well_typed (@X dim n).
Proof. 
  intros. split; intros H.
  constructor; assumption. 
  inversion H; subst; assumption. 
Qed.

Lemma uc_well_typed_Y : forall dim n, n < dim <-> uc_well_typed (@Y dim n).
Proof. 
  intros. split; intros H.
  constructor; assumption. 
  inversion H; subst; assumption. 
Qed.

Lemma uc_well_typed_Z : forall dim n, n < dim <-> uc_well_typed (@Z dim n).
Proof. 
  intros. split; intros H.
  constructor; assumption. 
  inversion H; subst; assumption. 
Qed.

Lemma uc_well_typed_ID : forall dim n, n < dim <-> uc_well_typed (@ID dim n).
Proof. 
  intros. split; intros H.
  constructor; assumption. 
  inversion H; subst; assumption. 
Qed.

Lemma uc_well_typed_Rx : forall dim θ n, n < dim <-> uc_well_typed (@Rx dim θ n).
Proof. 
  intros. split; intros H.
  constructor; assumption. 
  inversion H; subst; assumption. 
Qed.

Lemma uc_well_typed_Ry : forall dim θ n, n < dim <-> uc_well_typed (@Ry dim θ n).
Proof. 
  intros. split; intros H.
  constructor; assumption. 
  inversion H; subst; assumption. 
Qed.

Lemma uc_well_typed_Rz : forall dim θ n, n < dim <-> uc_well_typed (@Rz dim θ n).
Proof. 
  intros. split; intros H.
  constructor; assumption. 
  inversion H; subst; assumption. 
Qed.

Lemma uc_well_typed_CNOT : forall dim m n, 
  (m < dim /\ n < dim /\ m <> n) <-> uc_well_typed (@CNOT dim m n).
Proof. 
  intros. split; intros H.
  destruct H as [H1 [H2 H3]]. constructor; assumption. 
  split; try split; inversion H; subst; assumption. 
Qed.

Lemma uc_well_typed_SWAP : forall dim m n, 
  (m < dim /\ n < dim /\ m <> n) <-> uc_well_typed (@SWAP dim m n).
Proof. 
  intros. split; intros H.
  destruct H as [H1 [H2 H3]].
  repeat constructor; auto.
  inversion H; subst.
  inversion H2; subst.
  clear - H4 H5.
  apply uc_well_typed_CNOT in H4 as [? [? ?]].
  apply uc_well_typed_CNOT in H5 as [? [? ?]]. 
  auto.
Qed.

(* In general, we won't want to interact directly with the 'rotation' matrix. *)

Lemma denote_H : forall dim n, uc_eval (H n) = pad_u dim n hadamard.
Proof.
  intros. unfold uc_eval; simpl.
  rewrite hadamard_rotation.
  reflexivity.
Qed.

Lemma denote_X : forall dim n, uc_eval (X n) = pad_u dim n σx.
Proof.
  intros. unfold uc_eval; simpl.
  rewrite pauli_x_rotation.
  reflexivity.
Qed.

Lemma denote_Y : forall dim n, uc_eval (Y n) = pad_u dim n σy.
Proof.
  intros. unfold uc_eval; simpl.
  rewrite pauli_y_rotation.
  reflexivity.
Qed.

Lemma denote_Z : forall dim n, uc_eval (Z n) = pad_u dim n σz.
Proof.
  intros. unfold uc_eval; simpl.
  rewrite pauli_z_rotation.
  reflexivity.
Qed.

Lemma denote_ID : forall dim n, uc_eval (ID n) = pad_u dim n (I 2).
Proof.
  intros. unfold uc_eval; simpl.
  rewrite I_rotation.
  reflexivity.
Qed.

Lemma denote_SKIP : forall dim, dim > 0 -> uc_eval SKIP = I (2 ^ dim).
Proof.
  intros. unfold uc_eval; simpl.
  unfold pad_u, pad.
  rewrite I_rotation. 
  gridify.
  reflexivity.
Qed.

Lemma denote_Rx : forall dim θ n, uc_eval (Rx θ n) = pad_u dim n (x_rotation θ).
Proof.
  intros. unfold uc_eval; simpl.
  rewrite <- Rx_rotation.
  unfold pad_u, pad.
  gridify.
  apply f_equal2; try reflexivity.
  apply f_equal2; try reflexivity.
  unfold rotation. 
  solve_matrix.
  replace (-(PI/2))%R with (-(2*PI) + 3*PI/2)%R by lra.
  autorewrite with Cexp_db. lca.
  replace (-(PI/2))%R with (-(2*PI) + 3*PI/2)%R by lra.
  autorewrite with Cexp_db. lca.
Qed.

Lemma denote_Ry : forall dim θ n, uc_eval (Ry θ n) = pad_u dim n (y_rotation θ).
Proof.
  intros. unfold uc_eval; simpl.
  rewrite Ry_rotation.
  reflexivity.
Qed.

Lemma denote_Rz : forall dim θ n, uc_eval (Rz θ n) = pad_u dim n (phase_shift θ).
Proof.
  intros. unfold uc_eval; simpl.
  rewrite phase_shift_rotation.
  reflexivity.
Qed.

Lemma denote_cnot : forall dim m n, 
  uc_eval (CNOT m n) = ueval_cnot dim m n.
Proof. easy. Qed.

Definition ueval_swap (dim m n: nat) : Square (2^dim) :=
  if (m <? n) then
      @pad (1+(n-m-1)+1) m dim 
             ( ∣0⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ ∣0⟩⟨0∣ .+
               ∣0⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ ∣1⟩⟨0∣ .+
               ∣1⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ ∣0⟩⟨1∣ .+
               ∣1⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ ∣1⟩⟨1∣ )
  else if (n <? m) then
      @pad (1+(m-n-1)+1) n dim 
             ( ∣0⟩⟨0∣ ⊗ I (2^(m-n-1)) ⊗ ∣0⟩⟨0∣ .+
               ∣0⟩⟨1∣ ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨0∣ .+
               ∣1⟩⟨0∣ ⊗ I (2^(m-n-1)) ⊗ ∣0⟩⟨1∣ .+
               ∣1⟩⟨1∣ ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨1∣ )
  else
      Zero.

(* auxiliary lemmas for denote_swap *)
Lemma Mplus_swap_first_and_last : forall {m n} (A B C D : Matrix m n), 
  A .+ B .+ (C .+ D) = D .+ B .+ C .+ A.
Proof. intros. lma. Qed.

Lemma Mplus_swap_mid : forall {m n} (A B C D : Matrix m n), 
  A .+ B .+ C .+ D = A .+ C .+ B .+ D.
Proof. intros. lma. Qed.

Lemma denote_swap : forall dim m n,
  @uc_eval dim (SWAP m n) = ueval_swap dim m n.
Proof.
  intros.
  simpl; unfold ueval_swap. 
  unfold ueval_cnot, pad_ctrl, pad.
  gridify.
  - Qsimpl.
    rewrite Mplus_swap_first_and_last.
    reflexivity. 
  - Qsimpl.
    rewrite Mplus_swap_first_and_last.
    rewrite Mplus_swap_mid.
    reflexivity.
Qed.

Lemma denote_swap_alt : forall dim a b, uc_eval (SQIR.SWAP a b) = pad_swap dim a b.
Proof.
  intros. simpl.
  repeat rewrite denote_cnot.
  rewrite <- Mmult_assoc.
  reflexivity.
Qed.

Lemma unfold_ueval_cnot : forall dim m n, 
  ueval_cnot dim m n = 
    if (m <? n) then
      @pad (1+(n-m-1)+1) m dim (∣1⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ I 2)
    else if (n <? m) then
      @pad (1+(m-n-1)+1) n dim (σx ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨1∣ .+ I 2 ⊗ I (2^(m-n-1)) ⊗ ∣0⟩⟨0∣)
    else
      Zero.
Proof. easy. Qed.

Lemma unfold_ueval_r : forall dim n (U : base_Unitary 1), 
  ueval_r dim n U = match U with
                    | U_R θ ϕ λ => pad_u dim n (rotation θ ϕ λ)
                    end.
Proof. easy. Qed.

Lemma unfold_pad : forall n start dim A, 
  @pad n start dim A = 
  if start + n <=? dim then I (2^start) ⊗ A ⊗ I (2^(dim - (start + n))) else Zero.
Proof. easy. Qed.

Lemma unfold_pad_u : forall dim n A, 
  pad_u dim n A = 
  if n + 1 <=? dim then I (2^n) ⊗ A ⊗ I (2^(dim - (n + 1))) else Zero.
Proof. easy. Qed.

Lemma unfold_ueval_swap : forall dim m n, 
  ueval_swap dim m n = 
    if (m <? n) then
      @pad (1+(n-m-1)+1) m dim 
             ( ∣0⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ ∣0⟩⟨0∣ .+
               ∣0⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ ∣1⟩⟨0∣ .+
               ∣1⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ ∣0⟩⟨1∣ .+
               ∣1⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ ∣1⟩⟨1∣ )
    else if (n <? m) then
       @pad (1+(m-n-1)+1) n dim 
             ( ∣0⟩⟨0∣ ⊗ I (2^(m-n-1)) ⊗ ∣0⟩⟨0∣ .+
               ∣0⟩⟨1∣ ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨0∣ .+
               ∣1⟩⟨0∣ ⊗ I (2^(m-n-1)) ⊗ ∣0⟩⟨1∣ .+
               ∣1⟩⟨1∣ ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨1∣ )
    else
      Zero.
Proof. easy. Qed.

#[export] Hint Rewrite denote_H denote_X denote_Y denote_Z denote_ID denote_SKIP 
             denote_Rx denote_Ry denote_Rz denote_cnot denote_swap : eval_db.
#[export] Hint Rewrite unfold_ueval_r unfold_ueval_cnot unfold_ueval_swap unfold_pad unfold_pad_u : eval_db.

Global Opaque H X Y Z ID Rx Ry Rz CNOT SWAP.

(* Some unit tests *)

Lemma eval_H : uc_eval ((H 0) : base_ucom 1) = hadamard.
Proof.
  simpl. autorewrite with eval_db.
  simpl. Msimpl. reflexivity.
Qed.

Lemma eval_HHpar : uc_eval ((H 0; H 1) : base_ucom 2) = hadamard ⊗ hadamard.
Proof.
  simpl. autorewrite with eval_db.
  simpl. restore_dims. Msimpl. 
  restore_dims. Msimpl. 
  reflexivity.
Qed.

Lemma eval_HHseq : uc_eval ((H 0; H 0) : base_ucom 2) = I 4.
Proof.
  simpl. autorewrite with eval_db.
  simpl. Msimpl. solve_matrix.
Qed.

Lemma eval_CNOT : uc_eval ((CNOT 0 1) : base_ucom 2) = cnot.
Proof.
  simpl. autorewrite with eval_db.
  simpl. Msimpl. solve_matrix.
Qed.
