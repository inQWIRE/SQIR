Require Export SQIRE.
Require Export QWIRE.Quantum.
Require Import Setoid.

Local Open Scope matrix_scope.
Local Open Scope ucom_scope.

(** Denotation of Unitaries **)

Definition pad {n} (start dim : nat) (A : Square (2^n)) : Square (2^dim) :=
  if start + n <=? dim then I (2^start) ⊗ A ⊗ I (2^(dim - n - start)) else Zero.

Lemma WF_pad : forall n start dim (A : Square (2^n)),
  WF_Matrix A ->
  WF_Matrix (pad start dim A).
Proof.
  intros n start dim A WFA. unfold pad.
  bdestruct (start + n <=? dim); auto with wf_db.
Qed.  

(* k must be 1, but dependent types... *)
Definition ueval1 {k} (dim n : nat) (u : Unitary k) : Square (2^dim) :=
  @pad 1 n dim
  match u with  
  | U_H         => hadamard 
  | U_X         => σx
  | U_Y         => σy
  | U_Z         => σz
  | U_R ϕ       => phase_shift ϕ
  | _           => Zero
  end.

(* Restriction: m <> n and m, n < dim *)
Definition ueval_cnot (dim m n: nat) : Square (2^dim) :=
  if (m <? n) then
    @pad (1+(n-m-1)+1) m dim (∣1⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I (2^(n-m)))
  else if (n <? m) then
    @pad (1+(m-n-1)+1) n dim (σx ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨1∣ .+ I (2^(m-n)) ⊗ ∣0⟩⟨0∣)
  else
    Zero.

Definition ueval {n} (dim : nat) (u : Unitary n) (l : list nat) : Square (2^dim) :=
  match n, l with
  | 1, [i]   => ueval1 dim i u
  | 2, i::[j] => ueval_cnot dim i j
  | _, _     => Zero
  end.

(** Denotation of ucoms **)

Fixpoint uc_eval (dim : nat) (c : ucom) : Matrix (2^dim) (2^dim) :=
  match c with
  | uskip    => I (2^dim)
  | uapp u l => ueval dim u l
  | c1 ; c2  => uc_eval dim c2 × uc_eval dim c1 
  end.

(** Well-formedness **)

Lemma WF_ueval1 : forall dim n (u : Unitary 1), WF_Matrix (ueval1 dim n u).
Proof.
  intros dim n u.
  apply WF_pad.
  destruct u; auto with wf_db.
Qed.  
  
Lemma WF_ueval_cnot : forall dim m n, WF_Matrix (ueval_cnot dim m n). 
Proof.
  intros dim m n.
  unfold ueval_cnot.
  bdestruct (m <? n); [|bdestruct (n <? m)];
    try apply WF_pad; unify_pows_two; auto 10 with wf_db.    
Qed.  

Lemma WF_ueval : forall n dim (u : Unitary n) l, WF_Matrix (ueval dim u l).
Proof.
  intros n dim u l.
  destruct n as [|[|[|n']]]; simpl; auto with wf_db.
  - destruct l as [|i [| j l]]; simpl; auto with wf_db.
    apply WF_ueval1.
  - destruct l as [|i [| j [| k l]]]; simpl; auto with wf_db.
    apply WF_ueval_cnot.
Qed.  

Lemma WF_uc_eval : forall dim c, WF_Matrix (uc_eval dim c).
Proof.
  intros dim c.
  induction c; simpl; auto with wf_db.
  apply WF_ueval.
Qed.

Hint Resolve WF_pad WF_ueval1 WF_ueval_cnot WF_ueval WF_uc_eval : wf_db.


(* Some unit tests *)

Lemma eval_H : uc_eval 1 (H 0) = hadamard.
Proof.
  simpl. unfold ueval1, pad. (* have these automatically simplify *)
  simpl. Msimpl. reflexivity.
Qed.

Lemma eval_HHpar : uc_eval 2 (H 0; H 1) = hadamard ⊗ hadamard.
Proof.
  simpl. unfold ueval1, pad. (* have these automatically simplify *)
  simpl. restore_dims.  Msimpl. 
  restore_dims. Msimpl. 
  reflexivity.
Qed.

Lemma eval_HHseq : uc_eval 2 (H 0; H 0) = I 4.
Proof.
  simpl. unfold ueval1, pad. (* have these automatically simplify *)
  simpl. Msimpl. solve_matrix.
Qed.

Lemma eval_CNOT : uc_eval 2 (CNOT 0 1) = cnot.
Proof.
  unfold uc_eval. simpl.
  simpl. unfold ueval_cnot, pad. (* have these automatically simplify *)
  simpl. Msimpl. solve_matrix.
Qed.

(** Equivalence and Structural Rules **)

(* Precondition about typing? *)
Definition uc_equiv (c1 c2 : ucom) := forall dim, uc_eval dim c1 = uc_eval dim c2.

Infix "≡" := uc_equiv : ucom_scope.

Lemma uc_equiv_refl : forall c1, c1 ≡ c1. 
Proof. easy. Qed.

Lemma uc_equiv_sym : forall c1 c2, c1 ≡ c2 -> c2 ≡ c1. 
Proof. easy. Qed.

Lemma uc_equiv_trans : forall c1 c2 c3, c1 ≡ c2 -> c2 ≡ c3 -> c1 ≡ c3. 
Proof. intros c1 c2 c3 H12 H23 dim. rewrite H12. easy. Qed.

Lemma useq_assoc : forall c1 c2 c3, ((c1 ; c2) ; c3) ≡ (c1 ; (c2 ; c3)).
Proof.
  intros c1 c2 c3 dim. simpl.
  rewrite Mmult_assoc. easy.
Qed.

Lemma useq_congruence : forall c1 c1' c2 c2',
    c1 ≡ c1' ->
    c2 ≡ c2' ->
    c1 ; c2 ≡ c1' ; c2'.
Proof.
  intros c1 c1' c2 c2' Ec1 Ec2 dim.
  simpl.
  rewrite Ec1, Ec2.
  reflexivity.
Qed.

Add Relation ucom uc_equiv 
  reflexivity proved by uc_equiv_refl
  symmetry proved by uc_equiv_sym
  transitivity proved by uc_equiv_trans
  as uc_equiv_rel.

Add Morphism useq 
  with signature (@uc_equiv) ==> (@uc_equiv) ==> (@uc_equiv) as useq_mor.
Proof. intros x y H x0 y0 H0. apply useq_congruence; easy. Qed.

Lemma test_rel : forall c1 c2, c1 ≡ c2 -> c2 ≡ c1.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma test_mor : forall c1 c2, c1 ≡ c2 -> c2 ; c1 ≡ c1 ; c1.
Proof. intros. rewrite H. reflexivity. Qed.

(** uc_eval is unitary iff well-typed **)

Lemma pad_unitary : forall n (u : Square (2^n)) start dim,
    (start + n <= dim)%nat -> 
    WF_Unitary u ->
    WF_Unitary (pad start dim u).
Proof.
  intros n u start dim B [WF U].
  split. apply WF_pad; auto.
  unfold pad.
  bdestructΩ (start + n <=? dim).
  restore_dims_strong.
  setoid_rewrite kron_adjoint.
  restore_dims_strong. Msimpl.
  rewrite U.
  Msimpl.
  unify_matrices.
Qed.
  
Lemma ueval1_unitary : forall dim n (u : Unitary 1),
    (n < dim)%nat ->
    WF_Unitary (ueval1 dim n u).
Proof.
  intros dim n u H.
  unfold ueval1.
  apply pad_unitary. lia.
  dependent destruction u.
  - apply H_unitary.
  - apply σx_unitary.
  - apply σy_unitary.
  - apply σz_unitary.
  - apply phase_unitary.
Qed.  

Lemma ueval_cnot_unitary : forall dim m n,
    m <> n ->
    (m < dim)%nat ->
    (n < dim)%nat ->
    WF_Unitary (ueval_cnot dim m n).
Proof.
  intros dim m n NE Lm Ln.
  unfold ueval_cnot.
  bdestruct (m <? n).
  - apply pad_unitary. lia.
    split. unify_pows_two; auto with wf_db.
    restore_dims.
    rewrite Mplus_adjoint.
    Msimpl.
    restore_dims.
    rewrite kron_adjoint.
    Msimpl.
    restore_dims_strong.
    rewrite Mmult_plus_distr_l.
    rewrite 2 Mmult_plus_distr_r.
    rewrite kron_assoc.
    restore_dims_strong.
    Msimpl.
    unify_pows_two.
    rewrite Nat.sub_add by lia.
    remember (I (2 ^ (n - m - 1)) ⊗ σx) as A.
    gen A. unify_pows_two. rewrite Nat.sub_add by lia. intros A EA.
    restore_dims_strong.
    rewrite 2 kron_mixed_product.
    replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2)%nat by solve_matrix.
    replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2)%nat by solve_matrix.
    replace (∣1⟩⟨1∣ × ∣1⟩⟨1∣) with (∣1⟩⟨1∣) by solve_matrix.
    replace (∣0⟩⟨0∣ × ∣0⟩⟨0∣) with (∣0⟩⟨0∣) by solve_matrix.
    rewrite 2 kron_0_l.
    replace (σx × σx) with (I 2) by solve_matrix.
    Msimpl.
    unify_pows_two.
    rewrite Nat.sub_add by lia.
    (* For some reason I can't rewrite with Mplus_0_l or r here, so manually... *)
    match goal with
      |- ?A = ?B => replace A with (∣1⟩⟨1∣ ⊗ I (2 ^ (n - m)) .+ ∣0⟩⟨0∣ ⊗ I (2 ^ (n - m)))
    end.
    2:{ 
    prep_matrix_equality. unfold Mplus.
    unfold Zero. rewrite Cplus_0_l, Cplus_0_r.
    reflexivity.
    }
    rewrite <- kron_plus_distr_r.
    replace (∣1⟩⟨1∣ .+ ∣0⟩⟨0∣) with (I 2) by solve_matrix.
    Msimpl.
    unify_matrices.
  - bdestructΩ (n <? m). clear H NE.
    apply pad_unitary. lia.
    split.
    { unify_pows_two.
      replace ((m - n - 1 + 1 + 1))%nat with (S (m - n - 1 + 1))%nat by lia.
      auto with wf_db.
    }
    restore_dims.
    rewrite Mplus_adjoint.
    Msimpl.
    restore_dims.
    rewrite kron_adjoint.
    Msimpl.
    restore_dims_strong.
    rewrite Mmult_plus_distr_l.
    rewrite 2 Mmult_plus_distr_r.
    Msimpl.
    remember (σx ⊗ I (2 ^ (m - n - 1))) as A.
    gen A. unify_pows_two. replace (S (m - n - 1)) with (m - n)%nat by lia. intros A EA.
    restore_dims_strong.
    repeat rewrite kron_mixed_product.
    replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2)%nat by solve_matrix.
    replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2)%nat by solve_matrix.
    replace (∣1⟩⟨1∣ × ∣1⟩⟨1∣) with (∣1⟩⟨1∣) by solve_matrix.
    replace (∣0⟩⟨0∣ × ∣0⟩⟨0∣) with (∣0⟩⟨0∣) by solve_matrix.
    replace (σx × σx) with (I 2) by solve_matrix.
    rewrite 2 kron_0_r.
    Msimpl.
    unify_pows_two.
    rewrite Nat.sub_add by lia.
    rewrite Mplus_0_r.
    rewrite Mplus_0_l.
    replace (S (m - n - 1)) with (m - n)%nat by lia.
    restore_dims_strong.
    setoid_rewrite <- kron_plus_distr_l.
    replace (∣1⟩⟨1∣ .+ ∣0⟩⟨0∣) with (I 2) by solve_matrix.
    Msimpl.
    unify_matrices.
Qed.  

Lemma uc_eval_unitary : forall (dim : nat) (u : ucom),
    uc_well_typed dim u -> WF_Unitary (uc_eval dim u).
Proof.
  intros dim u H.
  unfold WF_Unitary.
  split. apply WF_uc_eval.
  induction u.
  - simpl. Msimpl. reflexivity.
  - inversion H; subst.
    simpl. Msimpl. rewrite <- Mmult_assoc. rewrite (Mmult_assoc (_)†).
    rewrite IHu2; trivial. Msimpl.
    rewrite IHu1; easy.
  - dependent destruction H.
    destruct l as [|a [|b [|]]]; try solve [inversion u].
    + simpl. destruct (ueval1_unitary dim a u) as [_ UU].
      specialize (H0 _ (or_introl eq_refl)); trivial.
      assumption.
    + simpl. destruct (ueval_cnot_unitary dim a b) as [_ UU].
      inversion H1; subst.
      intros F. apply H3. subst. constructor. auto.
      specialize (H0 _ (or_introl eq_refl)); trivial.
      specialize (H0 _ (or_intror (or_introl eq_refl))); trivial.
      assumption.
Qed.

Lemma WT_if_nonzero : forall (dim : nat) (u : ucom),
  uc_eval dim u <> Zero -> uc_well_typed dim u.
Proof.
  intros dim u.
  induction u; intros H.
  - constructor.
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
  - destruct n as [|[|[|]]]; try solve [inversion u].
    + simpl in *.
      destruct l as [|a [|b[|]]]; try contradiction.
      unfold ueval1, pad in H.
      bdestruct (a + 1 <=? dim).
      constructor; trivial.
      unfold in_bounds. intros x I. simpl in I. inversion I. lia.
      easy.
      constructor; auto. constructor.
      contradiction.
    + simpl in *.
      destruct l as [|a [|b[|]]]; try contradiction.
      unfold ueval_cnot, pad in H.
      bdestruct (a <? b).
      * bdestruct (a + (1 + (b - a - 1) + 1) <=? dim); try contradiction.
        constructor; trivial.
        unfold in_bounds. intros x I. simpl in I. inversion I. lia.
        inversion H2. lia. contradiction.
        constructor; auto.
        simpl; intros F.
        inversion F. lia.
        easy.
        constructor; auto; constructor.
      * bdestructΩ (b <? a); try contradiction. clear H0.
        bdestruct (b + (1 + (a - b - 1) + 1) <=? dim); try contradiction.
        constructor; trivial.
        unfold in_bounds. intros x I. simpl in I. inversion I. lia.
        inversion H2. lia. contradiction.
        constructor; auto.
        simpl; intros F.
        inversion F. lia.
        easy.
        constructor; auto; constructor.
Qed.

(* Now we get bidirectionality for free! *)

Lemma uc_eval_unitary_iff : forall (dim : nat) (u : ucom),
    uc_well_typed dim u <-> WF_Unitary (uc_eval dim u).
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

Lemma uc_eval_nonzero_iff : forall (dim : nat) (u : ucom),
  uc_eval dim u <> Zero <-> uc_well_typed dim u.
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

(** Proofs about high-level functions over unitary programs **)

Local Close Scope C_scope.
Local Close Scope R_scope.

Lemma reverse_u_correct : forall (dim : nat) (u : ucom),
  (uc_eval dim u)† = uc_eval dim (reverse_u u).
Proof.
  intros.
  induction u.
  - simpl. Msimpl. reflexivity.
  - simpl. Msimpl. rewrite IHu1. rewrite IHu2. reflexivity.
  - simpl. 
    destruct u;
    destruct l as [|a [|b [|]]]; simpl; try apply zero_adjoint_eq;
    unfold ueval1, ueval_cnot, pad.
    + bdestruct (a + 1 <=? dim); try apply zero_adjoint_eq;
      repeat setoid_rewrite kron_adjoint; Msimpl. 
      setoid_rewrite hadamard_sa. reflexivity.
    + bdestruct (a + 1 <=? dim); try apply zero_adjoint_eq;
      repeat setoid_rewrite kron_adjoint; Msimpl. 
      setoid_rewrite σx_sa. reflexivity.
    + bdestruct (a + 1 <=? dim); try apply zero_adjoint_eq;
      repeat setoid_rewrite kron_adjoint; Msimpl. 
      setoid_rewrite σy_sa. reflexivity.
    + bdestruct (a + 1 <=? dim); try apply zero_adjoint_eq;
      repeat setoid_rewrite kron_adjoint; Msimpl. 
      setoid_rewrite σz_sa. reflexivity.
    + bdestruct (a + 1 <=? dim); try apply zero_adjoint_eq;
      repeat setoid_rewrite kron_adjoint; Msimpl. 
      reflexivity.
    + bdestruct (a <? b).
      * bdestruct (a + (1 + (b - a - 1) + 1) <=? dim); try apply zero_adjoint_eq.
        repeat setoid_rewrite kron_adjoint; Msimpl.
        replace (2 ^ (1 + (b - a - 1) + 1)) with (2 * 2 ^ (b - a - 1) * 2) by unify_pows_two.
        rewrite Mplus_adjoint.
        repeat setoid_rewrite kron_adjoint; Msimpl.
        replace (2 * 2 ^ (b - a - 1) * 2) with (2 * 2 ^ (b - a)) by unify_pows_two.
        rewrite kron_adjoint; Msimpl.
        reflexivity.
      * bdestruct (b <? a); try apply zero_adjoint_eq.
        bdestruct (b + (1 + (a - b - 1) + 1) <=? dim); try apply zero_adjoint_eq.
        repeat setoid_rewrite kron_adjoint; Msimpl.
        replace (2 ^ (1 + (a - b - 1) + 1)) with (2 * 2 ^ (a - b - 1) * 2) by unify_pows_two.
        rewrite Mplus_adjoint.
        repeat setoid_rewrite kron_adjoint; Msimpl.
        replace (2 * 2 ^ (a - b - 1) * 2) with (2 ^ (a - b) * 2) by unify_pows_two.
        rewrite kron_adjoint; Msimpl.
        reflexivity.
Qed.

(** Automation **)

(* For handling non well-typed cases. (Shouldn't Msimpl do this?) *)
Ltac remove_zero_gates :=
  repeat rewrite Mmult_0_l;
  repeat rewrite Mmult_0_r;
  repeat rewrite Mmult_0_l; (* hacky *)
  repeat rewrite Mmult_0_r;
  repeat rewrite kron_0_l;
  repeat rewrite kron_0_r;
  repeat rewrite kron_0_l;
  repeat rewrite kron_0_r.

(* Remove extra identity gates. (Shouldn't Msimpl do this too?) *)
Ltac remove_id_gates :=
  repeat rewrite Mmult_1_l;
  repeat rewrite Mmult_1_r;
  try auto with wf_db.
  
(* Several of the type rewrites are just associativity issues, and lia
   is a little slow solving these. *)
Ltac rewrite_assoc :=
  repeat rewrite mult_assoc;
  easy.
