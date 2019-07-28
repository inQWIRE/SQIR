Require Export SQIRE.
Require Export QWIRE.Quantum.
Require Import Setoid.

Local Open Scope matrix_scope.
Local Open Scope ucom_scope.

(** Denotation of Unitaries **)

(* TODO: Put in QWIRE's quantum file *)
Lemma compose_super_eq : forall {m n p} (A : Matrix m n) (B : Matrix n p), 
      compose_super (super A) (super B) = super (A × B).
Proof.
  intros.
  unfold compose_super, super.
  apply functional_extensionality. intros ρ.
  rewrite Mmult_adjoint.
  repeat rewrite Mmult_assoc.
  reflexivity.
Qed.

(* Padding and lemmas *)
Definition pad {n} (start dim : nat) (A : Square (2^n)) : Square (2^dim) :=
  if start + n <=? dim then I (2^start) ⊗ A ⊗ I (2^(dim - n - start)) else Zero.

Lemma WF_pad : forall n start dim (A : Square (2^n)),
  WF_Matrix A ->
  WF_Matrix (pad start dim A).
Proof.
  intros n start dim A WFA. unfold pad.
  bdestruct (start + n <=? dim); auto with wf_db.
Qed.  

Lemma pad_mult : forall n dim start (A B : Square (2^n)),
  pad start dim A × pad start dim B = pad start dim (A × B).
Proof.
  intros.
  unfold pad.
  bdestruct (start + n <=? dim). 2: rewrite Mmult_0_l; reflexivity.
  restore_dims_strong.
  repeat rewrite kron_mixed_product.
  Msimpl.
  reflexivity.
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
    @pad (1+(n-m-1)+1) m dim (∣1⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ I 2)
  else if (n <? m) then
    @pad (1+(m-n-1)+1) n dim (σx ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨1∣ .+ I 2 ⊗ I (2^(m-n-1)) ⊗ ∣0⟩⟨0∣)
  else
    Zero.

(** Denotation of ucoms **)

Fixpoint uc_eval {dim} (c : ucom dim) : Matrix (2^dim) (2^dim) :=
  match c with
  | uskip       => I (2^dim)
  | c1 ; c2     => uc_eval c2 × uc_eval c1 
  | uapp1 u n   => ueval1 dim n u
  | uapp2 _ m n => ueval_cnot dim m n
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
    try apply WF_pad;
    unify_pows_two; auto with wf_db.
Qed.  

Lemma WF_uc_eval : forall {dim} (c : ucom dim), WF_Matrix (uc_eval c).
Proof.
  intros dim c.
  induction c; simpl; auto with wf_db.
  apply WF_ueval1.
  apply WF_ueval_cnot.
Qed.

Hint Resolve WF_pad WF_ueval1 WF_ueval_cnot WF_uc_eval : wf_db.

(* Some unit tests *)

Lemma eval_H : uc_eval ((H 0) : ucom 1) = hadamard.
Proof.
  simpl. unfold ueval1, pad. (* have these automatically simplify *)
  simpl. Msimpl. reflexivity.
Qed.

Lemma eval_HHpar : uc_eval ((H 0; H 1) : ucom 2) = hadamard ⊗ hadamard.
Proof.
  simpl. unfold ueval1, pad. (* have these automatically simplify *)
  simpl. restore_dims.  Msimpl. 
  restore_dims. Msimpl. 
  reflexivity.
Qed.

Lemma eval_HHseq : uc_eval ((H 0; H 0) : ucom 2) = I 4.
Proof.
  simpl. unfold ueval1, pad. (* have these automatically simplify *)
  simpl. Msimpl. solve_matrix.
Qed.

Lemma eval_CNOT : uc_eval ((CNOT 0 1) : ucom 2) = cnot.
Proof.
  unfold uc_eval. simpl.
  simpl. unfold ueval_cnot, pad. (* have these automatically simplify *)
  simpl. Msimpl. solve_matrix.
Qed.

(** Equivalence and Structural Rules **)

(* Precondition about typing? *)
Definition uc_equiv {dim} (c1 c2 : ucom dim) := uc_eval c1 = uc_eval c2.

Infix "≡" := uc_equiv : ucom_scope.

Lemma uc_equiv_refl : forall {dim} (c1 : ucom dim), c1 ≡ c1. 
Proof. easy. Qed.

Lemma uc_equiv_sym : forall {dim} (c1 c2 : ucom dim), c1 ≡ c2 -> c2 ≡ c1. 
Proof. easy. Qed.

Lemma uc_equiv_trans : forall {dim} (c1 c2 c3 : ucom dim), c1 ≡ c2 -> c2 ≡ c3 -> c1 ≡ c3. 
Proof. intros dim c1 c2 c3 H12 H23. unfold uc_equiv. rewrite H12. easy. Qed.

Lemma useq_assoc : forall {dim} (c1 c2 c3 : ucom dim), ((c1 ; c2) ; c3) ≡ (c1 ; (c2 ; c3)).
Proof.
  intros dim c1 c2 c3. 
  unfold uc_equiv; simpl.
  rewrite Mmult_assoc. 
  reflexivity.
Qed.

Lemma useq_congruence : forall {dim} (c1 c1' c2 c2' : ucom dim),
    c1 ≡ c1' ->
    c2 ≡ c2' ->
    c1 ; c2 ≡ c1' ; c2'.
Proof.
  intros dim c1 c1' c2 c2' Ec1 Ec2.
  unfold uc_equiv; simpl.
  rewrite Ec1, Ec2.
  reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (ucom dim) (@uc_equiv dim)
  reflexivity proved by uc_equiv_refl
  symmetry proved by uc_equiv_sym
  transitivity proved by uc_equiv_trans
  as uc_equiv_rel.

Add Parametric Morphism (dim : nat) : (@useq dim)
  with signature (@uc_equiv dim) ==> (@uc_equiv dim) ==> (@uc_equiv dim) as useq_mor.
Proof. intros x y H x0 y0 H0. apply useq_congruence; easy. Qed.

Lemma test_rel : forall (dim : nat) (c1 c2 : ucom dim), c1 ≡ c2 -> c2 ≡ c1.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma test_mor : forall (dim : nat) (c1 c2 : ucom dim), c1 ≡ c2 -> c2 ; c1 ≡ c1 ; c1.
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
    restore_dims_strong.
    rewrite Mmult_plus_distr_l.
    rewrite 2 Mmult_plus_distr_r.
    repeat rewrite kron_mixed_product.
    Msimpl.
    replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2)%nat by solve_matrix.
    replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2)%nat by solve_matrix.
    replace (∣1⟩⟨1∣ × ∣1⟩⟨1∣) with (∣1⟩⟨1∣) by solve_matrix.
    replace (∣0⟩⟨0∣ × ∣0⟩⟨0∣) with (∣0⟩⟨0∣) by solve_matrix.
    rewrite 2 kron_0_l.
    rewrite Mplus_0_l, Mplus_0_r.
    replace (σx × σx) with (I 2) by solve_matrix.
    rewrite <- 2 kron_plus_distr_r.
    replace (∣1⟩⟨1∣ .+ ∣0⟩⟨0∣) with (I 2)%nat by solve_matrix.
    Msimpl.
    unify_pows_two.
    reflexivity.
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
    restore_dims_strong.
    rewrite Mmult_plus_distr_l.
    rewrite 2 Mmult_plus_distr_r.
    repeat rewrite kron_mixed_product.
    Msimpl.
    restore_dims_strong.
    rewrite kron_mixed_product.
    Msimpl.
    replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2)%nat by solve_matrix.
    replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2)%nat by solve_matrix.
    replace (∣1⟩⟨1∣ × ∣1⟩⟨1∣) with (∣1⟩⟨1∣) by solve_matrix.
    replace (∣0⟩⟨0∣ × ∣0⟩⟨0∣) with (∣0⟩⟨0∣) by solve_matrix.
    replace (σx × σx) with (I 2) by solve_matrix.
    rewrite kron_0_r.
    rewrite Mplus_0_r.
    rewrite Mplus_0_l.
    Msimpl.
    unify_pows_two.
    setoid_rewrite <- kron_plus_distr_l.
    replace (∣1⟩⟨1∣ .+ ∣0⟩⟨0∣) with (I 2) by solve_matrix.
    Msimpl.
    unify_matrices.
Qed.  

Lemma uc_eval_unitary : forall (dim : nat) (c : ucom dim),
    uc_well_typed c -> WF_Unitary (uc_eval c).
Proof.
  intros dim c H.
  unfold WF_Unitary.
  split. apply WF_uc_eval.
  induction c.
  - simpl. Msimpl. reflexivity.
  - inversion H; subst.
    simpl. Msimpl. rewrite <- Mmult_assoc. rewrite (Mmult_assoc (_)†).
    rewrite IHc2; trivial. Msimpl.
    rewrite IHc1; easy.
  - inversion H; subst.
    simpl. destruct (ueval1_unitary dim n u H1) as [_ UU].
    assumption.
  - inversion H; subst.
    simpl. destruct (ueval_cnot_unitary dim n n0 H5 H3 H4) as [_ UU].
    assumption.
Qed.

Lemma WT_if_nonzero : forall (dim : nat) (c : ucom dim),
  uc_eval c <> Zero -> uc_well_typed c.
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
  - simpl in *. unfold ueval1, pad in H.
    bdestruct (n + 1 <=? dim); try contradiction. 
    constructor; lia.
  - simpl in *. unfold ueval_cnot, pad in H.
    bdestruct (n <? n0). 
    + bdestruct (n + (1 + (n0 - n - 1) + 1) <=? dim); try contradiction.
      constructor; lia.
    + bdestruct (n0 <? n); try contradiction.
      bdestruct (n0 + (1 + (n - n0 - 1) + 1) <=? dim); try contradiction.
      constructor; lia.
Qed.

(* Now we get bidirectionality for free! *)

Lemma uc_eval_unitary_iff : forall (dim : nat) (c : ucom dim),
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

Lemma uc_eval_nonzero_iff : forall (dim : nat) (c : ucom dim),
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

(** Proofs about high-level functions over unitary programs **)

Local Close Scope C_scope.
Local Close Scope R_scope.

Lemma invert_u_correct : forall (dim : nat) (c : ucom dim),
  (uc_eval c)† = uc_eval (invert_u c).
Proof.
  intros.
  induction c.
  - simpl. Msimpl. reflexivity.
  - simpl. Msimpl. rewrite IHc1. rewrite IHc2. reflexivity.
  - simpl. 
    dependent destruction u; unfold ueval1, pad; 
    bdestruct (n + 1 <=? dim); try apply zero_adjoint_eq;
    repeat setoid_rewrite kron_adjoint; Msimpl.
    + setoid_rewrite hadamard_sa. reflexivity.
    + setoid_rewrite σx_sa. reflexivity.
    + setoid_rewrite σy_sa. reflexivity.
    + setoid_rewrite σz_sa. reflexivity.
    + reflexivity.
  - simpl.
    dependent destruction u. 
    unfold ueval_cnot, pad.
    bdestruct (n <? n0).
    + bdestruct (n + (1 + (n0 - n - 1) + 1) <=? dim); try apply zero_adjoint_eq. 
      repeat setoid_rewrite kron_adjoint; Msimpl.
      replace (2 ^ (1 + (n0 - n - 1) + 1)) with (2 * 2 ^ (n0 - n - 1) * 2) by unify_pows_two.
      Msimpl.
      replace (2 * 2 ^ (n0 - n - 1) * 2) with (2 * 2 ^ (n0 - n)) by unify_pows_two.
      Msimpl.
      reflexivity.
    + bdestruct (n0 <? n); try apply zero_adjoint_eq. 
      bdestruct (n0 + (1 + (n - n0 - 1) + 1) <=? dim); try apply zero_adjoint_eq.
      repeat setoid_rewrite kron_adjoint; Msimpl.
      replace (2 ^ (1 + (n - n0 - 1) + 1)) with (2 * 2 ^ (n - n0 - 1) * 2) by unify_pows_two.
      Msimpl.
      replace (2 * 2 ^ (n - n0 - 1) * 2) with (2 ^ (n - n0) * 2) by unify_pows_two.
      Msimpl.
      reflexivity.
Qed.

(** Automation **)

(* TODO: If this isn't used anywhere, remove. *)

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
