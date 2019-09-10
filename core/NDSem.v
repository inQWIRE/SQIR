Require Import QWIRE.Quantum.
Require Import UnitarySem.
Require Import Setoid.

Local Open Scope com.

(* TODO: move *)

Definition norm {n} (ψ : Vector n) :=
  sqrt (fst (ψ ∘ ψ†)).  

Reserved Notation "c '/' ψ '⇩' ψ'"
                  (at level 40, ψ at level 39).

Inductive nd_eval {dim : nat} : base_com dim -> Vector (2^dim) -> Vector (2^dim) -> Prop :=
  | nd_skip : forall ψ, nd_eval skip ψ ψ
  | nd_uc : forall (u : base_ucom dim) (ψ : Vector (2^dim)),
      uc u / ψ ⇩ ((uc_eval u) × ψ)
  | nd_meas_t : forall (n : nat) (c1 c2 : base_com dim) (ψ ψ'' : Vector (2^dim)),
      let ψ' := @pad 1 n dim (∣1⟩⟨1∣) × ψ in 
      norm ψ' <> 0%R -> (* better way to say this in terms of partial trace? *)
      c1 / ψ' ⇩ ψ'' ->
      meas n c1 c2 / ψ ⇩ ψ'' 
      (* Alternatively, we could scale the output state:
           meas n c1 c2 / ψ ⇩ (scale (/(norm ψ'')) ψ'') *)
  | nd_meas_f : forall (n : nat) (c1 c2 : base_com dim) (ψ ψ'' : Vector (2^dim)),
      let ψ' := @pad 1 n dim (∣0⟩⟨0∣) × ψ in
      norm ψ' <> 0%R ->
      c2 / ψ' ⇩ ψ'' ->
      meas n c1 c2 / ψ ⇩ ψ'' 
  | nd_seq : forall (c1 c2 : base_com dim) (ψ ψ' ψ'' : Vector (2^dim)),
      c1 / ψ ⇩ ψ' ->
      c2 / ψ' ⇩ ψ'' ->
      (c1 ; c2) / ψ ⇩ ψ''

where "c '/' ψ '⇩' ψ'" := (nd_eval c ψ ψ').

Definition nd_equiv {dim} (c1 c2 : base_com dim) := forall (ψ ψ' : Vector (2^dim)), 
  c1 / ψ ⇩ ψ' <-> c2 / ψ ⇩ ψ'.

(* Maybe a new scope is warranted? *)
Infix "≡" := nd_equiv : com_scope.

Lemma nd_seq_assoc : forall {dim} (c1 c2 c3 : base_com dim),
    ((c1 ; c2) ; c3) ≡ (c1 ; (c2 ; c3)).
Proof.
  intros dim c1 c2 c3 ψ ψ'.
  split; intros E.
  - dependent destruction E.
    dependent destruction E1.
    econstructor; eauto.
    econstructor; eauto.
  - dependent destruction E.
    dependent destruction E2.
    econstructor; eauto.
    econstructor; eauto.
Qed.

Lemma nd_equiv_refl : forall {dim} (c1 : base_com dim), c1 ≡ c1. 
Proof. easy. Qed.

Lemma nd_equiv_sym : forall {dim} (c1 c2 : base_com dim), c1 ≡ c2 -> c2 ≡ c1. 
Proof. easy. Qed.

Lemma nd_equiv_trans : forall {dim} (c1 c2 c3 : base_com dim), 
  c1 ≡ c2 -> c2 ≡ c3 -> c1 ≡ c3. 
Proof. 
  intros dim c1 c2 c3 H12 H23 ψ ψ'. 
  specialize (H12 ψ ψ') as [L12 R12].
  specialize (H23 ψ ψ') as [L23 R23].
  split; auto.
Qed.

Add Parametric Relation (dim : nat) : (base_com dim) nd_equiv 
  reflexivity proved by nd_equiv_refl
  symmetry proved by nd_equiv_sym
  transitivity proved by nd_equiv_trans
  as nd_equiv_rel.

Lemma nd_seq_congruence : forall {dim} (c1 c1' c2 c2' : base_com dim),
    c1 ≡ c1' ->
    c2 ≡ c2' ->
    c1 ; c2 ≡ c1' ; c2'.
Proof.
  intros dim c1 c1' c2 c2' Ec1 Ec2 ψ ψ'.
  split; intros H; dependent destruction H.
  - (* rewrite Ec1 in H. //Fails? *)
    apply Ec1 in H.
    apply Ec2 in H0.
    econstructor; eauto.
  - apply Ec1 in H.
    apply Ec2 in H0.
    econstructor; eauto.
Qed.

Add Parametric Morphism (dim : nat) : (@seq base_Unitary dim)
  with signature nd_equiv ==> nd_equiv ==> nd_equiv as useq_mor.
Proof. intros x y H x0 y0 H0. apply nd_seq_congruence; easy. Qed.

Lemma double_pad_00 : forall dim q (ψ : Vector (2^dim)),
  @pad 1 q dim ∣0⟩⟨0∣ × (@pad 1 q dim ∣0⟩⟨0∣ × ψ) = @pad 1 q dim ∣0⟩⟨0∣ × ψ.
Proof.  
  intros.
  rewrite <- Mmult_assoc.
  rewrite pad_mult.
  repeat reduce_matrices.
  reflexivity.
Qed.  

Lemma double_pad_01 : forall dim q (ψ : Vector (2^dim)),
  @pad 1 q dim ∣1⟩⟨1∣ × (@pad 1 q dim ∣0⟩⟨0∣ × ψ) = Zero.
Proof.  
  intros.
  unfold pad.
  bdestruct (q + 1 <=? dim); try (Msimpl_light; trivial).
  rewrite <- Mmult_assoc. 
  restore_dims; repeat rewrite kron_mixed_product.
  Msimpl.
  replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
  repeat Msimpl_light.
  reflexivity.
Qed.  

Lemma double_pad_10 : forall dim q (ψ : Vector (2^dim)),
  @pad 1 q dim ∣0⟩⟨0∣ × (@pad 1 q dim ∣1⟩⟨1∣ × ψ) = Zero.
Proof.
  intros.
  unfold pad.
  bdestruct (q + 1 <=? dim); try (Msimpl_light; trivial).
  rewrite <- Mmult_assoc. 
  restore_dims; repeat rewrite kron_mixed_product.
  Msimpl.
  replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix.
  repeat Msimpl_light.
  reflexivity.
Qed.  

Lemma double_pad_11 : forall dim q (ψ : Vector (2^dim)),
  @pad 1 q dim ∣1⟩⟨1∣ × (@pad 1 q dim ∣1⟩⟨1∣ × ψ) = @pad 1 q dim ∣1⟩⟨1∣ × ψ.
Proof.  
  intros.
  rewrite <- Mmult_assoc.
  rewrite pad_mult.
  repeat reduce_matrices.
  reflexivity.
Qed.  

Lemma meas_reset : forall dim q, 
  @nd_equiv dim (measure q ; reset q) (reset q).
Proof.
  intros dim q ψ ψ'.
  split; intros H.
  - dependent destruction H;
    dependent destruction H;
    dependent destruction H0;
    dependent destruction H1; 
    subst ψ' ψ'0.
    + rewrite double_pad_11 in H0.
      rewrite double_pad_11 in H1.
      apply nd_meas_t; assumption.
    + contradict H0.
      rewrite double_pad_10.
      unfold norm, dot.
      rewrite Csum_0. 
      simpl; rewrite sqrt_0; reflexivity.
      intros; lca.
    + contradict H0. 
      rewrite double_pad_01.
      unfold norm, dot.
      rewrite Csum_0. 
      simpl; rewrite sqrt_0; reflexivity.
      intros; lca.
    + rewrite double_pad_00 in H0.
      rewrite double_pad_00 in H1.
      apply nd_meas_f; assumption.
  - dependent destruction H; subst ψ'.
    + econstructor.
      apply nd_meas_t; try assumption.
      apply nd_skip.
      apply nd_meas_t; rewrite double_pad_11; assumption.
    + econstructor.
      apply nd_meas_f; try assumption.
      apply nd_skip.
      apply nd_meas_f; rewrite double_pad_00; assumption.
Qed.
