Require Export VectorStates.

Local Coercion Nat.b2n : bool >-> nat.

(* General definitions useful for verifying quantum algorithms. *)

(** Boolean oracle (f : nat -> bool) **)

(* Definition of boolean oracle U : ∣ x ⟩∣ y ⟩ ↦ ∣ x ⟩∣ y ⊕ f(x) ⟩ *)
Definition boolean_oracle {n} (U : base_ucom (S n)) (f : nat -> bool) :=
  forall x (y : bool), (x < 2 ^ n)%nat -> 
    @Mmult _ _ 1 (uc_eval U) (basis_vector (2 ^ n) x ⊗ ∣ y ⟩) = 
      basis_vector (2 ^ n) x ⊗ ∣ xorb y (f x) ⟩.

Infix "<*>" := kron (at level 40, only parsing).

Definition pad_vector {n} dim (v : Vector (2 ^ n)) : Vector (2 ^ dim) :=
  v <*> kron_n (dim - n) qubit0.

Lemma wf_pad_vector :
  forall n dim (v : Vector (2 ^ n)),
  (n <= dim)%nat -> WF_Matrix v -> WF_Matrix (pad_vector dim v).
Proof.
  intros n dim v Hn Hw. unfold pad_vector.
  apply WF_kron; auto with wf_db.
  rewrite Nat.pow_1_l. reflexivity.
Qed.

Definition padded_boolean_oracle {dim} n
  (U : base_ucom dim) (f : nat -> bool) :=
  forall x (y : bool),
  (x < 2 ^ n)%nat ->
  @Mmult
      _ _ 1
      (uc_eval U)
      (@pad_vector (S n) dim (basis_vector (2 ^ n) x <*> ket y)) =
    @pad_vector (S n) dim (basis_vector (2 ^ n) x <*> ket (xorb y (f x))).

(* Count the number of inputs where f returns true; note that we never
   "run" this function, it's just a definition. *)
Fixpoint count (f : nat -> bool) n : nat :=
  match n with
  | O => O
  | S n' => f n' + count f n'
  end.

Definition negf (f : nat -> bool) i := negb (f i).

Lemma negf_involutive : forall f, negf (negf f) = f.
Proof.
  intros.
  unfold negf.
  apply functional_extensionality.
  intro.
  apply negb_involutive.
Qed.

Lemma count_bound : forall n (f : nat -> bool), (count f n <= n)%nat.
Proof.
  intros.
  induction n; simpl.
  lia.
  destruct (f n); simpl; lia.
Qed.  

Local Opaque Nat.sub.
Lemma count_negf : forall n (f : nat -> bool),
  count (negf f) n = (n - count f n)%nat.
Proof.
  intros.
  induction n; simpl.
  reflexivity.
  rewrite IHn.
  unfold negf.
  specialize (count_bound n f) as H.
  destruct (f n); simpl; lia.
Qed.

Lemma vsum_count : forall n (f : nat -> bool),
  vsum n (fun i : nat => if f i then I 1 else Zero) = 
    INR (count f n) .* I 1.
Proof.
  intros.
  induction n. 
  lma.
  rewrite vsum_extend_r, IHn.
  simpl count.
  rewrite plus_INR.
  destruct (f n); simpl; lma.
Qed.

Lemma count_zero: forall  (n : nat) (f : nat -> bool), 
  count f n = O -> forall i, (i < n)%nat -> f i = false.
Proof.
  intros n f H i Hi.
  induction n as [|n].
  lia.
  simpl in H.
  apply Nat.eq_add_0 in H as [? ?].
  bdestruct (i =? n); subst.
  destruct (f n); simpl in *; easy.
  apply IHn; lia.
Qed.
 
Lemma count_nonzero: forall  (n : nat) (f : nat -> bool), 
  count f n <> O -> exists i, (i < n)%nat /\ f i = true.
Proof.
  intros n f H.
  induction n as [|n].
  simpl in H.
  lia.
  simpl in H.
  bdestruct (count f n =? 0).
  rewrite H0 in H.
  exists n.
  split; try lia.
  destruct (f n); simpl in *; auto.
  apply IHn in H0. 
  destruct H0 as [x [? ?]].
  exists x.
  split; auto.
Qed.

(** Integer oracle (f : nat -> nat) **)

(* Special case U : ∣ x ⟩∣ 0 ⟩ ↦ ∣ x ⟩∣ f(x) ⟩ *)
Definition integer_oracle {n} (U : base_ucom (2 * n)) (f : nat -> nat) :=
  forall (x :nat), (x < 2 ^ n)%nat -> 
    @Mmult _ _ 1 (uc_eval U) (basis_vector (2 ^ n) x ⊗ basis_vector (2 ^ n) 0) = 
      basis_vector (2 ^ n) x ⊗ ((basis_vector (2 ^ n) (f x))).

(** Measurement probabilities **)

(* What is the probability of outcome ϕ given input ψ? *)
Definition probability_of_outcome {n} (ϕ ψ : Vector n) : R :=
  let c := (ϕ† × ψ) 0%nat 0%nat in
  (Cmod c) ^ 2.

Lemma probability_of_outcome_comm : forall {d} (ϕ ψ : Vector d),
  probability_of_outcome ϕ ψ = probability_of_outcome ψ ϕ.
Proof.
  intros d ψ ϕ. unfold probability_of_outcome.
  replace (ϕ † × ψ) with (ϕ † × ψ ††) by (rewrite adjoint_involutive; easy).
  rewrite <- Mmult_adjoint.
  unfold adjoint.
  rewrite Cmod_Cconj.
  reflexivity.
Qed.

Lemma probability_of_outcome_is_norm : forall {d} (ϕ ψ : Vector d),
  probability_of_outcome ϕ ψ = ((norm (ϕ† × ψ)) ^ 2)%R.
Proof.
  intros d ψ ϕ.
  unfold probability_of_outcome, Cmod, norm.
  apply f_equal2; try reflexivity.
  apply f_equal.
  unfold Mmult, adjoint.
  simpl.
  autorewrite with R_db.
  reflexivity.
Qed.

(* What is the probability of measuring ϕ on the first m qubits given
  (m + n) qubit input ψ? *)
Definition prob_partial_meas {m n} (ϕ : Vector (2^m)) (ψ : Vector (2^(m + n))) :=
  Rsum (2^n) (fun y => probability_of_outcome (ϕ ⊗ basis_vector (2^n) y) ψ).

Lemma rewrite_I_as_sum : forall m n,
  (m <= n)%nat -> 
  I m = Msum m (fun i => (basis_vector n i) × (basis_vector n i)†).
Proof.
  intros.
  induction m.
  simpl.
  unfold I.
  prep_matrix_equality.
  bdestruct_all; reflexivity.
  simpl.
  rewrite <- IHm by lia.
  unfold basis_vector.
  solve_matrix.
  bdestruct_all; simpl; try lca. 
  all: destruct m; simpl; try lca.
  all: bdestruct_all; lca.
Qed.

Lemma Rsum_Csum :
  forall n (f : nat -> R),
     fst (Csum (fun i => f i) n) = Rsum n f.
Proof.
  intros. induction n.
  - easy.
  - simpl. rewrite IHn. 
    destruct n.
    + simpl. lra.
    + rewrite tech5. simpl. easy.
Qed.

Lemma Rsum_Msum : forall n (f : nat -> Square 1),
  Rsum n (fun i : nat => fst (f i O O)) = fst (Msum n f O O).
Proof.
  intros.
  rewrite Msum_Csum.
  rewrite <- Rsum_Csum.
  induction n; simpl.
  reflexivity.
  rewrite IHn.
  reflexivity.
Qed.

Lemma prob_partial_meas_alt : 
  forall {m n} (ϕ : Vector (2^m)) (ψ : Vector (2^(m + n))),
  @prob_partial_meas m n ϕ ψ = ((norm ((ϕ ⊗ I (2 ^ n))† × ψ)) ^ 2)%R.
Proof.
  intros.
  unfold prob_partial_meas.
  erewrite Rsum_eq.
  2: { intros.
       rewrite probability_of_outcome_is_norm.
       unfold norm.
       rewrite pow2_sqrt.
       restore_dims.
       distribute_adjoint.
       Msimpl.
       repeat rewrite Mmult_assoc.
       restore_dims.
       rewrite <- (Mmult_assoc (ϕ ⊗ _)).
       rewrite kron_mixed_product.
       unify_pows_two.
       rewrite <- Mmult_assoc.
       reflexivity. 
       apply inner_product_ge_0. }  
  rewrite rewrite_I_as_sum by lia.
  rewrite kron_Msum_distr_l.
  rewrite Msum_adjoint.
  erewrite Msum_eq_bounded.
  2: { intros. distribute_adjoint. reflexivity. }
  rewrite Mmult_Msum_distr_r.
  unfold norm.
  rewrite pow2_sqrt.
  2: apply inner_product_ge_0.
  rewrite Msum_adjoint, Mmult_Msum_distr_l.
  erewrite Msum_eq_bounded.
  2: { intros.
      rewrite Mmult_Msum_distr_r. 
      erewrite Msum_eq_bounded.
      2: { intros.
           distribute_adjoint.
           Msimpl.
           repeat rewrite Mmult_assoc.
           restore_dims.
           rewrite <- (Mmult_assoc (ϕ ⊗ _)).
           rewrite kron_mixed_product.
           repeat rewrite Mmult_assoc.
           rewrite <- (Mmult_assoc (_†)).
           reflexivity. } 
     reflexivity. }
  rewrite Msum_diagonal.
  2: { intros. rewrite basis_vector_product_neq by auto.
       do 2 Msimpl. reflexivity. }
  erewrite Msum_eq_bounded.
  2: { intros. rewrite basis_vector_product_eq by assumption.
       Msimpl. unify_pows_two.
       repeat rewrite <- Mmult_assoc.
       reflexivity. }
  remember (fun i : nat => (ψ) † × (ϕ × (ϕ) † ⊗ (basis_vector (2 ^ n) i × (basis_vector (2 ^ n) i) †)) × ψ) as f.
  erewrite Rsum_eq.
  2: { intros.
       replace ((ψ) † × (ϕ × (ϕ) † ⊗ (basis_vector (2 ^ n) i × (basis_vector (2 ^ n) i) †)) × ψ) with (f i) by (subst; reflexivity).
       reflexivity. }
  apply Rsum_Msum.
Qed.

Lemma partial_meas_tensor : 
  forall {m n} (ϕ : Vector (2^m)) (ψ1 : Vector (2^m)) (ψ2 : Vector (2^n)),
  WF_Matrix ψ2 -> ψ2† × ψ2 = I 1 ->
  @prob_partial_meas m n ϕ (ψ1 ⊗ ψ2) = probability_of_outcome ϕ ψ1.
Proof.
  intros.
  rewrite prob_partial_meas_alt.
  rewrite probability_of_outcome_is_norm.
  unfold norm.
  apply f_equal2; try reflexivity.
  do 2 apply f_equal.
  distribute_adjoint.
  Msimpl.
  rewrite H0.
  Msimpl.
  reflexivity.
Qed.
