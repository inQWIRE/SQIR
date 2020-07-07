Require Import UnitaryOps.
Require Import Dirac.

Open Scope ucom.
Local Close Scope C_scope.
Local Close Scope R_scope.

Local Coercion Nat.b2n : bool >-> nat.

(* This file contains a definition of the Deutsch-Jozsa program, which determines
   whether a function is constant or balanced using one query to a boolean oracle.

   See, e.g., https://en.wikipedia.org/wiki/Deutsch%E2%80%93Jozsa_algorithm

   This file also contains proofs of correctness of the Deutsch-Jozsa program
   using two different methods. The first uses a standard definition of boolean
   oracles and follows the standard textbook proof of correctness. The second
   uses an inductive definition of boolean oracles, which allows for an inductive
   proof. *)

(** Definition of Deutsch-Jozsa program. **)

Definition deutsch_jozsa {n} (U : base_ucom (S n)) : base_ucom (S n) :=
  X n ; npar (S n) U_H ; U; npar (S n) U_H.

(** Proof of correctness #1 **)

(* Definition of boolean oracle U : ∣ x ⟩∣ y ⟩ ↦ ∣ x ⟩∣ y ⊕ f(x) ⟩ *)
Definition boolean_oracle {n} (U : base_ucom (S n)) (f : nat -> bool) :=
  forall x (y : bool), (x < 2 ^ n)%nat -> 
    @Mmult _ _ 1 (uc_eval U) (basis_vector (2 ^ n) x ⊗ ∣ y ⟩) = 
      basis_vector (2 ^ n) x ⊗ ∣ xorb y (f x) ⟩.

(* Count the number of inputs where f returns true; note that we never
   "run" this function, it's just a definition. *)
Fixpoint count f n :=
  match n with
  | O => O
  | S n' => f n' + count f n'
  end.

Definition balanced f n := n > 0 /\ count f (2 ^ n) = 2 ^ (n - 1).

Definition constant f n := count f (2 ^ n) = 0 \/ count f (2 ^ n) = 2 ^ n.

Local Open Scope C_scope.
Local Open Scope R_scope.

(* After running deutsch_jozsa, the probability of measuring the state
   (n ⨂ ∣0⟩) ⊗ ∣1⟩ will be a sum of terms of the form (-1)^(f x). The
   value of this sum can be rewritten as follows:
       ∑ (-1)^(f x) / n = 1 - 2 * count f / n.
   Note that if f is balanced, then this expression will be zero. If f is
   constant then the expression will either be 1 or -1. *)
Lemma Csum_of_minus_1 : forall (f : nat -> bool) n,
  (n > 0)%nat ->
  ((Csum (fun x => (-1) ^ f(x)) n) * / INR n)%C = 1 - 2 * INR (count f n) * / INR n.
Proof.
  intros.
  destruct n; try lia.
  clear H.
  induction n.
  simpl.
  destruct (f O); simpl; lca.
  simpl Csum in *.
  simpl count in *. 
  remember (Csum (fun x : nat => (-1) ^ f x) n)%C as sum.
  remember (count (fun x : nat => f x) n) as  cnt.
  clear Heqsum Heqcnt.
  rewrite Cmult_plus_distr_r.
  rewrite <- (Cmult_1_r (_ * / _)).
  rewrite <- (Cinv_r (INR (S n))).
  assert (forall a b c d, ((a * b) * (c * d))%C = ((a * d) * (c * b))%C).
  { intros. field. }
  rewrite H, IHn; clear.
  repeat rewrite plus_INR.
  rewrite <- RtoC_inv.
  rewrite RtoC_pow.
  repeat rewrite <- RtoC_mult.
  rewrite <- RtoC_plus.
  apply injective_projections; simpl; try reflexivity.
  field_simplify_eq.
  destruct (f (S n)); subst; simpl; lra.
  destruct n; try lra.
  repeat rewrite <- S_INR.
  split.
  4: apply C0_fst_neq; remember (S n) as Sn; simpl; subst.
  all: apply not_0_INR; lia.
Qed.

Lemma basis_vector_1_0 : basis_vector 1 0 = I 1.
Proof. 
  unfold basis_vector, I. 
  solve_matrix.
  bdestruct_all; reflexivity.
Qed.

(* In the Deutsch Jozsa problem we care about the probability of measuring ∣0...0⟩
   in the first n qubits (the last qubit always ends up in the ∣1⟩ state). *)
Lemma deutsch_jozsa_success_probability :
  forall {n : nat} (U : base_ucom (S n)) f,
  (n > 0)%nat ->
  boolean_oracle U f ->
  ((n ⨂ ∣0⟩ ⊗ ∣1⟩)† × (uc_eval (deutsch_jozsa U)) × (S n ⨂ ∣0⟩)) 0%nat 0%nat = 
      1 - 2 * INR (count f (2 ^ n)) * /2 ^ n.
Proof.
  intros n U f Hn H.
  unfold deutsch_jozsa.
  Opaque npar.
  simpl uc_eval.
  restore_dims. 
  rewrite npar_H by lia.
  autorewrite with eval_db.
  bdestruct_all.
  replace (S n - (n + 1))%nat with O by lia.
  simpl I.
  Msimpl_light.
  Transparent npar.
  simpl.
  restore_dims. 
  repeat (rewrite Mmult_assoc; restore_dims).
  Qsimpl. 
  rewrite H0_kron_n_spec_alt by auto.
  replace (hadamard × ∣1⟩) with ∣-⟩ by solve_matrix.
  restore_dims. 
  distribute_scale. 
  rewrite kron_vsum_distr_r.
  repeat rewrite Nat.mul_1_r.
  replace (2 ^ S n)%nat with (2 ^ n * 2)%nat by unify_pows_two.
  rewrite 2 Mmult_vsum_distr_l. 
  erewrite vsum_eq.  
  2: { intros i Hi.
       restore_dims.
       distribute_plus.
       distribute_scale.
       unfold boolean_oracle in H. 
       repeat rewrite Nat.mul_1_r.
       replace (2 ^ S n)%nat with (2 ^ n * 2)%nat in * by unify_pows_two.
       replace ∣ 0 ⟩ with ∣ Nat.b2n false ⟩ by reflexivity.
       rewrite (H i false) by assumption.
       replace ∣ 1 ⟩ with ∣ Nat.b2n true ⟩ by reflexivity.
       rewrite (H i true) by assumption.
       restore_dims.
       Qsimpl.
       rewrite <- 2 Mscale_kron_dist_r. 
       rewrite <- kron_plus_distr_l.
       rewrite <- 2 Mscale_mult_dist_r. 
       rewrite <- Mmult_plus_distr_l.
       replace (/√ 2 .* ∣ false ⊕ f i ⟩ .+ (- /√ 2) .* ∣ true ⊕ f i ⟩) with ((-1)^(f i) .* ∣-⟩). 
       distribute_scale.
       rewrite Hminus_spec.
       rewrite <- Mscale_kron_dist_l.
       reflexivity.
       destruct (f i); simpl; lma. }
  rewrite <- kron_vsum_distr_r.
  replace ∣ 1 ⟩ with ∣1⟩ by reflexivity. 
  Qsimpl.
  rewrite Mmult_vsum_distr_l.
  erewrite vsum_eq.
  2: { intros i Hi.
       rewrite basis_f_to_vec_alt by assumption.
       rewrite H_kron_n_spec by assumption.
       distribute_scale.
       rewrite Mmult_vsum_distr_l.
       erewrite vsum_unique. 
       2: { exists O.
            replace (n ⨂ ∣0⟩) with (basis_vector (2 ^ n) 0).
            split; [lia | split].
            distribute_scale. 
            restore_dims.
            rewrite basis_vector_product_eq by lia.
            reflexivity.
            intros j ? ?.
            distribute_scale. 
            restore_dims.
            rewrite basis_vector_product_neq by lia.
            lma.
            clear. induction n.
            simpl. apply basis_vector_1_0.
            replace (basis_vector (2 ^ S n) 0) with 
                (basis_vector (2 * 2 ^ n) (2 * 0)) by reflexivity.
            rewrite <- (basis_vector_append_0 (2 ^ n)). 
            rewrite IHn. reflexivity.
            apply Nat.pow_nonzero. lia.
            apply pow_positive. lia. }
       rewrite product_comm, nat_to_funbool_0, product_0.
       simpl.
       rewrite Mscale_1_l.
       rewrite Cmult_comm.
       rewrite <- Mscale_assoc.
       reflexivity. }
  rewrite <- Mscale_vsum_distr_r.
  rewrite Mscale_vsum_distr_l.
  restore_dims.
  distribute_scale.
  unfold scale, I; simpl.
  rewrite Cmult_1_r. 
  rewrite <- Cinv_mult_distr by nonzero.
  rewrite <- RtoC_mult.
  rewrite sqrt_def.
  rewrite Cmult_comm. 
  replace (2 ^ n)%R with (INR (2 ^ n)).
  apply Csum_of_minus_1. 
  apply pow_positive. lia. 
  rewrite INR_IZR_INZ.
  rewrite pow_IZR. 
  apply f_equal.
  clear. (* is there a simpler lemma to use here? *)
  induction n.
  reflexivity.
  replace (2 ^ S n)%nat with (2 * 2 ^ n)%nat by reflexivity.
  rewrite Nat2Z.inj_mul, IHn. 
  simpl Z.pow.
  rewrite Z.pow_pos_fold.
  rewrite Zpos_P_of_succ_nat. 
  replace (Z.succ (Z.of_nat n)) with (1 + Z.of_nat n)%Z by lia.
  rewrite Z.pow_add_r; lia.
  apply pow_le; lra.
Qed.

(* When measuring ψ, what is the probability that the outcome is o? *)
Definition probability_of_outcome {n} (ψ o : Vector n) :=
  let c := (o† × ψ) 0%nat 0%nat in
  Re c ^ 2 + Im c ^ 2.

(* accept := probability of measuring ∣0...0⟩ in the last n qubits is 1 *)
Definition accept {n : nat} (U : base_ucom (S n)) : Prop :=
  @probability_of_outcome (2 ^ S n) 
    (uc_eval (deutsch_jozsa U) × (S n ⨂ ∣0⟩)) 
    (n ⨂ ∣0⟩ ⊗ ∣1⟩) = 1. 

(* reject := probability of measuring ∣0...0⟩ in the last n qubits is 0 *)
Definition reject {n : nat} (U : base_ucom (S n)) : Prop :=
  @probability_of_outcome (2 ^ S n) 
    (uc_eval (deutsch_jozsa U) × (S n ⨂ ∣0⟩)) 
    (n ⨂ ∣0⟩ ⊗ ∣1⟩) = 0. 

Theorem deutsch_jozsa_constant_correct :
  forall {n} (f : nat -> bool) (U : base_ucom (S n)), 
  (n > 0)%nat -> constant f n -> boolean_oracle U f -> accept U.
Proof.
  intros n f U ? H ?. 
  unfold accept, probability_of_outcome.
  repeat rewrite Nat.pow_1_l. 
  rewrite <- Mmult_assoc.
  restore_dims.
  rewrite deutsch_jozsa_success_probability with (f0:=f); auto.
  unfold constant in H.
  destruct H; rewrite H; simpl; try lra.
  autorewrite with R_db.
  rewrite pow_INR. simpl. replace (1 + 1) with 2 by lra.
  field_simplify_eq; trivial.
  nonzero.
Qed.

Theorem deutsch_jozsa_balanced_correct :
  forall {n} (f : nat -> bool) (U : base_ucom (S n)), 
  (n > 0)%nat -> balanced f n -> boolean_oracle U f -> reject U.
Proof.
  intros n f U ? [_ H] ?. 
  unfold reject, probability_of_outcome.
  repeat rewrite Nat.pow_1_l. 
  rewrite <- Mmult_assoc.
  restore_dims.
  rewrite deutsch_jozsa_success_probability with (f0:=f); auto.
  rewrite H; simpl; try lra.
  autorewrite with R_db.
  rewrite pow_INR. simpl. replace (1 + 1) with 2 by lra.
  replace (2 * 2 ^ (n - 1) * / 2 ^ n) with 1.
  lra.
  field_simplify_eq; try nonzero.
  rewrite tech_pow_Rmult. 
  replace (S (n - 1)) with n by lia. 
  reflexivity.
Qed.

(** Proof of correctness #2 **)

(* Inductive definition of a boolean oracle. Note that in this definition
   the result bit is stored at the beginning rather than the end, so
   we have something like U : ∣ y ⟩∣ x ⟩ ↦ ∣ y ⊕ f(x) ⟩∣ x ⟩  *)
Inductive boolean : forall {n}, base_ucom (S n) -> Set :=
  | boolean_I : forall u, u ≡ SKIP -> @boolean 0 u
  | boolean_X : forall u, u ≡ X 0  -> @boolean 0 u
  | boolean_U : forall dim (u : base_ucom (S (S dim))) (u1 u2 : base_ucom (S dim)),
                boolean u1 -> boolean u2 ->
                uc_eval u = (uc_eval u1 ⊗ ∣0⟩⟨0∣) .+ (uc_eval u2 ⊗ ∣1⟩⟨1∣) ->
                boolean u.

(* TODO: Can we prove equivalence between these definitions? i.e.
     forall {n} (U : base_ucom (S n)),
       boolean U <-> exists f, boolean_oracle U f. *)

(* Slightly different version of DJ with the result bit at index 0. *)
Definition deutsch_jozsa' {n} (U : base_ucom n) : base_ucom n :=
  X 0 ; npar n U_H ; U; npar n U_H.

(* Counting for inductively defined oracles *)
Fixpoint count' {dim : nat} {u : base_ucom (S dim)} (P : boolean u) : nat :=
  match P with
  | boolean_I _ _ => 0
  | boolean_X _ _ => 1
  | boolean_U _ _ _ _ P1 P2 _ => (count' P1 + count' P2)
  end.

Definition balanced' {dim : nat} {u : base_ucom (S dim)} (P : boolean u) : Prop :=
  (dim > 0 /\ count' P = 2 ^ (dim - 1))%nat.

Definition constant' {dim : nat} {u : base_ucom (S dim)} (P : boolean u) : Prop :=
  (count' P = 0 \/ count' P = 2 ^ dim)%nat.

Lemma deutsch_jozsa_success_probability' :
  forall {n : nat} {U : base_ucom (S n)} (P : boolean U),
  ((∣1⟩ ⊗ n ⨂ ∣0⟩)† × (uc_eval (deutsch_jozsa' U)) × ((S n) ⨂ ∣0⟩)) 0%nat 0%nat = 
      1 - 2 * INR (count' P) * /2 ^ n.
Proof.
  intros.
  unfold deutsch_jozsa'. 
  rewrite kron_n_assoc by auto with wf_db.
  Opaque npar. 
  (* initial rewriting to get rid of X, H gates *)
  simpl uc_eval. restore_dims. 
  rewrite npar_H by lia.
  replace (S n - S n)%nat with O by lia.
  autorewrite with eval_db.
  bdestruct_all.
  simpl I.
  Msimpl_light.
  replace (n - 0)%nat with n by lia.
  rewrite kron_n_assoc by auto with wf_db.
  restore_dims. 
  repeat rewrite Mmult_assoc.
  restore_dims.
  Qsimpl.
  replace (hadamard × ∣1⟩) with ∣-⟩ by solve_matrix.
  rewrite H0_kron_n_spec.
  rewrite <- Mmult_assoc. 
  Qsimpl. 
  replace (hadamard) with (hadamard†) by (Qsimpl; easy).
  rewrite <- kron_n_adjoint by auto with wf_db.
  repeat rewrite <- Mmult_adjoint.
  rewrite H0_kron_n_spec. 
  replace (hadamard × ∣1⟩) with ∣-⟩ by solve_matrix.
  rewrite <- kron_adjoint.
  (* interesting part of the proof that looks at the structure of P *)
  induction n; dependent destruction P.
  - simpl. rewrite u0. clear.
    rewrite denote_SKIP; try lia.
    Msimpl_light. restore_dims.
    replace (∣-⟩† × ∣-⟩) with (I 1) by solve_matrix.
    lca.
  - simpl. rewrite u0. clear.
    autorewrite with eval_db; simpl.
    Msimpl_light. restore_dims.
    replace (∣-⟩† × (σx × ∣-⟩)) with (-1 .* I 1) by solve_matrix.
    lca.
  - simpl. rewrite e.
    restore_dims.
    repeat rewrite <- kron_assoc.
    restore_dims.
    setoid_rewrite kron_adjoint.
    rewrite Mmult_plus_distr_r.
    restore_dims.
    rewrite Mmult_plus_distr_l.
    repeat rewrite kron_mixed_product.
    replace ((∣+⟩) † × (∣0⟩⟨0∣ × ∣+⟩)) with ((1/2)%R .* I 1) by solve_matrix.
    replace ((∣+⟩) † × (∣1⟩⟨1∣ × ∣+⟩)) with ((1/2)%R .* I 1) by solve_matrix.
    repeat rewrite Mscale_kron_dist_r.
    rewrite <- Mscale_plus_distr_r.
    Msimpl_light. restore_dims.
    unfold scale, Mplus in *. 
    setoid_rewrite (IHn u1 P1); try lia.
    setoid_rewrite (IHn u2 P2); try lia.
    clear.
    rewrite <- RtoC_plus, <- RtoC_mult. 
    apply f_equal2; trivial. 
    rewrite plus_INR. 
    field_simplify_eq; trivial. 
    nonzero.
Qed.

(* accept := probability of measuring ∣0...0⟩ in the last n qubits is 1 *)
Definition accept' {n : nat} {U : base_ucom (S n)} (P : boolean U) : Prop :=
  @probability_of_outcome (2 ^ (S n)) 
    (uc_eval (deutsch_jozsa' U) × ((S n) ⨂ ∣0⟩)) 
    (∣1⟩ ⊗ n ⨂ ∣0⟩) = 1. 

(* reject := probability of measuring ∣0...0⟩ in the last n qubits is 0 *)
Definition reject' {n : nat} {U : base_ucom (S n)} (P : boolean U) : Prop :=
  @probability_of_outcome (2 ^ (S n)) 
    (uc_eval (deutsch_jozsa' U) × ((S n) ⨂ ∣0⟩)) 
    (∣1⟩ ⊗ n ⨂ ∣0⟩) = 0. 

Theorem deutsch_jozsa_constant_correct' :
  forall (n : nat) (U : base_ucom (S n)) (P : boolean U), constant' P -> accept' P.
Proof.
  intros n U P H. 
  unfold accept', probability_of_outcome.  
  restore_dims.
  rewrite <- Mmult_assoc.
  rewrite (deutsch_jozsa_success_probability' P). 
  destruct H; rewrite H; simpl; try lra.
  autorewrite with R_db.
  rewrite pow_INR. simpl. replace (1 + 1) with 2 by lra.
  field_simplify_eq; trivial.
  nonzero.
Qed.

Theorem deutsch_jozsa_balanced_correct' :
  forall (n : nat) (U : base_ucom (S n)) (P : boolean U), balanced' P -> reject' P.
Proof.
  intros n U P [H1 H2].
  unfold reject', probability_of_outcome. 
  restore_dims.
  rewrite <- Mmult_assoc.
  rewrite (deutsch_jozsa_success_probability' P).
  rewrite H2; simpl.
  autorewrite with R_db.
  rewrite pow_INR. simpl. replace (1 + 1) with 2 by lra.
  replace (2 * 2 ^ (n - 1) * / 2 ^ n) with 1.
  2: { field_simplify_eq; try nonzero.
       rewrite tech_pow_Rmult. 
       replace (S (n - 1)) with n by lia. 
       reflexivity. }
  lra.
Qed.
