Require Import List.
Require Import UnitaryOps.
Require Import Dirac.

Open Scope ucom.
Local Close Scope C_scope.
Local Close Scope R_scope.

(* Definition of Deutsch-Jozsa program. *)

Definition deutsch_jozsa {n} (U : base_ucom n) : base_ucom n :=
  X 0 ; npar n U_H ; U; npar n U_H.

(* Definition of boolean oracles *)

Inductive boolean : forall {n}, base_ucom (S n) -> Set :=
  | boolean_I : forall u, u ≡ SKIP -> @boolean 0 u
  | boolean_X : forall u, u ≡ X 0  -> @boolean 0 u
  | boolean_U : forall dim (u : base_ucom (S (S dim))) (u1 u2 : base_ucom (S dim)),
                boolean u1 -> boolean u2 ->
                uc_eval u = (uc_eval u1 ⊗ ∣0⟩⟨0∣) .+ (uc_eval u2 ⊗ ∣1⟩⟨1∣) ->
                boolean u.
  
Fixpoint count {dim : nat} {u : base_ucom (S dim)} (P : boolean u) : nat :=
  match P with
  | boolean_I _ _ => 0
  | boolean_X _ _ => 1
  | boolean_U _ _ _ _ P1 P2 _ => (count P1 + count P2)
  end.

Definition balanced {dim : nat} {u : base_ucom (S dim)} (P : boolean u) : Prop :=
  dim > 0 /\ count P = 2 ^ (dim - 1).

Definition constant {dim : nat} {u : base_ucom (S dim)} (P : boolean u) : Prop :=
  count P = 0 \/ count P = 2 ^ dim.

Local Open Scope C_scope.
Local Open Scope R_scope.

(* In the Deutsch Jozsa problem we care about the probability of measuring ∣0...0⟩
   in the last n qubits (the 1st qubit always ends up in the ∣1⟩ state). *)
Lemma deutsch_jozsa_success_probability :
  forall {n : nat} {U : base_ucom (S n)} (P : boolean U),
  ((∣1⟩ ⊗ n ⨂ ∣0⟩)† × (uc_eval (deutsch_jozsa U)) × ((S n) ⨂ ∣0⟩)) 0%nat 0%nat = 1 - 2 * INR (count P) * /2 ^ n.
Proof.
  intros.
  unfold deutsch_jozsa. 
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

(* When measuring ψ, what is the probability that the outcome is o? *)
Definition probability_of_outcome {n} (ψ o : Vector n) :=
  let c := (o† × ψ) 0%nat 0%nat in
  Re c ^ 2 + Im c ^ 2.

(* accept := probability of measuring ∣0...0⟩ in the last n qubits is 1 *)
Definition accept {n : nat} {U : base_ucom (S n)} (P : boolean U) : Prop :=
  @probability_of_outcome (2 ^ (S n)) (uc_eval (deutsch_jozsa U) × ((S n) ⨂ ∣0⟩)) (∣1⟩ ⊗ n ⨂ ∣0⟩) = 1. 

(* reject := probability of measuring ∣0...0⟩ in the last n qubits is 0 *)
Definition reject {n : nat} {U : base_ucom (S n)} (P : boolean U) : Prop :=
  @probability_of_outcome (2 ^ (S n)) (uc_eval (deutsch_jozsa U) × ((S n) ⨂ ∣0⟩)) (∣1⟩ ⊗ n ⨂ ∣0⟩) = 0. 

Theorem deutsch_jozsa_constant_correct :
  forall (n : nat) (U : base_ucom (S n)) (P : boolean U), constant P -> accept P.
Proof.
  intros n U P H. 
  unfold accept, probability_of_outcome.  
  restore_dims.
  rewrite <- Mmult_assoc.
  rewrite (deutsch_jozsa_success_probability P). 
  destruct H; rewrite H; simpl; try lra.
  autorewrite with R_db.
  rewrite pow_INR. simpl. replace (1 + 1) with 2 by lra.
  field_simplify_eq; trivial.
  nonzero.
Qed.

Theorem deutsch_jozsa_balanced_correct :
  forall (n : nat) (U : base_ucom (S n)) (P : boolean U), balanced P -> reject P.
Proof.
  intros n U P [H1 H2].
  unfold reject, probability_of_outcome. 
  restore_dims.
  rewrite <- Mmult_assoc.
  rewrite (deutsch_jozsa_success_probability P).
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


