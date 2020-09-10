Require Import UnitaryOps.
Require Import NDSem. (* just for the defn of norm *)
Local Open Scope ucom_scope.

(** Definition of Simon's program. **)
(* In Simon's problem, we are given a program U that encodes the function 
     f : {0,1}^n → {0,1}^n 
   with the property that 
     f(x) = f(y) iff x = y or x = y ⊕ s, for some unknown s.
   The goal of Simon's algorithm is to recover s. This can be done by running 
   the program below n times and performing some classical post-processing 
   (not shown here). *)

Definition simon {n} (U : base_ucom (2 * n)) : base_ucom (2 * n) :=
  cast (npar n U_H) (2 * n) ; U; cast (npar n U_H) (2 * n).

(** Preliminaries for simplifying the result of Simon's. **)

Local Open Scope C_scope.
Local Open Scope R_scope.

Definition boolean_oracle {n} (U : base_ucom (2 * n)) (f : nat -> nat) :=
  forall (x :nat), (x < 2 ^ n)%nat -> 
    @Mmult _ _ 1 (uc_eval U) (basis_vector (2 ^ n) x ⊗ basis_vector (2 ^ n) 0) = 
      basis_vector (2 ^ n) x ⊗ ((basis_vector (2 ^ n) (f x))).

Local Opaque Nat.mul.
Lemma two_n_kron_n: forall {m p} n (A : Matrix m p),
  WF_Matrix A -> (2 * n) ⨂ A = (n ⨂ A) ⊗ (n ⨂ A).
Proof.
  intros.
  induction n.
  simpl.
  Msimpl.
  reflexivity.
  replace (2 * (S n))%nat with (S (S (2 * n))) by lia.
  rewrite kron_n_assoc by assumption.
  rewrite (kron_n_assoc n) at 1 by assumption. 
  simpl.
  rewrite IHn.
  replace (m ^ (2 * n))%nat with (m ^ n * m ^ n)%nat.
  replace (p ^ (2 * n))%nat with (p ^ n * p ^ n)%nat.
  repeat rewrite kron_assoc. 
  restore_dims.
  reflexivity.
  1,2: replace (2 * n)%nat with (n + n)%nat by lia.
  1,2: rewrite Nat.pow_add_r; reflexivity.
Qed.

Lemma kron_n_0_is_0_vector : forall (n:nat), n ⨂ ∣0⟩ = basis_vector (2 ^ n) 0%nat.
Proof.
  intros.
  induction n.
  simpl.
  prep_matrix_equality.
  unfold basis_vector, I.
  bdestruct_all; reflexivity.
  simpl.
  rewrite IHn. replace (1 ^ n)%nat with 1%nat.
  rewrite (basis_vector_append_0 (2 ^ n) 0).
  rewrite Nat.mul_0_r.
  reflexivity.
  apply Nat.pow_nonzero. lia.
  apply pow_positive. lia.
  rewrite Nat.pow_1_l. reflexivity.
Qed.

Lemma simon_simplify : forall {n : nat} (U : base_ucom (2 * n)) f x,
   (n > 0)%nat -> (x < 2 ^ n)%nat ->
   boolean_oracle U f ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   @Mmult _ _ 1%nat ((basis_vector (2 ^ n) x)† ⊗ I (2 ^ n)) ((uc_eval (simon U)) × ((2 * n) ⨂ ∣0⟩)) = 
   / 2 ^ n .* vsum (2 ^ n) 
                (fun i => (-1) 
                   ^ Nat.b2n (product (nat_to_funbool n i) (nat_to_funbool n x) n)
                  .* basis_vector (2 ^ n) (f i)).
Proof.
  intros.
  unfold simon.
  simpl.
  (* why can't I do 'replace (2 * n)%nat with (n + n)%nat by lia.' here? *)
  assert (uc_eval (cast (npar n U_H) (2 * n)) = uc_eval (npar n U_H) ⊗ I (2 ^ n)).
  { replace (2 * n)%nat with (n + n)%nat by lia.
    rewrite <- pad_dims_r.
    reflexivity.
    apply npar_WT; assumption. }
  rewrite H3; clear H3.
  rewrite npar_H by assumption.
  rewrite two_n_kron_n.
  2: auto with wf_db. 
  repeat rewrite Mmult_assoc.
  replace (2 ^ (2 * n))%nat with  (2 ^ n * 2 ^ n)%nat.
  replace (1 ^ (2 * n))%nat with  (1 ^ n * 1 ^ n)%nat.
  Qsimpl.
  rewrite H0_kron_n_spec_alt by auto. 
  restore_dims.
  distribute_scale.
  replace (1 ^ n)%nat with 1%nat.
  rewrite kron_vsum_distr_r.
  replace (2 ^ (2 * n))%nat with  (2 ^ n * 2 ^ n)%nat.
  repeat rewrite Mmult_vsum_distr_l.
  rewrite kron_n_0_is_0_vector.
  erewrite vsum_eq.
  2: { intros i Hi. 
       unfold boolean_oracle in H1.
       replace ((2 ^ n) * (2 ^ n))%nat with (2 ^ (2 * n))%nat. 
       rewrite (H1 i) by assumption.
       Qsimpl. Search hadamard.
       replace (basis_vector (2 ^ n) i) with (f_to_vec n (nat_to_funbool n i)). 
       rewrite H_kron_n_spec by assumption. 
       distribute_scale.
       rewrite Mmult_vsum_distr_l.
       erewrite vsum_unique.
       2:{ exists x.
           split; [assumption | split].
           distribute_scale. 
           rewrite basis_vector_product_eq by lia.
           reflexivity.
           intros.
           distribute_scale. 
           rewrite basis_vector_product_neq by lia.
           lma. }
       distribute_scale. 
       Qsimpl.
       restore_dims.
       reflexivity.
       rewrite basis_f_to_vec_alt by assumption.
       reflexivity.
       unify_pows_two. }
  repeat rewrite Nat.mul_1_l.
  rewrite 2 Mscale_vsum_distr_r. 
  apply vsum_eq. 
  intros i Hi. 
  distribute_scale.
  apply f_equal2; try reflexivity.
  rewrite Cmult_assoc.
  apply f_equal2; try reflexivity.
  rewrite RtoC_pow.
  repeat rewrite <- RtoC_inv by nonzero.
  rewrite <- RtoC_mult.
  rewrite <- Rinv_mult_distr by nonzero.
  rewrite sqrt_def. 
  reflexivity.
  apply pow_le. lra.
  1,4: unify_pows_two.
  1,2: repeat rewrite Nat.pow_1_l; lia.
Qed.

(** Easy case: s = 0 **)
(* The proof of Simon algorithm can be divided into two cases: one where the 
   hidden value s is 0 and one where s is nonzero. In the first case, the output
   of Simon's will be an even distribution over all possible output states. *)

Lemma norm_scale : forall {n} c (v : Vector n), norm (c .* v) = (Cmod c) * norm v.
Proof.
  intros n c v.
  unfold norm.
  rewrite Mscale_adj.
  distribute_scale.
  unfold scale.
  simpl.
  replace (fst c * snd c + - snd c * fst c) with 0.
  autorewrite with R_db C_db.
  replace (fst c * fst c) with (fst c ^ 2) by lra.
  replace (snd c * snd c) with (snd c ^ 2) by lra.
  rewrite sqrt_mult_alt.
  reflexivity.
  apply Rplus_le_le_0_compat; apply pow2_ge_0.
  lra.  
Qed.

Lemma product_of_vsums : forall n m a b f,
  (n <= m)%nat ->
  (forall x, (x < n)%nat -> (f x < m)%nat) ->         (* f is bounded *)
  (forall x y, (x < n)%nat -> (y < n)%nat ->
          f x = f y -> x = y) ->             (* f is injective *)
  (vsum n (fun i : nat => (a i) .* basis_vector m (f i)))†
    × (vsum n (fun i : nat => (b i) .* basis_vector m (f i))) 
  = Csum (fun i => ((a i) ^* * b i)%C) n .* I 1.
Proof.
  intros n m a b f Hn Hf1 Hf2.
  induction n; simpl vsum. 
  simpl Csum. Msimpl. reflexivity.
  rewrite Mplus_adjoint.
  distribute_plus.
  rewrite IHn; try lia.
  2: intros; apply Hf1; lia.
  2: intros; apply Hf2; lia.
  rewrite Mscale_adj.
  distribute_scale.
  rewrite basis_vector_product_eq. 
  2: apply Hf1; lia.
  rewrite Mmult_vsum_distr_l.
  erewrite vsum_0.
  2: { intros x Hx. distribute_scale. 
       rewrite basis_vector_product_neq.
       lma. 
       1,2: apply Hf1; lia.
       intro contra. 
       apply Hf2 in contra; lia. }
  rewrite <- (adjoint_involutive _ _ (basis_vector m (f n))).
  rewrite <- Mmult_adjoint.
  rewrite Mmult_vsum_distr_l.
  erewrite vsum_0.
  2: { intros x Hx. distribute_scale. 
       rewrite basis_vector_product_neq.
       lma.
       1,2: apply Hf1; lia.
       intro contra. 
       apply Hf2 in contra; lia. }
  Msimpl.
  simpl Csum.
  rewrite Mscale_plus_distr_l.
  reflexivity.
Qed.

Lemma norm_vsum : forall n d c f,
  (n <= d)%nat ->
  (forall x, (x < n)%nat -> (f x < d)%nat) ->
  (forall x y, (x < n)%nat -> (y < n)%nat -> f x = f y -> x = y) -> 
  norm (vsum n (fun i : nat => (c i) .* basis_vector d (f i))) = 
    √ (fst (Csum (fun i => ((c i) ^* * c i)%C) n)).
Proof.
  intros n d c f ? ? ?.
  unfold norm.
  rewrite product_of_vsums; auto; try lia. 
  simpl. autorewrite with R_db.
  reflexivity.
Qed.

Theorem simon_zero : forall {n : nat} (U : base_ucom (2 * n)) f x,
   (n > 0)%nat -> (x < 2 ^ n)%nat ->
   boolean_oracle U f ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->     (* f is bounded *)
   (forall x y, (x < 2 ^ n)%nat -> f x = f y <-> x = y) -> (* f x = f y <-> x = y *)
   @norm (2 ^ n) 
         (@Mmult _ _ 1%nat ((basis_vector (2^n) x)† ⊗ I (2 ^n)) 
                         ((uc_eval (simon U)) × ((2 * n) ⨂ ∣0⟩))) 
   = sqrt (1 /2 ^ n).
Proof.
  intros. 
  erewrite simon_simplify with (f0:=f); auto.
  rewrite norm_scale.
  rewrite norm_vsum; auto.
  rewrite Csum_1.
  simpl.
  rewrite RtoC_pow.
  rewrite <- RtoC_inv by nonzero.
  rewrite pow_INR.
  unfold Cmod; simpl.
  replace (1 + 1)%R with 2 by lra.
  autorewrite with R_db.
  rewrite <- sqrt_mult_alt.
  rewrite Rmult_assoc.
  rewrite Rinv_l by nonzero.
  autorewrite with R_db.
  reflexivity.
  apply Rmult_le_pos.
  1,2: left; apply Rinv_0_lt_compat, pow_lt; lra.
  intro x0.
  destruct (product (nat_to_funbool n x0) (nat_to_funbool n x) n); simpl; lca.
  intros. apply H3; auto.
Qed.

(** Hard case: s <> 0 **)
(* In the second case (s != 0), the program will output a string y
   such that y ⋅ s = 0. Each possible y is output with probability
   1 / 2 ^ (n - 1). *)

Definition bitwise_xor n x y := 
  let n1f := nat_to_funbool n x in
  let n2f := nat_to_funbool n y in
  funbool_to_nat n (fun i => xorb (n1f i) (n2f i)).

Definition bitwise_product n x y :=
  product (nat_to_funbool n x) (nat_to_funbool n y) n.

Lemma bitwise_xor_bound : forall (n x y: nat), (bitwise_xor n x y < 2 ^ n)%nat. 
Proof.
  intros.
  unfold bitwise_xor. 
  apply funbool_to_nat_bound.
Qed.

Lemma bitwise_xor_eq: forall (n x: nat), (bitwise_xor n x x = 0)%nat.
Proof.
  intros.
  unfold bitwise_xor.
  erewrite funbool_to_nat_eq.
  2: { intros.
       rewrite xorb_nilpotent.
       reflexivity. }
  rewrite <- (nat_to_funbool_0 n).
 rewrite nat_to_funbool_inverse. 
 reflexivity.
 apply pow_positive. lia.
Qed.

Lemma bitwise_xor_0_l : forall n x,
  (x < 2 ^ n)%nat -> bitwise_xor n 0 x = x.
Proof.
  intros.
  unfold bitwise_xor.
  rewrite nat_to_funbool_0.
  replace (funbool_to_nat n (fun i : nat => false ⊕ nat_to_funbool n x i)) 
    with (funbool_to_nat n (nat_to_funbool n x)).
  apply nat_to_funbool_inverse; auto.
  apply f_equal2; auto.
  apply functional_extensionality.
  intros.
  rewrite xorb_false_l. 
  reflexivity.
Qed.

Lemma bitwise_xor_assoc : forall n x y z,
  bitwise_xor n x (bitwise_xor n y z) = bitwise_xor n (bitwise_xor n x y) z.
Proof.
  intros.
  unfold bitwise_xor.
  apply funbool_to_nat_eq.
  intros.
  rewrite 2 funbool_to_nat_inverse by assumption.
  rewrite <- xorb_assoc.
  reflexivity.
Qed.

Lemma bitwise_xor_comm: forall n x y,
          bitwise_xor n x y = bitwise_xor n y x.
Proof.
  intros.
  unfold bitwise_xor.
  eapply funbool_to_nat_eq.
  intros.
  rewrite <- xorb_comm.
  reflexivity.
Qed.

Lemma bitwise_xor_0_l_strong : forall n x y,
  (y < 2 ^ n)%nat -> bitwise_xor n y x = x -> y = O.
Proof.
  intros.
  assert (bitwise_xor n x (bitwise_xor n y x) = bitwise_xor n x x) by auto.
  rewrite (bitwise_xor_comm _ y) in H1.
  rewrite bitwise_xor_assoc in H1.
  rewrite bitwise_xor_eq in H1.
  rewrite bitwise_xor_0_l in H1 by auto.
  assumption.
Qed.

Lemma bitwise_product_xor_distr : forall n x y z,
  bitwise_product n (bitwise_xor n x y) z =
    (bitwise_product n x z) ⊕ (bitwise_product n y z).
Proof.
  intros.
  unfold bitwise_product. 
  assert (forall m, (n <= m)%nat ->
    product (nat_to_funbool m (bitwise_xor m x y)) (nat_to_funbool m z) n =
    product (nat_to_funbool m x) (nat_to_funbool m z) n
      ⊕ product (nat_to_funbool m y) (nat_to_funbool m z) n).
  { intros.
    induction n.
    reflexivity.
    simpl.
    rewrite IHn by lia.
    unfold bitwise_xor.
    rewrite funbool_to_nat_inverse by lia.
    rewrite andb_comm.
    rewrite andb_xorb_dist.  
    rewrite 2 (andb_comm (nat_to_funbool _ z _)).
    rewrite (xorb_assoc _ _ (xorb _ _)).
    rewrite <- (xorb_assoc _ (product _ _ _) (product _ _ _)).
    rewrite (xorb_comm (andb _ _) (product _ _ _)).
    repeat rewrite xorb_assoc.
    reflexivity. }
  apply H.
  lia.
Qed.

Definition to_injective n s f x :=
  let y := bitwise_xor n x s in 
  if (x <? y)%nat then f x else ((2 ^ n)%nat + f x)%nat.

Lemma to_injective_is_injective (n s:nat) (f:nat -> nat) : 
   (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s \/ x = y) ->
   (forall x y, (x < (2 ^ n))%nat -> (y < (2 ^ n))%nat -> 
        to_injective n s f x = to_injective n s f y -> x = y).
Proof.
  intros.
  unfold to_injective in H6.
  bdestruct (x <? bitwise_xor n x s).
  bdestruct (y <? bitwise_xor n y s).
  rewrite H3 in H6; auto.
  destruct H6; auto.
  rewrite <- H6 in H7.
  rewrite bitwise_xor_assoc, bitwise_xor_eq in H7.
  rewrite bitwise_xor_0_l in H7; auto.
  rewrite <- H6 in H8.
  rewrite (bitwise_xor_comm n x), bitwise_xor_assoc, bitwise_xor_eq in H8.
  rewrite bitwise_xor_0_l in H8; auto.
  lia.
  assert (f x < 2 ^ n)%nat by auto.
  lia.
  bdestruct (y <? bitwise_xor n y s).
  assert (f y < 2 ^ n)%nat by auto.
  lia.
  assert (f x = f y)%nat by lia.
  rewrite H3 in H9; auto.
  destruct H9; auto.
  rewrite <- H9 in H7.
  rewrite bitwise_xor_assoc, bitwise_xor_eq in H7.
  rewrite bitwise_xor_0_l in H7; auto.
  rewrite <- H9 in H8.
  rewrite (bitwise_xor_comm n x), bitwise_xor_assoc, bitwise_xor_eq in H8.
  rewrite bitwise_xor_0_l in H8; auto.
  lia.
Qed.

Lemma bitwise_xor_bijective: forall (n s: nat), 
   (n > 0)%nat -> (s < 2 ^ n)%nat ->
   weak_finite_bijection (2 ^ n) (fun i => bitwise_xor n i s).
Proof.
  intros.
  split. 
  intros.
  apply bitwise_xor_bound.
  exists (fun i => bitwise_xor n i s).
  repeat split; intros.
  apply bitwise_xor_bound.
  rewrite <- bitwise_xor_assoc, bitwise_xor_eq, bitwise_xor_comm.
  apply bitwise_xor_0_l.
  assumption.
  rewrite <- bitwise_xor_assoc, bitwise_xor_eq, bitwise_xor_comm.
  apply bitwise_xor_0_l.
  assumption.
Qed.

Lemma bitwise_xor_vsum_reorder: forall (n m s :nat) (f:nat -> nat) a, 
  (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
  vsum (2 ^ n) (fun i : nat => (a i) .* basis_vector m (f (bitwise_xor n i s))) =
  vsum (2 ^ n) (fun i : nat => (a (bitwise_xor n i s)) .* basis_vector m (f i)).
Proof.
  intros.
  rewrite vsum_reorder with (f0:= (fun i => bitwise_xor n i s)).
  erewrite vsum_eq.
  2: { intros.
       rewrite (bitwise_xor_comm _ (bitwise_xor _ _ _)).
       rewrite (bitwise_xor_comm _ _ s) at 2.
       rewrite bitwise_xor_assoc, bitwise_xor_eq, bitwise_xor_0_l.
       reflexivity.
       assumption. }
  reflexivity.
  apply bitwise_xor_bijective; auto.
Qed.

Lemma vsum_to_injective : forall n s f a,
  (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
  (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
  (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
       f x = f y <-> (bitwise_xor n x y = s \/ x = y)) ->
  vsum (2 ^ n) (fun i : nat => 
               (a i + a (bitwise_xor n i s)) .* 
                  (basis_vector (2 * 2 ^ n) ((to_injective n s f) i))) =
    (∣0⟩ .+ ∣1⟩) ⊗ vsum (2 ^ n) (fun i : nat => a i .* basis_vector (2 ^ n) (f i)).
Proof.
  intros.
  erewrite vsum_eq.
  2: { intros.
       rewrite -> Mscale_plus_distr_l.
       reflexivity. }
  rewrite vsum_plus.
  rewrite <- bitwise_xor_vsum_reorder; auto.
  rewrite <- vsum_plus.
  erewrite vsum_eq.
  2: { intros.
       rewrite <- Mscale_plus_distr_r.
       unfold to_injective.
       rewrite <- bitwise_xor_assoc, bitwise_xor_eq.
       rewrite (bitwise_xor_comm _ _ 0), bitwise_xor_0_l; auto.
       replace (f (bitwise_xor n i s)) with (f i).
       bdestruct (i <? bitwise_xor n i s).
       bdestructΩ (bitwise_xor n i s <? i).
       rewrite <- basis_vector_prepend_0.
       rewrite Nat.add_comm.
       rewrite <- basis_vector_prepend_1.
       restore_dims.
       rewrite <- kron_plus_distr_r.
       rewrite <- Mscale_kron_dist_r.
       reflexivity.
       1,3: lia.
       1,2: auto. 
       assert (bitwise_xor n i s <> i).
       intro contra.
       rewrite bitwise_xor_comm in contra.
       apply bitwise_xor_0_l_strong in contra; auto.
       lia.
       bdestructΩ (bitwise_xor n i s <? i).
       rewrite Nat.add_comm.
       rewrite <- basis_vector_prepend_1.
       rewrite <- basis_vector_prepend_0.
       restore_dims.
       rewrite <- kron_plus_distr_r.
       rewrite Mplus_comm.
       rewrite <- Mscale_kron_dist_r.
       reflexivity.
       1,3: lia.
       1,2: auto. 
       rewrite H3.
       left.
       rewrite bitwise_xor_assoc, bitwise_xor_eq.
       apply bitwise_xor_0_l.
       1,2: assumption. 
       apply bitwise_xor_bound. }
  rewrite <- kron_vsum_distr_l.
  reflexivity.
Qed.

Lemma norm_vsum_rewrite: forall (n s:nat) (f:nat -> nat) a,
  (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
  (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
  (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
       f x = f y <-> (bitwise_xor n x y = s \/ x = y)) ->
  norm (vsum (2 ^ n) (fun i : nat => (a i) .* (basis_vector (2 ^ n) (f i)))) = 
    (sqrt (1 / 2)) * 
       norm (vsum (2 ^ n) (fun i : nat => 
               (a i + a (bitwise_xor n i s)) .* 
                 (basis_vector (2 * 2 ^ n) ((to_injective n s f) i)))).
Proof.
  intros. 
  rewrite vsum_to_injective by assumption.
  unfold norm.
  Msimpl.
  rewrite Mmult_plus_distr_l.
  rewrite 2 Mmult_plus_distr_r.
  Qsimpl.
  replace (I 1 .+ I 1) with (2 .* I 1) by solve_matrix.
  rewrite Mscale_kron_dist_l.
  Msimpl.
  unfold scale; simpl.
  autorewrite with R_db.
  rewrite sqrt_mult_alt by lra. 
  rewrite <- Rmult_assoc.
  rewrite <- sqrt_mult_alt by lra. 
  rewrite Rinv_l by lra. 
  rewrite sqrt_1, Rmult_1_l. 
  reflexivity.
Qed.

(* If s ⋅ x = 0, then the probability that simon outputs x is (1 / 2 ^ (n - 1)). *)
Theorem simon_nonzero_A : forall {n : nat} (U : base_ucom (2 * n)) f x s,
   (n > 0)%nat -> (x < 2 ^ n)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   boolean_oracle U f ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> (bitwise_xor n x y = s \/ x = y)) ->
   bitwise_product n s x = false ->
   @norm (2 ^ n) (@Mmult _ _ 1%nat ((basis_vector (2 ^ n) x)† ⊗ I (2 ^ n)) 
                                 ((uc_eval (simon U)) × ((2 * n) ⨂ ∣0⟩)))
                      = sqrt (1 /2 ^ (n - 1)).
Proof.
  intros. 
  rewrite simon_simplify with (f0:=f); auto.
  rewrite norm_scale.
  rewrite norm_vsum_rewrite with (s:=s) by assumption.
  rewrite norm_vsum.
  erewrite Csum_eq_bounded.
  2: { intros i Hi.
       replace (product (nat_to_funbool n i) (nat_to_funbool n x) n) 
         with (bitwise_product n i x) by reflexivity.
       replace (product (nat_to_funbool n (bitwise_xor n i s)) (nat_to_funbool n x) n) 
         with (bitwise_product n (bitwise_xor n i s) x) by reflexivity.
       rewrite bitwise_product_xor_distr.
       rewrite H6.
       rewrite xorb_false_r.
       remember (bitwise_product n i x) as b.
       repeat rewrite RtoC_pow.
       rewrite <- RtoC_plus.
       unfold Cconj; simpl.
       rewrite Ropp_0.
       replace (((-1) ^ Nat.b2n b + (-1) ^ Nat.b2n b)%R, 0)%C with (RtoC ((-1) ^ Nat.b2n b + (-1) ^ Nat.b2n b)%R) by reflexivity.
       rewrite <- RtoC_mult.
       replace (((-1) ^ Nat.b2n b + (-1) ^ Nat.b2n b) * ((-1) ^ Nat.b2n b + (-1) ^ Nat.b2n b)) with (2 ^ 2).
       reflexivity.
       destruct b; simpl; lra. }
  rewrite Csum_constant.
  simpl.
  rewrite RtoC_pow.
  rewrite <- RtoC_inv by nonzero.
  rewrite pow_INR.
  unfold Cmod; simpl.
  replace (1 + 1)%R with 2 by lra.
  autorewrite with R_db.
  rewrite <- sqrt_mult_alt.
  rewrite <- sqrt_mult_alt.
  apply f_equal.
  replace (2 ^ n) with (2 * 2 ^ (n - 1)).
  field_simplify_eq; nonzero.
  replace (2 * 2 ^ (n - 1)) with (2 ^ 1 * 2 ^ (n - 1)) by lra. 
  rewrite <- pow_add.
  replace (1 + (n - 1))%nat with n by lia.
  reflexivity.
  apply Rmult_le_pos.
  1,2: left; apply Rinv_0_lt_compat, pow_lt; lra. 
  lra.
  lia.
  intros. unfold to_injective.
  apply H4 in H7.
  destruct (x0 <? bitwise_xor n x0 s); lia.
  intros.
  apply to_injective_is_injective in H9; auto.
Qed.

(* If s ⋅ x = 1, then the probability that simon outputs x is 0. *)
Theorem simon_nonzero_B : forall {n : nat} (U : base_ucom (2 * n)) f x s,
   (n > 0)%nat -> (x < 2 ^ n)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   boolean_oracle U f ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> (bitwise_xor n x y = s \/ x = y)) ->
   bitwise_product n s x = true ->
   @norm (2 ^ n) (@Mmult _ _ 1%nat ((basis_vector (2 ^ n) x)† ⊗ I (2 ^ n)) 
                                 ((uc_eval (simon U)) × ((2 * n) ⨂ ∣0⟩)))
                      = 0.
Proof.
  intros. 
  rewrite simon_simplify with (f0:=f); auto.
  rewrite norm_scale.
  rewrite norm_vsum_rewrite with (s:=s) by assumption.
  rewrite norm_vsum.
  erewrite Csum_0.
  2: { intro i.
       replace (product (nat_to_funbool n i) (nat_to_funbool n x) n) 
         with (bitwise_product n i x) by reflexivity.
       replace (product (nat_to_funbool n (bitwise_xor n i s)) (nat_to_funbool n x) n) 
         with (bitwise_product n (bitwise_xor n i s) x) by reflexivity.
       rewrite bitwise_product_xor_distr.
       rewrite H6.
       remember (bitwise_product n i x) as b.
       repeat rewrite RtoC_pow.
       rewrite <- RtoC_plus.
       unfold Cconj; simpl.
       rewrite Ropp_0.
       replace (((-1) ^ Nat.b2n b + (-1) ^ Nat.b2n (b ⊕ true))%R, 0)%C with (RtoC ((-1) ^ Nat.b2n b + (-1) ^ Nat.b2n (b ⊕ true))%R) by reflexivity.
       rewrite <- RtoC_mult.
       apply f_equal.
       destruct b; simpl; lra. }
  simpl.
  rewrite sqrt_0.
  lra.
  lia.
  intros. unfold to_injective.
  apply H4 in H7.
  destruct (x0 <? bitwise_xor n x0 s); lia.
  intros.
  apply to_injective_is_injective in H9; auto.
Qed.