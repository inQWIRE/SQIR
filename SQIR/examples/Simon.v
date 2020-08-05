Require Import UnitaryOps.
Require Import NDSem. (* just for the defn of norm *)
Require Import Coq.Arith.EqNat.
Require Import Logic.Classical.
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

Lemma bitwise_xor_eq_aux: forall (n x: nat), (bitwise_xor n x x = 0)%nat.
Proof.
unfold bitwise_xor. intros.
assert ((fun i : nat => nat_to_funbool n x i ⊕ nat_to_funbool n x i) = (fun i : nat => false)).
apply functional_extensionality_dep. intros. rewrite -> xorb_nilpotent. reflexivity.
rewrite -> H.
rewrite <- (nat_to_funbool_0 n).
rewrite nat_to_funbool_inverse. reflexivity. 
apply Nat.lt_le_trans with (m := (2 ^ 0)%nat). simpl. lia.
apply Nat.pow_le_mono_r. lia. lia.
Qed.

Lemma bitwise_xor_eq: forall (n s x y: nat), (n > 0)%nat ->
       (x = y)%nat ->  bitwise_xor n x y = s -> (s = 0)%nat.
Proof.
intros.
rewrite H0 in H1.
rewrite bitwise_xor_eq_aux in H1.
rewrite -> H1. reflexivity.
Qed.

Lemma bitwise_xor_neq : forall (n s x y: nat), (n > 0)%nat -> (s <> 0)%nat -> (s < 2 ^ n)%nat
   -> (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> bitwise_xor n x y = s -> x <> y.
Proof.
intros.
intros conra.
apply bitwise_xor_eq in H4.
rewrite H4 in H0. contradiction.
1 - 2: assumption.
Qed.

Lemma bitwise_xor_bound : forall (n x y: nat), (bitwise_xor n x y < 2 ^ n)%nat. 
Proof.
intros.
unfold bitwise_xor. 
apply funbool_to_nat_bound.
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

Lemma bitwise_xor_cancel : forall n x y,
  (y < 2 ^ n)%nat ->
  bitwise_xor n x (bitwise_xor n x y) = y.
Proof.
  intros.
  unfold bitwise_xor.
  erewrite funbool_to_nat_eq.
  2: { intros.
       rewrite funbool_to_nat_inverse by assumption.
       rewrite <- xorb_assoc.
       rewrite xorb_nilpotent.
       rewrite xorb_false_l.
       reflexivity. }
 rewrite nat_to_funbool_inverse; auto. 
Qed.

Lemma bitwise_xor_comm: forall n x y,
          bitwise_xor n x y = bitwise_xor n y x.
Proof.
  intros.
  unfold bitwise_xor.
  erewrite funbool_to_nat_eq.
  2: { intros.
       rewrite <- xorb_comm.
       reflexivity. }
  reflexivity.
Qed.

Lemma xor_eq: forall (n x y s: nat),
  (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> (s < 2 ^ n)%nat ->
   (forall i : nat,
  (i < n)%nat ->
  nat_to_funbool n x i ⊕ nat_to_funbool n y i =
  nat_to_funbool n s i) <-> (forall i : nat,
  (i < n)%nat ->
  nat_to_funbool n y i =
  nat_to_funbool n x i ⊕ nat_to_funbool n s i).
Proof.
intros.
split.
unfold nat_to_funbool. simpl.
intros.
apply H2 in H3.
rewrite <- H3. unfold xorb.
destruct (list_to_funbool n (nat_to_binlist n x) i).
destruct (list_to_funbool n  (nat_to_binlist n  y) i). reflexivity. reflexivity.
destruct (list_to_funbool n  (nat_to_binlist n  y) i). reflexivity. reflexivity.
unfold nat_to_funbool. simpl.
intros.
apply H2 in H3.
rewrite -> H3. unfold xorb.
destruct (list_to_funbool n  (nat_to_binlist n  x) i).
destruct (list_to_funbool n  (nat_to_binlist n  s) i). reflexivity. reflexivity.
destruct (list_to_funbool n  (nat_to_binlist n  s) i). reflexivity. reflexivity.
Qed.

Lemma nat_to_funbool_fun_aux : forall (n:nat) f f', f = f' -> funbool_to_nat n f = funbool_to_nat n f'.
Proof.
intros. 
rewrite -> H. reflexivity.
Qed.

Lemma nat_to_funbool_funs_1_aux: forall (n:nat) (f f':nat -> bool), 
            (forall i : nat, (i < S n)%nat -> f i = f' i) ->
             (forall i : nat, (i < n)%nat -> f i = f' i).
Proof.
intros.
assert (i < S n)%nat.
apply Nat.lt_trans with (m := (n)%nat). apply H0.
simpl. lia.
apply H in H1. rewrite -> H1. reflexivity.
Qed.

Lemma nat_to_funbool_funs_1 : forall f f' n, (forall i:nat , (i < n)%nat -> f i = f' i)
         -> funbool_to_nat n f = funbool_to_nat n f'. 
Proof. 
intros.
unfold funbool_to_nat.
induction n.
simpl. reflexivity.
simpl.
assert (forall i : nat, (i < n)%nat -> f i = f' i).
apply nat_to_funbool_funs_1_aux. apply H.
apply IHn in H0.
rewrite -> H0.
assert (f n = f' n).
apply H. lia.
rewrite -> H1. reflexivity.
Qed.

Lemma forall_extend: forall (n:nat) (f f': nat -> bool), 
        (forall i:nat, (i < n)%nat -> f i = f' i)
          -> f n = f' n 
         -> (forall i:nat, (i < S n)%nat -> f i = f' i).
Proof.
intros.
assert ((i < n)%nat \/ (i = n)%nat). lia.
destruct H2. apply H in H2. apply H2.
rewrite H2. apply H0.
Qed.


Lemma nat_to_funbool_funs_2 : forall n f f', funbool_to_nat n f = funbool_to_nat n f'
    -> (forall i:nat , (i < n)%nat -> f i = f' i).
Proof.
intro n.
unfold funbool_to_nat.
induction n. intros. inversion H0.
intros f f' H.
simpl in H.
destruct (Nat.b2n (f n)) eqn:eq1.
destruct (Nat.b2n (f' n)) eqn:eq2.
assert (binlist_to_nat (funbool_to_list n f) = binlist_to_nat (funbool_to_list n f')).
lia.
specialize (IHn f f' H0).
apply forall_extend. apply IHn.
rewrite <- eq1 in eq2. unfold Nat.b2n in eq2.
destruct (f' n) eqn:eq3.
destruct (f n) eqn:eq4. reflexivity. inversion eq2.
destruct (f n) eqn:eq4. inversion eq2. reflexivity. 
destruct (n0).
assert (Nat.even (2 * binlist_to_nat (funbool_to_list n f)) = true). lia.
assert (Nat.even (2 * binlist_to_nat (funbool_to_list n f')) = true). lia.
simpl in H. rewrite H in H0.
rewrite Nat.even_succ in H0.
apply Nat.even_spec in H1. apply Nat.odd_spec in H0.
specialize (Nat.Even_Odd_False 
           (2 * binlist_to_nat (funbool_to_list n f')) H1 H0) as R.
inversion R.
unfold Nat.b2n in eq2.
destruct (f' n) eqn:eq3. inversion eq2. inversion eq2.
destruct (Nat.b2n (f' n)) eqn:eq2.
destruct (n0).
assert (Nat.even (2 * binlist_to_nat (funbool_to_list n f)) = true). lia.
assert (Nat.even (2 * binlist_to_nat (funbool_to_list n f')) = true). lia.
simpl in H. rewrite <- H in H1.
rewrite Nat.even_succ in H1.
apply Nat.even_spec in H0. apply Nat.odd_spec in H1.
specialize (Nat.Even_Odd_False 
           (2 * binlist_to_nat (funbool_to_list n f)) H0 H1) as R.
inversion R.
unfold Nat.b2n in eq1.
destruct (f n) eqn:eq3. inversion eq1. inversion eq1.
unfold Nat.b2n in eq1. unfold Nat.b2n in eq2.
destruct (f n) eqn:eq3.
destruct (f' n) eqn:eq4. 
rewrite <- eq1 in H. rewrite <- eq2 in H. simpl in H.
assert (binlist_to_nat (funbool_to_list n f) = binlist_to_nat (funbool_to_list n f')).
lia. specialize (IHn f f' H0).
apply forall_extend. apply IHn.
rewrite -> eq3. rewrite -> eq4. reflexivity.
inversion eq2. inversion eq1.
Qed.

Lemma bitwise_xor_assoc: forall (n x y s: nat), (n > 0)%nat -> 
       (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> (s < 2 ^ n)%nat ->
        bitwise_xor n x y = s <-> y = bitwise_xor n x s.
Proof.
intros.
unfold bitwise_xor.
specialize (nat_to_funbool_inverse n s) as H3.
apply H3 in H2 as H4.
rewrite <- H4.
specialize (nat_to_funbool_inverse n y) as H5.
apply H5 in H1 as H6.
rewrite <- H6.
split.
intros.
apply nat_to_funbool_funs_1.
specialize (nat_to_funbool_funs_2 n (fun i : nat =>
        nat_to_funbool n x i
        ⊕ nat_to_funbool n (funbool_to_nat n (nat_to_funbool n y)) i) (nat_to_funbool n s) H7).
simpl.
intros H8. apply xor_eq. assumption. assumption. apply funbool_to_nat_bound. 
rewrite -> H5 in H8. rewrite H4. apply H8. assumption.
intros.
apply nat_to_funbool_funs_1.
specialize (nat_to_funbool_funs_2 n (nat_to_funbool n y) (fun i : nat =>
        nat_to_funbool n x i
        ⊕ nat_to_funbool n (funbool_to_nat n (nat_to_funbool n s)) i) H7).
simpl.
intros H8. apply xor_eq. assumption. apply funbool_to_nat_bound. assumption.
rewrite -> H4 in H8. rewrite H5. apply H8. assumption.
Qed.

(* Another possibility is to define a function f which is one-to-one from f. 
   Since for all x f x < 2 ^ n, then the following is an injective function.
    But I don't know how to prove it in Coq. *)
Definition to_injective (n s:nat) (f:nat -> nat) : (nat -> nat) :=
    (fun x => let y := bitwise_xor n x s in if (x <? y)%nat then f x else ((2 ^ n)%nat + f x)%nat).

Definition rev_injective (n:nat) : (nat -> nat) :=
    (fun x => if (x <? n)%nat then x else (x - n)%nat).

Definition wf_basis_vector (n k : nat) : Vector n :=
  fun i j => if (i =? k) && (j =? 0) && (i <? n) then C1 else C0.

Lemma wf_basis_vector_product_eq : forall (d n:nat),
  (n < d)%nat -> (wf_basis_vector d n)† × wf_basis_vector d n = I 1.
Proof.
  intros. 
  prep_matrix_equality.
  unfold wf_basis_vector, adjoint, Mmult, I.
  bdestruct (x =? y); bdestruct (x <? 1); simpl.
  apply Csum_unique.
  exists n.
  repeat split; auto.
  bdestruct_all; simpl; lca.
  intros i Hi. bdestructΩ (i =? n). lca.
  all: apply Csum_0; intro i; bdestruct_all; simpl; lca.
Qed.

Lemma wf_basis_vector_product_neq : forall d m n,
  (m <> n)%nat 
           -> (wf_basis_vector d m)† × wf_basis_vector d n = Zero.
Proof.
  intros.
  prep_matrix_equality.
  unfold wf_basis_vector, adjoint, Mmult, Zero.
  apply Csum_0. 
  intro i; bdestruct_all; lca.
Qed.

Lemma self_lt_not_aux: forall (n:nat), S n <> n.
Proof.
intro n.
induction n.
intros H.
inversion H.
intros H.
inversion H.
rewrite <- H1 in IHn at 2.
contradiction.
Qed.

Lemma self_lt_not: forall (n:nat), (n < n)%nat -> False.
Proof.
intro n.
induction n.
intros. inversion H.
intros. inversion H.
specialize (self_lt_not_aux n). intros.
rewrite <- H1 in H0 at 2.
contradiction.
apply lt_S_n in H.
apply IHn in H.
contradiction.
Qed.

Lemma plus_greater: forall (n x:nat), (n <= n + x)%nat.
Proof.
induction n.
intros. lia.
simpl. intros. lia.
Qed.

Lemma less_false: forall (x y:nat), (x <? y)%nat = false -> (y <= x)%nat.
Proof.
intros.
specialize (Nat.ltb_lt x y) as H1.
assert ((x <? y) = false <-> ~ (x < y)%nat).
split.
intros.
destruct H1. intros R. apply H2 in R. rewrite R in H0. inversion H0.
intros. apply H. apply H0 in H.
lia.
Qed.

Lemma lesseq_false: forall (x y:nat), (x <=? y)%nat = false -> (y < x)%nat.
Proof.
intros.
specialize (Nat.leb_le x y) as H1.
assert ((x <=? y) = false <-> ~ (x <= y)%nat).
split.
intros.
destruct H1. intros R. apply H2 in R. rewrite R in H0. inversion H0.
intros. apply H. apply H0 in H.
lia.
Qed.

Lemma to_injective_aux (n s:nat) (f:nat -> nat) : 
   (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s) ->
      (exists (x y:nat), (x < 2 ^ n)%nat /\ (y < 2 ^ n)%nat /\ x <> y 
          /\ (to_injective n s f) x = (to_injective n s f) y ) -> False.
Proof.
intros.
destruct H4. destruct H4. destruct H4.
destruct H5. destruct H6.
unfold to_injective in H7.
specialize (H3 x x0 H4 H5) as eq.
destruct (x <? bitwise_xor n x s) eqn:eq1.
destruct (x0 <? bitwise_xor n x0 s) eqn:eq2.
apply eq in H7 as H8.
apply bitwise_xor_assoc in H8.
rewrite <- H8 in eq1.
specialize (H3 x0 x H5 H4) as eq3.
symmetry in H7.
apply eq3 in H7 as H9.
apply bitwise_xor_assoc in H9.
rewrite <- H9 in eq2. 
apply Nat.ltb_lt in eq1. apply Nat.ltb_lt in eq2. 
specialize (Nat.lt_trans x x0 x eq1 eq2) as H10.
apply self_lt_not in H10. inversion H10.
assumption. assumption. assumption.
assumption. assumption. assumption.
assumption. assumption.
specialize (H2 x H4) as H8.
specialize (plus_greater (2 ^ n) (f x0))  as H9.
assert (f x <> 2 ^ n + f x0)%nat. lia.
rewrite -> H7 in H10. contradiction.
destruct (x0 <? bitwise_xor n x0 s) eqn:eq2.
specialize (H2 x0 H5) as H8.
specialize (plus_greater (2 ^ n) (f x))  as H9.
assert (f x0 <> 2 ^ n + f x)%nat. lia.
rewrite -> H7 in H10. contradiction.
apply plus_reg_l in H7.
apply eq in H7 as H8.
apply bitwise_xor_assoc in H8.
specialize (H3 x0 x H5 H4) as eq3.
symmetry in H7.
apply eq3 in H7 as H9.
apply bitwise_xor_assoc in H9.
rewrite <- H9 in eq2. 
rewrite <- H8 in eq1. 
inversion eq1.
inversion eq1.
apply less_false in eq1.
apply less_false in eq2.
assert (x0 < x)%nat. lia.
assert (x < x0)%nat. lia.
specialize (Nat.lt_trans x x0 x H13 H10) as H14.
apply self_lt_not in H14. inversion H14.
1 - 8 : assumption.
Qed.

Theorem deMorgan1 : forall (n s:nat) (f:nat -> nat),
  ((exists x y : nat,
        (x < 2 ^ n)%nat /\
        (y < 2 ^ n)%nat /\
        x <> y /\
        to_injective n s f x =
        to_injective n s f y) -> False) -> (forall x y: nat, ~(
        (x < 2 ^ n)%nat /\
        (y < 2 ^ n)%nat /\
        x <> y /\
        to_injective n s f x =
        to_injective n s f y) ).
Proof.
  intros n s f NxPx x0 y0 Px0.
  apply NxPx.
  exists x0. exists y0.
  exact Px0.
Qed.


Lemma to_injective_really (n s:nat) (f:nat -> nat) : 
   (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s) ->
     (forall x y, (x < (2 ^ n))%nat -> (y < (2 ^ n))%nat
        -> (to_injective n s f) x = (to_injective n s f) y <-> x = y).
Proof.
intros.
specialize (to_injective_aux n s f H H0 H1 H2 H3) as H6.
specialize (deMorgan1 n s f H6) as H7.
specialize (H7 x y) as H8.
simpl in H8.
apply not_and_or in H8.
destruct H8. contradiction.
apply not_and_or in H8. 
destruct H8. contradiction.
apply not_and_or in H8. 
destruct H8. simpl in H8. unfold not in H8.
apply NNPP in H8.
split. intros. apply H8. intros. rewrite -> H8. reflexivity.
split. intros. rewrite -> H9 in H8. contradiction.
intros. rewrite H9 in H8. contradiction.
Qed.

Definition first_half {n} (A: Vector (2 * n)) : Vector n :=
    (fun x y => if x <? n then A x y else C0).

Definition second_half {n} (A: Vector (2 * n)) : Vector n :=
    (fun x y => if x <? n then A (x+n)%nat y else C0).

Definition V4 : Vector 4 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => 1%R
  | (1, 0) => 2%R
  | (2, 0) => 3%R
  | (3, 0) => 4%R
  | _ => C0
  end.

Definition V2 : Vector 2 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => 1%R
  | (1, 0) => 2%R
  | _ => C0
  end.


Example test_first_half: first_half V4 = V2.
Proof.
unfold first_half.
apply  functional_extensionality_dep. intros. simpl.
apply  functional_extensionality_dep. intros. simpl.
destruct (x <? 2)%nat eqn:eq1.
unfold V4, V2.
destruct x. reflexivity.
destruct x. reflexivity.
inversion eq1.
apply less_false in eq1.
destruct x. inversion eq1.
destruct x. inversion eq1. inversion H0.
unfold V2. reflexivity.
Qed.

Definition V21 : Vector 2 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => 3%R
  | (1, 0) => 4%R
  | _ => C0
  end.

Example test_second_half: second_half V4 = V21.
Proof.
unfold second_half.
apply  functional_extensionality_dep. intros. simpl.
apply  functional_extensionality_dep. intros. simpl.
destruct (x <? 2)%nat eqn:eq1.
unfold V4, V2.
destruct x. reflexivity.
destruct x. reflexivity.
inversion eq1.
apply less_false in eq1.
destruct x. inversion eq1.
destruct x. inversion eq1. inversion H0.
unfold V21. reflexivity.
Qed.

Lemma injective_fun_truth: (forall (n x s:nat) (f:nat -> nat),
          f x = if x <? bitwise_xor n x s then (to_injective n  s f) x
                                          else (((to_injective n  s f) x) - 2 ^ n)%nat).
Proof.
intros.
unfold to_injective.
destruct (x <? bitwise_xor n x s). reflexivity. lia.
Qed.

Lemma injective_fun_property: (forall (n s:nat) (f:nat -> nat),
    (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
     (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat)
       -> (forall (x y:nat), (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat
             -> (2 ^ n <= (to_injective n  s f) y)%nat 
          -> (to_injective n  s f) x = ((to_injective n  s f) y - 2 ^ n)%nat -> f x = f y)).
Proof.
intros.
unfold to_injective in H5.
unfold to_injective in H6.
destruct (x <? bitwise_xor n x s).
destruct (y <? bitwise_xor n y s).
apply H2 in H4.
specialize (Nat.lt_le_trans (f y) (2 ^ n) (f y) H4 H5) as H7. lia.
rewrite -> H6. lia.
destruct (y <? bitwise_xor n y s).
apply H2 in H4.
specialize (Nat.lt_le_trans (f y) (2 ^ n) (f y) H4 H5) as H7. lia.
apply H2 in H4. 
assert (2 ^ n <= 2 ^ n + f x)%nat. lia. rewrite H6 in H7. 
specialize (Nat.lt_le_trans (f y) (2 ^ n) (2 ^ n + f y - 2 ^ n)%nat H4 H7) as H8. lia.
Qed.

Lemma injective_fun_property_1: (forall (n s:nat) (f:nat -> nat),
    (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
     (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat)
    -> (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s) 
       -> (forall (x y:nat), (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat
             -> f x = f y -> (x < y)%nat -> (2 ^ n <= (to_injective n  s f) y)%nat 
              /\ (to_injective n  s f) x = ((to_injective n  s f) y - 2 ^ n)%nat)).
Proof.
intros.
unfold to_injective.
specialize (H3 x y H4 H5) as H8.
apply H8 in H6 as H9. apply bitwise_xor_assoc in H9.
specialize (H3 y x H5 H4) as eq1.
symmetry in H6.
apply eq1 in H6 as eq2. apply bitwise_xor_assoc in eq2.
split.
rewrite <- eq2.
destruct (y <? x) eqn:eq3. apply Nat.ltb_lt in eq3.
specialize (Nat.lt_trans x y x H7 eq3) as R. lia. lia.
rewrite <- H9. rewrite <- eq2.
destruct (x <? y) eqn:eq3.
destruct (y <? x) eqn:eq4. apply Nat.ltb_lt in eq4.
specialize (Nat.lt_trans x y x H7 eq4) as R. lia. 
rewrite -> H6. lia.
apply less_false in eq3.
specialize (Nat.lt_le_trans x y x H7 eq3) as R. lia. 
1 - 8 : assumption.
Qed.

Lemma injective_fun_property_2: (forall (n s:nat) (f:nat -> nat),
    (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
     (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat)
    -> (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s) 
       -> (forall (x y:nat), (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat
             -> f x = f y -> (2 ^ n <= (to_injective n  s f) y)%nat 
              -> (to_injective n  s f) x = ((to_injective n  s f) y - 2 ^ n)%nat
              -> (x < y)%nat)).
Proof.
unfold to_injective.
intros.
specialize (H3 x y H4 H5) as H9.
apply H9 in H6 as H10. apply bitwise_xor_assoc in H10.
specialize (H3 y x H5 H4) as eq1.
symmetry in H6.
apply eq1 in H6 as eq2. apply bitwise_xor_assoc in eq2.
rewrite <- eq2 in H7.
rewrite <- H10 in H8.
rewrite <- eq2 in H8.
destruct (y <? x) eqn:eq3.  apply Nat.ltb_lt in eq3.
destruct (x <? y) eqn:eq4.  apply Nat.ltb_lt in eq4.
specialize (Nat.lt_trans x y x eq4 eq3) as R. lia. 
apply H2 in H5.
specialize (Nat.le_lt_trans (2 ^ n) (f y) (2 ^ n) H7 H5) as R. lia. 
apply less_false in eq3.
destruct (x <? y) eqn:eq4. apply Nat.ltb_lt in eq4. apply eq4.
apply less_false in eq4.
assert (x = y)%nat. lia. rewrite H11 in H8.
assert ((2 ^ n + f y - 2 ^ n)%nat = f y). lia.
rewrite H12 in H8.
rewrite plus_comm in H8.
assert (f y = f y + 0)%nat by lia. rewrite H13 in H8 at 2.
apply plus_reg_l in H8. 
assert (2 ^ n > 0)%nat by lia. rewrite H8 in H14.
inversion H14.
1 - 8: assumption.
Qed.


Lemma injective_fun_property_3: forall (n s:nat) (f:nat -> nat),
    (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
     (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat)
    -> (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s) 
       -> (forall (x:nat), (x < 2 ^ n)%nat -> 
             ((to_injective n  s f) x < 2 ^ n)%nat -> 
            (exists (y:nat), (y < 2 ^ n)%nat /\ (x < y)%nat /\ f x = f y)).
Proof.
intros.
remember (bitwise_xor n x s) as y.
assert (bitwise_xor n x s < 2 ^ n)%nat.
unfold bitwise_xor. apply funbool_to_nat_bound.
rewrite <- Heqy in H6.
apply bitwise_xor_assoc in Heqy as H7.
apply H3 in H7.
exists y. split. apply H6.
unfold to_injective in H5.
rewrite <- Heqy in H5.
destruct (x <? y) eqn:eq1. apply Nat.ltb_lt in eq1. 
split. apply eq1. apply H7. lia.
1 - 6 : assumption.
Qed.

Lemma injective_fun_property_4: forall (n s:nat) (f:nat -> nat),
    (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
     (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat)
    -> (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s) 
       -> (forall (x:nat), (x < 2 ^ n)%nat -> 
             ((to_injective n  s f) x < 2 ^ n)%nat -> 
            (exists (y:nat), (y < 2 ^ n)%nat /\ (x < y)%nat
           /\ (to_injective n  s f) x = ((to_injective n  s f) y - 2 ^ n)%nat)).
Proof.
intros.
specialize (injective_fun_property_3 n s f H H0 H1 H2 H3 x H4 H5) as H6.
destruct H6. destruct H6. destruct H7.
exists x0. split. assumption. split. assumption.
unfold to_injective in H5.
unfold to_injective.
specialize (H3 x x0 H4 H6) as eq1.
apply eq1 in H8 as eq2. apply bitwise_xor_assoc in eq2.
specialize (H3 x0 x H6 H4) as eq3.
symmetry in H8.
apply eq3 in H8 as eq4. apply bitwise_xor_assoc in eq4.
rewrite <- eq2 in H5. rewrite <- eq2. rewrite <- eq4.
destruct (x <? x0) eqn:eq5. apply Nat.ltb_lt in eq5.
destruct (x0 <? x) eqn:eq6. apply Nat.ltb_lt in eq6.
specialize (Nat.lt_trans x x0 x eq5 eq6) as R. lia. lia. 
apply less_false in eq5.
specialize (Nat.lt_le_trans x x0 x H7 eq5) as R. lia.
1 - 8: assumption. 
Qed.

Lemma injective_rev_property: (forall (n s:nat) (f:nat -> nat),
(n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
     (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat)
       -> (forall (x:nat), (x < 2 ^ n)%nat
         -> rev_injective (2 ^ n) ((to_injective n s f) x) = f x)).
Proof.
intros.
unfold rev_injective, to_injective.
destruct (x <? bitwise_xor n x s) eqn:eq1. apply Nat.ltb_lt in eq1.
destruct (f x <? 2 ^ n) eqn:eq2. apply Nat.ltb_lt in eq2.
reflexivity.
apply less_false in eq2. apply H2 in H3.
specialize (Nat.lt_le_trans (f x) (2 ^ n)%nat (f x) H3 eq2) as R. lia. 
destruct (2 ^ n + f x <? 2 ^ n) eqn:eq2. apply Nat.ltb_lt in eq2.
assert (f x < 0)%nat by lia. inversion H4.
lia.
Qed.

Lemma basis_vector_injective_pro_1: forall (n:nat) (f:nat -> nat), 
      (forall (x:nat), (x < n)%nat -> (f x < 2 * n)%nat)
    -> (forall (x:nat), (x < n)%nat -> (f x < n)%nat -> 
          (exists (y:nat), (y < n)%nat /\ (n <= f y)%nat /\ (f x = f y - n)%nat))
    -> (forall x y, (x < n)%nat -> f x = f y <-> x = y)
    -> (forall (i:nat), (first_half (basis_vector (2 * n) (f i)))
         = if (f i <? n) then basis_vector n (f i) else Zero).
Proof.
intros.
unfold first_half, basis_vector.
prep_matrix_equality.
destruct (x <? n) eqn:eq1. apply Nat.ltb_lt in eq1.
destruct (f i <? n) eqn:eq2. apply Nat.ltb_lt in eq2.
reflexivity.
destruct ((x =? f i) && (y =? 0)) eqn:eq3. apply andb_true_iff in eq3.
destruct eq3. apply Nat.eqb_eq in H2. apply Nat.eqb_eq in H3.
rewrite <- H2 in eq2. apply less_false in eq2.
specialize (Nat.lt_le_trans x n x eq1 eq2) as R. lia.
reflexivity. 
destruct (f i <? n) eqn:eq2. 
apply less_false in eq1.
apply Nat.ltb_lt in eq2.
destruct ((x =? f i) && (y =? 0)) eqn:eq3. apply andb_true_iff in eq3.
destruct eq3. apply Nat.eqb_eq in H2. apply Nat.eqb_eq in H3.
rewrite <- H2 in eq2.
specialize (Nat.lt_le_trans x n x eq2 eq1) as R. lia.
reflexivity. reflexivity.
Qed.

Lemma basis_vector_injective_pro_2: forall (n:nat) (f:nat -> nat), 
      (forall (x:nat), (x < n)%nat -> (f x < 2 * n)%nat)
    -> (forall (x:nat), (x < n)%nat -> (f x < n)%nat -> 
          (exists (y:nat), (y < n)%nat /\ (n <= f y)%nat /\ (f x = f y - n)%nat))
    -> (forall x y, (x < n)%nat -> f x = f y <-> x = y)
    -> (forall (i:nat), (i < n)%nat -> (second_half (basis_vector (2 * n) (f i)))
         = if (n <=? f i) then basis_vector n (f i - n)%nat else Zero).
Proof.
intros.
unfold second_half, basis_vector.
prep_matrix_equality.
destruct (x <? n) eqn:eq1. apply Nat.ltb_lt in eq1.
destruct (n <=? f i) eqn:eq2. apply Nat.leb_le in eq2.
destruct ((x + n =? f i) && (y =? 0)) eqn:eq3. apply andb_true_iff in eq3.
destruct eq3. apply Nat.eqb_eq in H3. apply Nat.eqb_eq in H4.
destruct ((x =? f i - n) && (y =? 0)) eqn:eq4. apply andb_true_iff in eq4.
destruct eq4. apply Nat.eqb_eq in H5. apply Nat.eqb_eq in H6.
reflexivity.
apply andb_false_iff in eq4.
destruct eq4. apply Nat.eqb_neq in H5. rewrite <- H3 in H5. lia.
apply Nat.eqb_neq in H5. rewrite <- H4 in H5. lia.
destruct ((x =? f i - n) && (y =? 0)) eqn:eq4. apply andb_true_iff in eq4.
destruct eq4. apply Nat.eqb_eq in H3. apply Nat.eqb_eq in H4.
apply andb_false_iff in eq3. destruct eq3. apply Nat.eqb_neq in H5.
rewrite H3 in H5. lia. apply Nat.eqb_neq in H5. rewrite H4 in H5. lia.
reflexivity.
destruct ((x + n =? f i) && (y =? 0)) eqn:eq3. apply andb_true_iff in eq3.
destruct eq3. apply Nat.eqb_eq in H3. apply Nat.eqb_eq in H4.
apply lesseq_false in eq2. rewrite <- H3 in eq2. lia.
reflexivity.
apply less_false in eq1.
destruct (n <=? f i) eqn:eq2. apply Nat.leb_le in eq2.
destruct ((x =? f i - n) && (y =? 0)) eqn:eq3. apply andb_true_iff in eq3.
destruct eq3. apply Nat.eqb_eq in H3. apply Nat.eqb_eq in H4.
rewrite -> H3 in eq1. apply H in H2. 
assert (2 * n <= f i)%nat. lia. 
specialize (Nat.lt_le_trans (f i) (2 * n) (f i) H2 H5) as R. lia.
reflexivity. reflexivity.
Qed.

Lemma basis_vector_to_injective_1: forall (n s:nat) (f:nat -> nat), 
   (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
    (forall (i:nat), (i < 2 ^ n)%nat ->
           basis_vector (2 ^ n) (f i) =
              if (i <? bitwise_xor n i s)%nat
               then first_half (basis_vector (2 * 2 ^ n) ((to_injective n s f) i))
               else second_half (basis_vector (2 * 2 ^ n) ((to_injective n s f) i))).
Proof.
intros.
unfold first_half, second_half, to_injective, basis_vector.
destruct (i <? bitwise_xor n i s) eqn:eq1. apply Nat.ltb_lt in eq1.
prep_matrix_equality.
destruct (x <? 2 ^ n) eqn:eq2. apply Nat.ltb_lt in eq2. reflexivity.
apply less_false in eq2.
destruct ((x =? f i) && (y =? 0)) eqn:eq3. apply andb_true_iff in eq3.
destruct eq3. apply Nat.eqb_eq in H4. rewrite H4 in eq2.
apply H2 in H3. lia. reflexivity.
prep_matrix_equality.
apply less_false in eq1.
destruct (x <? 2 ^ n) eqn:eq2. apply Nat.ltb_lt in eq2. 
destruct ((x =? f i) && (y =? 0)) eqn:eq3. apply andb_true_iff in eq3.
destruct eq3. apply Nat.eqb_eq in H4. 
destruct ((x + 2 ^ n =? 2 ^ n + f i) && (y =? 0)) eqn:eq3. reflexivity.
apply andb_false_iff in eq3. destruct eq3. apply Nat.eqb_neq in H6. lia. 
apply Nat.eqb_eq in H5. apply Nat.eqb_neq in H6. lia.
apply andb_false_iff in eq3.
destruct ((x + 2 ^ n =? 2 ^ n + f i) && (y =? 0)) eqn:eq4.
apply andb_true_iff in eq4. destruct eq4. apply Nat.eqb_eq in H4. 
destruct eq3. apply Nat.eqb_neq in H6. lia.
apply Nat.eqb_eq in H5. apply Nat.eqb_neq in H6. lia.
reflexivity. apply less_false in eq2.
destruct ((x =? f i) && (y =? 0)) eqn:eq3.
apply andb_true_iff in eq3. destruct eq3.
apply Nat.eqb_eq in H4. apply Nat.eqb_eq in H5.
apply H2 in H3. lia. reflexivity.
Qed.

Lemma basis_vector_to_injective_2: forall (n s:nat) (f:nat -> nat), 
   (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
    (forall (i:nat), (i < 2 ^ n)%nat ->
              (if (i <? bitwise_xor n i s)%nat
               then first_half (basis_vector (2 * 2 ^ n) ((to_injective n s f) i))
               else second_half (basis_vector (2 * 2 ^ n) ((to_injective n s f) i)))
          = (first_half (basis_vector (2 * 2 ^ n) ((to_injective n s f) i))) .+ 
             (second_half (basis_vector (2 * 2 ^ n) ((to_injective n s f) i)))).
Proof.
intros.
unfold first_half, second_half, to_injective, basis_vector, Mplus.
destruct (i <? bitwise_xor n i s) eqn:eq1. apply Nat.ltb_lt in eq1.
prep_matrix_equality.
destruct (x<? 2 ^ n) eqn:eq2. apply Nat.ltb_lt in eq2.
destruct ((x =? f i) && (y =? 0)) eqn:eq3. apply andb_true_iff in eq3.
destruct eq3. apply Nat.eqb_eq in H4. 
destruct ((x + 2 ^ n =? f i) && (y =? 0)) eqn:eq4. apply andb_true_iff in eq4.
destruct eq4. apply Nat.eqb_eq in H6. lia. lca.
apply andb_false_iff in eq3.
destruct eq3. apply Nat.eqb_neq in H4.
destruct ((x + 2 ^ n =? f i) && (y =? 0)) eqn:eq4.
apply andb_true_iff in eq4. destruct eq4.
apply Nat.eqb_eq in H5. apply H2 in H3.
assert (2 ^ n <= f i)%nat by lia. lia. lca.
destruct ((x + 2 ^ n =? f i) && (y =? 0)) eqn:eq3.
apply andb_true_iff in eq3. destruct eq3. apply Nat.eqb_eq in H5.
apply H2 in H3. 
assert (2 ^ n <= f i)%nat by lia. lia. lca. lca.
apply less_false in eq1.
prep_matrix_equality.
destruct (x <? 2 ^ n) eqn:eq2.  apply Nat.ltb_lt in eq2. 
destruct ((x + 2 ^ n =? 2 ^ n + f i) && (y =? 0)) eqn:eq3.
apply andb_true_iff in eq3. destruct eq3. apply Nat.eqb_eq in H4.
assert (x = f i)%nat by lia.
destruct ((x =? 2 ^ n + f i) && (y =? 0)) eqn:eq4.
apply andb_true_iff in eq4. destruct eq4. apply Nat.eqb_eq in H7. lia. lca.
apply andb_false_iff in eq3.
destruct ((x =? 2 ^ n + f i) && (y =? 0)) eqn:eq4.
apply andb_true_iff in eq4. destruct eq4. apply Nat.eqb_eq in H4.
assert (2 ^ n <= x)%nat by lia. lia. lca. lca.
Qed.

Lemma basis_vector_to_injective_next: forall (n s:nat) (f:nat -> nat), 
   (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
    (forall (i:nat), (i < 2 ^ n)%nat ->
        basis_vector (2 ^ n) (f i)
          = (first_half (basis_vector (2 * 2 ^ n) ((to_injective n s f) i))) .+ 
             (second_half (basis_vector (2 * 2 ^ n) ((to_injective n s f) i)))).
Proof.
intros.
specialize (basis_vector_to_injective_1 n s f H H0 H1 H2 i H3) as H4.
rewrite -> H4.
specialize (basis_vector_to_injective_2 n s f H H0 H1 H2 i H3) as H5.
apply H5.
Qed.

Lemma basis_vector_first_half: forall (n s:nat) (f:nat -> nat), 
   (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
    (forall (i:nat), (i < 2 ^ n)%nat
      -> first_half (basis_vector (2 * 2 ^ n) ((to_injective n s f) i))
          = (wf_basis_vector (2 ^ n) ((to_injective n s f) i))).
Proof.
intros.
unfold first_half, to_injective, wf_basis_vector, basis_vector.
prep_matrix_equality.
destruct (x <? 2 ^ n) eqn:eq1. apply Nat.ltb_lt in eq1.
destruct ((x =? (if i <? bitwise_xor n i s then f i
            else (2 ^ n + f i)%nat)) && (y =? 0)) eqn:eq2.
reflexivity. reflexivity.
destruct ((x =? (if i <? bitwise_xor n i s 
            then f i else (2 ^ n + f i)%nat)) && (y =? 0) && false) eqn:eq2.
apply andb_true_iff in eq2. destruct eq2. inversion H5. reflexivity.
Qed.


Lemma basis_vector_second_half: forall (n s:nat) (f:nat -> nat), 
   (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> (bitwise_xor n x y = s \/ x = y)) ->
    (forall (i:nat), (i < 2 ^ n)%nat
      -> second_half (basis_vector (2 * 2 ^ n) ((to_injective n s f) i))
          = (wf_basis_vector (2 ^ n) ((to_injective n s f) (bitwise_xor n i s)))).
Proof.
intros.
unfold second_half, to_injective, wf_basis_vector, basis_vector.
prep_matrix_equality.
assert (bitwise_xor n (bitwise_xor n i s) s
      = bitwise_xor n s (bitwise_xor n s i)). 
rewrite bitwise_xor_comm.
assert (bitwise_xor n i s = bitwise_xor n s i) by apply bitwise_xor_comm.
rewrite -> H5. reflexivity.
rewrite -> H5. rewrite -> bitwise_xor_cancel.
destruct (x <? 2 ^ n) eqn:eq1. apply Nat.ltb_lt in eq1.
destruct ((x + 2 ^ n =? (if i <? bitwise_xor n i s
          then f i else (2 ^ n + f i)%nat)) && (y =? 0)) eqn:eq2.
apply andb_true_iff in eq2. destruct eq2. apply Nat.eqb_eq in H6.
destruct ((x =?
   (if bitwise_xor n i s <? i
    then f (bitwise_xor n i s)
    else (2 ^ n + f (bitwise_xor n i s))%nat)) && (y =? 0) && true) eqn:eq3.
reflexivity.
apply andb_false_iff in eq3. destruct eq3.
apply andb_false_iff in H8. destruct H8.
apply Nat.eqb_neq in H8.
destruct (i <? bitwise_xor n i s) eqn:eq4. apply Nat.ltb_lt in eq4.
destruct (bitwise_xor n i s <? i) eqn:eq5. apply Nat.ltb_lt in eq5. lia.
apply less_false in eq5.
apply H2 in H4. rewrite <- H6 in H4. lia.
assert (x = f i)%nat by lia. apply less_false in eq4.
destruct (bitwise_xor n i s <? i) eqn:eq5. apply Nat.ltb_lt in eq5.
remember (bitwise_xor n i s) as j.
specialize (bitwise_xor_bound n i s) as H10. 
rewrite <- Heqj in H10.
rewrite <- bitwise_xor_assoc in Heqj.
specialize (H3 i j H4 H10).
destruct H3. destruct H11. left. apply Heqj. lia.
assumption. assumption. assumption. assumption.
apply less_false in eq5.
assert (bitwise_xor n i s = i) by lia.
apply bitwise_xor_assoc in H10.
symmetry in H10.
apply bitwise_xor_neq in H10. contradiction.
assumption. lia. assumption. assumption. assumption. assumption.
assumption. assumption. assumption. 
apply Nat.eqb_eq in H7. apply Nat.eqb_neq in H8. lia. inversion H8.
destruct ((x =?
   (if bitwise_xor n i s <? i
    then f (bitwise_xor n i s)
    else (2 ^ n + f (bitwise_xor n i s))%nat)) && (y =? 0) && true) eqn:eq3.
apply andb_false_iff in eq2. apply andb_true_iff in eq3. destruct eq3. destruct eq2.
destruct (i <? bitwise_xor n i s) eqn:eq4. apply Nat.ltb_lt in eq4.
apply Nat.eqb_neq in H8.
destruct (bitwise_xor n i s <? i) eqn:eq5. apply Nat.ltb_lt in eq5. lia.
apply andb_true_iff in H6. destruct H6. apply Nat.eqb_eq in H6. 
rewrite H6 in eq1. lia.
destruct (bitwise_xor n i s <? i) eqn:eq5. apply andb_true_iff in H6. 
destruct H6. apply Nat.ltb_lt in eq5. apply Nat.eqb_eq in H6.   
apply Nat.eqb_neq in H8. rewrite H6 in H8.
remember (bitwise_xor n i s) as j.
assert (j < 2 ^ n)%nat by lia.
specialize (H3 i j H4 H10).
destruct H3. destruct H11. left. 
apply bitwise_xor_assoc in Heqj. apply Heqj.
assumption. assumption. assumption. assumption. lia.
apply andb_true_iff in H6. destruct H6. apply less_false in eq5.
apply less_false in eq4.
assert (i = bitwise_xor n i s) by lia.
apply bitwise_xor_assoc in H10.
apply bitwise_xor_neq in H10. contradiction.
assumption. lia. assumption. assumption. assumption.
assumption. assumption. assumption. assumption.
apply andb_true_iff in H6. 
destruct H6. apply Nat.eqb_neq in H8. apply Nat.eqb_eq in H9. lia.
reflexivity.
destruct ((x =?
   (if bitwise_xor n i s <? i
    then f (bitwise_xor n i s)
    else (2 ^ n + f (bitwise_xor n i s))%nat)) && (y =? 0) && false) eqn:eq2.
apply andb_true_iff in eq2. destruct eq2. inversion H7.
reflexivity. assumption.
Qed.

Lemma basis_vector_to_injective_all: forall (n s:nat) (f:nat -> nat), 
   (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> (bitwise_xor n x y = s \/ x = y)) ->
    (forall (i:nat), (i < 2 ^ n)%nat ->
        basis_vector (2 ^ n) (f i)
          = (wf_basis_vector (2 ^ n) ((to_injective n s f) i)) .+ 
             (wf_basis_vector (2 ^ n) ((to_injective n s f) (bitwise_xor n i s)))).
Proof.
intros.
specialize (basis_vector_to_injective_next n s f H H0 H1 H2 i H4) as H5.
rewrite -> basis_vector_first_half in H5.
rewrite -> basis_vector_second_half in H5.
apply H5.
1 - 11 : assumption.
Qed.


Lemma basic_vector_double: forall (n s:nat) (f:nat -> nat), 
   (n > 0)%nat ->
   (forall x, (x < n)%nat -> (f x < 2 * n)%nat) ->
   (forall x, (x < n)%nat -> (f x < n)%nat -> (exists y, (y < n)%nat /\ (n <= f y)%nat))
  -> (forall x, (x < n)%nat -> (n <= f x)%nat -> (exists y, (y < n)%nat /\ (f y < n)%nat))
  -> (forall x y, (x < n)%nat -> (y < n)%nat -> f x = f y <-> x = y)
   -> (vsum n (fun i => basis_vector (2 * n) (f i)))†
      × (vsum n (fun i => basis_vector (2 * n) (f i))) = 
      (1 / 2) .* ((vsum n (fun i => wf_basis_vector n (f i)))†
                    × (vsum n (fun i => wf_basis_vector n (f i)))).
Proof.
intros.
Qed.

(*
    (forall (i:nat), (i < 2 ^ n)%nat ->
        basis_vector (2 ^ n) (f i)
          = (wf_basis_vector (2 ^ n) ((to_injective n s f) i)) .+ 
             (wf_basis_vector (2 ^ n) ((to_injective n s f) (bitwise_xor n i s)))).
Proof.
intros.
specialize (basis_vector_to_injective_next n s f H H0 H1 H2 i H4) as H5.
rewrite -> basis_vector_first_half in H5.
rewrite -> basis_vector_second_half in H5.
apply H5.
1 - 11 : assumption.
Qed.
*)



Lemma wf_product_of_vsums : forall n m a b f,
  (n <= m)%nat ->
  (forall x, (x < n)%nat -> (f x < 2 * m)%nat) ->         (* f is bounded *)
  (forall x y, (x < n)%nat -> (y < n)%nat ->
          f x = f y -> x = y) ->             (* f is injective *)
  (vsum n (fun i : nat => (a i) .* wf_basis_vector m (f i)))†
    × (vsum n (fun i : nat => (b i) .* wf_basis_vector m (f i))) 
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
  rewrite wf_basis_vector_product_eq. 
  rewrite Mmult_vsum_distr_l.
  erewrite vsum_0.
  2: { intros x Hx. distribute_scale. 
       rewrite wf_basis_vector_product_neq.
       lma. 
       intro contra. 
       apply Hf2 in contra; lia. }
  rewrite <- (adjoint_involutive _ _ (wf_basis_vector m (f n))).
  rewrite <- Mmult_adjoint.
  rewrite Mmult_vsum_distr_l.
  erewrite vsum_0.
  2: { intros x Hx. distribute_scale. 
       rewrite wf_basis_vector_product_neq.
       lma.
       intro contra. 
       apply Hf2 in contra; lia. }
  Msimpl.
  simpl Csum.
  rewrite Mscale_plus_distr_l.
  reflexivity.
Admitted.

(* My plan was to define a funtion that reorders terms i ∈ [0..2^n] 
   so that i is adjacent to i ⊕ s. Unfortunately, I've had no luck 
   proving anything useful about my reordering function. So the 
   final proof of Simon's relies on three admitted lemmas. -KH 

   A couple properties about reorder_indices' that may be useful for
   induction:
     - 2 ^ n - 2 * i + 2 <= ctr
     - ctr <= 2 ^ n - i
     - Nat.Even ctr
*)
Fixpoint reorder_indices' n s i f ctr :=
  match i with 
  | O => f
  | S i' =>
      if i' <? bitwise_xor n i' s 
      then let f' := update (update f ctr i') (S ctr) (bitwise_xor n i' s) in
           reorder_indices' n s i' f' (S (S ctr))
      else reorder_indices' n s i' f ctr
  end.
Definition reorder_indices n s := 
  reorder_indices' n s (2 ^ n)%nat (fun i:nat => i) O.

Lemma reorder_indices_finite_bijection : forall n s,
  (s > O)%nat -> (s < 2 ^ n)%nat ->
  finite_bijection (2 ^ n) (reorder_indices n s).
Proof.
Admitted.

Lemma reorder_indices_rewrite_odd_index : forall n s x,
  (2 * x < 2 ^ n)%nat ->
  let r := reorder_indices n s in
  r (2 * x + 1)%nat = bitwise_xor n (r (2 * x)%nat) s.
Proof.
Admitted.

Lemma reorder_indices_bitwise_xor_injective : forall n s x y,
  let r := reorder_indices n s in
  bitwise_xor n (r (2 * x)%nat) (r (2 * y)%nat) = s -> x = y.
Proof.
Admitted.

Lemma vsum_combine_reordered_terms : forall n d s f α,
  (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
  (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> (bitwise_xor n x y = s \/ x = y)) ->
  vsum (2 ^ n) (fun i => (α i) .* basis_vector d (f i)) =
    vsum (2 ^ (n - 1))
         (fun i => let r := reorder_indices n s in
                (α (r (2 * i)%nat) + α (r (2 * i + 1)%nat))  
                  .* basis_vector d (f (r (2 * i)%nat))).
Proof.
  intros.
  specialize (reorder_indices_finite_bijection n s H0 H1) as Hre.
  rewrite vsum_reorder with (f0:=reorder_indices n s) by assumption.
  replace (2 ^ n)%nat with (2 * 2 ^ (n - 1))%nat by unify_pows_two.
  rewrite vsum_sum2. 
  rewrite <- vsum_plus.
  apply vsum_eq.
  intros i Hi.
  simpl.
  rewrite Mscale_plus_distr_l.
  apply f_equal2; try reflexivity.
  rewrite reorder_indices_rewrite_odd_index.
  replace (f (bitwise_xor n (reorder_indices n s (2 * i)) s))
    with (f (reorder_indices n s (2 * i))).
  reflexivity.  
  rewrite H2. left.
  rewrite bitwise_xor_cancel; auto.
  destruct Hre as [Hre _].
  rewrite <- Hre. 
  replace (2 ^ n)%nat with (2 * (2 ^ (n - 1)))%nat by unify_pows_two.
  lia.
  apply funbool_to_nat_bound.
  replace (2 ^ n)%nat with (2 * (2 ^ (n - 1)))%nat by unify_pows_two.
  lia.
Qed.

Theorem simon_nonzero : forall {n : nat} (U : base_ucom (2 * n)) f x s,
   (n > 0)%nat -> (x < 2 ^ n)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   boolean_oracle U f ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> (bitwise_xor n x y = s \/ x = y)) ->
   bitwise_product n x s = false ->
   @norm (2 ^ n) (@Mmult _ _ 1%nat ((basis_vector (2 ^ n) x)† ⊗ I (2 ^ n)) ((uc_eval (simon U)) × ((2 * n) ⨂ ∣0⟩)))
                      = sqrt (1 /2 ^ (n - 1)).
Proof.
  intros. 
  rewrite simon_simplify with (f0:=f); auto.
  rewrite norm_scale.
  rewrite vsum_combine_reordered_terms with (s:=s); auto. 
  rewrite norm_vsum.  
  erewrite Csum_eq_bounded.
  2: { intros i Hi.
       replace (product (nat_to_funbool n (reorder_indices n s (2 * i))) (nat_to_funbool n x) n) 
         with (bitwise_product n (reorder_indices n s (2 * i)) x) by reflexivity.
       replace (product (nat_to_funbool n (reorder_indices n s (2 * i + 1))) (nat_to_funbool n x) n) 
         with (bitwise_product n (reorder_indices n s (2 * i + 1)) x) by reflexivity.
       remember (reorder_indices n s (2 * i)) as i'.
       replace (reorder_indices n s (2 * i + 1)) 
         with (bitwise_xor n i' s).
       rewrite bitwise_product_xor_distr.
       assert (bitwise_product n s x = false).
       { unfold bitwise_product. rewrite product_comm; auto. }
       rewrite H7; clear H7.
       rewrite xorb_false_r.
       remember (bitwise_product n i' x) as b.
       repeat rewrite RtoC_pow.
       rewrite <- RtoC_plus.
       unfold Cconj; simpl.
       rewrite Ropp_0.
       replace (((-1) ^ Nat.b2n b + (-1) ^ Nat.b2n b)%R, 0)%C with (RtoC ((-1) ^ Nat.b2n b + (-1) ^ Nat.b2n b)%R) by reflexivity.
       rewrite <- RtoC_mult.
       replace (((-1) ^ Nat.b2n b + (-1) ^ Nat.b2n b) * ((-1) ^ Nat.b2n b + (-1) ^ Nat.b2n b)) with (2 ^ 2).
       reflexivity.
       destruct b; simpl; lra. 
       rewrite reorder_indices_rewrite_odd_index. 
       subst. reflexivity.
       replace (2 ^ n)%nat with (2 * 2 ^ (n - 1))%nat by unify_pows_two.
       lia. }
  rewrite Csum_constant.
  simpl.
  rewrite RtoC_pow.
  rewrite <- RtoC_inv by nonzero.
  rewrite pow_INR.
  unfold Cmod; simpl.
  replace (1 + 1)%R with 2 by lra.
  autorewrite with R_db.
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
  apply Nat.pow_le_mono_r; lia.
  intros. apply H4.
  specialize (reorder_indices_finite_bijection n s H1 H2) as [Hre _].
  rewrite <- Hre.
  replace (2 ^ n)%nat with (2 * 2 ^ (n - 1))%nat by unify_pows_two.
  lia.  
  intros.
  rewrite H5 in H9.
  destruct H9.
  apply reorder_indices_bitwise_xor_injective in H9; auto.
  specialize (reorder_indices_finite_bijection n s H1 H2) as Hre.
  apply finite_bijection_is_injective 
    with (x:=(2 * x0)%nat) (y:=(2 * y)%nat) in Hre; auto. 
  lia.
  specialize (reorder_indices_finite_bijection n s H1 H2) as [Hre _].
  rewrite <- Hre.
  replace (2 ^ n)%nat with (2 * 2 ^ (n - 1))%nat by unify_pows_two.
  lia. 
  specialize (reorder_indices_finite_bijection n s H1 H2) as [Hre _].
  rewrite <- Hre.
  replace (2 ^ n)%nat with (2 * 2 ^ (n - 1))%nat by unify_pows_two.
  lia.   
Qed.
