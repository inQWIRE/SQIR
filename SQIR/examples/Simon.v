Require Import List.
Require Import UnitaryOps.
Require Import Dirac.
Require Import NDSem.
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

(* TODO: move to QWIRE *)
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
  (* f is bounded and one-to-one for x < m *)
  (forall x, (x < m)%nat -> (f x < m)%nat) ->
  (forall x y, (x < m)%nat -> f x = f y <-> x = y) -> 
  (vsum n (fun i : nat => (a i) .* basis_vector m (f i)))†
    × (vsum n (fun i : nat => (b i) .* basis_vector m (f i))) = Csum (fun i => ((a i) ^* * b i)%C) n .* I 1.
Proof.
  intros n m a b f Hn Hf1 Hf2.
  induction n; simpl vsum. 
  simpl Csum. Msimpl. reflexivity.
  rewrite Mplus_adjoint.
  distribute_plus.
  rewrite IHn by lia.
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
       rewrite Hf2 in contra; lia. }
  rewrite <- (adjoint_involutive _ _ (basis_vector m (f n))).
  rewrite <- Mmult_adjoint.
  rewrite Mmult_vsum_distr_l.
  erewrite vsum_0.
  2: { intros x Hx. distribute_scale. 
       rewrite basis_vector_product_neq.
       lma.
       1,2: apply Hf1; lia.
       intro contra. 
       rewrite Hf2 in contra; lia. }
  Msimpl.
  simpl Csum.
  rewrite Mscale_plus_distr_l.
  reflexivity.
Qed.

Lemma norm_vsum : forall n d c f,
  (n <= d)%nat ->
  (forall x, (x < d)%nat -> (f x < d)%nat) ->
  (forall x y, (x < d)%nat -> f x = f y <-> x = y) -> 
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
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> f x = f y <-> x = y) ->
   @norm (2 ^ n) (@Mmult _ _ 1%nat ((basis_vector (2^n) x)† ⊗ I (2 ^n)) ((uc_eval (simon U)) × ((2 * n) ⨂ ∣0⟩))) = sqrt (1 /2 ^ n).
Proof.
  intros. 
  erewrite simon_simplify with (f0:=f); auto.
  rewrite norm_scale.
  rewrite norm_vsum; try assumption.
  2: lia.
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

Fixpoint inverse_set n (f : nat -> nat) y :=
  match n with
  | O => []
  | S n' => if f n' =? y then n' :: inverse_set n' f y 
                        else inverse_set n' f y
  end.

Definition inverse_set_1 n f x := List.nth 0%nat (inverse_set n f x) O.
Definition inverse_set_2 n f x := List.nth 1%nat (inverse_set n f x) O.

Definition has_element len f i := 
  match inverse_set len f i with
      | [] => false
      | x::xs => true
 end.

Fixpoint codomain' len n (f: nat -> nat) :=
  match n with
    | 0 => []
    | S n' => if has_element len f n' then n' :: codomain' len n' f else codomain' len n' f
end.

Definition codomain n f := codomain' n n f.

Lemma codomain_property : forall (n i: nat) (f: nat -> nat), List.In i (codomain n f) -> inverse_set n f i <> [].
Proof.
intro n.
unfold codomain.
induction n.
simpl. intros. inversion H.
simpl. unfold has_element. intros.
destruct (f n =? i) eqn:eq.
simpl. intro H1. symmetry in H1. inversion H1. 
Admitted.

Lemma codomain_col1 : forall (n i: nat) (f: nat -> nat), List.In i (codomain n f)
    -> (exists x, List.In x (inverse_set n f i)).
Proof.
intros.
specialize (codomain_property n i f H) as H0.
destruct (inverse_set n f i). contradiction.
exists n0. unfold List.In. left. reflexivity.
Qed.

Lemma list_in_aux: forall (l: list nat) (x n:nat), List.In x (n :: l) -> x = n \/ List.In x l.
Proof.
intro l.
induction l.
simpl.
intros.
destruct H.
left. auto.
right. auto.
simpl.
intros.
destruct H.
left. auto.
destruct H.
right. left. apply H.
right. right. apply H.
Qed.

Lemma list_in_aux_1: forall (l: list nat) (x n:nat), x = n \/ List.In x l ->  List.In x (n :: l).
Proof.
intro l.
induction l.
simpl.
intros.
destruct H.
left. auto. inversion H.
simpl.
intros.
destruct H.
left. auto.
destruct H.
right. left. apply H.
right. right. apply H.
Qed.

(* Inverse set properties. One is saying that the inverse set has elements all find the co-mapping of i for the function f. 
   the second rule says that all the finding elements will not be greater than the upper bound n. *)
Lemma inverse_set_property: forall (n i x: nat) (f:nat -> nat), List.In x (inverse_set n f i) -> f x = i.
Proof.
intro n.
induction n.
simpl. intros. inversion H.
simpl. intros.
destruct (f n =? i) eqn:eq.
apply list_in_aux in H.
destruct H. rewrite -> H. symmetry in eq. apply beq_nat_eq in eq. apply eq.
apply IHn in H. apply H.
apply IHn in H. apply H.
Qed.

Lemma inverse_set_property_1: forall (n i x: nat) (f:nat -> nat), List.In x (inverse_set n f i) -> (x < n)%nat.
Proof.
intro n.
induction n.
simpl. intros. inversion H.
simpl. intros.
destruct (f n =? i) eqn:eq.
apply list_in_aux in H.
destruct H. lia.
apply IHn in H. lia.
apply IHn in H. lia.
Qed.

Lemma less_than_eq: forall (x n:nat), (x < S n)%nat <-> (x = n)%nat \/ (x < n)%nat.
Proof.
intros.
split.
intros.
lia.
intros.
destruct H. rewrite -> H. lia. lia.
Qed.

(* This lemma shows that the inverse_set can always find the right answer. *)
Lemma inverse_mem: forall (n x i:nat) (f:nat -> nat), (n > 0)%nat -> (x < n)%nat
           -> f x = i -> List.In x (inverse_set n f i).
Proof.
intro n.
destruct n.
intros. inversion H.
intros.
induction n.
simpl. intros.
destruct x.
destruct (f 0%nat =? i) eqn:eq1.
simpl. left. reflexivity. rewrite H1 in eq1. rewrite <- beq_nat_refl in eq1. discriminate eq1.
inversion H0. inversion H3.
assert (List.In x (inverse_set (S (S n)) f i) =
     List.In x (if f (S n) =? i then S n :: inverse_set (S n) f i else inverse_set (S n) f i)).
simpl. reflexivity.
apply less_than_eq in H0. rewrite -> H2.
destruct H0. rewrite H0 in H1. rewrite -> H1.
destruct (i =? i) eqn:eq1. apply list_in_aux_1. left. apply H0. 
rewrite <- beq_nat_refl in eq1. inversion eq1.
assert ((S n) > 0)%nat. lia.
apply IHn in H3.
destruct (f (S n) =? i). apply list_in_aux_1.
right. apply H3. apply H3. apply H0.
Qed.

Fixpoint size_of_range' nmax n f :=
  match n with
  | O => O
  | S n' => match inverse_set nmax f n' with
           | [] => size_of_range' nmax n' f
           | _ => (1 + size_of_range' nmax n' f)%nat
           end
  end.
Definition size_of_range n f := size_of_range' n n f.

(* This show that the associtivity of the bitwise_xor function. *)
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

(* I think this axiom can be proved in Coq but I don't know how to do it. *)
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

Lemma nat_to_funbool_funs_2 : forall n f f', (n > 0)%nat -> funbool_to_nat n f = funbool_to_nat n f'
    -> (forall i:nat , (i < n)%nat -> f i = f' i).
Proof. 
unfold funbool_to_nat.
intro n.
induction n as [ n IHn ] using (well_founded_induction lt_wf).
intros f f' H H1.
destruct n. inversion H.
Admitted.

Lemma bitwise_xor_assoc: forall (n x y s: nat), (n > 0)%nat -> (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> (s < 2 ^ n)%nat ->
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
        ⊕ nat_to_funbool n (funbool_to_nat n (nat_to_funbool n y)) i) (nat_to_funbool n s) H H7).
simpl.
intros H8. apply xor_eq. assumption. assumption. apply funbool_to_nat_bound. 
rewrite -> H5 in H8. rewrite H4. apply H8. assumption.
intros.
apply nat_to_funbool_funs_1.
specialize (nat_to_funbool_funs_2 n (nat_to_funbool n y) (fun i : nat =>
        nat_to_funbool n x i
        ⊕ nat_to_funbool n (funbool_to_nat n (nat_to_funbool n s)) i) H H7).
simpl.
intros H8. apply xor_eq. assumption. apply funbool_to_nat_bound. assumption.
rewrite -> H4 in H8. rewrite H5. apply H8. assumption.
Qed.

Lemma length_two_meaning_aux: forall (l:list nat) (x y: nat), length (x::(y::l)) = 2%nat -> l = [].
Proof.
intro l.
induction l.
intros. reflexivity. intros.
inversion H.
Qed.

Lemma length_one_meaning: forall (l: list nat), length l = 1%nat -> (exists (x:nat), l = (x::[])).
Proof.
intros.
destruct l.
inversion H.
destruct l.
exists n. reflexivity.
inversion H.
Qed.

Lemma length_two_meaning: forall (l: list nat), length l = 2%nat -> (exists (x y:nat), l = (x::(y::[]))).
Proof.
intros.
destruct l.
inversion H.
destruct l.
inversion H.
exists n.
exists n0.
apply length_two_meaning_aux in H.
rewrite -> H. reflexivity.
Qed.

Lemma length_two_meaning_1: forall (l: list nat) (x y:nat), l = (x::(y::[])) -> length l = 2%nat.
Proof.
intros.
destruct l.
inversion H.
destruct l.
inversion H.
induction l.
simpl. reflexivity.
inversion H.
Qed.

Lemma bitwise_product_xor_distr : forall n x y z,
  bitwise_product n (bitwise_xor n x y) z =
    xorb (bitwise_product n x z) (bitwise_product n y z).
Proof.
  intros.
  unfold bitwise_product, bitwise_xor.
Admitted.

Lemma restrict_form: forall (x y n s:nat) (f:nat -> nat), (n > 0)%nat -> 
             f x = f y <-> bitwise_xor n x y = s -> 
          (forall x y, (x < 2 ^ n)%nat ->(y < 2 ^ n)%nat -> f x = f y <-> bitwise_xor n x y = s).
Proof.
Admitted.

(* This indicates shows that the inverse set of the two-to-one function has exactly two elements. 
   and two cols saying that what is the consequence of the two element set. *)
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

Lemma bitwise_xor_neq_col:
  forall n f s x i,
   (n > 0)%nat -> (x < 2 ^ n)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
    f x = i ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s) ->
      (exists (y : nat), f y = i /\ (x <> y) /\ (y < 2 ^ n)%nat).
Proof.
intros.
remember (bitwise_xor n x s) as y.
apply bitwise_xor_assoc in Heqy as H6.
apply bitwise_xor_neq in H6 as H7.
apply H5 in H6. exists y. split. 
rewrite <- H6. apply H3. split. apply H7.
unfold bitwise_xor in Heqy.
rewrite -> Heqy. apply funbool_to_nat_bound.
assumption. unfold bitwise_xor in Heqy.
rewrite -> Heqy. apply funbool_to_nat_bound.
assumption. intros conra. rewrite conra in H1. inversion H1.
assumption. assumption.
rewrite -> Heqy. apply funbool_to_nat_bound.
assumption. assumption.
rewrite -> Heqy. apply funbool_to_nat_bound.
assumption.
Qed.

Lemma all_three_different_inserse_set:
    (forall (n x y z i: nat) (f: nat -> nat) (l: list nat), 
           inverse_set n f i = (x::(y::(z::l)))
            -> x <> y /\ y <> z /\ z <> x).
Proof.
intro n. induction n.
intros. simpl in H. inversion H.
intros.
simpl inverse_set in H.
destruct (f n%nat =? i).
Admitted.

Lemma list_three: forall (n:nat) (l: list nat), length l = S (S (S n))
  -> (exists (x y z: nat) (l':list nat), l = (x::(y::(z::l')))).
Proof.
intros.
destruct l.
inversion H.
destruct l.
inversion H.
destruct l.
inversion H.
exists n0. exists n1. exists n2. exists l. reflexivity.
Qed.

Lemma inverse_two: forall n f s x i,
   (n > 0)%nat -> (x < 2 ^ n)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
    f x = i ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s) ->
       (length (inverse_set (2 ^ n) f i) = 2%nat).
Proof.
intros.
destruct (length (inverse_set (2 ^ n) f i)) eqn:eq.
assert ((inverse_set (2 ^ n) f i) = []).
apply length_zero_iff_nil. apply eq.
apply (inverse_mem (2 ^ n)) in H3.
rewrite -> H6 in H3.
apply in_nil in H3. inversion H3.
assert (0 < 2 ^ n)%nat.
apply Nat.lt_le_trans with (m := (2 ^ 0)%nat). simpl. lia.
apply Nat.pow_le_mono_r. lia. lia.
apply H7. assumption.
destruct n0.
specialize (bitwise_xor_neq_col n f s x i H H0 H1 H2 H3 H4 H5) as H6.
destruct H6. destruct H6. destruct H7.
apply (inverse_mem (2 ^ n)) in H3.
apply (inverse_mem (2 ^ n)) in H6.
apply length_one_meaning in eq. destruct eq.
rewrite -> H9 in H3.
rewrite -> H9 in H6.
unfold List.In in H3.
destruct H3.
unfold List.In in H6.
destruct H6.
rewrite <- H3 in H7. rewrite H6 in H7. contradiction.
inversion H6. inversion H3.
assert (0 < 2 ^ n)%nat.
apply Nat.lt_le_trans with (m := (2 ^ 0)%nat). simpl. lia.
apply Nat.pow_le_mono_r. lia. lia. apply H9.
assumption.
assert (0 < 2 ^ n)%nat.
apply Nat.lt_le_trans with (m := (2 ^ 0)%nat). simpl. lia.
apply Nat.pow_le_mono_r. lia. lia. apply H9.
assumption.
destruct n0. reflexivity.
apply list_three in eq. destruct eq. destruct H6. destruct H6. destruct H6.
assert (List.In x0 (inverse_set (2 ^ n) f i)) as eq1.
rewrite -> H6. unfold List.In. left. reflexivity.
assert (List.In x1 (inverse_set (2 ^ n) f i)) as eq2.
rewrite -> H6. unfold List.In. right. left. reflexivity.
assert (List.In x2 (inverse_set (2 ^ n) f i)) as eq3.
rewrite -> H6. unfold List.In. right. right. left. reflexivity.
apply inverse_set_property_1 in eq1 as Hx0.
apply inverse_set_property_1 in eq2 as Hx1.
apply inverse_set_property_1 in eq3 as Hx2.
apply inverse_set_property in eq1.
apply inverse_set_property in eq2.
apply inverse_set_property in eq3.
apply all_three_different_inserse_set in H6 as H7.
destruct H7. destruct H8. 
assert (f x0 = f x1) as eq4. rewrite -> eq1. rewrite -> eq2. reflexivity.
assert (f x0 = f x2) as eq5. rewrite -> eq1. rewrite -> eq3. reflexivity.
apply H5 in eq4. apply H5 in eq5.
apply bitwise_xor_assoc in eq4.
apply bitwise_xor_assoc in eq5. rewrite <- eq4 in eq5.
rewrite eq5 in H8. contradiction.
1 - 12: assumption.
Qed.

Lemma inverse_two_col1: forall n f s x i,
   (n > 0)%nat -> (x < 2 ^ n)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
    f x = i ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s) ->
       (exists (x y:nat), inverse_set (2 ^ n) f i = (x::(y::[]))).
Proof.
intros.
specialize (inverse_two n f s x i H H0 H1 H2 H3 H4 H5) as H6.
apply length_two_meaning in H6.
destruct H6. destruct H6.
exists x0. exists x1. apply H6.
Qed.

Lemma inverse_two_col2: forall n f s x i,
   (n > 0)%nat -> (x < 2 ^ n)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
    f x = i ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s) ->
       (exists (x y:nat), inverse_set (2 ^ n) f i = (x::(y::[])) /\ f x = f y).
Proof.
intros.
specialize (inverse_two_col1 n f s x i H H0 H1 H2 H3 H4 H5) as H6.
destruct H6. destruct H6.
exists x0. exists x1.
split. apply H6.
assert (List.In x0 (inverse_set (2 ^ n) f i) /\ List.In x1 (inverse_set (2 ^ n) f i)).
split. rewrite H6. simpl. left. reflexivity.
rewrite H6. simpl. right. left. reflexivity.
destruct H7.
apply inverse_set_property in H7.
apply inverse_set_property in H8.
rewrite H7. rewrite H8. reflexivity.
Qed.

Lemma inverse_two_aux: forall (n:nat) (f: nat -> nat), (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat)
          -> (exists (x i:nat), (x < 2 ^ n)%nat /\ f x = i).
Proof.
intros.
exists 0%nat.
exists (f 0%nat).
split. 
apply Nat.lt_le_trans with (m := (2 ^ 0)%nat). simpl. lia.
apply Nat.pow_le_mono_r. lia. lia.
reflexivity.
Qed.

Lemma inverse_zero: forall n f i,
   (forall (x:nat), (x < n)%nat -> f x <> i) ->
       (length (inverse_set n f i) = 0%nat).
Proof.
intros.
induction n.
simpl. reflexivity.
simpl.
destruct (f n =? i) eqn:eq.
specialize (H n).
assert (n < S n)%nat. lia. 
apply H in H0.
assert (f n = i). apply beq_nat_true in eq. assumption.
rewrite H1 in H0. contradiction.
apply IHn. intros. apply H. lia.
Qed.

Lemma inverse_zero_two_aux: forall (n x i:nat) (f:nat -> nat), (x < n)%nat ->
     (f x = i)%nat \/ (forall (x:nat), (x < n)%nat -> (f x <> i)%nat).
Proof.
intros.
induction n. simpl. inversion H.
assert ((x < n)%nat \/ x = n). lia.
destruct H0. apply IHn in H0.
Admitted.

Lemma inverse_zero_two: forall n f s i,
   (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s) ->
      (length (inverse_set (2 ^ n) f i) = 0%nat \/ length (inverse_set (2 ^ n) f i) = 2%nat).
Proof.
intros.
apply inverse_two_aux in H2 as H4. destruct H4. destruct H4. destruct H4.
specialize (inverse_zero_two_aux (2 ^ n) x i f H4) as H6.
destruct H6. right. 
specialize (inverse_two n f s x i H H4 H0 H1 H6 H2 H3) as H8.
apply H8. 
left. apply inverse_zero. apply H6.
Qed.

(* This is the lemma we need -- not sure how to prove it! Usually for vsums I
   would do induction on the dimension, but I don't think that will work here.
    I don't think that this theorem can be proved, even if we remove the if then else condition. 
    It will require an order defined on the z to be the increasing order of the (f i).
 *)
Lemma matrix_plus_inj: forall (m n : nat) (A B C: Matrix m n), B = C -> A .+ B = A .+ C.
Proof.
intros.
rewrite -> H. reflexivity.
Qed.

Lemma vsum_inverse : 
  forall {n m} (f : nat -> nat) a,
    (n <= m)%nat ->
   (forall x, (x < m)%nat -> (f x < m)%nat) ->
   (forall i, length (inverse_set m f i) = 0%nat \/ length (inverse_set m f i) = 2%nat) ->
   vsum n (fun i : nat => (a i) .* basis_vector m (f i)) =
     vsum n
          (fun z : nat => if length (inverse_set m f z) =? 2%nat then 
            (a (inverse_set_1 m f z) + a (inverse_set_2 m f z))
              .* basis_vector m z else Zero). 
Proof. 
intros.
induction n; simpl vsum. reflexivity.
  rewrite IHn by lia.
  distribute_scale.
apply matrix_plus_inj.
Admitted.

(* Another possibility: Defining a getOppose function. *)

Definition getOppose len f i x := 
             if x =? inverse_set_1 len f i
                      then inverse_set_2 len f i else inverse_set_1 len f i.

(* we might need to show that the following:*)
Lemma opp_reverse: forall (n i x :nat) (f:nat -> nat),
 (forall x, (x < n)%nat -> (f x < n)%nat) ->
   (forall i, length (inverse_set n f i) = 2%nat) ->
         getOppose n f i (getOppose n f i x) = x.
Proof. Admitted.

Lemma opp_eq: forall {n m} (f : nat -> nat) a,
    (n <= m)%nat ->
   (forall x, (x < m)%nat -> (f x < m)%nat) ->
   (forall i, length (inverse_set m f i) = 0%nat \/ length (inverse_set m f i) = 2%nat) ->
   vsum n (fun i : nat => (a i) .* basis_vector m (f i)) 
     = vsum n (fun i : nat => (a i) .* basis_vector m (f (getOppose n f (f i) i))).
Proof. Admitted.

Lemma opp_eq_1: forall {n m} (f : nat -> nat) a,
    (n <= m)%nat ->
   (forall x, (x < m)%nat -> (f x < m)%nat) ->
   (forall i, length (inverse_set m f i) = 0%nat \/ length (inverse_set m f i) = 2%nat) ->
   vsum n (fun i : nat => (a i) .* basis_vector m (f (getOppose n f (f i) i))) 
     = vsum n (fun i : nat => (a (getOppose n f (f i) i)) .* basis_vector m i).
Proof. Admitted.

(* So we prove the above several lemmas. Then the idea is to
   vsum n (a i .* basic_vector n (f i)) = 
   vsum n (a i .* basic_vector n (f getoppose i)) = 
   vsum n (a (getoppose i) .* basic_vector n (f i))

    Then, we might be able to show that the following. 
 *)
Lemma vsum_inverse_1 : 
  forall {n m} (f : nat -> nat) a,
    (n <= m)%nat ->
   (forall x, (x < m)%nat -> (f x < m)%nat) ->
   (forall i, length (inverse_set m f i) = 0%nat \/ length (inverse_set m f i) = 2%nat) ->
    (vsum n (fun i : nat => (a i) .* basis_vector m (f i)))†
      × (vsum n (fun i : nat => (a i) .* basis_vector m (f i))) =
          Csum (fun i => ((a i + a (getOppose n f (f i) i)) ^* * (a i + a (getOppose n f (f i) i)))%C) n .* I 1.
Proof. Admitted.


(* Another possibility is to define a function f which is one-to-one from f. 
   Since for all x f x < 2 ^ n, then the following is an injective function.
    But I don't know how to prove it in Coq. *)
Definition to_injective (n s:nat) (f:nat -> nat) : (nat -> nat) :=
    (fun x => let y := bitwise_xor n x s in if (x <? y)%nat then f x else ((2 ^ n)%nat + f x)%nat).

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
     (forall x y, (x < (2 ^ n))%nat -> (y < (2 ^ n))%nat -> (to_injective n s f) x = (to_injective n s f) y <-> x = y).
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

Lemma basis_vector_injective: forall (n s i:nat) (f:nat -> nat),
    (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
     (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s) 
    -> basis_vector (2 ^ n) (f i)
              = first_half (basis_vector (2 * 2 ^ n) ((to_injective n  s f) i)).
Proof.
intros.
Admitted.

(* Then, we will prove the following. However, 
    This is hard for me. Since I don't know how to manage to show the induction on n over 2 ^ n => 2 ^ (S n). *)
Lemma vsum_inverse_2 : forall (n s :nat) (f:nat -> nat) a,
   (n > 0)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s) ->
        (vsum (2 ^ n) (fun i : nat => (a i) .* basis_vector (2 ^ n) (f i)))
      = vsum (2 ^ n) 
               (fun i : nat => (1 / 2) .* (((a i) + (a (bitwise_xor n i s))) .* basis_vector (2 ^ n) ((to_injective n s f) i))).
Proof. 
intros.
destruct n.
inversion H.
induction n ; simpl vsum.
unfold to_injective, bitwise_xor. simpl.
unfold funbool_to_nat. simpl.
Admitted.




(* Find all x < n s.t. f(x) = y. *)
Fixpoint get_inverses n (f : nat -> nat) y :=
  match n with
  | O => []
  | S n' => if f n' =? y then n' :: get_inverses n' f y 
                        else get_inverses n' f y
  end.

(* Find all y < n s.t. f(x) = y for some x < n. *)
Fixpoint get_range' nmax n (f : nat -> nat) :=
  match n with
  | O => []
  | S n' => match get_inverses nmax f n' with
           | [] => get_range' nmax n' f
           | _ => n' :: get_range' nmax n' f
           end
  end.
Definition get_range n f := get_range' n n f.

Lemma inverse_exists : forall m n f,
  (forall x, f x < m)%nat -> (m <= n)%nat ->
  exists y, ((y < n)%nat /\ get_inverses n f y <> []).
Proof.
  intros.
  induction n.
  specialize (H O); lia.
  simpl.
  bdestruct (m =? S n).
  subst.
  exists (f n).
  split.
  apply H.
  rewrite Nat.eqb_refl. 
  easy.
  assert (m <= n)%nat by lia.
  specialize (IHn H2).
  destruct IHn as [y [IH1 IH2]].
  exists y.
  split. lia.
  bdestruct (f n =? y).
  easy.
  apply IH2.
Qed.

Lemma range_is_empty_implies_n_eq_0 : forall m n f,
  (m > 0)%nat -> (forall x, f x < m)%nat -> (m <= n)%nat ->
  length (get_range' m n f) = O -> n = O.
Proof.
  intros.
  assert (forall i, (i < n)%nat -> get_inverses m f i = []).
  { intros. clear H1.
    induction n.
    lia.
    simpl in *.
    destruct (get_inverses m f n) eqn:invs.
    bdestruct (i =? n).
    subst. assumption. 
    apply IHn; try lia.
    simpl in H2. lia. }
  assert (m <= m)%nat by lia.
  specialize (inverse_exists m m f H0 H4). 
  intros [y [foo bar]].
  contradict bar.
  apply H3. lia.
Qed.

(* Construct a new function f' whose range has one less element than 
   the range of f. The value returned is the function & the size of its
   domain. 

   This function is used in the proof below. *)
(*Fixpoint construct_f' nmax n (f : nat -> nat) idx : (nat -> nat) * nat :=
  match n with
  | O => (fun _ => O) , O
  | S n' => match construct_f' nmax f n' with
           | [] => get_range' nmax n' f
           | _ => n' :: get_range' nmax n' f
           end
  end.
Definition get_range n f := get_range' n n f.

Lemma :

length (get_range n f) = S m ->
construct_f .... = (n', f') ->
length (get_range n' f') = m

vsum m
    (fun i : nat =>
     (Σ^ length (get_inverses n f (nth i (get_range n f) O))
      (fun j : nat =>
       α (nth j (get_inverses n f (nth i (get_range n f) O)) O)))
     .* basis_vector d (nth i (get_range n f) O))
=
vsum m
    (fun i : nat =>
     (Σ^ length (get_inverses n' f' (nth i (get_range n' f') O))
      (fun j : nat =>
       α (nth j (get_inverses n' f' (nth i (get_range n' f') O)) O)))
     .* basis_vector d (nth i (get_range n' f') O))


length (get_range n f) = S O ->
construct_f ... = (0, fun _ => O)



(* Reorder a terms (α i) .* ∣ f i ⟩ of a vsum expression based on the
   value of the basis vector. *) 
Lemma vsum_inverse_general : forall n d fmax f α,
  (n > 0)%nat -> (forall x : nat, (f x < fmax)%nat) -> (fmax <= n)%nat ->
  let range := get_range n f in
  vsum n (fun i => (α i) .* basis_vector d (f i)) =
    vsum (List.length range) 
         (fun i => let z := List.nth i range O in
                let invs := get_inverses n f z in
                (Csum (fun i => α (List.nth i invs O)) (List.length invs)) 
                  .* basis_vector d z).
Proof.
  intros. subst range.
  remember (length (get_range n f)) as m.
  generalize dependent f.
  generalize dependent n.
  induction m; intros.
  - simpl.
    symmetry in Heqm.
    apply range_is_empty_implies_n_eq_0 in Heqm; try lia.
    intro x. specialize (H0 x). lia.
  - simpl in *.


-> given S n' = length (get_range n f), find nH fH s.t. n' = length (get_range nH fH)

    remember (get_range n f) as range.
    rewrite <- IHn'.


Lemma vsum_inverse' : forall {n} (f : nat -> nat) s a,
  (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
  (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> f x = f y <-> bitwise_xor n x y = s) ->
  vsum (2 ^ n) (fun i => (a i) .* basis_vector (2 ^ n) (f i)) =
    vsum (2 ^ n) (fun i => let i' := bitwise_xor n i s in
                  (if i <? i' then (a i + a i') else C0)
                  .* basis_vector (2 ^ n) (f i)). 
Proof.

  
Admitted.

Theorem simon_nonzero : forall {n : nat} (U : base_ucom (2 * n)) f x s,
   (n > 0)%nat -> (x < 2 ^ n)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   boolean_oracle U f ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s) ->
   bitwise_product n x s = false ->
   @norm (2 ^ n) (@Mmult _ _ 1%nat ((basis_vector (2 ^ n) x)† ⊗ I (2 ^ n)) ((uc_eval (simon U)) × ((2 * n) ⨂ ∣0⟩)))
                      = sqrt (1 /2 ^ (n - 1)).
Proof.
  intros. 
  rewrite simon_simplify with (f0:=f); auto.
  rewrite norm_scale.
  rewrite norm_vsum; auto.
  erewrite Csum_eq_bounded.



Lemma foo : forall n s,
Csum (fun i : nat => if i <? bitwise_xor n i s then 2 ^ 2 else 0) (2 ^ n) = 2 ^ 2 * 2 ^ (n - 1).
Proof.
  intros.
  induction n. lia.
  simpl.




*)




(* This is the more general form of the lemma above. It might be worthwhile
   trying to prove this first. In the case of Simon's, size_of_range will
   always be n/2 and (List.length invs) will be 2. *)
Lemma vsum_inverse_general : forall {d} n f (v : nat -> nat -> Vector d),
  vsum n (fun i => v i (f i)) =
    vsum (size_of_range n f) 
         (fun z => let invs := inverse_set n f z in
                    vsum (List.length invs) (fun i => v (List.nth i invs O) z)).
Proof. Admitted.


Lemma inverse_2_is_s_away_from_inverse_1 : forall n f s x i,
   (n > 0)%nat -> (x < 2 ^ n)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
    f x = i ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s) ->
  inverse_set_2 (2 ^ n) f i = bitwise_xor n (inverse_set_1 (2 ^ n) f i) s.
Proof. 
intros.
specialize (inverse_two_col2 n f s x i H H0 H1 H2 H3 H4 H5) as H6.
unfold inverse_set_2, inverse_set_1.
destruct H6. destruct H6. destruct H6.
rewrite -> H6. simpl.
assert (List.In x0 (inverse_set (2 ^ n) f i) /\ List.In x1 (inverse_set (2 ^ n) f i)).
split. rewrite H6. simpl. left. reflexivity.
rewrite H6. simpl. right. left. reflexivity.
destruct H8.
apply inverse_set_property_1 in H8.
apply inverse_set_property_1 in H9.
specialize (H5 x0 x1 H8 H9) as H10.
destruct H10.
apply H10 in H7. 
apply bitwise_xor_assoc in H7. apply H7.
1 - 4: assumption.
Qed.

Theorem simon_nonzero : forall {n : nat} (U : base_ucom (2 * n)) f x s,
   (n > 0)%nat -> (x < 2 ^ n)%nat -> (s > 0)%nat -> (s < 2 ^ n)%nat ->
   boolean_oracle U f ->
   (forall x, (x < 2 ^ n)%nat -> (f x < 2 ^ n)%nat) ->
   (forall x y, (x < 2 ^ n)%nat -> (y < 2 ^ n)%nat -> 
        f x = f y <-> bitwise_xor n x y = s) ->
   bitwise_product n x s = false ->
   @norm (2 ^ n) (@Mmult _ _ 1%nat ((basis_vector (2 ^ n) x)† ⊗ I (2 ^ n)) ((uc_eval (simon U)) × ((2 * n) ⨂ ∣0⟩)))
                      = sqrt (1 /2 ^ (n - 1)).
Proof.
  intros. 
  rewrite simon_simplify with (f0:=f); auto.
  Admitted.
  (*rewrite vsum_inverse with (s0:=s); auto.  
  rewrite norm_scale.
  rewrite norm_vsum; auto.
  erewrite Csum_eq_bounded.
  2: { intros i Hi.
       replace (product (nat_to_funbool n (inverse_set_1 (2 ^ n) f i)) (nat_to_funbool n x) n) with (bitwise_product n (inverse_set_1 (2 ^ n) f i) x) by reflexivity.
       replace (product (nat_to_funbool n (inverse_set_2 (2 ^ n) f i)) (nat_to_funbool n x) n) with (bitwise_product n (inverse_set_2 (2 ^ n) f i) x) by reflexivity.
       rewrite inverse_2_is_s_away_from_inverse_1 with (s:=s); auto.
       rewrite bitwise_product_xor_distr.
       assert (bitwise_product n s x = false).
       { unfold bitwise_product. rewrite product_comm; auto. }
       rewrite H7; clear H7.
       rewrite xorb_false_r.
       remember (bitwise_product n (inverse_set_1 (2 ^ n) f i) x) as b.
       repeat rewrite RtoC_pow.
       rewrite <- RtoC_plus.
       unfold Cconj; simpl.
       rewrite Ropp_0.
       replace (((-1) ^ Nat.b2n b + (-1) ^ Nat.b2n b)%R, 0)%C with (RtoC ((-1) ^ Nat.b2n b + (-1) ^ Nat.b2n b)%R) by reflexivity.
       rewrite <- RtoC_mult.
       replace (((-1) ^ Nat.b2n b + (-1) ^ Nat.b2n b) * ((-1) ^ Nat.b2n b + (-1) ^ Nat.b2n b)) with (2 ^ 2).
       reflexivity.
       destruct b; simpl; lra. 
       assert (2 ^ (n - 1) < 2 ^ n)%nat. 
       apply Nat.pow_lt_mono_r; lia.
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
  intros. reflexivity.
Qed.


*)