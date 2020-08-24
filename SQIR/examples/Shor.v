(*From Interval Require Import Tactic.*)
Require Import Reals Psatz ZArith Znumtheory.
Require Export VectorStates QPE.

Local Close Scope R_scope.

Local Coercion INR : nat >-> R.
Local Coercion Z.of_nat : nat >-> BinNums.Z.

(* r is the order of a modulo p *)
Definition Order (a r N : nat) :=
  0 < r /\
  a^r mod N = 1 /\
  (forall r' : nat, (0 < r' /\ a^r' mod N = 1) -> r' >= r).

Lemma Order_N_nonzero :
  forall a r N,
    Order a r N ->
    0 < N.
Proof.
  intros. 
  destruct (0 <? N)%nat eqn:E.
  - apply Nat.ltb_lt in E; easy.
  - apply Nat.ltb_ge in E. assert (N=0) by omega. destruct H as [_ [? _]]. rewrite H0 in H. simpl in H. omega.
Qed.

(* Parameter assumptions of the Shor'salgorithm *)
Definition BasicSetting (a r N m n : nat) :=
  0 < a < N /\
  Order a r N /\
  N^2 <= 2^m < 2 * N^2 /\
  N <= 2^n < 2 * N.

Definition basisPowerA (a r N n : nat) := basis_vector (2^n) (a^r mod N).

Local Open Scope R_scope.

Definition ω_neg (r : nat) := Cexp (-2 * PI / r).

(* The ψ states are the eigenstates of the target circuit. Described in https://cs.uwaterloo.ca/~watrous/LectureNotes/CPSC519.Winter2006/10.pdf. *)
Definition ψ (a r N j n : nat) :=
  (1 / √r) .* vsum r (fun x => (ω_neg r)^(j * x) .* (basisPowerA a x N n)).

Lemma ω_neg_sum_zero : forall r, Csum (fun i =>  (ω_neg r ^ (i * 0))%C) r = r.
Proof.
  intros.
  apply Csum_1.
  intros.
  unfold ω_neg.
  rewrite Cexp_pow.
  rewrite Nat.mul_0_r.
  autorewrite with R_db.
  apply Cexp_0.
Qed. 

(* Proved in a slightly different form in Csum_Cexp_nonzero in QPE.v. We should 
   update the two files to use consistent notation. *)
Lemma ω_neg_sum_nonzero :
  forall (r k : nat),
    0 < r ->
    0 < k < r -> 
    Csum (fun i => (ω_neg r ^ (i * k))%C) r = 0.
Proof.
  intros.
  assert (((fun (x : nat) => (ω_neg r)^(x * k)) = (fun (x : nat) => ((ω_neg r) ^ k) ^ x))%C).
  { apply functional_extensionality. intros. unfold ω_neg. do 3 rewrite Cexp_pow.
    rewrite mult_INR. replace (-2 * PI / r * (x * k)) with (-2 * PI / r * k * x) by lra. easy.
  }
  rewrite H1. rewrite Csum_geometric_series. unfold ω_neg. do 2 rewrite Cexp_pow.
  replace (-2 * PI / r * k * r) with (-(2 * PI * k)) by (field; lra). rewrite Cexp_neg.
  rewrite <- Cexp_pow. rewrite Cexp_2PI.
  replace (1 ^ k)%C with C1 by (rewrite RtoC_pow; rewrite pow1; auto).
  replace (1 - / 1)%C with C0 by lca. lca.
  unfold ω_neg. rewrite Cexp_pow. unfold Cexp. intro. inversion H2. rewrite H4 in H5. rewrite Rplus_0_l in H5.
  assert (0 < / r * k < 1).
  { destruct H0. split. 
    - apply Rinv_0_lt_compat in H. apply Rmult_lt_0_compat; assumption.
    - pose (Rinv_lt_contravar k r (Rmult_lt_0_compat k r H0 H) H3) as H6.
      pose (Rmult_lt_compat_r k (/ r) (/ k) H0 H6) as H7.
      rewrite <- Rinv_l_sym in H7; lra.
  }
  rewrite <- sin_neg in H5. replace (- (-2 * PI / r * k)) with (2 * PI / r * k) in H5 by lra.
  assert (0 < 2 * PI).
  { apply Rmult_lt_0_compat; try lra. apply PI_RGT_0.
  }
  assert (0 < 2 * PI / r * k < 2 * PI).
  { destruct H3. replace (2 * PI / r * k) with ((2 * PI) * (/ r * k)) by lra. split.
    - apply Rmult_lt_0_compat; lra. 
    - pose (Rmult_lt_compat_l (2 * PI) (/ r * k) 1 H6 H7) as H8.
      autorewrite with R_db in H8. assumption.
  }
  destruct H7.
  apply sin_eq_O_2PI_0 in H5; try (apply Rlt_le; assumption).
  destruct H5 as [? |[? | ?]]; try lra.
  replace ((-2 * PI / r * k)) with (- (2 * PI / r * k)) in H4 by lra. rewrite H5 in H4.
  rewrite cos_neg in H4. rewrite cos_PI in H4. lra.
Qed.

Lemma sum_of_ψ_is_one :
  forall a r N m n : nat,
    BasicSetting a r N m n ->
    (1 / √r) .* vsum r (fun j => ψ a r N j n) = basis_vector (2^n) 1.
Proof.
  intros.
  destruct H as [? [[? _] _]]. (* we only need a few parts of H *)
  unfold ψ.
  rewrite <- Mscale_vsum_distr_r.
  rewrite Mscale_assoc.
  rewrite vsum_swap_order.
  erewrite vsum_eq.
  2: { intros. rewrite Mscale_vsum_distr_l. reflexivity. }
  erewrite vsum_unique.
  2: { exists O.
       split. assumption.
       split.
       rewrite ω_neg_sum_zero. reflexivity.
       intros.
       rewrite ω_neg_sum_nonzero.
       lma.
       apply lt_0_INR; assumption. split. apply not_eq_sym in H2. apply neq_0_lt in H2. apply lt_0_INR; assumption. apply lt_INR; assumption.
  }
  unfold basisPowerA.
  rewrite Nat.pow_0_r.
  rewrite Nat.mod_1_l by lia.
  rewrite Mscale_assoc.
  replace (1 / √ r * (1 / √ r) * r)%C with C1.
  lma.
  field_simplify_eq.
  rewrite <- RtoC_mult.
  rewrite sqrt_def. 
  reflexivity.
  apply pos_INR.
  apply RtoC_neq.
  apply sqrt_neq_0_compat.
  apply lt_0_INR. 
  assumption.
Qed.

Lemma mod_pow :
  forall a b N,
    (0 < N)%nat ->
    a^b mod N = (a mod N)^b mod N.
Proof.
  intros. induction b.
  - simpl; auto.
  - simpl. rewrite Nat.mul_mod; try omega. rewrite IHb. apply Nat.mul_mod_idemp_r. omega.
Qed.

Lemma MultiGroup_modulo_N :
  forall a r N x,
    Order a r N ->
    a^x mod N = a^(x mod r) mod N.
Proof.
  intros. assert (HN := H). apply Order_N_nonzero in HN.
  destruct H as [? [? ?]]. replace (a ^ x mod N)%nat with ((a^(r * (x / r) + x mod r)) mod N)%nat.
  2: { rewrite <- Nat.div_mod; omega. }
  rewrite Nat.pow_add_r. rewrite Nat.mul_mod; try omega.
  rewrite Nat.pow_mul_r. rewrite mod_pow; try omega.
  rewrite H0. rewrite Nat.pow_1_l. rewrite <- Nat.mul_mod; try omega. rewrite Nat.mul_1_l. easy.
Qed.

(* The description of the circuit implementing "multiply a modulo N". *)
Definition MultiplyCircuitProperty (a N n : nat) (c : base_ucom n) :=
  forall x : nat,
    (0 <= x < N ->
     (uc_eval c) × (basis_vector (2^n) x) = basis_vector (2^n) (a * x mod N))
    (*/\
    (N <= x ->
     (uc_eval c) × (basis_vector (2^n) x) = basis_vector (2^n) x)*).

Lemma MC_eigenvalue :
  forall (a r N j m n : nat) (c : base_ucom n),
    BasicSetting a r N m n ->
    MultiplyCircuitProperty a N n c ->
    (uc_eval c) × (ψ a r N j n) = Cexp (2 * PI * j / r) .* (ψ a r N j n).
Admitted.

Definition round (x : R) := up (x - /2).

(* The target basis we focus on, when the sampling result locates near k/r *)
Definition s_closest (m k r : nat) :=
  Z.to_nat (round (k / r * 2^m)%R).

(* Copied from QPEGeneral.v *)
Definition probability_of_outcome {n} (ψ o : Vector n) : R := 
  (Cmod ((o† × ψ) 0%nat 0%nat)) ^ 2.

Lemma QPE_MC_partial_correct :
  forall (a r N k m n : nat) (c : base_ucom n),
    BasicSetting a r N m n ->
    MultiplyCircuitProperty a N n c ->
    0 <= k < r ->
    probability_of_outcome ((uc_eval (QPE m n c)) × ((basis_vector (2^m) 0) ⊗ (ψ a r N k n))) ((basis_vector (2^m) (s_closest m k r)) ⊗ (ψ a r N k n)) >= 4 / (PI ^ 2).
Admitted.

Lemma QPE_MC_correct :
  forall (a r N k m n : nat) (c : base_ucom n),
    BasicSetting a r N m n ->
    MultiplyCircuitProperty a N n c ->
    0 <= k < r ->
    probability_of_outcome ((uc_eval (QPE m n c)) × ((basis_vector (2^m) 0) ⊗ (basis_vector (2^n) 1))) ((basis_vector (2^m) (s_closest m k r)) ⊗ (ψ a r N k n)) >= 4 / (PI ^ 2 * r).
Admitted.


(* Finds p/q such that |s/2^m-p/q|<=1/2^(m+1) and q<N. Must make sure 2^m>N^2 to secure the uniqueness. *)
Fixpoint CF_ite (n a b p1 q1 p2 q2 N : nat) : nat * nat :=
  if q1 <? N then
    match n with
    | O => (p1, q1)
    | S n => let c := (b / a)%nat in
            CF_ite n (b mod a)%nat a (c*p1+p2)%nat (c*q1+q2)%nat p1 q1 N
    end
  else (p2, q2).

Compute (CF_ite 3 26 100 0 1 1 0 5).

(* Not sure if this bound is correct. But it seems enough *)
Definition CF_bound (N : nat) := (Nat.log2 N + 1)%nat.

Definition ContinuedFraction (s N m : nat) : nat * nat := CF_ite (CF_bound N) s (2^m) 0 1 1 0 N.  

(* "Partial correct" of ContinuedFraction function. "Partial" because it is exactly correct only when k and r are coprime. Otherwise it will output (p, q) such that p/q=k/r. *)
Lemma ContinuedFraction_partial_correct :
  forall (a r N k m n : nat),
    BasicSetting a r N m n ->
    rel_prime k r ->
    ContinuedFraction (s_closest m k r) N m = (k, r).
Admitted.

Fixpoint Rsum_ite (n k : nat) (f : nat -> R) : R :=
  match k with
  | O => f O
  | S k' => (f k') + (Rsum_ite n k' f)
  end.

Definition Rsum (n : nat) (f : nat -> R) : R := Rsum_ite n n f.

(* Euler's totient function *)
Definition ϕ (n : nat) := Rsum n (fun x => if rel_prime_dec x n then 1 else 0).

(* This might need to be treated as an axiom. [1979 Hardy & Wright, Thm 328] *)
Lemma ϕ_n_over_n_lowerbound :
  exists β, 
    β>0 /\
    forall (n : nat),
      2 < n ->
      (ϕ n) / n >= β / (Nat.log2 (Nat.log2 n)).
Admitted.

(* The final success probability of Shor's order finding algorithm. It counts the k's coprime to r and their probability of being collaped to. *)
Definition probability_of_success (a r N m n : nat) (c : base_ucom n) :=
  Rsum r (fun k => if rel_prime_dec k r then
                  probability_of_outcome ((uc_eval (QPE m n c)) × ((basis_vector (2^m) 0) ⊗ (basis_vector (2^n) 1))) ((basis_vector (2^m) (s_closest m k r)) ⊗ (ψ a r N k n))
                else 0).

(* The correctness specification. It succeed with prob proportional to 1/(log log N), which is asymptotically small, but big enough in practice.
   With better technique (calculate the LCM of multiple outputs), the number of rounds may be reduced to constant. But I don't know how to specify that, and the analysis in Shor's original paper refers the correctness to "personal communication" with Knill. *)
Lemma Shor_correct :
  exists β, 
    β>0 /\
    forall (a r N m n : nat) (c : base_ucom n),
      BasicSetting a r N m n ->
      MultiplyCircuitProperty a N n c ->
      probability_of_success a r N m n c >= β / (Nat.log2 (Nat.log2 N)).
Admitted.

