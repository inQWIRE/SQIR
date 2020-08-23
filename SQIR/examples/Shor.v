(*From Interval Require Import Tactic.*)
Require Import Reals Psatz ZArith Znumtheory.
Require Export VectorStates QPE.

Local Close Scope R_scope.

Local Coercion INR : nat >-> R.
Local Coercion Z.of_nat : nat >-> BinNums.Z.

(* r is the order of a modulo p *)
Definition Order (a r p : nat) :=
  0 < r /\
  a^r mod p = 1 /\
  (forall r' : nat, (0 < r' /\ a^r' mod p = 1) -> r' = r).

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
Lemma ω_neg_sum_nonzero : forall r j, (j <> 0)%nat -> 
  Csum (fun i =>  (ω_neg r ^ (i * j))%C) r = 0.
Proof.
Admitted.

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
       rewrite ω_neg_sum_nonzero by auto.
       lma. }
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

(* The description of the circuit implementing "multiply a modulo N". *)
Definition MultiplyCircuitProperty (a N n : nat) (c : base_ucom n) :=
  forall x : nat,
    (0 <= x < N ->
     (uc_eval c) × (basis_vector (2^n) x) = basis_vector (2^n) (a * x mod N))
    /\
    (N <= x ->
     (uc_eval c) × (basis_vector (2^n) x) = basis_vector (2^n) x).
                 
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
    (forall (n : nat),
      2 < n ->
      (ϕ n) / n >= β / (Nat.log2 (Nat.log2 n))).
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
    (forall (a r N m n : nat) (c : base_ucom n),
      BasicSetting a r N m n ->
      MultiplyCircuitProperty a N n c ->
      probability_of_success a r N m n c >= β / (Nat.log2 (Nat.log2 N))).
Admitted.

