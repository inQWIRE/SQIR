Require Import Psatz ZArith Znumtheory.
Require Import euler.Asympt euler.Misc euler.Primes euler.Prod.
Require Import QuantumLib.Prelim QuantumLib.RealAux QuantumLib.Summation.


(* ==================================== *)
(* = Euler's totient function rebuild = *)
(* ==================================== *)

Local Open Scope nat_scope.
Local Coercion Z.of_nat : nat >-> BinNums.Z.
Local Coercion INR : nat >-> R.

Lemma not_rel_prime_0_n :
  forall n, n > 1 -> ~ rel_prime 0 n.
Proof.
  intros. intro. unfold rel_prime in H0.
  assert (Zis_gcd 0 n n) by (apply Zis_gcd_sym, Zis_gcd_0).
  destruct (Zis_gcd_unique _ _ _ _ H0 H1); lia.
Qed.

Lemma not_rel_prime_n_n :
  forall n, n > 1 -> ~ rel_prime n n.
Proof.
  intros. intro. unfold rel_prime in H0. specialize (Zis_gcd_refl n) as H1.
  destruct (Zis_gcd_unique _ _ _ _ H0 H1); lia.
Qed.

Lemma rel_prime_0_1 :
  rel_prime 0 1.
Proof.
  unfold rel_prime. apply Zis_gcd_1.
Qed.

Local Opaque Nat.modulo Z.gcd Z.of_nat.
Lemma Natgcd_Zgcd :
  forall (m a b : nat),
    a <= m ->
    Z.of_nat (Nat.gcd a b) = Z.gcd a b.
Proof.
  induction m. intros. replace a with 0 by lia. simpl. symmetry. rewrite <- Nat2Z.inj_abs_nat. rewrite Zabs2Nat.id. easy.
  intros. bdestruct (a <=? m). apply IHm; easy. replace a with (S m) by lia.
  simpl. assert (b mod S m < S m) by (apply Nat.mod_upper_bound; lia).
  assert (b mod S m <= m) by lia.
  rewrite IHm by easy. rewrite mod_Zmod by lia. apply Z.gcd_mod. lia.
Qed.
Local Transparent Nat.modulo Z.gcd Z.of_nat.

Lemma rel_prime_Nat_gcd :
  forall (a b : nat),
    rel_prime a b ->
    Nat.gcd a b = 1.
Proof.
  intros. unfold rel_prime in H.
  assert (Z.gcd a b = 1).
  { apply Zis_gcd_gcd. lia. easy.
  }
  rewrite <- Natgcd_Zgcd with (m := a) in H0 by lia. lia.
Qed.

Lemma not_rel_prime_Nat_gcd :
  forall (a b : nat),
    ~ rel_prime a b ->
    Nat.gcd a b <> 1.
Proof.
  intros. unfold rel_prime in H. 
  assert (Z.gcd a b <> 1).
  { intro. specialize (Zgcd_is_gcd a b) as G. rewrite H0 in G. easy.
  }
  rewrite <- Natgcd_Zgcd with (m := a) in H0 by lia. lia.
Qed.

Local Open Scope R_scope.

(* Euler's totient function *)
Definition ϕ (n : nat) := big_sum (fun x => if rel_prime_dec x n then 1 else 0) n.

Lemma ϕ_φ_aux :
  forall l (n : nat),
    (n > 1)%nat ->
    big_sum (fun x : nat => if rel_prime_dec x n then 1 else 0) (S l) =
    length (filter (fun d : nat => Nat.gcd n d =? 1) (List.seq 1 l)).
Proof.
  induction l; intros. simpl.
  specialize (not_rel_prime_0_n _ H) as G.
  destruct (rel_prime_dec 0 n); try easy. lra.
  rewrite <- big_sum_extend_r. 
  rewrite IHl by easy. rewrite seq_extend. rewrite filter_app. rewrite app_length.
  destruct (rel_prime_dec (S l) n).
  - apply rel_prime_Nat_gcd in r. simpl.
    rewrite Nat.gcd_comm. apply Nat.eqb_eq in r.
    rewrite r. rewrite plus_INR. simpl. lra.
  - apply not_rel_prime_Nat_gcd in n0. simpl.
    rewrite Nat.gcd_comm. apply Nat.eqb_neq in n0.
    rewrite n0. rewrite plus_INR. simpl. lra.
Qed.

Lemma ϕ_iter_inc :
  forall (n : nat),
    (n > 1)%nat ->
    big_sum (fun x => if rel_prime_dec x n then 1 else 0) (S n) = 
      big_sum (fun x => if rel_prime_dec x n then 1 else 0) n.
Proof.
  intros. rewrite <- big_sum_extend_r. specialize (not_rel_prime_n_n _ H) as G.
  destruct (rel_prime_dec n n). easy. rewrite Rplus_0_r. reflexivity.
Qed.

Lemma ϕ_φ_equal :
  forall n, (n > 1)%nat -> ϕ n = φ n.
Proof.
  intros. unfold ϕ. unfold φ. unfold coprimes.
  rewrite <- ϕ_iter_inc by easy. apply ϕ_φ_aux. easy.
Qed.
  
(* There exists a better bound by [1979 Hardy & Wright, Thm 328] *)
Lemma ϕ_n_over_n_lowerbound :
  forall (n : nat),
    (2 <= n)%nat ->
    (ϕ n) / n >= exp(-2) / (Nat.log2 n ^ 4).
Proof.
  intros. rewrite ϕ_φ_equal by lia. apply φ_lower_bound. easy.
Qed.


