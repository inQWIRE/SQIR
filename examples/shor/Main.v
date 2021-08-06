Require Import Shor.
Require Import euler.Primes.
Require Import AltGateSet.
Require Import AltShor.
Require Import Run.

(* The definitions and proofs in this file are largely wrappers around definitions
   and proofs in other files. At some point, I might clean up the code in the 
   other files directly so this file won't be necessary. -KH *)


(** Coq definitions that will be extracted to OCaml **)

(* Shor's runs on (n + k) qubits and returns the result of measuring n qubits. *)
Definition n (N : nat) := Nat.log2 (2 * N^2).
Definition k (N : nat) := AltShor.num_qubits (Nat.log2 (2 * N)).

(* Shor circuit *)
(* RNR: Why is this necessary? *)
(* KH: not necessary :) *)
Definition shor_circuit (a N : nat) := AltShor.shor_circuit a N. 

(* Continued fraction expansion *)
Definition cont_frac_exp (a N o : nat) := Shor.OF_post a N o (n N).

(* given r = ord(a,N), try to find a factor of N (based on Shor.Factor_post) *)
Definition factor (a N r : nat) := 
  let cand1 := Nat.gcd (a ^ (r / 2) - 1) N in
  let cand2 := Nat.gcd (a ^ (r / 2) + 1) N in 
  if (1 <? cand1) && (cand1 <? N) then Some cand1      (* candidate #1 is a factor *)
  else if (1 <? cand2) && (cand2 <? N) then Some cand2 (* candidate #2 is a factor *)
  else None.                                           (* failed to find factor *)

(* End-to-end definition of Shor's algorithm.

1. Run the circuit generated by (shor_circuit a N) on input  ∣0⟩_{n + k}.
2. Measure the first n qubits, resulting in the n-bit number x.
3. Run cont. frac. expansion to get r, which is a candidate for the order (ord a N).
4. Use r to try to factor N.

  The probability that cont_frac_exp correctly returns (ord a N) is at least
  1/polylog(N), as shown in shor_OF_correct. The probability that factor
  returns a factor of N (given the correct order) is at least 1/2, as shown
  in shor_factor_correct. *)

Print U.
Print ucom.
Search ucom base_ucom.

Definition end_to_end_shors a N rnd :=
  let n := n N in
  let k := k N in
  let circ := shor_circuit a N in
  let x := run_ucom_part n k (to_base_ucom (n+k) circ) rnd in
  let r := cont_frac_exp a N x in
  factor a N r.


(** Some utilities for stating correctness properties. **)

(* The probability that measuring the first m qubits of v produces x. *)
Definition prob_meas_outcome m n (v : Vector (2^(m+n))) (x : nat) : R :=
  @prob_partial_meas m n (basis_vector (2^m) x) v.

(* The probability that the result of measuring the first m qubits of v 
   satisfies predicate f. *)
Definition prob_meas_outcome_sats_pred m n (v : Vector (2^(m+n))) (f : nat -> bool) :=
  Rsum (2^m) (fun x => if f x then prob_meas_outcome m n v x else 0).

(* The probability that a number < Nmax satisfies predicate f
   (i.e. the # of values that satisfy f divided by Nmax) *)
Definition prob_value_sats_pred Nmax f : R :=
  INR (ShorAux.cnttrue Nmax f) / INR Nmax.

(* The probability that a number < Nmax satisfies predicate f, given that
   it satisfies predicate g (i.e. the # of values that satisfy f & g divided 
   by the # of values that satisfy g) *)
Definition cond_prob_value_sats_pred Nmax (f g : nat -> bool) : R :=
  prob_value_sats_pred Nmax (fun x => f x && g x) / prob_value_sats_pred Nmax g.


(** Correctness properties for Shor's **)

(* Fact #1 - the probability that run_circuit returns ord(a,N) is at least 
   κ / (Nat.log2 N)^4 where κ is about 0.055 (see Shor.v).

   This is awkward because I describe "the probability that run_circuit +
   cont_frac_exp returns ord(a,N)" using cond_prob_value_sats_pred. I'm pretty
   such that the axiom above won't let me prove this... suggestions? -KH *)
(* TODO: Revise this. *)
(*
Lemma shor_OF_correct : forall (a N : nat),
  (0 < a < N)%nat ->
  (Nat.gcd a N = 1)%nat ->
  cond_prob_value_sats_pred 
      (2 ^ n N)
      (fun x => x =? ord a N)
      (fun x => x =? cont_frac_exp a N (run_ucom_part (n N + k N) (n N) (shor_circuit a N)))
    >= κ / INR (Nat.log2 N)^4.
Proof.
Admitted.
 *)

(* Fact #2 - Assuming that N has the form (p ^ k * q) for prime p > 2, k > 0, 
   q > 2, and p ^ k coprime to q...
   the probability that ord(a,N) can be used to find a factor is at least 1/2.

   TODO: Can we state the constraint on N in a more succint way? I think what we 
   have now is equivalent to saying that N is not prime, not even, and not a power
   of a prime. Do we have a proof of this? -KH *) 
Definition k1 a N : nat := ((ord a N) / 2) + 1.
Definition k2 a N : nat := ((ord a N) / 2) - 1.
Definition coprime (a b : nat) : Prop := Nat.gcd a b = 1%nat.
Definition nontrivial_factor a b := 
  (a <? b) && (1 <? Nat.gcd a b) && (Nat.gcd a b <? b).

Search prime.

(** * Section on Prime Numbers *)

(* TODO: move to Euler repo *)

Section Primes.

Require Import Wf.

Local Open Scope nat_scope.

(* TODO: Develop this, use Prime as main definition of primality.
   (Prime shouldn't be defined in terms of a primality checker.
Definition divides (a b : nat) := exists n, a * n = b. 

Infix "|" := divides (at level 30).

Definition Prime (p : nat) := p > 1 /\ forall a, a | p -> a = 1 \/ a = p.

Definition Composite (n : nat) := exists a b, a > 1 /\ b > 1 /\ a * b = n.
 *)

Lemma NatOdd2x :
  forall x, ~ Nat.Odd (x * 2).
Proof.
  induction x. simpl. intro. inversion H. lia.
  intro. simpl in *. rewrite Nat.Odd_succ_succ in H. easy.
Qed.

Lemma coprime_list_prod :
  forall p l f,
    (forall q, In q l -> Nat.gcd p q = 1) ->
    Nat.gcd p (fold_left Nat.mul (map (fun x : nat => x ^ f x) l) 1) = 1.
Proof.
  intros. induction l.
  simpl. apply Nat.gcd_1_r.
  simpl. replace (a ^ f a + 0) with (1 * (a ^ f a)) by lia.
  rewrite <- Misc.List_fold_left_mul_assoc.
  apply Misc.Nat_gcd_1_mul_r.
  apply IHl. intros. apply H. apply in_cons. easy.
  apply pow_coprime. apply H. constructor. easy.
Qed.

Lemma simplify_primality : forall N,
    ~ (prime N) -> Nat.Odd N -> (forall p k, prime p -> N <> p ^ k) ->
    (exists p k q, (k <> 0) /\ prime p /\ (p > 2) /\ (q > 2) /\ coprime (p ^ k) q /\ N = p ^ k * q)%nat.
Proof.
  intros.
  assert (GN : N > 1).
  { destruct H0. specialize (H1 2 0 eq_refl). simpl in *. lia. }  
  destruct (prime_divisors N) as [| p [| q l]] eqn:E.
  - apply Primisc.prime_divisors_nil_iff in E. lia.
  - assert (Hp: In p (prime_divisors N)) by (rewrite E; constructor; easy).
    apply Prod.prime_divisors_aux in Hp. destruct Hp as [Hp Hpn].
    assert (HN0: N <> 0) by lia.
    specialize (Prod.prime_divisor_pow_prod N HN0) as G.
    rewrite E in G. simpl in G.    
    specialize (H1 p (Prod.pow_in_n N p) Hp).
    remember (p ^ Prod.pow_in_n N p) as pk.
    rewrite <- G in H1. lia.
  - assert (Hp: In p (prime_divisors N)) by (rewrite E; constructor; easy).
    assert (Hq: In q (prime_divisors N)) by (rewrite E; constructor; constructor; easy).
    assert (Hp': In p (prime_decomp N)) by (apply Primisc.prime_divisors_decomp; easy).
    assert (Hq': In q (prime_decomp N)) by (apply Primisc.prime_divisors_decomp; easy).
    apply in_prime_decomp_divide in Hp'. apply in_prime_decomp_divide in Hq'.
    apply Prod.prime_divisors_aux in Hp. destruct Hp as [Hp Hpn].
    apply Prod.prime_divisors_aux in Hq. destruct Hq as [Hq Hqn].
    remember (q :: l) as lq.
    assert (HN0: N <> 0) by lia.
    specialize (Prod.prime_divisor_pow_prod N HN0) as G.
    rewrite E in G. simpl in G.
    replace (p ^ Prod.pow_in_n N p + 0) with (1 * (p ^ Prod.pow_in_n N p)) in G by lia.
    rewrite <- Misc.List_fold_left_mul_assoc in G.
    remember (Prod.prod (map (fun x : nat => x ^ Prod.pow_in_n N x) lq)) as Plq.
    exists p, (Prod.pow_in_n N p), Plq.
    split. lia. split. easy.
    split. assert (2 <= p) by (apply prime_ge_2; easy).
    bdestruct (2 =? p). rewrite <- H3 in Hp'. destruct Hp'. rewrite H4 in H0. apply NatOdd2x in H0. easy. lia.
    assert (HeqPlq' := HeqPlq).
    simpl in HeqPlq'. rewrite <- HeqPlq' in G.
    rewrite Heqlq in HeqPlq.
    rewrite map_cons, Prod.prod_extend in HeqPlq.
    split.
    bdestruct (Plq =? 0). rewrite H2 in G. lia.
    bdestruct (Plq =? 1).
    assert (2 <= q) by (apply prime_ge_2; easy).
    assert (Prod.pow_in_n N q < q ^ Prod.pow_in_n N q) by (apply Nat.pow_gt_lin_r; lia).
    assert (2 <= q ^ Prod.pow_in_n N q) by lia.
    destruct (Prod.prod (map (fun x : nat => x ^ Prod.pow_in_n N x) l)); lia.
    bdestruct (Plq =? 2). rewrite H4 in G. rewrite <- G in H0. rewrite Nat.mul_comm in H0. apply NatOdd2x in H0. easy.
    lia.
    split. unfold coprime. apply Prod.Nat_gcd_1_pow_l.
    rewrite HeqPlq'. apply coprime_list_prod.
    intros. assert (In q0 (prime_divisors N)) by (rewrite E; apply in_cons; easy).
    assert (p <> q0).
    { specialize (Prod.prime_divisors_distinct N) as T. rewrite E in T.
      inversion T. intro. subst. easy.
    } 
    apply Prod.prime_divisors_aux in H3. destruct H3 as [Hq0 Hq0n].
    apply eq_primes_gcd_1; easy.
    lia.
Qed.

End Primes.

(* Can replace with conditions above using simplify_primality. *)
Lemma shor_factor_correct : forall (* p k q *) N a,
(*  (k <> 0)%nat -> prime p -> (p > 2)%nat -> (q > 2)%nat -> coprime (p ^ k) q ->
  N = (p ^ k * q)%nat -> *)
  ~ (prime N) -> Nat.Odd N -> (forall p k, prime p -> N <> p ^ k)%nat ->
  coprime a N -> 
  let is_a_factor x := nontrivial_factor (a ^ k1 a N) N || 
                         nontrivial_factor (a ^ k2 a N) N in
  cond_prob_value_sats_pred N is_a_factor (fun a => Nat.gcd a N =? 1) >= 1/2.
Proof.
  intros.
  apply simplify_primality in H; trivial. clear H0 H1.
  destruct H as [p [k [q [H0 [H1 [H3 [H4 [H5 H6]]]]]]]].
  unfold cond_prob_value_sats_pred.
  apply Rle_ge.
  apply Generic_proof.Rdiv_ge_mult_pos.
  lra.
  rewrite Rdiv_unfold, <- Rmult_assoc, <- Rdiv_unfold.
  apply Generic_proof.Rdiv_le_mult_pos.
  (* probably true -KH *) admit.
  rewrite Rmult_1_l.
  replace (fun x : nat => is_a_factor x && (Nat.gcd x N =? 1))
    with (fun x : nat => (Nat.gcd x N =? 1) && is_a_factor x).
  subst N.
  unfold prob_value_sats_pred.
  (* should be able to get this out of ShorAux.reduction_factor_order_finding *)
  admit.
Admitted.


(*

assuming you choose between all valid a's (= a coprime to N) with uniform probability
the sum of the intervals for a's that lead to a factor will be at least 0.5

-->

assuming you choose between all valid a's with uniform probability
the success prob == the prob that we chose an a that leads to a factor
                    * the prob that order finding succeeds

*)

(* Goal:

Given a < N s.t. a and N are coprime, there is at least a 1/2 * κ / (Nat.log2 N)^4
probability that Shor's algorithm returns a non-trivial factor of N. *)

(* Lemma end_to_end_shors_probability : *)
  

