Require Export SQIR.UnitaryOps QuantumLib.VectorStates.
Require Import QuantumLib.Summation.
Require Import QuantumLib.DiscreteProb.

Local Coercion Nat.b2n : bool >-> nat.

(* General definitions useful for specifying & verifying quantum algorithms. *)


(* ======================================== *)
(**    Boolean oracle (f : nat -> bool)    **)
(* ======================================== *)

(* Definition of boolean oracle U : ∣ x ⟩∣ y ⟩ ↦ ∣ x ⟩∣ y ⊕ f(x) ⟩ *)
Definition boolean_oracle {n} (U : base_ucom (S n)) (f : nat -> bool) :=
  forall x (y : bool), (x < 2 ^ n)%nat -> 
    @Mmult _ _ 1 (uc_eval U) (basis_vector (2 ^ n) x ⊗ ∣ y ⟩) = 
      basis_vector (2 ^ n) x ⊗ ∣ xorb y (f x) ⟩.

Definition pad_vector {n} dim (v : Vector (2 ^ n)) : Vector (2 ^ dim) :=
  v ⊗ kron_n (dim - n) ∣0⟩.

Lemma wf_pad_vector :
  forall n dim (v : Vector (2 ^ n)),
  (n <= dim)%nat -> WF_Matrix v -> WF_Matrix (pad_vector dim v).
Proof.
  intros n dim v Hn Hw. unfold pad_vector.
  apply WF_kron; auto with wf_db.
  rewrite Nat.pow_1_l. reflexivity.
Qed.

(* Alternate form of boolean_oracle that uses ancilla qubits.
   The qubits are ordered as follows: 
     input x (n qubits) ; output y (1 qubit) ; ancillae (dim-n-1 qubits) *)
Definition padded_boolean_oracle {dim} n
  (U : base_ucom dim) (f : nat -> bool) :=
  forall x (y : bool),
  (x < 2 ^ n)%nat ->
  @Mmult
      _ _ 1
      (uc_eval U)
      (@pad_vector (S n) dim (basis_vector (2 ^ n) x ⊗ ∣ y ⟩ )) =
    @pad_vector (S n) dim (basis_vector (2 ^ n) x ⊗ ∣ xorb y (f x) ⟩ ).


(* ======================================= *)
(**    Integer oracle (f : nat -> nat)    **)
(* ======================================= *)

(* Special case U : ∣ x ⟩∣ 0 ⟩ ↦ ∣ x ⟩∣ f(x) ⟩ *)
Definition integer_oracle {n} (U : base_ucom (2 * n)) (f : nat -> nat) :=
  forall (x :nat), (x < 2 ^ n)%nat -> 
    @Mmult _ _ 1 (uc_eval U) (basis_vector (2 ^ n) x ⊗ basis_vector (2 ^ n) 0) = 
      basis_vector (2 ^ n) x ⊗ ((basis_vector (2 ^ n) (f x))).


(* ========================================== *)
(**    Count the solutions to a predicate    **)
(* ========================================== *)

(* Count the number of inputs in [a,a+b) where f returns true; note that
   we never "run" this function, it's just used in specifications. *)
Fixpoint count (f : nat -> bool) a b : nat :=
  match b with
  | O => O
  | S b' => (f (a + b') + count f a b')%nat
  end.

Definition count0 f := count f 0.
Definition count1 f := count f 1.

Lemma count_extend : forall f a b, 
  count f a (S b)  = if (f (a + b)%nat) then S (count f a b) else count f a b.
Proof. intros. simpl. destruct (f (a + b)%nat); reflexivity. Qed.

Lemma count_upper_bound : forall a b (f : nat -> bool), (count f a b <= b)%nat.
Proof.
  intros.
  induction b; simpl.
  lia.
  destruct (f (a + b)%nat); simpl; lia.
Qed.

Lemma count_all_false : forall a b, count (fun _ => false) a b = O.
Proof. induction b; intros; simpl; try apply IHn; easy. Qed.

Lemma count_all_true : forall a b, count (fun _ => true) a b = b.
Proof. induction b; intros; simpl; lia. Qed.

Lemma count_zero: forall  a b (f : nat -> bool), 
  count f a b = O -> forall i, (a <= i < a + b)%nat -> f i = false.
Proof.
  intros a b f H i Hi.
  induction b as [|b].
  lia.
  simpl in H.
  apply Nat.eq_add_0 in H as [? ?].
  bdestruct (i =? a + b)%nat; subst.
  destruct (f (a + b)%nat); simpl in *; easy.
  apply IHb; lia.
Qed.
 
Lemma count_nonzero: forall  a b (f : nat -> bool), 
  count f a b <> O <-> exists i, (a <= i < a + b)%nat /\ f i = true.
Proof.
  intros a b f.
  split; intro H.
  - induction b as [|b].
    simpl in H.
    lia.
    simpl in H.
    bdestruct (count f a b =? 0).
    rewrite H0 in H.
    exists (a + b)%nat.
    split; try lia.
    destruct (f (a + b)%nat); simpl in *; auto.
    apply IHb in H0. 
    destruct H0 as [x [? ?]].
    exists x.
    split. lia. auto.
  - destruct H as [x [Hx1 Hx2]]. 
    induction b. lia.
    bdestruct (x =? a + b)%nat. subst. simpl. rewrite Hx2. simpl. lia.
    simpl. destruct (f (a + b))%nat; lia.
Qed.

Lemma count_eq : forall a b f g,
    (forall x, (a <= x < a + b)%nat -> f x = g x) ->
    count f a b = count g a b.
Proof.
  induction b; intros. reflexivity.
  assert (f (a + b) = g (a + b))%nat by (apply H; lia).
  simpl. rewrite H0. rewrite IHb with (g := g). reflexivity.
  intros. apply H. lia.
Qed.

Lemma count_update_oob : forall f x v a b, 
  (x < a)%nat \/ (a + b <= x)%nat -> 
  count f a b = count (update f x v) a b.
Proof.
  intros. apply count_eq. intros.
  rewrite update_index_neq. easy. lia.
Qed.

Lemma count_update : forall f x v a b, 
  (a <= x < a + b)%nat -> 
  f x = true -> 
  count (update f x v) a b = if v then count f a b else ((count f a b) - 1)%nat.
Proof.
  induction b; intros. lia.
  destruct v. rewrite update_same; easy.
  bdestruct (x =? a + b)%nat. subst. simpl. rewrite update_index_eq. rewrite H0.
  rewrite <- count_update_oob; simpl; lia.
  simpl. rewrite update_index_neq by easy. 
  destruct (f (a + b))%nat. rewrite IHb by (try easy; try lia).
  assert (count f a b <> 0)%nat. 
  apply count_nonzero. exists x. split. lia. assumption.
  lia.
  rewrite IHb. easy. lia. easy.
Qed.

Lemma count_update_false : forall a b x f, 
  (a <= x < a + b)%nat -> 
  f x = true -> 
  S (count (update f x false) a b) = count f a b.
Proof.
  intros. 
  assert (count f a b <> 0)%nat. 
  apply count_nonzero. exists x. split. lia. assumption.
  rewrite count_update by assumption.
  lia.
Qed.

Lemma count0_Nsum : forall n f, count0 f n = big_sum (fun i => if f i then S O else O) n.
Proof.
  unfold count0.
  intros. induction n. reflexivity. 
  simpl. rewrite IHn. destruct (f n); simpl; lia.
Qed.

Lemma count1_Nsum : forall n f,
  f O = false -> 
  f n = false ->
  count1 f n = big_sum (fun i => if f i then S O else O) n.
Proof.
  unfold count1.
  intros n f HO Hn. 
  assert (H : count f 1 n = big_sum (fun i => if f i then S O else O) (S n)).
  { clear Hn.
    induction n. simpl. rewrite HO. reflexivity.
    simpl. rewrite IHn. destruct (f (S n)); simpl; lia. }
  destruct n. reflexivity.
  rewrite H. simpl. rewrite Hn. simpl. lia.
Qed.

Lemma count_complement : forall a b f g, 
  (count (fun i => f i && g i) a b + count (fun i => f i && ¬ (g i)) a b = count f a b)%nat.
Proof.
  intros. induction b. easy.
  simpl. destruct (f (a + b))%nat; destruct (g (a + b))%nat; simpl; lia.
Qed.

Lemma count_implies : forall a b f g,
  (forall x, a <= x < a + b -> f x = true -> g x = true)%nat ->
  (count f a b <= count g a b)%nat.
Proof.
  intros. induction b. easy.
  assert (count f a b <= count g a b)%nat.
  { apply IHb. intros. apply H. lia. easy. }
  simpl. destruct (f (a + b))%nat eqn:Hf. apply H in Hf. 
  2: lia.
  rewrite Hf. lia.
  destruct (g (a + b))%nat; simpl; lia.
Qed.

Lemma count_orb : forall a b f g,
  count (fun i => f i || g i) a b = 
    (count f a b + count (fun i => (¬ (f i)) && g i)  a b)%nat.
Proof.
  intros.
  rewrite <- count_complement with (g:=f).
  assert (forall n1 n2 n3 n4, n1 = n3 -> n2 = n4 -> n1 + n2 = n3 + n4)%nat by lia.
  apply H; apply count_eq; intros; destruct (f x); destruct (g x); reflexivity.
Qed.

Definition negf (f : nat -> bool) i := negb (f i).

Lemma negf_involutive : forall f, negf (negf f) = f.
Proof.
  intros.
  unfold negf.
  apply functional_extensionality.
  intro.
  apply negb_involutive.
Qed.

Local Opaque Nat.sub.
Lemma count_negf : forall a b (f : nat -> bool),
  count (negf f) a b = (b - count f a b)%nat.
Proof.
  intros.
  induction b; simpl.
  reflexivity.
  rewrite IHb.
  unfold negf.
  specialize (count_upper_bound a b f) as H.
  destruct (f (a + b))%nat; simpl; lia.
Qed.

Lemma vsum_count0 : forall n (f : nat -> bool),
  big_sum (fun i : nat => if f i then I 1 else Zero) n = 
    INR (count0 f n) .* I 1.
Proof.
  unfold count0.
  intros.
  induction n. 
  lma.
  rewrite <- big_sum_extend_r, IHn.
  simpl count.
  rewrite plus_INR.
  destruct (f n); simpl; lma.
Qed.

Lemma nth_repeat : forall (n i : nat) (r : R),
  (i < n)%nat -> nth i (repeat r n) 0 = r.
Proof.
  intros n i r Hi.
  rewrite nth_indep with (d':=r).
  clear Hi.
  gen i.
  induction n; intro i; simpl; destruct i; try reflexivity.
  apply IHn.
  rewrite repeat_length.
  assumption.
Qed.

Lemma pr_outcome_sum_count : forall l u f,
  (l < u)%nat ->
  pr_outcome_sum (uniform l u) f 
  = (INR (count1 (fun x => f (l + x - 1)%nat) (u - l)) / INR (u - l))%R.
Proof.
  intros l u f H.
  unfold uniform.
  rewrite pr_outcome_sum_append.
  rewrite pr_outcome_sum_repeat_false.
  rewrite Rplus_0_l.
  remember (u - l)%nat as n.
  assert (Hn:(n > 0)%nat) by lia.
  clear - Hn.
  unfold pr_outcome_sum.
  rewrite 2 repeat_length.
  rewrite big_sum_eq_bounded with (g:=fun i => ((1 / INR n)%R ⋅ (if f (l + i)%nat then 1 else 0))%R).
  rewrite <- big_sum_scale_l.
  replace (INR (count1 (fun x : nat => f (l + x - 1)%nat) n) / INR n)%R with (1 / INR n * INR (count1 (fun x : nat => f (l + x - 1)%nat) n))%R by lra.
  apply f_equal2; try reflexivity.
  clear Hn.
  induction n.
  reflexivity.
  rewrite <- big_sum_extend_r.
  simpl.
  rewrite IHn.
  unfold count1. simpl.
  replace (l + S n - 1)%nat with (l + n)%nat by lia.
  destruct (f (l + n)%nat). 
  rewrite S_O_plus_INR.
  simpl. lra.
  simpl. lra.
  intros i Hi. 
  destruct (f (l + i)%nat).
  rewrite nth_repeat by assumption.
  unfold Vscale. simpl. lra.
  unfold Vscale. simpl. lra.
Qed.

(* ======================================== *)
(**         Other misc. utilities          **)
(* ======================================== *)

(* Copied from euler/Asympt.v *)
Lemma seq_extend :
  forall n x, List.seq x (S n) = List.seq x n ++ [(x + n)%nat].
Proof.
  induction n; intros. simpl. rewrite Nat.add_0_r. easy.
  replace (List.seq x (S (S n))) with (x :: List.seq (S x) (S n)) by easy.
  rewrite IHn. simpl. replace (x + S n)%nat with (S (x + n))%nat by lia.
  easy.
Qed.

Lemma count_filter_seq : forall a b f, 
  count f a b = length (filter f (List.seq a b)).
Proof.
  induction b; intros.
  reflexivity.
  rewrite seq_extend. rewrite filter_app. rewrite app_length.
  rewrite <- IHb. simpl.
  destruct (f (a + b))%nat. simpl. lia.
  simpl. lia.
Qed.

Lemma Csum_1 : forall f n, (forall x, f x = 1%C) -> 
  @big_sum Complex.C C_is_monoid f n = INR n. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn, H. 
    destruct n; lca.    
Qed.

Lemma times_n_C : forall (c : Complex.C) n, times_n c n = (INR n * c)%C.
Proof.
  intros c n. 
  induction n; simpl. 
  lca. 
  rewrite IHn.
  destruct n; lca.
Qed.

Lemma Csum_mult_l : forall (c : Complex.C) f n, (c * Σ f n)%C = Σ (fun x => c * f x) n.
Proof.
  intros c f n.
  induction n.
  + simpl; lca.
  + simpl.
    rewrite Cmult_plus_distr_l.
    rewrite IHn.
    reflexivity.
Qed.

Lemma Nsum_scale : forall n f d,
  (big_sum (fun i => d * f i) n = d * big_sum f n)%nat.
Proof.
  intros. induction n. simpl. lia. 
  simpl. rewrite IHn. lia.
Qed.

Lemma Nsum_add : forall n f g,
  (big_sum (fun i => f i + g i) n = big_sum f n + big_sum g n)%nat.
Proof.
  intros. induction n. easy.
  simpl. rewrite IHn. lia.
Qed.
