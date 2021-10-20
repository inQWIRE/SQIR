Require Import UnitarySem.
Require Import VectorStates.

(* MOVE TO: Matrix.v *)
Fixpoint vec_to_list' {nmax : nat} (n : nat) (v : Vector nmax) :=
  match n with
  | O    => nil
  | S n' => v (nmax - n)%nat O :: vec_to_list' n' v
  end.
Definition vec_to_list {n : nat} (v : Vector n) := vec_to_list' n v.

Lemma vec_to_list'_length : forall m n (v : Vector n), length (vec_to_list' m v) = m.
Proof.
  intros.
  induction m; auto.
  simpl. rewrite IHm.
  reflexivity.
Qed.

Lemma vec_to_list_length : forall n (v : Vector n), length (vec_to_list v) = n.
Proof. intros. apply vec_to_list'_length. Qed.

Lemma nth_vec_to_list' : forall {m n} (v : Vector n) x,
  (m <= n)%nat -> (x < m)%nat -> nth x (vec_to_list' m v) 0 = v (n - m + x)%nat O.
Proof.
  intros m n v x Hm.
  gen x.
  induction m; intros x Hx.
  lia.
  simpl.
  destruct x.
  rewrite Nat.add_0_r.
  reflexivity.
  rewrite IHm by lia.
  replace (n - S m + S x)%nat with (n - m + x)%nat by lia.
  reflexivity.
Qed.

Lemma nth_vec_to_list : forall n (v : Vector n) x,
  (x < n)%nat -> nth x (vec_to_list v) 0 = v x O.
Proof.
  intros. 
  unfold vec_to_list. 
  rewrite nth_vec_to_list' by lia.
  replace (n - n + x)%nat with x by lia.
  reflexivity.
Qed.

(* MOVE TO: Complex.v *)
Definition Cmod2 (c : C) : R := fst c ^ 2 + snd c ^ 2.
Lemma Cmod2_ge_0 : forall c, 0 <= Cmod2 c.
Proof. intros. simpl. field_simplify. apply Rplus_le_le_0_compat; apply pow2_ge_0. Qed.

(* We will represent a (discrete) probability distribution over [0,n) 
   using a length n list of real numbers. We support sampling from this
   distribution using the 'sample' function below. *)

Require Import examples.Utilities.

Definition distribution (l : list R) := 
  (length l > 0)%nat /\ 
  Forall (fun x => 0 <= x) l /\
  Rsum (length l) (fun i => nth i l 0) = 1.

(* Choose an element from the distribution based on random number r ∈ [0,1).
   
   Example: Say that the input list is l = [.2, .3, .4, .1] (which might correspond
   to the probabilities of measuring the outcomes 00, 01, 10, 11). Then this
   function will return:
    * 0 for r ∈ [0, .2)
    * 1 for r ∈ [.2, .5)
    * 2 for r ∈ [.5, .9)
    * 3 for r ∈ [.9, 1) 

   The probability of getting a particular outcome is the size of the intervals of
   r values that produce that outcome. (See r_interval below.) *)
Fixpoint sample (l : list R) (r : R) : nat :=
  match l with
  | nil    => 0 (* error case *)
  | x :: l' => if Rlt_le_dec r x then 0 else S (sample l' (r-x))
  end.

(* Intuitively, the probability that an element satisfies boolean predicate 
   f is the sum over all element for which f holds. *)
Definition pr_outcome_sum (l : list R) (f : nat -> bool) : R :=
  Rsum (length l) (fun i => if f i then nth i l 0 else 0).

Definition pr_outcome_sum_extend_yp :
  forall l f a,
    (pr_outcome_sum (a :: l) f = (if (f 0%nat) then a else 0) + pr_outcome_sum l (fun i => f (S i)))%R.
Proof.
  intros. unfold pr_outcome_sum.
  simpl. destruct (length l).
  - simpl. destruct (f 0%nat); lra.
  - rewrite decomp_sum by lia. simpl.
    destruct (f 0%nat); lra.
Qed.    

    
(* Mathematically, the probability that an element satisifes a (not necessarily
   boolean) predicate is the size of the range of r-values for which the element
   returned from "sample" satisfies the predicate. *)
(* @Robert: Seem ok? Suggestions for a more descriptive name? Also: would it
   be easier to use pr_outcome_sum directly? Maybe it's useful for defining 
   independence? *)
(* RNR: Name is okay though we could use something like probability or measure (the second has regretable ambiguity in context)? If you can use pr_outcome_sum directly, that fine, but that requires the list of probabilities. I wish I'd written down exactly why I took this approach. *) 
(* TODO: should the bounds be on r1, r2 be leq instead of lt? *)
(* RNR: leq and lt are identical for continuous arithmetic, so whichever is easier to work with. *)

Inductive interval_sum (P : R -> Prop) (rl rr : R) : R -> Prop :=
| SingleInterval : forall r1 r2, rl <= r1 <= r2 /\ r2 <= rr ->
    (forall r, r1 < r < r2 -> P r) ->               
    (forall r, rl < r < r1 -> ~ P r) ->
    (forall r, r2 < r < rr -> ~ P r) ->
    interval_sum P rl rr (r2 - r1)%R
(* We could add [~ P rm] to this case to guarantee unique intervals,
   but still no proof uniqueness *) 
| CombineIntervals : forall rm r1 r2, rl <= rm <= rr -> 
    interval_sum P rl rm r1 ->
    interval_sum P rm rr r2 ->
    interval_sum P rl rr (r1 + r2).


Lemma interval_sum_shift :
  forall P rl rr r a,
    interval_sum P rl rr r ->
    interval_sum (fun x => P (x - a)%R) (rl + a)%R (rr + a)%R r.
Proof.
  intros.
  induction H.
  - replace (r2 - r1)%R with ((r2 + a) - (r1 + a))%R by lra.
    constructor; intros; try lra.
    apply H0. lra.
    apply H1. lra.
    apply H2. lra.
  - apply CombineIntervals with (rm := (rm + a)%R); try lra; try easy.
Qed.

Lemma interval_sum_same :
  forall P1 P2 rl rr r,
    interval_sum P1 rl rr r ->
    (forall x, rl <= x <= rr -> (P1 x <-> P2 x)) ->
    interval_sum P2 rl rr r.
Proof.
  intros.
  induction H.
  - constructor; intros; try lra.
    apply H0. lra. apply H1. lra.
    intro. apply H0 in H5. assert (~ P1 r). apply H2. lra. easy. lra.
    intro. apply H0 in H5. assert (~ P1 r). apply H3. lra. easy. lra.
  - apply CombineIntervals with (rm := rm); try lra.
    apply IHinterval_sum1. intros. apply H0. lra.
    apply IHinterval_sum2. intros. apply H0. lra.
Qed.

Lemma interval_sum_shift_alt :
  forall P rl rr r a,
    interval_sum (fun x => P (x + a)%R) (rl - a)%R (rr - a)%R r ->
    interval_sum P rl rr r.
Proof.
  intros.
  replace rl with ((rl - a) + a)%R by lra.
  replace rr with ((rr - a) + a)%R by lra.
  remember (fun x => P (x + a)%R) as P'.
  eapply interval_sum_same.
  apply interval_sum_shift. apply H.
  split; intros. subst. replace (x - a + a)%R with x in H1 by lra. easy.
  subst. replace (x - a + a)%R with x by lra. easy.
Qed.

Lemma interval_sum_gt_0 : forall P rl rr r,
    interval_sum P rl rr r ->
    r >= 0.
Proof. intros. induction H; lra. Qed.

Lemma interval_sum_break :
  forall P rl rm rr r,    
    interval_sum P rl rr r ->
    rl <= rm <= rr ->
    exists r1 r2 : R, interval_sum P rl rm r1 /\ interval_sum P rm rr r2 /\
                 (r = r1 + r2)%R.
Proof.
  intros.
  induction H.
  - intros.
    destruct (Rle_lt_dec rm r1); [| destruct (Rlt_le_dec rm r2)]. 
    + exists (rm - rm)%R, (r2 - r1)%R.
      repeat split; try lra.
      * apply SingleInterval; intros; auto; try lra.
        apply H2; lra.
      * apply SingleInterval; intros; auto; try lra.
        apply H2; lra.
    + exists (rm - r1)%R, (r2 - rm)%R.
      repeat split; try lra.
      * apply SingleInterval; intros; auto; try lra.
        apply H1; lra.
      * apply SingleInterval; intros; auto; try lra.
        apply H1; lra.
    + exists (r2 - r1)%R, (rm - rm)%R.
      repeat split; try lra.
      * apply SingleInterval; intros; auto; try lra.
        apply H3; lra.
      * apply SingleInterval; intros; auto; try lra.
        apply H3; lra.
  - intros.
    destruct (Rtotal_order rm0 rm) as [L1 | [L2 | L3]].
    + clear IHinterval_sum1.
      destruct IHinterval_sum2 as [x1 [x2 [S1 [S2 E]]]]. lra.
      subst.
      exists (r1 + x1)%R, x2.
      repeat split; auto; try lra.
      apply CombineIntervals with rm0; auto; lra.
    + subst. eauto.
    + clear IHinterval_sum2.
      destruct IHinterval_sum1 as [x1 [x2 [S1 [S2 E]]]]. lra.
      subst.
      exists x1, (x2 + r2)%R.
      repeat split; auto; try lra.
      apply CombineIntervals with rm0; auto; lra.
Qed.
      
Lemma interval_sum_unique : forall P rl rr r1 r2,
    interval_sum P rl rr r1 ->
    interval_sum P rl rr r2 ->
    r1 = r2.
Proof.
  intros.
  (* r3 - r0 = r4 - r1, H 1234 5678 *)
  (*   P : R -> Prop
  rl, rr, r0, r3 : R
  H : interval_sum P rl rr (r3 - r0)
  r1, r4 : R
  H0 : interval_sum P rl rr (r4 - r1)
  H1 : rl <= r0 <= r3 /\ r3 <= rr
  H2 : forall r : R, r0 < r < r3 -> P r
  H3 : forall r : R, rl < r < r0 -> ~ P r
  H4 : forall r : R, r3 < r < rr -> ~ P r
  H5 : rl <= r1 <= r4 /\ r4 <= rr
  H6 : forall r : R, r1 < r < r4 -> P r
  H7 : forall r : R, rl < r < r1 -> ~ P r
  H8 : forall r : R, r4 < r < rr -> ~ P r
  ============================
  (r3 - r0)%R = (r4 - r1)%R
   *)
  gen r2.
  induction H; intros.
  gen r1 r2.
  induction H3; intros.
  rename r2 into r4.
  rename H2 into H8. rename H1 into H7. rename H6 into tmp6. rename H0 into H6. rename H5 into tmp5. rename H into H5. rename H4 into H1. rename tmp6 into H4. rename tmp5 into H2. 
  {
    destruct (total_order_T r0 r3) as [[L03 | E03] | G03]; try lra.
    2: {
      destruct (total_order_T r1 r4) as [[L14 | E14] | G14]; try lra.
      remember ((r1 + r4) / 2)%R as r14.
      assert (r1 < r14 < r4)%R by lra.
      destruct (total_order_T r0 r14) as [[L | E] | G]; try lra.
      + assert (P r14) by (apply H6; lra).
        assert (~ P r14) by (apply H4; lra).
        easy.
      + remember ((r14 + r4) / 2)%R as r144.
        assert (r14 < r144 < r4)%R by lra.
        assert (P r144) by (apply H6; lra).
        assert (~ P r144) by (apply H4; lra).
        easy.
      + assert (P r14) by (apply H6; lra).
        assert (~ P r14) by (apply H3; lra).
        easy.
    }
    destruct (total_order_T r0 r1) as [[L01 | E01] | G01].
    - destruct (total_order_T r1 r3) as [[L13 | E13] | G13].
      + remember ((r0 + r1) / 2)%R as r01.
        assert (r0 < r01 < r1)%R by lra.
        assert (P r01) by (apply H2; lra).
        assert (~ P r01) by (apply H7; lra).
        easy.
      + remember ((r0 + r1) / 2)%R as r01.
        assert (r0 < r01 < r1)%R by lra.
        assert (P r01) by (apply H2; lra).
        assert (~ P r01) by (apply H7; lra).
        easy.
      + remember ((r0 + r3) / 2)%R as r03.
        assert (r0 < r03 < r3)%R by lra.
        assert (P r03) by (apply H2; lra).
        assert (~ P r03) by (apply H7; lra).
        easy.
    - destruct (total_order_T r3 r4) as [[L34 | E34] | G34]; try lra.
      + remember ((r3 + r4) / 2)%R as r34.
        assert (r3 < r34 < r4)%R by lra.
        assert (P r34) by (apply H6; lra).
        assert (~ P r34) by (apply H4; lra).
        easy.
      + remember ((r3 + r4) / 2)%R as r43.
        assert (r4 < r43 < r3)%R by lra.
        assert (P r43) by (apply H2; lra).
        assert (~ P r43) by (apply H8; lra).
        easy.
    - destruct (total_order_T r0 r4) as [[L04 | E04] | G04].
      + remember ((r0 + r1) / 2)%R as r10.
        assert (r1 < r10 < r0)%R by lra.
        assert (P r10) by (apply H6; lra).
        assert (~ P r10) by (apply H3; lra).
        easy.
      + remember ((r0 + r1) / 2)%R as r10.
        assert (r1 < r10 < r0)%R by lra.
        assert (P r10) by (apply H6; lra).
        assert (~ P r10) by (apply H3; lra).
        easy.
      + remember ((r0 + r3) / 2)%R as r03.
        assert (r0 < r03 < r3)%R by lra.
        assert (P r03) by (apply H2; lra).
        assert (~ P r03) by (apply H8; lra).
        easy.
  }
  - destruct (Rlt_le_dec r0 rm) as [LT0m | LE0m]; try lra;
      destruct (Rlt_le_dec r3 rm) as [LT3m | LE3m]; try lra.
    + assert (r3 - r0 = r1)%R.
      { apply IHinterval_sum1; try intros. apply H1; lra. lra. apply H2; lra. apply H3; lra.
      }
      assert (rr - rr = r2)%R.
      { apply IHinterval_sum2; try intros. apply H3; lra. lra. apply H2; lra. apply H3; lra.
      }
      lra.
    + assert (rm - r0 = r1)%R.
      { apply IHinterval_sum1; try intros. apply H1; lra. lra. apply H2; lra. apply H3; lra.
      }
      assert (r3 - rm = r2)%R.
      { apply IHinterval_sum2; try intros. apply H3; lra. lra. apply H2; lra. apply H3; lra.
      }
      lra.
    + assert (rm - rm = r1)%R.
      { apply IHinterval_sum1; try intros. apply H1; lra. lra. apply H2; lra. apply H3; lra.
      }
      assert (r3 - r0 = r2)%R.
      { apply IHinterval_sum2; try intros. apply H1; lra. lra. apply H2; lra. apply H3; lra.
      }
      lra.
  - inversion H2.
    + destruct (Rlt_le_dec r3 rm) as [LT3m | LE3m];
        destruct (Rlt_le_dec r4 rm) as [LT4m | LE4m]; try lra.
      * assert (r1 = r4 - r3)%R.
        { apply IHinterval_sum1.
          constructor; try intros. lra.
          apply H4; lra. apply H5; lra. apply H6; lra.
        }
        assert (r2 = rr - rr)%R.
        { apply IHinterval_sum2.
          constructor; try intros. lra.
          apply H4; lra. apply H6; lra. apply H6; lra.
        }
        lra.
      * assert (r1 = rm - r3)%R.
        { apply IHinterval_sum1.
          constructor; try intros. lra.
          apply H4; lra. apply H5; lra. apply H6; lra.
        }
        assert (r2 = r4 - rm)%R.
        { apply IHinterval_sum2.
          constructor; try intros. lra.
          apply H4; lra. apply H6; lra. apply H6; lra.
        }
        lra.
      * assert (r1 = rm - rm)%R.
        { apply IHinterval_sum1.
          constructor; try intros. lra.
          apply H4; lra. apply H5; lra. apply H6; lra.
        }
        assert (r2 = r4 - r3)%R.
        { apply IHinterval_sum2.
          constructor; try intros. lra.
          apply H4; lra. apply H5; lra. apply H6; lra.
        }
        lra.
    + destruct (Rlt_le_dec rm rm0) as [LTmm | LEmm].
      * destruct (interval_sum_break P rl rm rm0 _ H4) as [l1 [l2 [G1 [G2 G3]]]]. lra.
        assert (r1 = l1) by (apply IHinterval_sum1; easy).
        assert (r2 = l2 + r4)%R.
        { apply IHinterval_sum2. apply CombineIntervals with (rm := rm0); try lra; try easy.
        }
        lra.
      * destruct (interval_sum_break P rm0 rm rr _ H5) as [l1 [l2 [G1 [G2 G3]]]]. lra.
        assert (r1 = r3 + l1)%R.
        { apply IHinterval_sum1. apply CombineIntervals with (rm := rm0); try lra; try easy.
        }
        assert (r2 = l2) by (apply IHinterval_sum2; easy).
        lra.
Qed.

(* Mathematical measure of P on the interval (0,1) *) 
Definition pr_P P r := interval_sum P 0%R 1%R r.

(* Given our definition of sample, we can define a function to "run" a 
   quantum program and return the result of measuring all qubits.

   rnd is a random input in [0,1]. *)
Definition run {dim} (c : base_ucom dim) : list R :=
  let v := (uc_eval c) × basis_vector (2^dim) 0 in
  map Cmod2 (vec_to_list v).
Definition run_and_measure {dim} (c : base_ucom dim) (rnd : R) : nat :=
  sample (run c) rnd.

(* The pr_outcome_sum and pr_P definitions of probability are consistent. *)

Lemma Rsum_gt_f0 : forall f k,
  (forall n, 0 <= f n)  ->  
  f O <= sum_f_R0 f k.
Proof.
  intros.
  induction k.
  - simpl. lra.
  - simpl. specialize (H (S k)). lra.
Qed.

Lemma Rsum_list_extend :
  forall l a x,
    (Rsum (length (a :: l)) (fun i => nth i (a :: l) x) = a + Rsum (length l) (fun i => nth i l x))%R.
Proof.
  intros. simpl.
  destruct (length l) eqn:E.
  - simpl. lra.
  - rewrite decomp_sum by lia. easy.
Qed.

Lemma Rsum_list_geq_0 :
  forall l,
    Forall (fun x => 0 <= x) l ->
    0 <= Rsum (length l) (fun i => nth i l 0).
Proof.
  induction l; intros.
  - simpl. lra.
  - inversion H; subst. specialize (IHl H3).
    rewrite Rsum_list_extend. lra.
Qed.


(* This should be one case for the below lemma *)
Lemma single_interval_size : forall k l r,
    (k < length l)%nat ->
    Forall (fun x => 0 <= x) l ->
    Rsum (length l) (fun i => nth i l 0) = r ->
    interval_sum (fun rnd => sample l rnd = k) 0 r (nth k l 0).
Proof.
  intros.
  gen k r.
  induction l; intros; simpl in H; try lia.
  inversion H0; subst.
  destruct k; simpl.
  - replace a with (a-0)%R by lra.
    econstructor; intros; try lra. 
    + split; [lra|]. clear -H4 H5. (* RNR: could just use lemma above, but requires a bit of massaging *)
      induction (length l).
      simpl. lra.
      simpl.
      bdestruct (n <? length l)%nat.
      eapply Forall_nth with (i:=n) (d:=0) in H5. lra. easy.
      rewrite nth_overflow by lia.
      lra.
    + destruct (Rlt_le_dec r (a - 0)); try lra. easy.
    + destruct (Rlt_le_dec r (a - 0)); try lra. easy.
  - apply lt_S_n in H.
    replace (sum_f_R0 (fun i : nat => match i with
                                 | 0%nat => a
                                 | S m => nth m l 0
                                 end) (length l)) with (Rsum (length (a :: l)) (fun i : nat => nth i (a :: l) 0)) by easy.
    remember (Rsum (length (a :: l)) (fun i : nat => nth i (a :: l) 0)) as r.
    assert (Rsum (length l) (fun i : nat => nth i l 0) = r - a)%R.
    { rewrite Rsum_list_extend in Heqr. lra.
    }
    specialize (IHl H5 k H (r - a)%R H1).
    replace (nth k l 0) with (0 + (nth k l 0))%R by lra.
    assert (0 <= r - a).
    { rewrite <- H1. apply Rsum_list_geq_0. easy.
    }
    apply CombineIntervals with (rm := a); try lra.
    * replace 0%R with (0 - 0)%R by lra.
      constructor; intros; try lra.
      ** destruct (Rlt_le_dec r0 a). lia. lra.
    * remember (fun rnd => (sample l rnd) = k) as P.
      remember (fun x => P (x - a)%R) as P'.
      apply interval_sum_same with (P1 := P').
      ** replace a with (0 + a)%R by lra.
         replace r with ((r - a) + a)%R by lra.
         rewrite HeqP'. apply interval_sum_shift with (a := a).
         easy.
      ** intros. rewrite HeqP'. split.
         *** intros. rewrite HeqP in H6.
             destruct (Rlt_le_dec x a); try lra. lia.
         *** intros. destruct (Rlt_le_dec x a); try lra.
             rewrite HeqP. lia.
Qed.

(* RNR: Rather than length <> 0, I'd use that all entries of l are > 0, and (if needed) that they sum to 1 or some r (like above). *) 
Lemma pr_outcome_sum_eq_aux' : forall (l : list R) (f : nat -> bool) r,
    Forall (fun x => 0 <= x) l ->
    Rsum (length l) (fun i => nth i l 0) = r ->
    interval_sum  (fun rnd => f (sample l rnd) = true) 0 r (pr_outcome_sum l f).
Proof.
  induction l; intros.
  - simpl in *. subst. unfold pr_outcome_sum. simpl.
    replace 0 with (0 - 0)%R by lra. constructor; try intros; try lra.
  - rewrite Rsum_list_extend in H0.
    remember (fun i => f (S i)) as sf.
    assert (interval_sum (fun rnd : R => sf (sample l rnd) = true) 0 (r - a)%R (pr_outcome_sum l sf)).
    { apply IHl. inversion H; easy. lra.
    }
    rewrite pr_outcome_sum_extend_yp.
    assert (interval_sum (fun rnd : R => f (sample (a :: l) rnd) = true) 0 a (if f 0%nat then a else 0)).
    { destruct (f 0%nat) eqn:E.
      - replace a with (a - 0)%R by lra.
        constructor;
          try (inversion H; lra);
          try (intros; simpl; destruct (Rlt_le_dec r0 (a - 0)); try easy; try lra).
      - replace 0 with (a - a)%R by lra.
        constructor;
          try (inversion H; lra);
          try (intros; simpl; destruct (Rlt_le_dec r0 a); try easy; try lra).
        rewrite E. easy.
    }
    assert (interval_sum (fun rnd : R => f (sample (a :: l) rnd) = true) a r (pr_outcome_sum l sf)).
    { (*remember (fun rnd : R => f (sample (a :: l) rnd) = true) as P.*)
      apply interval_sum_shift_alt with (a := a).
      replace (a - a)%R with 0 by lra.
      eapply interval_sum_same. apply H1.
      split; intros.
      - simpl. destruct (Rlt_le_dec (x + a) a); try lra. subst. replace (x + a - a)%R with x by lra. easy.
      - subst. simpl in H4. destruct (Rlt_le_dec (x + a) a) in H4; try lra. replace (x + a - a)%R with x in H4 by lra. easy.
    }
    rewrite Heqsf in H3.
    apply CombineIntervals with (rm := a); try easy.
    inversion H.
    assert (0 <= Rsum (length l) (fun i : nat => nth i l 0)) by (apply Rsum_list_geq_0; easy).
    lra.
Qed.

Lemma pr_outcome_sum_eq_aux : forall (l : list R) (f : nat -> bool),
    distribution l ->
    pr_P (fun rnd => f (sample l rnd) = true) (pr_outcome_sum l f).
Proof.
  intros. destruct H as [H [H0 H1]]. unfold pr_P.
  apply pr_outcome_sum_eq_aux'; easy.
Qed.

Lemma pr_P_unique : forall P r1 r2,
    pr_P P r1 ->
    pr_P P r2 ->
    r1 = r2.
Proof.
  intros.
  apply interval_sum_unique with (P:=P) (rl:=R0) (rr:=R1); auto. 
Qed.

(* Alternative definition that requires uniqueness. *)
Lemma pr_outcome_sum_eq : forall f l r,
  distribution l ->
  pr_outcome_sum l f = r <-> pr_P (fun rnd => f (sample l rnd) = true) r.
Proof.
  split; intros.
  - rewrite <- H0.
    apply pr_outcome_sum_eq_aux.
    easy.
  - eapply pr_P_unique.
    apply pr_outcome_sum_eq_aux; trivial.
    easy.
Qed.

Lemma Rsum_shift : forall n (f : nat -> R),
  Rsum (S n) f = (f O + Rsum n (fun x => f (S x)))%R.
Proof.
  intros n f. 
  simpl.
  induction n; simpl.
  lra.
  rewrite IHn.
  destruct n; simpl; lra.
Qed.

Lemma pr_outcome_sum_extend : forall x l f,
  pr_outcome_sum (x :: l) f 
  = if f O
    then (x + pr_outcome_sum l (fun y => f (S y)))%R
    else pr_outcome_sum l (fun y => f (S y)).
Proof.
  intros x l f.
  unfold pr_outcome_sum.
  simpl length.
  rewrite Rsum_shift.
  destruct (f O); simpl.
  reflexivity.
  lra.
Qed.

Lemma pr_outcome_sum_append : forall l1 l2 f,
  pr_outcome_sum (l1 ++ l2) f
  = (pr_outcome_sum l1 f + pr_outcome_sum l2 (fun x => f (length l1 + x)%nat))%R.
Proof.
  intros l1 l2.
  induction l1; intro f.
  unfold pr_outcome_sum.
  simpl.
  lra.
  simpl.
  rewrite 2 pr_outcome_sum_extend.
  rewrite IHl1.
  destruct (f O); lra.
Qed.

Lemma pr_outcome_sum_repeat_false : forall n f,
  pr_outcome_sum (repeat 0 n) f = 0.
Proof.
  intros n f.
  unfold pr_outcome_sum, Rsum.
  destruct n as [| n]; trivial.
  simpl.
  apply sum_eq_R0.
  intros x Hx.
  destruct (f x); trivial.
  destruct x; trivial.
  rewrite repeat_length in Hx.
  replace n with (x + (S (n - x - 1)))%nat by lia.
  rewrite <- repeat_combine.
  simpl.
  rewrite <- repeat_length with (n:=x) (x:=0) at 1.
  rewrite nth_middle.
  trivial.
Qed.