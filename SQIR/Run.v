Require Import UnitarySem.
Require Import VectorStates.

Definition Cmod2 (c : C) : R := fst c ^ 2 + snd c ^ 2.
Lemma Cmod2_ge_0 : forall c, 0 <= Cmod2 c.
Proof. intros. simpl. field_simplify. apply Rplus_le_le_0_compat; apply pow2_ge_0. Qed.

(* We will represent a (discrete) probability distribution over [0,n) 
   using a length n list of real numbers. We support sampling from this
   distribution using the 'sample' function below. *)

Definition sum_over_list (l : list R) := Rsum (length l) (fun i => nth i l 0).

Lemma sum_over_list_cons : forall x l,
  sum_over_list (x :: l) = (x + sum_over_list l)%R.
Proof.
  intros x l.
  unfold sum_over_list.
  simpl length. 
  rewrite Rsum_shift.
  simpl nth.
  reflexivity.
Qed.

Lemma sum_over_list_append : forall l1 l2,
  sum_over_list (l1 ++ l2) = (sum_over_list l1 + sum_over_list l2)%R.
Proof.
  intros l1 l2.
  induction l1.
  unfold sum_over_list. 
  simpl. lra.
  simpl. 
  rewrite 2 sum_over_list_cons, IHl1.
  lra.
Qed.

Definition distribution (l : list R) := 
  Forall (fun x => 0 <= x) l /\ sum_over_list l = 1.

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

Definition pr_outcome_sum_extend' :
  forall l f a,
    (pr_outcome_sum (a :: l) f = (if (f 0%nat) then a else 0) + pr_outcome_sum l (fun i => f (S i)))%R.
Proof.
  intros.
  rewrite pr_outcome_sum_extend.
  destruct (f O).
  reflexivity. lra.
Qed.    

Lemma pr_outcome_sum_replace_f : forall l f1 f2,
  (forall x, (x < length l )%nat-> f1 x = f2 x) ->
  pr_outcome_sum l f1 = pr_outcome_sum l f2.
Proof.
  intros l f1 f2 H.
  unfold pr_outcome_sum.
  apply Rsum_eq_bounded.
  intros.
  rewrite H; auto.
Qed.

Lemma pr_outcome_sum_false : forall l f,
  (forall i, (i < length l)%nat -> f i = false) ->
  pr_outcome_sum l f = 0.
Proof.
  induction l; intros f Hf.
  reflexivity.
  rewrite pr_outcome_sum_extend.
  rewrite Hf.
  apply IHl.
  intros i Hi.
  apply Hf.
  simpl. lia.
  simpl. lia.
Qed.

Lemma pr_outcome_sum_true : forall l f,
  (forall i, (i < length l)%nat -> f i = true) ->
  pr_outcome_sum l f = sum_over_list l.
Proof.
  induction l; intros f Hf.
  reflexivity.
  rewrite pr_outcome_sum_extend.
  rewrite Hf.
  rewrite IHl.
  rewrite sum_over_list_cons.
  reflexivity.
  intros i Hi.
  apply Hf.
  simpl. lia.
  simpl. lia.
Qed.

Lemma pr_outcome_sum_negb : forall l f,
  pr_outcome_sum l f = (sum_over_list l - pr_outcome_sum l (fun x => negb (f x)))%R.
Proof.
  induction l; intro f.
  unfold pr_outcome_sum, sum_over_list.
  simpl. lra.
  rewrite 2 pr_outcome_sum_extend.
  rewrite sum_over_list_cons.
  rewrite IHl.
  destruct (f O); simpl; lra.
Qed.

Lemma pr_outcome_sum_orb : forall l f1 f2,
  Forall (fun x => 0 <= x) l ->
  pr_outcome_sum l f1 <= pr_outcome_sum l (fun rnd => f1 rnd || f2 rnd).
Proof.
  intros l f1 f2 Hl.
  gen f1 f2.
  induction l; intros f1 f2. 
  unfold pr_outcome_sum.
  simpl. lra.
  rewrite 2 pr_outcome_sum_extend.
  inversion Hl; subst.
  destruct (f1 O); simpl.
  apply Rplus_le_compat_l.
  apply IHl; auto.
  destruct (f2 O); simpl.
  rewrite <- (Rplus_0_l (pr_outcome_sum l _)).
  apply Rplus_le_compat; auto.
  apply IHl; auto.
Qed.

Lemma pr_outcome_sum_implies : forall l f1 f2,
  Forall (fun x => 0 <= x) l ->
  (forall x, f1 x = true -> f2 x = true) ->
  (pr_outcome_sum l f1 <= pr_outcome_sum l f2)%R. 
Proof.
  intros l f1 f2 Hl.
  gen f1 f2.
  induction l; intros f1 f2 H.
  unfold pr_outcome_sum.
  simpl. lra.
  rewrite 2 pr_outcome_sum_extend.
  inversion Hl; subst.
  destruct (f1 O) eqn:f1O.
  apply H in f1O.
  rewrite f1O.
  apply Rplus_le_compat_l.
  auto.
  destruct (f2 O).
  rewrite <- (Rplus_0_l (pr_outcome_sum _ _)).
  apply Rplus_le_compat; auto.
  auto.
Qed.

(* Mathematically, the probability that an element satisifes a (not necessarily
   boolean) predicate is the size of the range of r-values for which the element
   returned from "sample" satisfies the predicate. *)
Inductive interval_sum (P : R -> Prop) (rl rr : R) : R -> Prop :=
| SingleInterval : forall r1 r2, rl <= r1 <= r2 /\ r2 <= rr ->
    (forall r, r1 < r < r2 -> P r) ->               
    (forall r, rl < r < r1 -> ~ P r) ->
    (forall r, r2 < r < rr -> ~ P r) ->
    interval_sum P rl rr (r2 - r1)%R
(* We could add [~ P rm] to this case to guarantee unique intervals *) 
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

Lemma interval_sum_gt_0 : forall P rl rr r, interval_sum P rl rr r -> r >= 0.
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
    rewrite pr_outcome_sum_extend'.
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
  intros. destruct H as [H H0]. unfold pr_P.
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

(** Joint distributions **)

Fixpoint scale r l :=
  match l with
  | nil => nil
  | h :: t => (r * h)%R :: scale r t
  end.

(* Combine distributions l1 and l2, where l2 may depend on the value of l1 *)
Fixpoint join' l1 l2 n :=
  match n with
  | O => nil
  | S n' => join' l1 l2 n' ++ scale (nth n' l1 0) (l2 n')
  end.
Definition join l1 l2 := join' l1 l2 (length l1).

(* Return the first k bits of an n-bit nat x as a nat. *)
Definition first_k k n x := (x / 2 ^ (n - k))%nat.

(* Return the last k bits of an n-bit nat x as a nat. *)
Definition last_k k n x := (x - (first_k (n - k) n x * 2 ^ k))%nat.

Lemma simplify_first_k : forall m n x y,
  (y < 2 ^ n)%nat ->
  first_k m (m + n) (2 ^ n * x + y) = x.
Proof.
  intros m n x y Hy.
  unfold first_k. 
  replace (m + n - m)%nat with n by lia.
  rewrite Nat.mul_comm.
  rewrite Nat.div_add_l. 
  rewrite Nat.div_small by assumption. 
  lia. 
  apply Nat.pow_nonzero.
  lia.
Qed.

Lemma simplify_last_k : forall m n x y,
  (y < 2 ^ n)%nat ->
  last_k n (m + n) (2 ^ n * x + y) = y.
Proof.
  intros m n x y Hy.
  unfold last_k. 
  replace (m + n - n)%nat with m by lia.
  rewrite simplify_first_k by assumption.
  lia.
Qed.

Lemma sum_over_list_scale : forall x l,
  sum_over_list (scale x l) = (x * sum_over_list l)%R.
Proof.
  intros x l.
  induction l.
  unfold sum_over_list. 
  simpl. lra.
  simpl.
  rewrite 2 sum_over_list_cons, IHl.
  lra.
Qed.

Lemma sum_over_list_firstn : forall n l, (n < length l)%nat ->
  sum_over_list (firstn (S n) l) = (sum_over_list (firstn n l) + nth n l 0)%R.
Proof.
  intros n.
  induction n; intros l Hn.
  destruct l.
  simpl in Hn.
  lia.
  simpl.
  unfold sum_over_list.
  simpl.
  lra.
  destruct l.
  simpl in Hn.
  lia.
  destruct l.
  simpl in Hn.
  lia.
  rewrite firstn_cons.
  rewrite sum_over_list_cons.
  rewrite IHn.
  rewrite firstn_cons.
  rewrite sum_over_list_cons.
  simpl.
  lra.
  simpl in *.
  lia.
Qed.

Lemma Forall_scale_geq : forall a l,
  (0 <= a)%R ->
  Forall (fun x : R => 0 <= x) l -> 
  Forall (fun x : R => 0 <= x) (scale a l).
Proof.
  intros a l Ha Hl.
  induction l; simpl.
  constructor.
  inversion Hl; subst.
  constructor.
  apply Rmult_le_pos; auto.
  apply IHl.
  assumption.
Qed.

Lemma distribution_join : forall l1 l2,
  distribution l1 ->
  (forall i, (i < length l1)%nat -> distribution (l2 i)) ->
  distribution (join l1 l2).
Proof.
  intros l1 l2 [Hl1_1 Hl1_2] Hl2.
  assert (Hl2_1 : forall i, (i < length l1)%nat -> Forall (fun x : R => 0 <= x) (l2 i)).
  intros i Hi.
  specialize (Hl2 i Hi).
  destruct Hl2; assumption.
  assert (Hl2_2 : forall i, (i < length l1)%nat -> sum_over_list (l2 i) = 1).
  intros i Hi.
  specialize (Hl2 i Hi).
  destruct Hl2; assumption.
  clear Hl2.
  assert (H1 : forall n, (n <= length l1)%nat -> Forall (fun x : R => 0 <= x) (join' l1 l2 n)). 
  { clear Hl1_2 Hl2_2.
    intros n Hn.
    induction n; simpl.
    constructor.
    apply Forall_app.
    split.
    apply IHn. lia.
    apply Forall_scale_geq.
    rewrite Forall_nth in Hl1_1.
    apply Hl1_1; auto.
    apply Hl2_1.
    lia. }
  assert (H2 : forall n, (n <= length l1)%nat -> 
    sum_over_list (join' l1 l2 n) = sum_over_list (firstn n l1)). 
  { clear Hl1_1 Hl1_2 Hl2_1.
    intros n Hn.
    induction n.
    simpl. reflexivity.
    simpl join'.
    rewrite sum_over_list_append.
    rewrite IHn by lia.
    rewrite sum_over_list_scale.
    rewrite sum_over_list_firstn by lia.
    rewrite (Hl2_2 n Hn). 
    lra. }
  split.
  apply H1. 
  lia.
  unfold join.
  rewrite H2 by lia.
  rewrite firstn_all.
  assumption.
Qed.

Lemma length_scale : forall a l, length (scale a l) = length l.
Proof.
  intros a l.
  induction l.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Lemma pr_outcome_sum_scale : forall a l f, 
  pr_outcome_sum (scale a l) f = (a * pr_outcome_sum l f)%R.
Proof.
  intros a l.
  induction l; intro f.
  unfold pr_outcome_sum.
  simpl. lra.
  unfold pr_outcome_sum in *.
  simpl length.
  rewrite 2 Rsum_shift.
  simpl nth.
  rewrite IHl.
  destruct (f O); lra.
Qed.

Lemma length_join' : forall l1 l2 i n,
  (i <= length l1)%nat ->
  (forall i, (i < length l1)%nat -> length (l2 i) = (2 ^ n)%nat) -> 
  length (join' l1 l2 i) = (2 ^ n * i)%nat.
Proof.
  intros l1 l2 i n Hi Hl2.
  induction i.
  simpl. 
  lia. 
  simpl.
  rewrite app_length.
  rewrite IHi by lia.
  rewrite length_scale.
  rewrite Hl2 by lia.
  lia.
Qed.

Lemma nth_firstn : forall {A} i n (l : list A) d,
  (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros A i n l d Hi.
  generalize dependent n.
  generalize dependent i.
  induction l; intros i n Hi.
  rewrite firstn_nil.
  reflexivity.
  destruct n. lia.
  rewrite firstn_cons.
  simpl.
  destruct i.
  reflexivity.
  apply IHl.
  lia.
Qed.

Lemma pr_outcome_sum_firstn : forall n l f, (n < length l)%nat ->
  pr_outcome_sum (firstn (S n) l) f = 
    ((if f n then nth n l 0 else 0) + pr_outcome_sum (firstn n l) f)%R.
Proof.
  intros n l f.
  generalize dependent l.
  induction n; intros l Hn.
  destruct l.
  simpl in Hn.
  lia.
  simpl.
  unfold pr_outcome_sum.
  simpl.
  destruct (f O); lra.
  destruct l.
  simpl in Hn.
  lia.
  rewrite IHn by lia.
  destruct l.
  simpl in Hn.
  lia.
  rewrite 2 firstn_cons.
  unfold pr_outcome_sum.
  Local Opaque firstn.
  simpl length.
  rewrite 2 Rsum_extend.
  repeat rewrite firstn_length_le.
  assert (aux : forall a b c d, (a < 2 + d)%nat ->
            nth a (b :: c :: firstn d l) 0 = nth a (b :: c :: l) 0).
  { clear.
    intros a b c d H.
    destruct a.
    reflexivity.
    destruct a.
    reflexivity.
    simpl.
    apply nth_firstn.
    lia. }
  apply f_equal2.
  rewrite aux. reflexivity. simpl in Hn. lia.
  apply f_equal2.
  rewrite aux. reflexivity. simpl in Hn. lia.
  apply Rsum_eq_bounded.
  intros i Hi.
  rewrite aux by lia. 
  rewrite nth_firstn. reflexivity. lia.
  lia.
  simpl in Hn. lia.
Qed.

Local Transparent firstn.
Lemma pr_outcome_sum_join_geq : forall l1 l2 f1 f2 r1 r2 m n,
  distribution l1 ->
  (0 <= r2)%R ->
  pr_outcome_sum l1 f1 >= r1 ->
  (forall i, (i <= length l1)%nat ->
        length (l2 i) = (2 ^ n)%nat /\
        pr_outcome_sum (l2 i) (f2 i) >= r2) -> (* note: r2 independent of i *)
  let f1f2 z := (let x := first_k m (m + n) z in
                 let y := last_k n (m + n) z in
                 f1 x && f2 x y) in
  pr_outcome_sum (join l1 l2) f1f2 >= (r1 * r2)%R.
Proof.
  intros l1 l2 f1 f2 r1 r2 m n Hl1dist Hr2 Hl1 Hl2 f1f2.
  assert (forall i, (i <= length l1)%nat ->
    pr_outcome_sum (join' l1 l2 i) f1f2 >= 
      pr_outcome_sum (firstn i l1) f1 * r2).
  { intros i Hi.
    induction i.
    unfold pr_outcome_sum.
    simpl.
    lra.
    simpl join'.
    rewrite pr_outcome_sum_append.
    rewrite pr_outcome_sum_scale.
    rewrite Rplus_comm.
    erewrite pr_outcome_sum_replace_f.
    2: { intros x Hx.
         subst f1f2.
         destruct (Hl2 i) as [H _].
         lia.
         rewrite length_join' with (n:=n).
         rewrite H in Hx.
         rewrite simplify_first_k by assumption.
         rewrite simplify_last_k by assumption.
         simpl.
         reflexivity.
         lia.
         intros j Hj. 
         destruct (Hl2 j) as [? _].
         lia.
         assumption. }
    rewrite pr_outcome_sum_firstn by lia.
    rewrite Rmult_plus_distr_r.
    apply Rplus_ge_compat.
    destruct (f1 i) eqn:f1i.
    erewrite pr_outcome_sum_replace_f.
    2: { intros x Hx. simpl. reflexivity. }
    apply Rmult_ge_compat_l.
    destruct Hl1dist as [Hl1dist _].
    rewrite Forall_nth in Hl1dist. 
    apply Rle_ge.
    apply Hl1dist.
    lia.
    destruct (Hl2 i) as [_ H].
    lia.
    assumption.
    rewrite Rmult_0_l.
    apply Rle_ge.
    apply Rmult_le_pos.
    destruct Hl1dist as [Hl1dist _].
    rewrite Forall_nth in Hl1dist. 
    apply Hl1dist.
    lia. 
    rewrite pr_outcome_sum_false.
    lra.
    intros. 
    reflexivity.
    apply IHi.
    lia. }
  eapply Rge_trans.
  apply H.
  reflexivity.
  rewrite firstn_all. 
  apply Rmult_ge_compat_r.
  lra.
  assumption.
Qed.

(** Repeat independent runs **)

(* rnds  : source of randomness for sampling
   niter : max number of iterations
   body  : operation to iterate *)
Fixpoint iterate {A} (rnds : list R) (body : R -> option A) :=
  match rnds with
  | nil => None
  | rnd :: rnds' => 
      match body rnd with
      | Some v => Some v
      | None => iterate rnds' body
      end
  end.

Inductive pr_Ps : ((list R) -> Prop) -> nat -> R -> Prop :=
| pr_Ps_base : forall (Ps : (list R) -> Prop), Ps nil -> pr_Ps Ps O 1
| pr_Ps_rec : forall Ps i r1 P r2,
    pr_Ps Ps i r1 ->
    pr_P P r2 ->
    (forall rnd rnds, (length rnds <= i)%nat -> (Ps (rnd :: rnds) <-> Ps rnds /\ P rnd)) ->
    pr_Ps Ps (S i) (r1 * r2).

Lemma pr_P_same :
  forall P1 P2 r,
    (forall rnd, 0 <= rnd <= 1 -> P1 rnd <-> P2 rnd) ->
    pr_P P1 r ->
    pr_P P2 r.
Proof.
  unfold pr_P. intros.
  apply interval_sum_same with (P1 := P1); assumption.
Qed.

Lemma pr_Ps_same :
  forall i Ps1 Ps2 r,
    (forall rnds, (length rnds <= i)%nat -> (Ps1 rnds <-> Ps2 rnds)) ->
    pr_Ps Ps1 i r ->
    pr_Ps Ps2 i r.
Proof.
  induction i; intros.
  - inversion H0; subst.
    rewrite H in H1 by easy.
    constructor. assumption.
  - inversion H0; subst.
    apply pr_Ps_rec with (P := P); try assumption.
    apply IHi with (Ps1 := Ps1); try assumption.
    intros. apply H. lia.
    intros. rewrite <- H, H5, <- H by (simpl; lia).
    reflexivity.
Qed.

Lemma pr_Ps_nil :
  forall i Ps r,
    pr_Ps Ps i r ->
    Ps nil.
Proof.
  induction i; intros.
  - inversion H; easy.
  - inversion H; subst.
    apply IHi with (r := r1). assumption.
Qed.

Lemma pr_Ps_unique : forall Ps i r1 r2,
  pr_Ps Ps i r1 ->
  pr_Ps Ps i r2 ->
  r1 = r2.
Proof.
  intros Ps i. gen Ps.
  induction i; intros.
  - inversion H; inversion H0; lra.
  - inversion H; inversion H0; subst.
    specialize (IHi Ps r0 r4 H2 H8).
    apply pr_P_same with (P2 := P0) in H3.
    specialize (pr_P_unique P0 r3 r5 H3 H9) as G.
    subst. reflexivity.
    intros rnd HH. split; intros.
    + specialize (pr_Ps_nil i Ps r0 H2) as G.
      assert (Ps nil /\ P rnd) by easy.
      rewrite <- H5 in H4 by (simpl; lia).
      rewrite H11 in H4 by (simpl; lia).
      easy.
    + specialize (pr_Ps_nil i Ps r0 H2) as G.
      assert (Ps nil /\ P0 rnd) by easy.
      rewrite <- H11 in H4 by (simpl; lia).
      rewrite H5 in H4 by (simpl; lia).
      easy.
Qed.

Definition isSome {A} (o : option A) := match o with None => false | _ => true end.
Definition isNone {A} (o : option A) := match o with None => true | _ => false end.

Lemma pr_iterate_None :
  forall {A} n (body : R -> option A) r,
    pr_P (fun rnd => isNone (body rnd) = true) r ->
    pr_Ps (fun rnds => isNone (iterate rnds body) = true) n (r ^ n)%R.
Proof.
  intros. induction n.
  - constructor. reflexivity.
  - replace (r ^ (S n))%R with (r^n * r)%R by (simpl; lra).
    apply pr_Ps_rec with (P := (fun rnd : R => isNone (body rnd) = true)) (r2 := r) in IHn; try assumption.
    split; intros.
    simpl in H1. destruct (body rnd) eqn:E; try easy.
    simpl. destruct (body rnd) eqn:E; try easy.
Qed.



(*
Fixpoint iterate {A} (rnds : nat -> R) (niter : nat) (body : R -> option A) :=
  match niter with
  | 0 => None
  | S niter' => 
      match body (rnds niter') with
      | Some v => Some v
      | None => iterate rnds niter' body
      end
  end.

Inductive pr_indPs : (nat -> (R -> Prop)) -> nat -> R -> Prop :=
| pr_ind_base : forall Ps, pr_indPs Ps O 1
| pr_ind_rec : forall Ps i r1 r2,
    pr_P (Ps i) r1 ->
    pr_indPs Ps i r2 ->
    pr_indPs Ps (S i) (r1 * r2).


(* "pr_Ps P i r" says that predicate P is true with probability r and makes 
    i random choices from some random stream of reals. *)
Inductive pr_Ps : ((nat -> R) -> Prop) -> nat -> R -> Prop :=
| pr_Ps_base : pr_Ps (fun _ => True) O 1
| pr_Ps_rec : forall P1 i r1 P2 r2 P,
    pr_Ps P1 i r1 -> 
    pr_P P2 r2 ->
    (forall rnds, P rnds <-> P1 rnds /\ P2 (rnds i)) ->
    pr_Ps P (S i) (r1 * r2).

Definition isNone {A} (o : option A) := match o with None => true | _ => false end.
Definition isSome {A} (o : option A) := match o with Some _ => true | _ => false end.

Lemma pr_iterate_None : forall {A} niter (body : R -> option A) r,
  (niter > 0)%nat ->
  pr_P (fun rnd => isNone (body rnd) = true) r ->
  pr_Ps (fun rnds => isNone (iterate rnds niter body) = true) niter (r ^ niter)%R.
Proof.
  intros A niter body r H1 H2.
  induction niter.
  lia.
  clear H1.
  destruct niter.
  clear IHniter.
  simpl.
  rewrite Rmult_comm.
  eapply pr_Ps_rec.
  apply pr_Ps_base.
  apply H2.
  intro rnds.
  simpl.
  destruct (body (rnds O)).
  split; intros; easy.
  split; intros; easy.
  remember (S niter) as niter'.
  simpl.
  rewrite Rmult_comm.
  eapply pr_Ps_rec.
  apply IHniter.
  subst. lia.
  apply H2.
  intro rnds.
  simpl.
  destruct (body (rnds niter')).
  split; intros; easy.
  split; intros; easy.
Qed.

(* @Robert @Yuxiang I don't think there's any way to prove this from first 
   principles. Are we ok with this axiom? Our alternatives are: change the definition
   of pr_Ps to make something like this provable (possibly reuse join?), or give 
   up on having a general statement about multiple iterations ;-;  -Kesha *)

Axiom negate_pr_Ps : forall f i r, 
  pr_Ps (fun rnds => f rnds = true) i r ->
  pr_Ps (fun rnds => f rnds = false) i (1 - r)%R.

(* This might be provable, I haven't thought about it very carefully. -Kesha *)
Lemma pr_Ps_unique : forall P i r1 r2,
    pr_Ps P i r1 ->
    pr_Ps P i r2 ->
    r1 = r2.
Proof.
  intros P i. gen P.
  induction i; intros.
  - inversion H; inversion H0; lra.
  - inversion H; inversion H0; subst.

Lemma pr_iterate_Some : forall {A} niter (f : nat -> option A) l r,
  (niter > 0)%nat ->
  distribution l ->
  pr_P (fun rnd => isSome (f (sample l rnd)) = true) r ->
  pr_Ps (fun rnds => isSome (iterate rnds niter (fun rnd => f (sample l rnd))) = true) niter (1 - ((1 - r) ^ niter))%R.
Proof.
  intros A niter f l r Hniter Hl H.
  remember (fun rnd => f (sample l rnd)) as body.
  replace (fun rnds => isSome (iterate rnds niter body) = true) 
    with (fun rnds => isNone (iterate rnds niter body) = false). 
  apply negate_pr_Ps.
  apply pr_iterate_None; auto.
  subst.
  rewrite <- pr_outcome_sum_eq with (f:=(fun x => isNone (f x))) by assumption.
  rewrite <- pr_outcome_sum_eq with (f:=(fun x => isSome (f x))) in H by assumption.
  rewrite pr_outcome_sum_negb in H.
  destruct Hl as [_ Hl].
  rewrite Hl in H.
  replace (fun x : nat => ¬ (isSome (f x))) 
    with (fun x : nat => isNone (f x)) in H.
  lra.
  apply functional_extensionality.
  intro x. 
  destruct (f x); auto.
  apply functional_extensionality.
  intro x. 
  destruct (iterate x niter body); simpl. 
  (* umm... is this true? @Robert? -Kesha *)
Admitted.
*)
