Require Import UnitarySem.
Require Import VectorStates.

(* TODO: Move this file to QuantumLib? *)

Definition Cmod2 (c : C) : R := fst c ^ 2 + snd c ^ 2.

Lemma Cmod2_ge_0 : forall c, 0 <= Cmod2 c.
Proof. 
  intros. simpl. field_simplify. apply Rplus_le_le_0_compat; apply pow2_ge_0.
Qed.

Lemma Cmod2_Cmod_sqr : forall c, (Cmod2 c = (Cmod c)^2)%R.
Proof.
  intros. unfold Cmod2, Cmod. rewrite R_sqrt.pow2_sqrt. lra.
  simpl. nra.
Qed.


(* ============================================ *)
(**   Definition of probability distribution   **)
(* ============================================ *)

(* We will represent a (discrete) probability distribution over [0,n) 
   using a length n list of real numbers. We support sampling from this
   distribution using the 'sample' function below. *)

Definition sum_over_list (l : list R) := Rsum (length l) (fun i => nth i l 0).

Definition distribution (l : list R) := 
  Forall (fun x => 0 <= x) l /\ sum_over_list l = 1.

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

Lemma sum_over_list_geq_0 : forall l,
  Forall (fun x => 0 <= x) l ->
  0 <= sum_over_list l.
Proof.
  induction l; intros.
  - unfold sum_over_list. simpl. lra.
  - inversion H; subst. specialize (IHl H3).
    rewrite sum_over_list_cons. lra.
Qed.


(* ================================ *)
(**   Sample from a distribution   **)
(* ================================ *)

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

Lemma sample_ub : forall l r, (sample l r <= length l)%nat.
Proof.
  induction l; intros. easy.
  simpl. specialize (IHl (r - a)%R). destruct (Rlt_le_dec r a); lia.
Qed.

Lemma sample_ub_lt :  forall l r, 
  0 <= r < sum_over_list l -> 
  (sample l r < length l)%nat.
Proof.
  induction l; intros. unfold sum_over_list in H. simpl in H. lra.
  simpl. destruct (Rlt_le_dec r a). lia.
  apply lt_n_S. apply IHl. rewrite sum_over_list_cons in H. lra.
Qed.

Lemma sample_lb : forall l r, (0 <= sample l r)%nat.
Proof.
  induction l; intros. easy.
  simpl. specialize (IHl (r - a)%R). destruct (Rlt_le_dec r a); lia.
Qed.

Lemma sample_max : forall l r,
    Forall (fun x => 0 <= x) l ->
    sum_over_list l <= r ->
    sample l r = length l.
Proof.
  induction l; intros. easy.
  simpl. rewrite sum_over_list_cons in H0.
  inversion H; subst.
  specialize (sum_over_list_geq_0 l H4) as G.
  assert (sum_over_list l <= r - a)%R by lra.
  specialize (IHl (r - a)%R H4 H1) as T. rewrite T.
  destruct (Rlt_le_dec r a). lra. lia.
Qed.

Lemma sample_append : forall l1 l2 r,
    Forall (fun x => 0 <= x) l1 ->
    Forall (fun x => 0 <= x) l2 ->
    sum_over_list l1 <= r ->
    (sample (l1 ++ l2) r = (length l1) + sample l2 (r - sum_over_list l1))%nat.
Proof.
  induction l1; intros.
  - simpl. f_equal. unfold sum_over_list. simpl. lra.
  - inversion H; subst.
    specialize (sum_over_list_geq_0 l1 H5) as G.
    rewrite sum_over_list_cons in *.
    simpl.
    destruct (Rlt_le_dec r a); try lra.
    f_equal. rewrite IHl1; try easy; try lra.
    f_equal. f_equal. lra.
Qed.

Lemma sample_repeat_lb : forall m l r,
    0 <= r ->
    (m <= sample (repeat 0%R m ++ l) r)%nat.
Proof.
  induction m; intros.
  lia. simpl.
  destruct (Rlt_le_dec r 0). lra.
  specialize (IHm l r H).
  replace (r - 0)%R with r by lra.
  lia.
Qed.


(* ======================================================================== *)
(** Probability that a distribution satisfies a predicate (pr_outcome_sum) **)
(* ======================================================================== *)

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
    (pr_outcome_sum (a :: l) f = (if (f O) then a else 0) + pr_outcome_sum l (fun i => f (S i)))%R.
Proof.
  intros.
  rewrite pr_outcome_sum_extend.
  destruct (f O).
  reflexivity. lra.
Qed.    

Lemma pr_outcome_sum_replace_f : forall l f1 f2,
  (forall x, (x < length l)%nat -> f1 x = f2 x) ->
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

Lemma pr_outcome_sum_ge_0 :
  forall l f, Forall (fun x => 0 <= x) l -> 0 <= pr_outcome_sum l f.
Proof.
  induction l; intros.
  - unfold pr_outcome_sum. simpl. lra.
  - inversion H; subst. unfold pr_outcome_sum.
    replace (length (a :: l)) with (S (length l)) by easy.
    rewrite Rsum_shift. simpl.
    specialize (IHl (fun x => f (S x)) H3).
    unfold pr_outcome_sum in IHl.
    destruct (f O); lra.
Qed.


(* ================================================================== *)
(**   Probability that a distribution satisfies a predicate (pr_P)   **)
(* ================================================================== *)

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
    exists r1 r2 : R, interval_sum P rl rm r1 /\ interval_sum P rm rr r2 /\ (r = r1 + r2)%R.
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

(* TODO: clean up this proof *)      
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

Lemma pr_P_same :
  forall P1 P2 r,
    (forall rnd, 0 <= rnd <= 1 -> P1 rnd <-> P2 rnd) ->
    pr_P P1 r ->
    pr_P P2 r.
Proof.
  unfold pr_P. intros.
  apply interval_sum_same with (P1 := P1); assumption.
Qed.

Lemma pr_outcome_sum_eq_aux' : forall (l : list R) (f : nat -> bool) r,
    Forall (fun x => 0 <= x) l ->
    sum_over_list l = r ->
    interval_sum  (fun rnd => f (sample l rnd) = true) 0 r (pr_outcome_sum l f).
Proof.
  induction l; intros.
  - unfold sum_over_list in *.
    simpl in *. subst. unfold pr_outcome_sum. simpl.
    replace 0 with (0 - 0)%R by lra. constructor; try intros; try lra.
  - rewrite sum_over_list_cons in H0.
    remember (fun i => f (S i)) as sf.
    assert (interval_sum (fun rnd : R => sf (sample l rnd) = true) 0 (r - a)%R (pr_outcome_sum l sf)).
    { apply IHl. inversion H; easy. lra.
    }
    rewrite pr_outcome_sum_extend'.
    assert (interval_sum (fun rnd : R => f (sample (a :: l) rnd) = true) 0 a (if f O then a else 0)).
    { destruct (f O) eqn:E.
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
    assert (0 <= sum_over_list l) by (apply sum_over_list_geq_0; easy).
    lra.
Qed.

(* The pr_outcome_sum and pr_P definitions of probability are consistent. *)
Lemma pr_outcome_sum_eq_aux : forall (l : list R) (f : nat -> bool),
    distribution l ->
    pr_P (fun rnd => f (sample l rnd) = true) (pr_outcome_sum l f).
Proof.
  intros. destruct H as [H H0]. unfold pr_P.
  apply pr_outcome_sum_eq_aux'; easy.
Qed.

Lemma pr_outcome_sum_leq_exists : forall l f r,
  distribution l ->
  pr_outcome_sum l f <= r ->
  exists r0, (0 <= r0 <= r)%R /\ pr_P (fun rnd => f (sample l rnd) = true) r0.
Proof.
  intros l f r  HlHr.
  exists (pr_outcome_sum l f).
  split; auto.
  split. apply pr_outcome_sum_ge_0. apply HlHr. auto.
  apply pr_outcome_sum_eq_aux; auto.
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


(* ======================================================= *)
(**   Distribution created by running a quantum circuit   **)
(* ======================================================= *)

(* Given our definition of sample, we can define a function to "run" a 
   quantum program and return the result of measuring all qubits.

   rnd is a random input in [0,1]. *)
Definition run {dim} (c : base_ucom dim) : list R :=
  let v := (uc_eval c) × basis_vector (2^dim) 0 in
  map Cmod2 (vec_to_list v).

Definition run_and_measure {dim} (c : base_ucom dim) (rnd : R) : nat :=
  sample (run c) rnd.

Lemma pos_Cmod2_list :
  forall l, Forall (fun x => 0 <= x) (map Cmod2 l).
Proof.
  induction l; intros.
  - simpl. constructor.
  - simpl. constructor. apply Cmod2_ge_0. apply IHl.
Qed.

Local Opaque Rsum.
Lemma sum_over_list_Cmod2_vec_to_list' : forall d x l,
  sum_over_list (map Cmod2 (@vec_to_list' x d l)) = 
    Rsum d (fun i : nat => (Cmod (l (i + x - d)%nat O) ^ 2)%R).
Proof.
  induction d; intros.
  - unfold sum_over_list. reflexivity.
  - simpl. rewrite sum_over_list_cons. rewrite IHd. simpl.
    rewrite Rsum_shift.
    replace (0 + x - S d)%nat with (x - S d)%nat by lia.
    rewrite Cmod2_Cmod_sqr. simpl.
    f_equal.
Qed.
Local Transparent Rsum.

Lemma sum_over_list_Cmod2_vec_to_list :
  forall d (l : Vector d),
    sum_over_list (map Cmod2 (vec_to_list l)) = 
      Rsum d (fun i : nat => (Cmod (l i O) ^ 2)%R).
Proof.
  intros. unfold vec_to_list.
  rewrite sum_over_list_Cmod2_vec_to_list'.
  apply Rsum_eq_bounded. intros.
  replace (i + d - d)%nat with i by lia.
  reflexivity.
Qed.

Lemma distribution_run : forall {dim} c,
    uc_well_typed c ->
    distribution (@run dim c).
Proof.
  intros. unfold run. split.
  - apply pos_Cmod2_list.
  - rewrite sum_over_list_Cmod2_vec_to_list.
    rewrite <- rewrite_norm. rewrite Mmult_adjoint.
    rewrite <- Mmult_assoc. 
    rewrite Mmult_assoc with (A := (basis_vector (2 ^ dim) 0) †).
    specialize (uc_eval_unitary dim c H) as G.
    destruct G. rewrite H1.
    restore_dims. rewrite Mmult_1_r.
    rewrite basis_vector_product_eq. reflexivity.
    apply pow_positive. lia.
    apply WF_adjoint. apply basis_vector_WF.
    apply pow_positive. lia.
Qed.

Lemma length_run : forall n (c : base_ucom n),
  length (run c) = (2 ^ n)%nat. 
Proof.
  intros n c.
  unfold run.
  rewrite map_length.
  rewrite vec_to_list_length.
  reflexivity.
Qed.


(* ========================== *)
(**   Uniform distribution   **)
(* ========================== *)

(* Uniform sampling in the range [lower, upper) *)
Definition uniform (lower upper : nat) : list R :=
  repeat 0 lower ++ repeat (1/ INR (upper - lower))%R (upper - lower).

Lemma repeat_gt0 : forall m r, 0 <= r -> Forall (fun x => 0 <= x) (repeat r m).
Proof.
  induction m; intros. simpl. constructor.
  simpl. constructor. easy. apply IHm. easy.
Qed.

Lemma sum_over_list_repeat : forall m x, (sum_over_list (repeat x m) = INR m * x)%R.
Proof.
  induction m; intros.
  - simpl. unfold sum_over_list. simpl. lra.
  - simpl. rewrite sum_over_list_cons. rewrite IHm.
    destruct m; simpl; lra.
Qed.

Lemma sample_uniform : forall l u r, 
  (l < u)%nat -> 0 <= r < 1 -> (l <= sample (uniform l u) r < u)%nat.
Proof.
  intros. split.
  - unfold uniform. apply sample_repeat_lb. easy.
  - unfold uniform. rewrite sample_append. rewrite repeat_length.
    assert (T: (forall a b c, a < c -> b < c - a -> a + b < c)%nat) by (intros; lia).
    apply T. easy.
    replace (u - l)%nat 
      with (length (repeat (1 / INR (u - l))%R (u - l))) at 3 by apply repeat_length.
    apply sample_ub_lt.
    replace l with (length (repeat 0 l)) at 1 2 by apply repeat_length.
    repeat rewrite sum_over_list_repeat.
    replace (INR (u - l) * (1 / INR (u - l)))%R 
      with (INR (u - l) * / INR (u - l))%R by lra.
    rewrite Rinv_r. lra.
    apply not_0_INR. lia.
    apply repeat_gt0; lra.
    apply repeat_gt0. unfold Rdiv. rewrite Rmult_1_l.
    apply Rlt_le. apply Rinv_0_lt_compat. apply lt_0_INR. lia.
    rewrite sum_over_list_repeat. lra.
Qed.

Lemma distribution_uniform : forall l r,
  (l < r)%nat ->
  distribution (uniform l r).
Proof.
  intros. split; unfold uniform.
  - apply Forall_app. split; apply repeat_gt0. lra.
    unfold Rdiv.
    assert (0 < / INR (r - l)).
    { apply Rinv_0_lt_compat. apply lt_0_INR. lia. }
    lra.
  - rewrite sum_over_list_append.
    do 2 rewrite sum_over_list_repeat.
    unfold Rdiv.
    replace (INR l * 0 + INR (r - l) * (1 * / INR (r - l)))%R 
      with (INR (r - l) * / INR (r - l))%R by lra.
    rewrite <- Rinv_r_sym. easy.
    assert (0 < INR (r - l)) by (apply lt_0_INR; lia).
    lra.
Qed.

Lemma length_uniform : forall l r, (l <= r)%nat -> (length (uniform l r) = r)%nat.
Proof.
  intros. unfold uniform. rewrite app_length, repeat_length, repeat_length. lia.
Qed.


(* ======================== *)
(**   Joint distribution   **)
(* ======================== *)

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

(* When sampling from (join l1 l2) where |l1|=n and |l2|=m, 
   you can use the following functions to extract the result. *)
 Definition fst_join (m x : nat) := (x / m)%nat.
 Definition snd_join (m x : nat) := (x mod m)%nat.

Lemma simplify_fst : forall n x y,
  (y < 2 ^ n)%nat ->
  fst_join (2 ^ n) (x * 2 ^ n + y) = x.
Proof.
  intros n x y Hy.
  unfold fst_join. 
  rewrite Nat.div_add_l. 
  rewrite Nat.div_small by assumption. 
  lia. 
  apply Nat.pow_nonzero.
  lia.
Qed.

Lemma simplify_snd : forall n x y,
  (y < 2 ^ n)%nat ->
  snd_join (2 ^ n) (x * 2 ^ n + y) = y.
Proof.
  intros n x y Hy.
  unfold snd_join. 
  rewrite Nat.add_comm.
  rewrite Nat.mod_add.
  apply Nat.mod_small. 
  assumption.
  apply Nat.pow_nonzero.
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

Lemma length_join' : forall x l1 l2 m,
  (forall k, (k < x)%nat -> length (l2 k) = m) ->
  (length (join' l1 l2 x) = x * m)%nat.
Proof.
  induction x; intros.
  - reflexivity.
  - simpl. rewrite app_length. rewrite IHx with (m := m).
    rewrite length_scale. rewrite H. lia. lia.
    intros. apply H. lia.
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

Lemma pr_outcome_sum_firstn : forall n l f, 
  (n < length l)%nat ->
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

(* If the probability of f1 in distr1(=l1) is r1 and the probability of 
   f2 in distr2(=l2) is r2, then the probability of f1&f2 in (join l1 l2)
   is r1 * r2. *)
Local Transparent firstn.
Lemma pr_outcome_sum_join_geq : forall l1 l2 f1 f2 r1 r2 n,
  distribution l1 ->
  (0 <= r2)%R ->
  pr_outcome_sum l1 f1 >= r1 ->
  (forall i, (i < length l1)%nat ->
        length (l2 i) = (2 ^ n)%nat /\
        pr_outcome_sum (l2 i) (f2 i) >= r2) -> (* note: r2 independent of i *)
  let f1f2 z := (let x := fst_join (2 ^ n) z in
                 let y := snd_join (2 ^ n) z in
                 f1 x && f2 x y) in
  pr_outcome_sum (join l1 l2) f1f2 >= (r1 * r2)%R.
Proof.
  intros l1 l2 f1 f2 r1 r2 n Hl1dist Hr2 Hl1 Hl2 f1f2.
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
         rewrite length_join' with (m:=(2^n)%nat).
         rewrite H in Hx.
         rewrite simplify_fst by assumption.
         rewrite simplify_snd by assumption.
         simpl.
         reflexivity.
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

Lemma scale_zero : forall l, scale 0 l = repeat 0 (length l).
Proof.
  induction l; intros.
  - reflexivity.
  - simpl. rewrite IHl.
    replace (0 * a)%R with 0 by lra.
    reflexivity.
Qed.

Lemma join'_starting_zero :  forall x l1 l2,
  join' (0 :: l1) l2 (S x) = repeat 0 (length (l2 O)) ++ join' l1 (fun i => l2 (S i)) x.
Proof.
  induction x; intros.
  - simpl. rewrite scale_zero.
    rewrite <- app_nil_end. reflexivity.
  - remember (S x) as Sx.
    simpl. rewrite IHx.
    subst. simpl.
    rewrite app_assoc. reflexivity.
Qed.

Lemma join_starting_zero : forall l1 l2,
  join (0 :: l1) l2 = repeat 0 (length (l2 O)) ++ join l1 (fun i => l2 (S i)).
Proof.
  intros. unfold join.
  rewrite <- join'_starting_zero. reflexivity.
Qed.

Local Opaque scale.
Lemma fst_join_uniform : forall (x m : nat) l2 rnd,
  (1 < x)%nat ->
  0 <= rnd < 1 ->
  (forall k, (k < x)%nat -> length (l2 k) = m) ->
  (forall k, (k < x)%nat -> distribution (l2 k)) ->
  (0 < m)%nat ->
  (1 <= fst_join m (sample (join (uniform 1 x) l2) rnd) < x)%nat.
Proof.
  intros. destruct x. lia. destruct x. lia.
  remember (repeat (1 / INR (S (S x) - 1))%R (S (S x) - 1)) as unm.
  assert ((join (uniform 1 (S (S x))) l2) = (repeat 0%R (length (l2 O)) ++ join unm (fun i : nat => l2 (S i)))).
  { unfold uniform. rewrite <- Hequnm.
    simpl. rewrite join_starting_zero. reflexivity.
  }
  assert (m <= (sample (join (uniform 1 (S (S x))) l2) rnd))%nat.
  { rewrite H4. rewrite H1 by lia. apply sample_repeat_lb. easy. }
  assert ((sample (join (uniform 1 (S (S x))) l2) rnd) < (S (S x)) * m)%nat.
  { replace ((S (S x)) * m)%nat with (length (join (uniform 1 (S (S x))) l2)).
    apply sample_ub_lt.
    assert (distribution (join (uniform 1 (S (S x))) l2)).
    { apply distribution_join. apply distribution_uniform. lia.
      intros. apply H2. rewrite length_uniform in H6; lia.  
    }
    destruct H6. rewrite H7. assumption.
    unfold join. rewrite length_join' with (m := m). rewrite length_uniform; lia.
    rewrite length_uniform by lia. apply H1. 
  }
  unfold fst_join. split.
  apply Nat.div_le_lower_bound; lia.
  apply Nat.div_lt_upper_bound; lia.
Qed.


(* ============================= *)
(**   Repeat independent runs   **)
(* ============================= *)

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
    (forall rnd rnds, Ps (rnd :: rnds) <-> Ps rnds /\ P rnd) ->
    pr_Ps Ps (S i) (r1 * r2).

Lemma pr_Ps_same :
  forall i Ps1 Ps2 r,
    (forall rnds, Ps1 rnds <-> Ps2 rnds) ->
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
    intros. rewrite <- H, H5, <- H. 
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
    simpl in H0. destruct (body rnd) eqn:E; try easy.
    simpl. destruct (body rnd) eqn:E; try easy.
Qed.

