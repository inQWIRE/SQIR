Require Import Reals Psatz ZArith Znumtheory Btauto Interval.Tactic euler.Asympt.
Require Export Utilities.

Local Coercion INR : nat >-> R.
Local Coercion Z.of_nat : nat >-> BinNums.Z.

(* ====================== *)
(* =   sum_f_R0 facts   = *)
(* ====================== *)

Lemma rsum_swap_order :
  forall (m n : nat) (f : nat -> nat -> R),
    sum_f_R0 (fun j => sum_f_R0 (fun i => f j i) m) n = sum_f_R0 (fun i => sum_f_R0 (fun j => f j i) n) m.
Proof.
  intros. induction n; try easy.
  simpl. rewrite IHn. rewrite <- sum_plus. reflexivity.
Qed.

Lemma find_decidable :
    forall (m t : nat) (g : nat -> nat),
    (exists i, i <= m /\ g i = t)%nat \/ (forall i, i <= m -> g i <> t)%nat.
Proof.
  induction m; intros.
  - destruct (dec_eq_nat (g 0%nat) t).
    + left. exists 0%nat. split; easy.
    + right. intros. replace i with 0%nat by lia. easy.
  - destruct (IHm t g).
    + left. destruct H. exists x. destruct H. split; lia.
    + destruct (dec_eq_nat (g (S m)) t).
      -- left. exists (S m). lia.
      -- right. intros. inversion H1. lia. apply H. lia.
Qed.

Lemma rsum_unique :
    forall (n : nat) (f : nat -> R) (r : R),
    (exists (i : nat), i <= n /\ f i = r /\ (forall (j : nat), j <= n -> j <> i -> f j = 0)) ->
    sum_f_R0 f n = r.
Proof.
  intros.
  destruct H as (? & ? & ? & ?).
  induction n. simpl. apply INR_le in H. inversion H. subst. easy.
  simpl. bdestruct (S n =? x).
  - subst. replace (sum_f_R0 f n) with 0. lra.
    symmetry. apply sum_eq_R0. intros. apply H1. apply le_INR. constructor. easy. lia.
  - apply INR_le in H. inversion H. lia. subst. replace (f (S n)) with 0.
    rewrite IHn. lra. apply le_INR. easy. intros. apply H1; auto. apply Rle_trans with n; auto.
    apply le_INR. lia. symmetry. apply H1; auto. apply Rle_refl.
Qed.

Theorem rsum_subset :
  forall (m n : nat) (f : nat -> R)  (g : nat -> nat),
    m < n -> (forall (i : nat), 0 <= f i) -> (forall i, i <= m -> g i <= n)%nat ->
    (forall i j, i <= m -> j <= m -> g i = g j -> i = j)%nat ->
    sum_f_R0 (fun i => f (g i)) m <= sum_f_R0 f n.
Proof.
  intros.
  set (h := (fun (i : nat) => sum_f_R0 (fun (j : nat) => if i =? g j then f (g j) else 0) m)).
  assert (forall (i : nat), i <= n -> h i <= f i).
  { intros. unfold h. simpl.
    destruct (find_decidable m i g).
    - destruct H4 as (i0 & H4 & H5).
      replace (sum_f_R0 (fun j : nat => if i =? g j then f (g j) else 0) m) with (f i). lra.
      symmetry. apply rsum_unique. exists i0. split.
      + apply le_INR. easy.
      + split. subst.  rewrite Nat.eqb_refl. easy.
        intros. assert (i <> g j). unfold not. intros. subst. apply H2 in H8. apply H7. easy.
        easy. apply INR_le. easy.
      + replace (i  =? g j) with false. easy. symmetry. apply eqb_neq. easy.
    - replace (sum_f_R0 (fun j : nat => if i =? g j then f (g j) else 0) m) with 0. easy.
      symmetry. apply sum_eq_R0. intros. apply H4 in H5. rewrite eqb_neq. easy. lia.
  }
  assert (sum_f_R0 h n <= sum_f_R0 f n).
  { apply sum_Rle. intros. apply H3. apply le_INR. easy. }
  apply Rle_trans with (sum_f_R0 h n); auto.
  unfold h. rewrite rsum_swap_order.
  replace (sum_f_R0 (fun i : nat => f (g i)) m) with 
  (sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat => if j =? g i then f (g i) else 0) n) m).
  apply Rle_refl. apply sum_eq. intros.
  apply rsum_unique. exists (g i). split.
  - apply le_INR. auto. split.
  - rewrite Nat.eqb_refl. easy.
  - intros. rewrite eqb_neq; easy.
Qed.


(* ============================= *)
(* =   Number theory results   = *)
(* ============================= *)

Local Close Scope R_scope.
Local Open Scope Z_scope.

(*
   exteuc a b = (n, m) :
   a * n + b * m = gcd a b
*)
Fixpoint exteuc (a b : nat) :=
  match a with
  | O => (0, 1)
  | S a' => let (p, q) := exteuc (b mod (S a')) (S a') in
           (q - (b / a) * p, p)
  end.

Lemma exteuc_correct :
  forall (t a b : nat),
    (a < t)%nat ->
    let (n, m) := exteuc a b in
    a * n + b * m = Nat.gcd a b.
Proof.
  Local Opaque Nat.modulo Nat.div Z.mul.
  induction t; intros. lia.
  bdestruct (a <? t)%nat. apply IHt. lia.
  assert (a = t) by lia.
  destruct a. simpl. lia.
  simpl. rename a into a'. remember (S a') as a.
  replace (Z.pos (Pos.of_succ_nat a')) with (Z.of_nat a) by lia.
  assert (b mod a < a)%nat by (apply Nat.mod_upper_bound; lia).
  assert (b mod a < t)%nat by lia.
  specialize (IHt (b mod a)%nat a H3).
  destruct (exteuc (b mod a) a) as (p, q) eqn:E.
  rewrite mod_Zmod in IHt by lia. rewrite Zmod_eq_full in IHt by lia.
  nia.
Qed.

Local Close Scope Z_scope.
Local Open Scope nat_scope.

Definition modinv (a N : nat) := let (n, m) := exteuc a N in Z.to_nat (n mod N)%Z.

Lemma modinv_correct :
  forall a N,
    0 < N ->
    a * (modinv a N) mod N = (Nat.gcd a N) mod N.
Proof.
  intros. unfold modinv. 
  assert (a < S a) by lia.
  specialize (exteuc_correct (S a) a N H0) as G.
  destruct (exteuc a N) as (n, m) eqn:E.
  assert (((a * n + N * m) mod N)%Z = Nat.gcd a N mod N).
  { rewrite G. rewrite mod_Zmod by lia. easy.
  }
  rewrite <- Zplus_mod_idemp_r in H1. replace (N * m)%Z with (m * N)%Z in H1 by lia.
  rewrite Z_mod_mult in H1. rewrite Z.add_0_r in H1.
  rewrite <- Zmult_mod_idemp_r in H1.
  replace (n mod N)%Z with (Z.of_nat (Z.to_nat (n mod N)%Z)) in H1.
  2:{ rewrite Z2Nat.id. easy.
      assert (0 < N)%Z by lia.
      specialize (Z.mod_pos_bound n N H2) as T.
      lia.
  }
  rewrite <- Nat2Z.inj_mul in H1.
  rewrite <- mod_Zmod in H1 by lia. 
  apply Nat2Z.inj_iff. easy.
Qed.

Lemma modinv_upper_bound :
  forall a N,
    0 < N ->
    modinv a N < N.
Proof.
  intros. unfold modinv. destruct (exteuc a N).
  pattern N at 2. replace N with (Z.to_nat (Z.of_nat N)) by (rewrite Nat2Z.id; easy).
  assert (0 <= z mod N < N)%Z by (apply Z_mod_lt; lia). 
  apply Z2Nat.inj_lt; lia.
Qed.

(* r is the order of a modulo p *)
Definition Order (a r N : nat) :=
  0 < r /\
  a^r mod N = 1 /\
  (forall r' : nat, (0 < r' /\ a^r' mod N = 1) -> r' >= r).

Lemma pow_mod :
  forall a b n : nat,
    a^b mod n = (a mod n)^b mod n.
Proof.
  intros. induction b. easy.
  bdestruct (n =? 0). subst. easy.
  simpl. rewrite Nat.mul_mod by easy. rewrite IHb. rewrite Nat.mul_mod_idemp_r by easy.
  easy.
Qed.

Lemma Order_N_lb :
  forall a r N,
    Order a r N ->
    1 < N.
Proof.
  intros. 
  destruct (0 <? N)%nat eqn:E.
  - destruct (1 <? N)%nat eqn:S.
    + apply Nat.ltb_lt in S; easy.
    + apply Nat.ltb_ge in S. destruct H as [_ [? _]].
      apply Nat.ltb_lt in E. replace N with 1%nat in H by lia. simpl in H. discriminate H.
  - apply Nat.ltb_ge in E. assert (N=0) by lia. destruct H as [_ [? _]]. rewrite H0 in H. Local Transparent Nat.modulo. simpl in H. lia.
Qed.

Lemma Order_a_nonzero :
  forall a r N,
    Order a r N ->
    0 < a.
Proof.
  intros. assert (HN := H). apply Order_N_lb in HN.
  destruct (0 <? a)%nat eqn:E.
  - apply Nat.ltb_lt in E; easy.
  - apply Nat.ltb_ge in E. assert (a=0) by lia. destruct H as [? [? _]]. rewrite H0 in H1. rewrite Nat.pow_0_l in H1. rewrite Nat.mod_0_l in H1 by lia. lia. lia.
Qed.

Lemma Order_a_inv_ex :
  forall a r N,
    Order a r N ->
    exists a_inv,
      (a * a_inv) mod N = 1.
Proof.
  intros. exists (a^(pred r))%nat. destruct H as [? [? _]].
  assert (a * a ^ Init.Nat.pred r = a^1 * a^(Init.Nat.pred r))%nat. rewrite Nat.pow_1_r; easy. rewrite H1.
  rewrite <- Nat.pow_add_r. rewrite Nat.succ_pred; lia.
Qed.

Lemma natmul1 :
  forall a b,
    b <> 1 ->
    ~(a * b = 1).
Proof.
  intros. intro. destruct a; destruct b; try lia.
  destruct b. lia. assert (S a >= 1) by lia. assert (S (S b) >= 2) by lia.
  assert (S a * S (S b) >= 2) by nia. lia.
Qed.

Lemma Order_rel_prime :
  forall a r N,
    Order a r N ->
    Nat.gcd a N = 1.
Proof.
  intros. destruct (Order_a_inv_ex _ _ _ H) as [ainv G].
  specialize (Nat.gcd_divide a N) as [[a' Ha] [N' HN]].
  remember (Nat.gcd a N) as g. bdestruct (g =? 1). easy.
  rewrite Ha, HN in G. replace (a' * g * ainv) with (a' * ainv * g) in G by lia.
  rewrite Nat.mul_mod_distr_r in G. specialize (natmul1 ((a' * ainv) mod N') g H0) as T. easy.
  apply Order_N_lb in H. lia.
  apply Order_N_lb in H. lia.
Qed.

Lemma Order_modinv_correct :
  forall a r N,
    Order a r N ->
    (a * (modinv a N)) mod N = 1.
Proof.
  intros. specialize (Order_rel_prime _ _ _ H) as G.
  apply Order_N_lb in H.
  rewrite modinv_correct by lia. rewrite G.
  rewrite Nat.mod_small; easy.
Qed.

Lemma inv_pow :
  forall a r N a_inv x,
    Order a r N ->
    (a * a_inv) mod N = 1 ->
    (a^x * a_inv^x) mod N = 1.
Proof.
  intros. assert (HN := H). apply Order_N_lb in HN. induction x.
  - simpl. apply Nat.mod_1_l. easy.
  - simpl. rewrite Nat.mul_assoc. rewrite (Nat.mul_shuffle0 a (a^x)%nat a_inv).
    rewrite mult_assoc_reverse with (n:=(a * a_inv)%nat). rewrite <- Nat.mul_mod_idemp_l with (a:=(a * a_inv)%nat); try lia. rewrite H0. rewrite Nat.mul_1_l. apply IHx.
Qed.

Lemma Pow_minus_aux :
  forall a r N a_inv x d,
    Order a r N ->
    (a * a_inv) mod N = 1 ->
    a^d mod N = (a^(x + d) * a_inv^x) mod N.
Proof.
  intros. replace (x + d)%nat with (d + x)%nat by lia. rewrite Nat.pow_add_r.
  assert (HN := H). apply Order_N_lb in HN.
  rewrite <- Nat.mul_assoc. rewrite <- Nat.mul_mod_idemp_r; try lia. rewrite inv_pow with (r:=r); auto. rewrite Nat.mul_1_r. easy.
Qed.

Lemma Pow_minus :
  forall a r N a_inv x1 x2,
    Order a r N ->
    x1 <= x2 ->
    (a * a_inv) mod N = 1 ->
    a^(x2-x1) mod N = (a^x2 * a_inv^x1) mod N.
Proof.
  intros. rewrite Pow_minus_aux with (r:=r) (a:=a) (x:=x1) (a_inv:=a_inv); try easy. replace (x1 + (x2 - x1))%nat with (x2 - x1 + x1)%nat by lia. rewrite Nat.sub_add; easy.
Qed.

Lemma Pow_diff :
  forall a r N x1 x2,
    Order a r N ->
    0 <= x1 < r ->
    0 <= x2 < r ->
    x1 < x2 ->
    a^x1 mod N <> a^x2 mod N.
Proof.
  intros. intro.
  assert (Ha_inv := H). apply Order_a_inv_ex in Ha_inv. destruct Ha_inv as [a_inv Ha_inv].
  assert (HN := H). apply Order_N_lb in HN.
  assert (a^(x2-x1) mod N = 1).
  rewrite Pow_minus with (r:=r) (a_inv:=a_inv); try lia; try easy.
  rewrite <- Nat.mul_mod_idemp_l; try lia.
  rewrite <- H3. rewrite Nat.mul_mod_idemp_l; try lia.
  rewrite <- Pow_minus with (r:=r); try lia; try easy.
  rewrite Nat.sub_diag. simpl. apply Nat.mod_1_l; easy.
  destruct H as [_ [_ Hminimal]].
  specialize (Hminimal (x2 - x1)%nat) as Hcounter.
  assert (0 < x2 - x1 /\ a ^ (x2 - x1) mod N = 1)%nat by lia.
  apply Hcounter in H. lia.
Qed.

Lemma Pow_diff_neq :
  forall a r N x1 x2,
    Order a r N ->
    0 <= x1 < r ->
    0 <= x2 < r ->
    x1 <> x2 ->
    a^x1 mod N <> a^x2 mod N.
Proof.
  intros. apply not_eq in H2. destruct H2.
  - apply Pow_diff with (r:=r); easy.
  - apply not_eq_sym. apply Pow_diff with (r:=r); easy.
Qed.

Lemma Pow_pos :
  forall (a r N i : nat),
    Order a r N ->
    a^i mod N > 0.
Proof.
  intros. unfold gt. destruct (Nat.lt_ge_cases 0 (a ^ i mod N)). easy.
  inversion H0.  exfalso. cut (a^r mod N = 0).
  intros. destruct H as (Ha & Hb & Hc). lia.
  assert (N <> 0).
  { assert (1 < N). { apply (Order_N_lb a r _). easy. } lia. }
  destruct (Nat.lt_ge_cases i r).
  - assert (r = (i + (r - i))%nat) by lia.
    rewrite H4. rewrite -> Nat.pow_add_r. rewrite Nat.mul_mod. rewrite H2. simpl.
    apply Nat.mod_0_l.
    easy. easy.
  - assert (r = (i - (i - r))%nat) by lia.
    rewrite H4. specialize (Order_a_inv_ex a r N H) as e. destruct e.
    rewrite (Pow_minus _ r _ x _ _); try easy; try lia.
    rewrite Nat.mul_mod. rewrite H2. simpl.
    apply Nat.mod_0_l. easy. easy.
Qed.

(* from https://gist.github.com/jorpic/bf37de156f48ea438076 *)
Lemma nex_to_forall : forall k n x : nat, forall f,
 (~exists k, k < n /\ f k = x) -> k < n -> f k <> x.
Proof.
  intros k n x f H_nex H_P H_Q. 
  apply H_nex; exists k; auto.
Qed.

(* from https://gist.github.com/jorpic/bf37de156f48ea438076 *)
Lemma exists_or_not :
  forall n x : nat, forall f : nat -> nat,
    (exists k, k < n /\ f k = x) \/ (~exists k, k < n /\ f k = x).
Proof.
  intros n x f.
  induction n.
  - right. intro H_ex.
    destruct H_ex as [k [Hk Hf]]. easy.
  - destruct IHn as [H_ex | H_nex].
    + destruct H_ex as [k [H_kn H_fk]].
      left; exists k; auto.
    + destruct (eq_nat_dec (f n) x) as [H_fn_eqx | H_fn_neq_x].
      * left; exists n; auto.
      * right. intro H_nex'.
        destruct H_nex' as [k [H_kn H_fk]].
        apply H_fn_neq_x.
        apply lt_n_Sm_le in H_kn.
        apply le_lt_or_eq in H_kn.
        destruct H_kn as [H_lt | H_eq]. 
        - contradict H_fk.
          apply (nex_to_forall k n x f H_nex H_lt).
        - rewrite <- H_eq; assumption.
Qed.

(* from https://gist.github.com/jorpic/bf37de156f48ea438076 *)
Theorem pigeonhole
    :  forall n : nat, forall f : nat -> nat, (forall i, i <= n -> f i < n)
    -> exists i j, i <= n /\ j < i /\ f i = f j.
Proof.
  induction n.
  - intros f Hf.
    specialize (Hf 0 (le_refl 0)). easy.
  - intros f Hf.
    destruct (exists_or_not (n+1) (f (n+1)%nat) f) as [H_ex_k | H_nex_k].
    + destruct H_ex_k as [k [Hk_le_Sn Hfk]].
      exists (n+1)%nat, k.
      split; [lia | split; [assumption | rewrite Hfk; reflexivity]].
    + set (g := fun x => if eq_nat_dec (f x) n then f (n+1)%nat else f x).
      assert (forall i : nat, i <= n -> g i < n).
      { intros. unfold g.
        destruct (eq_nat_dec (f i) n).
        - apply nex_to_forall with (k := i) in H_nex_k. 
          + specialize (Hf (n+1)%nat); lia.
          + lia.
        - specialize (Hf i); lia.
      }
      destruct (IHn g H) as [x H0].
      destruct H0 as [y [H1 [H2 H3]]].
      exists x, y. split; [lia | split ; [assumption | idtac]].
      (* lemma g x = g y -> f x = f y *)
      unfold g in H3.
      destruct eq_nat_dec in H3.
      { destruct eq_nat_dec in H3.
        - rewrite e; rewrite e0. reflexivity.
        - contradict H3.
          apply not_eq_sym.
          apply nex_to_forall with (n := (n+1)%nat).
          apply H_nex_k. lia.
      }
      { destruct eq_nat_dec in H3.
        - contradict H3.
          apply nex_to_forall with (n := (n+1)%nat).
          apply H_nex_k. lia.
        - assumption.
      }
Qed.

Lemma Order_r_lt_N :
  forall a r N,
    Order a r N ->
    r < N.
Proof.
  intros.
  destruct (Nat.lt_ge_cases r N). easy.
  remember (fun i => pred (a^i mod N))%nat as f.
  cut (exists i j, i <= pred r /\ j < i /\ f i = f j).
  - intros. destruct H1 as (i & j & H1 & H2 & H3).
    cut (f i <> f j). easy.
    rewrite Heqf.
    assert (forall (a b : nat), a > 0 -> b > 0 -> a <> b -> pred a <> pred b).
    { intros. lia. }
    apply H4.
    + apply (Pow_pos _ r _ _). easy.
    + apply (Pow_pos _ r _ _). easy.
    + assert (forall T (x y : T), x <> y -> y <> x) by auto.
      apply H5. apply (Pow_diff _ r _ j i); try lia. easy.
  - apply pigeonhole. intros. subst. 
    assert (forall (a b : nat), a > 0 -> b > 0 -> a < b -> pred a < pred b) by (intros; lia).
    apply H2. apply (Pow_pos _ r _ _); easy. destruct H. auto.
    cut (a^i mod N < N). lia.
    apply Nat.mod_upper_bound. 
    assert (1 < N). { apply (Order_N_lb a r _). easy. } lia.
Qed.

(* ============================================= *)
(* =   Additional lemmas on Vsum, C and Csum   = *)
(* ============================================= *)
(*
   Some of the proofs in this section should be distributed
   to the related files.
*)

Local Open Scope R_scope.
Lemma Cpow_add :
  forall (c : C) (n m : nat),
    (c ^ (n + m) = c^n * c^m)%C.
Proof.
  intros. induction n. simpl. lca.
  simpl. rewrite IHn. lca.
Qed.

Lemma Cpow_mult :
  forall (c : C) (n m : nat),
    (c ^ (n * m) = (c ^ n) ^ m)%C.
Proof.
  intros. induction m. rewrite Nat.mul_0_r. easy.
  replace (n * (S m))%nat with (n * m + n)%nat by lia. simpl. rewrite Cpow_add. rewrite IHm. lca.
Qed.

Lemma RtoC_Rsum_Csum :
  forall n (f : nat -> R),
    fst (Csum f n) = Rsum n f.
Proof.
  intros. induction n.
  - easy.
  - simpl. rewrite IHn. destruct n.
    + simpl. lra.
    + rewrite tech5. simpl. easy.
Qed.

Lemma Rsum_extend :
  forall n (f : nat -> R),
    Rsum (S n) f = f n + Rsum n f.
Proof.
  intros. destruct n; simpl; lra.
Qed.

Lemma Csum_fst_distr :
  forall n (f : nat -> C),
    fst (Csum f n) = Rsum n (fun i => fst (f i)).
Proof.
  intros. induction n.
  - easy.
  - rewrite Rsum_extend. simpl. rewrite IHn. lra.
Qed.

Lemma Rsum_geq :
  forall n (f : nat -> R) A,
    (forall (i : nat), (i < n)%nat -> f i >= A) ->
    Rsum n f >= n * A.
Proof.
  intros. induction n. simpl. lra.
  assert (Rsum n f >= n * A).
  { apply IHn. intros. apply H. lia.
  }
  rewrite Rsum_extend. replace (S n * A) with (A + n * A).
  apply Rplus_ge_compat.
  apply H; lia. assumption.
  destruct n. simpl. lra. simpl. lra.
Qed.

Lemma Rsum_geq_0 :
  forall n (f : nat -> R),
    (forall (i : nat), (i < n)%nat -> f i >= 0) ->
    Rsum n f >= 0.
Proof.
  intros. specialize (Rsum_geq n f 0 H) as G. lra.
Qed.

Lemma Rsum_nonneg_Rsum_zero :
  forall n (f : nat -> R),
    (forall (i : nat), (i < n)%nat -> f i >= 0) ->
    Rsum n f <= 0 ->
    Rsum n f = 0.
Proof.
  intros. specialize (Rsum_geq_0 n f H) as G. lra.
Qed.

Lemma Rsum_nonneg_f_zero :
  forall n (f : nat -> R),
    (forall (i : nat), (i < n)%nat -> f i >= 0) ->
    Rsum n f = 0 ->
    (forall (i : nat), (i < n)%nat -> f i = 0).
Proof.
  intros. induction n. lia.
  rewrite Rsum_extend in H0.
  assert (f n >= 0) by (apply H; lia).
  assert (forall (i : nat), (i < n)%nat -> f i >= 0) by (intros; apply H; lia).
  assert (Rsum n f <= 0) by lra.
  specialize (Rsum_nonneg_Rsum_zero n f H3 H4) as G.
  bdestruct (i =? n)%nat. rewrite G in H0. rewrite H5. lra.
  apply IHn; try assumption. lia.
Qed.

Lemma Rsum_Cmod_sqr_geq_0 :
  forall n (f : nat -> C),
    Rsum n (fun i : nat => Cmod (f i) ^ 2) >= 0.
Proof.
  intros. apply Rsum_geq_0. intros. rewrite <- Cmod_pow. specialize (Cmod_ge_0 (f i ^ 2)) as G. lra.
Qed.

Lemma Cplx_norm_zero :
  forall n (f : nat -> C),
    Rsum n (fun i => Cmod (f i) ^ 2) = 0 ->
    forall (i : nat), (i < n)%nat -> f i = 0.
Proof.
  intros n f H.
  assert (forall i : nat, (i < n)%nat -> Cmod (f i) ^ 2 = 0).
  { apply Rsum_nonneg_f_zero. 
    intros. rewrite <- Cmod_pow. specialize (Cmod_ge_0 (f i ^ 2)) as G. lra.
    apply H.
  }
  intros. apply H0 in H1. specialize (Rsqr_0_uniq (Cmod (f i))) as G. rewrite Rsqr_pow2 in G. apply G in H1. apply Cmod_eq_0. easy.
Qed.

Lemma Cmod_sqr_fst :
  forall c : C,
    Cmod c ^ 2 = fst (c^* * c)%C.
Proof.
  intros. specialize (Cmod_sqr c) as G. rewrite RtoC_pow in G. unfold RtoC in G. rewrite surjective_pairing in G. apply pair_equal_spec in G. destruct G as [G _]. easy.
Qed.

Lemma Cmod_R_geq_0 :
  forall r,
    r >= 0 ->
    Cmod r = r.
Proof.
  intros. unfold Cmod. simpl. replace (r * (r * 1) + 0 * (0 * 1)) with (r * r) by nra. apply sqrt_square. lra.
Qed.

Lemma Cconj_minus_distr :
  forall c1 c2 : C,
    ((c1 - c2)^* = c1^* - c2^* )%C.
Proof.
  intros. lca.
Qed.

Lemma Cplx_norm_decomp :
  forall n (u v : nat -> C),
    Rsum n (fun i : nat => Cmod (u i - v i) ^ 2)
    = fst (Csum (fun i : nat => (u i) * (u i)^* + (v i) * (v i)^* - (u i) * (v i)^* - (v i) * (u i)^* )%C n).
Proof.
  intros. symmetry. erewrite Rsum_eq. apply Csum_fst_distr.
  intros. rewrite Cmod_sqr_fst.
  assert (forall {A B} (f : A -> B) (x y : A), x = y -> f x = f y) by (intros; rewrite H; easy).
  apply H. lca.
Qed.

Lemma Cplx_Cauchy :
  forall n (u v : nat -> C),
    (Rsum n (fun i => Cmod (u i) ^ 2)) * (Rsum n (fun i => Cmod (v i) ^ 2)) >= Cmod (Csum (fun i => ((u i)^* * (v i))%C) n) ^ 2.
Proof.
  intros.
  destruct (total_order_T (Rsum n (fun i => Cmod (v i) ^ 2)) 0) as [H | H].
  - destruct H as [H | H].
    + specialize (Rsum_Cmod_sqr_geq_0 n v) as G. lra.
    + assert (forall i : nat, (i < n)%nat -> v i = 0).
      { intros. apply Cplx_norm_zero with (n:=n); easy.
      }
      assert (forall a b : R, a >= 0 -> b >= 0 -> a * b >= 0) by (intros; nra).
      eapply Rge_trans. apply H1; apply Rsum_Cmod_sqr_geq_0.
      rewrite Csum_0_bounded. rewrite Cmod_0. simpl. nra.
      intros. rewrite H0. lca. easy.
  - remember (Rsum n (fun i : nat => Cmod (v i) ^ 2)) as Rv2.
    remember (Rsum n (fun i : nat => Cmod (u i) ^ 2)) as Ru2.
    erewrite Rsum_eq in HeqRv2 by (intros; apply Cmod_sqr_fst).
    erewrite Rsum_eq in HeqRu2 by (intros; apply Cmod_sqr_fst).
    rewrite <- Csum_fst_distr in HeqRv2.
    rewrite <- Csum_fst_distr in HeqRu2.
    rewrite <- Cmod_Cconj.
    rewrite Csum_conj_distr.
    erewrite Csum_eq.
    2:{ apply functional_extensionality. intros. rewrite Cconj_mult_distr. rewrite Cconj_involutive. rewrite Cmult_comm. reflexivity.
    }
    remember (Csum (fun i => ((v i)^* * (u i))%C) n) as uvin.    
    remember ((RtoC (/ Rv2)) * uvin)%C as lamb.
    assert (0 < / Rv2) by (apply Rinv_0_lt_compat; easy).
    apply Rle_ge. apply Rmult_le_reg_r with (r := / Rv2); try easy. rewrite Rmult_assoc. rewrite Rinv_r by lra. rewrite Rmult_1_r. apply Rge_le. apply Rminus_ge.
    
    assert (G: Rsum n (fun i => Cmod ((u i) - lamb * (v i))%C ^ 2) >= 0) by apply Rsum_Cmod_sqr_geq_0.
    rewrite Cplx_norm_decomp in G.
    assert (T: (forall m (f1 f2 f3 f4 : nat -> C), Csum (fun i => f1 i + f2 i - f3 i - f4 i)%C m = Csum f1 m + Csum f2 m - Csum f3 m - Csum f4 m)%C).
    { intros. induction m. lca. repeat rewrite <- Csum_extend_r. rewrite IHm. lca.
    }
    assert (forall i, (u i * (u i) ^* + lamb * v i * (lamb * v i) ^* - u i * (lamb * v i) ^* - lamb * v i * (u i) ^* = (u i) ^* * (u i) + (lamb ^* * lamb) * ((v i) ^* * (v i)) - lamb ^* * ((v i) ^* * (u i)) - lamb * ((v i) ^* * (u i)) ^* )%C).
    { intros. rewrite Cconj_mult_distr.
      rewrite Cmult_comm with (x := u i).
      rewrite <- Cmult_assoc with (x := lamb). rewrite Cmult_assoc with (x := v i). rewrite Cmult_comm with (x := v i). rewrite <- Cmult_assoc with (x := lamb ^* ). rewrite Cmult_assoc with (x := lamb). rewrite Cmult_comm with (x := lamb). rewrite Cmult_comm with (x := v i).
      rewrite Cmult_assoc with (x := u i). rewrite Cmult_comm with (x := u i). rewrite Cmult_comm with (x := (v i) ^* ) (y := u i). rewrite Cmult_assoc with (x := lamb ^* ).
      rewrite Cmult_comm with (x := u i) (y := (v i) ^* ). rewrite Cconj_mult_distr. rewrite Cconj_involutive. rewrite Cmult_assoc with (x := lamb).
      easy.
    }
    erewrite Csum_eq in G by (apply functional_extensionality; apply H1).
    rewrite T in G.
    erewrite <- Csum_mult_l with (c := (lamb ^* * lamb)%C) in G.
    erewrite <- Csum_mult_l with (c := lamb ^* ) in G.
    erewrite <- Csum_mult_l with (c := lamb) in G.
    rewrite <- Csum_conj_distr in G.
    rewrite <- Hequvin in G.
    assert (Tfst: forall c1 c2 c3 c4 : C, fst (c1 + c2 - c3 - c4)%C = fst c1 + fst c2 - fst c3 - fst c4).
    { intros. unfold Cminus, Cplus. simpl. lra.
    }
    rewrite Tfst in G.
    rewrite <- HeqRu2 in G.
    assert (Trcoef: forall c1 c2 : C, fst (c1 ^* * c1 * c2)%C = Cmod c1 ^2 * fst c2).
    { intros. rewrite <- Cmod_sqr. unfold Cmult. simpl. nra.
    }
    rewrite Trcoef in G.
    rewrite <- HeqRv2 in G.

    assert (Hsub1: Cmod lamb ^ 2 * Rv2 = Cmod uvin ^ 2 * / Rv2).
    { rewrite Heqlamb. rewrite Cmod_mult. rewrite Rmult_comm with (r2 := Rv2). rewrite Cmod_R_geq_0 by lra. replace ((/ Rv2 * Cmod uvin) ^ 2) with (/ Rv2 * Cmod uvin ^ 2 * / Rv2). repeat rewrite <- Rmult_assoc. rewrite Rinv_r by lra. lra.
      simpl. nra.
    }
    rewrite Hsub1 in G.
    assert (Hsub2: fst (lamb ^* * uvin)%C = Cmod uvin ^ 2 * / Rv2).
    { rewrite Heqlamb. rewrite Cconj_mult_distr.
      replace (fst ((/ Rv2)%R ^* * uvin ^* * uvin)%C) with (fst (uvin ^* * uvin)%C * (/Rv2)) by (simpl; nra).
      rewrite Cmod_sqr_fst. easy.
    }
    rewrite Hsub2 in G.
    assert (Hsub3: fst (lamb * uvin^* )%C = Cmod uvin ^ 2 * / Rv2).
    { rewrite <- Cconj_involutive with (c := (lamb * uvin ^* )%C). rewrite Cconj_mult_distr. rewrite Cconj_involutive.
      assert (Tfstconj : forall c : C, fst (c ^* ) = fst c) by (intros; unfold Cconj; easy).
      rewrite Tfstconj. apply Hsub2.
    }
    rewrite Hsub3 in G.
    lra.
Qed.


(* ==================================== *)
(* = Euler's totient function rebuild = *)
(* ==================================== *)

Local Open Scope nat_scope.

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
Definition ϕ (n : nat) := Rsum n (fun x => if rel_prime_dec x n then 1 else 0).

Lemma ϕ_φ_aux :
  forall l (n : nat),
    (n > 1)%nat ->
    Rsum (S l) (fun x : nat => if rel_prime_dec x n then 1 else 0) =
    length (filter (fun d : nat => Nat.gcd n d =? 1) (List.seq 1 l)).
Proof.
  induction l; intros. simpl.
  specialize (not_rel_prime_0_n _ H) as G.
  destruct (rel_prime_dec 0 n); easy.
  rewrite Rsum_extend. rewrite IHl by easy. rewrite seq_extend. rewrite Misc.filter_app. rewrite app_length.
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
    Rsum (S n) (fun x => if rel_prime_dec x n then 1 else 0) = Rsum n (fun x => if rel_prime_dec x n then 1 else 0).
Proof.
  intros. rewrite Rsum_extend. specialize (not_rel_prime_n_n _ H) as G.
  destruct (rel_prime_dec n n). easy. lra.
Qed.

Lemma ϕ_φ_equal :
  forall n, (n > 1)%nat -> ϕ n = φ n.
Proof.
  intros. unfold ϕ. unfold φ. unfold coprimes.
  rewrite <- ϕ_iter_inc by easy. apply ϕ_φ_aux. easy.
Qed.
  
(* There exists a better bound by [1979 Hardy & Wright, Thm 328] *)
Lemma ϕ_n_over_n_lowerbound :
  exists β, 
    β>0 /\
    forall (n : nat),
      (2 <= n)%nat ->
      (ϕ n) / n >= β / (Nat.log2 n ^ 4).
Proof.
  destruct (φ_lower_bound) as [β [G T]]. exists β. split. easy.
  intros. rewrite ϕ_φ_equal by lia. apply G. easy.
Qed.

(* ============================== *)
(* = Continued Fraction Results = *)
(* ============================== *)


Local Open Scope nat_scope.

(* Continued fraction algorithm. Calc p_n and q_n, which is the continued fraction expansion of a / b for n terms. *)
Fixpoint CF_ite (n a b p1 q1 p2 q2 : nat) : nat * nat :=
  match n with
  | O => (p1, q1)
  | S n => if a =? 0 then (p1, q1)
          else let c := (b / a) in
               CF_ite n (b mod a) a (c*p1+p2) (c*q1+q2) p1 q1
  end.

(* Set up the initial parameters. *)
Definition ContinuedFraction (step a b : nat) : nat * nat := CF_ite step a b 0 1 1 0.

(* Because (a, b) decreases exactly the same as the Euclidean's algorithm, the step bound is the same. "+1" for the initial step shift. *)
Definition CF_bound b := 2 * (Nat.log2 b + 1).

Local Close Scope nat_scope.
Local Open Scope R_scope.

Lemma Rabs_center :
  forall x y z d1 d2,
    Rabs (x - y) < d1 ->
    Rabs (x - z) < d2 ->
    Rabs (y - z) < d1 + d2.
Proof.
  intros. 
  rewrite Rabs_minus_sym in H0.
  apply Rabs_def2 in H. apply Rabs_def2 in H0.
  apply Rabs_def1; lra.
Qed.

Lemma Rabs_split :
  forall x y z,
    Rabs (y - z) <= Rabs (x - y) + Rabs (x - z).
Proof.
  intros. replace (y - z) with ((y - x) + (x - z)) by lra.
  specialize (Rabs_triang (y - x) (x - z)) as G.
  rewrite Rabs_minus_sym with (x := y) in G.
  apply G.
Qed.

Lemma Rabs_Z_lt_1 :
  forall z,
    Rabs (IZR z) < 1 ->
    (z = 0)%Z.
Proof.
  intros. rewrite <- abs_IZR in H. apply lt_IZR in H. lia.
Qed.

Lemma ClosestFracUnique_aux :
  forall (p1 q1 p2 q2 N : nat),
    (0 < q1 <= N)%nat ->
    (0 < q2 <= N)%nat ->
    Rabs (p1 / q1 - p2 / q2) < / N^2 ->
    p1 / q1 = p2 / q2.
Proof.
  intros p1 q1 p2 q2 N H H1 H0. destruct H as [H00 H01]. destruct H1 as [H10 H11].
  assert (H: (0 < N)%nat) by lia. assert (H2 := H). assert (H3 := H).
  apply lt_INR in H. simpl in H. apply lt_INR in H00. simpl in H00. apply lt_INR in H10. simpl in H10.
  apply le_INR in H01. apply le_INR in H11.
  replace (p1 / q1 - p2 / q2) with (IZR (p1 * q2 - p2 * q1)%Z / (q1 * q2)) in H0.
  2:{ rewrite minus_IZR. do 2 rewrite mult_IZR. repeat rewrite <- INR_IZR_INZ. field. lra.
  }
  assert (forall a b, b <> 0 -> Rabs (a / b) = Rabs a / Rabs b).
  { intros. replace (a / b) with (a * /b) by lra. rewrite Rabs_mult. rewrite Rabs_Rinv; easy.
  }
  assert (0 < q1 * q2) by (apply Rmult_lt_0_compat; lra).
  rewrite H1 in H0 by lra.
  assert (Rabs (q1 * q2) = q1 * q2).
  { apply Rabs_pos_eq. apply Rmult_le_pos; lra.
  }
  rewrite H5 in H0. unfold Rdiv in H0. apply Rmult_lt_compat_r with (r:=q1*q2) in H0; try assumption.
  rewrite Rmult_assoc in H0. rewrite Rinv_l in H0 by lra. rewrite Rmult_1_r in H0.
  assert (/ N ^ 2 * (q1 * q2) <= 1).
  { apply Rmult_le_reg_l with (r:=N^2). simpl. rewrite Rmult_1_r. apply Rmult_lt_0_compat; easy.
    rewrite <- Rmult_assoc. rewrite Rinv_r. rewrite Rmult_1_r. rewrite Rmult_1_l. simpl. rewrite Rmult_1_r. apply Rmult_le_compat; lra.
    simpl. rewrite Rmult_1_r. apply Rmult_integral_contrapositive_currified; lra.
  }
  specialize (Rlt_le_trans _ _ _ H0 H6) as H7.
  apply Rabs_Z_lt_1 in H7.
  assert (p1 * q2 = p2 * q1).
  { repeat rewrite INR_IZR_INZ. repeat rewrite <- mult_IZR. replace (p1 * q2)%Z with (p2 * q1)%Z by lia. easy.
  }
  apply Rmult_eq_reg_r with (r:=q1 * q2); try lra.
  replace (p1 / q1 * (q1 * q2)) with (p1 * q2 * (/ q1 * q1)) by lra. rewrite Rinv_l by lra.
  replace (p2 / q2 * (q1 * q2)) with (p2 * q1 * (/ q2 * q2)) by lra. rewrite Rinv_l by lra.
  rewrite H8. easy.
Qed.

Lemma ClosestFracUnique_aux' :
  forall (p1 q1 p2 q2 : nat),
    (0 < q1)%nat ->
    (0 < q2)%nat ->
    Rabs (p1 / q1 - p2 / q2) < / q1 * / q2 ->
    p1 / q1 = p2 / q2.
Proof.
  intros p1 q1 p2 q2 H0 H1 H2. apply lt_INR in H0. simpl in H0. apply lt_INR in H1. simpl in H1.
  replace (p1 / q1 - p2 / q2) with (IZR (p1 * q2 - p2 * q1)%Z / (q1 * q2)) in H2.
  2:{ rewrite minus_IZR. do 2 rewrite mult_IZR. repeat rewrite <- INR_IZR_INZ. field. lra.
  }
  assert (forall a b, b <> 0 -> Rabs (a / b) = Rabs a / Rabs b).
  { intros. replace (a / b) with (a * /b) by lra. rewrite Rabs_mult. rewrite Rabs_Rinv; easy.
  }
  assert (0 < q1 * q2) by (apply Rmult_lt_0_compat; lra).
  rewrite H in H2 by lra.
  assert (Rabs (q1 * q2) = q1 * q2).
  { apply Rabs_pos_eq. apply Rmult_le_pos; lra.
  }
  rewrite H4 in H2. unfold Rdiv in H2. apply Rmult_lt_compat_r with (r:=q1*q2) in H2; try easy.
  rewrite Rmult_assoc in H2. rewrite Rinv_l in H2 by lra.
  replace (/ q1 * / q2 * (q1 * q2)) with ((/ q1 * q1) * (/ q2 * q2)) in H2 by lra.
  do 2 rewrite <- Rinv_l_sym in H2 by lra. do 2 rewrite Rmult_1_r in H2.
  apply Rabs_Z_lt_1 in H2.
  assert (p1 * q2 = p2 * q1).
  { repeat rewrite INR_IZR_INZ. repeat rewrite <- mult_IZR. replace (p1 * q2)%Z with (p2 * q1)%Z by lia. easy.
  }
  apply Rmult_eq_reg_r with (r:=q1 * q2); try lra.
  replace (p1 / q1 * (q1 * q2)) with (p1 * q2 * (/ q1 * q1)) by lra. rewrite Rinv_l by lra.
  replace (p2 / q2 * (q1 * q2)) with (p2 * q1 * (/ q2 * q2)) by lra. rewrite Rinv_l by lra.
  rewrite H5. easy.
Qed.

Lemma ClosestFracUnique_CF :
  forall (p1 q1 p2 q2 : nat),
    (0 < q1 <= q2)%nat ->
    Rabs (p1 / q1 - p2 / q2) < / q1 * / q2 ->
    (p1 * q2 = p2 * q1)%nat.
Proof.
  intros. 
  assert (0 < q1)%nat by lia. assert (0 < q2)%nat by lia.
  specialize (ClosestFracUnique_aux' p1 q1 p2 q2 H1 H2 H0) as G.
  apply lt_INR in H1. apply lt_INR in H2. simpl in H1, H2.
  unfold Rdiv in G.
  apply Rmult_eq_compat_r with (r := q1) in G.
  apply Rmult_eq_compat_r with (r := q2) in G.
  replace (p1 * / q1 * q1 * q2) with ((/ q1 * q1) * p1 * q2) in G by lra.
  replace (p2 * / q2 * q1 * q2) with ((/ q2 * q2) * p2 * q1) in G by lra.
  do 2 rewrite <- Rinv_l_sym in G by lra. do 2 rewrite Rmult_1_l in G.
  do 2 rewrite <- mult_INR in G.
  apply INR_eq in G. easy.
Qed.

Lemma ClosestFracUnique_CF' :
  forall (p1 q1 p2 q2 : nat),
    (0 < q1 <= q2)%nat ->
    Rabs (p1 / q1 - p2 / q2) < / q2^2 ->
    (p1 * q2 = p2 * q1)%nat.
Proof.
  intros. assert (0 < q2 <= q2)%nat by lia.
  specialize (ClosestFracUnique_aux p1 q1 p2 q2 q2 H H1 H0) as G.
  destruct H as [H00 H01]. destruct H1 as [H10 H11].
  apply lt_INR in H00. simpl in H00. apply lt_INR in H10. simpl in H10.
  apply le_INR in H01. apply le_INR in H11.
  unfold Rdiv in G.
  apply Rmult_eq_compat_r with (r := q1) in G.
  apply Rmult_eq_compat_r with (r := q2) in G.
  replace (p1 * / q1 * q1 * q2) with ((/ q1 * q1) * p1 * q2) in G by lra.
  replace (p2 * / q2 * q1 * q2) with ((/ q2 * q2) * p2 * q1) in G by lra.
  do 2 rewrite <- Rinv_l_sym in G by lra. do 2 rewrite Rmult_1_l in G.
  do 2 rewrite <- mult_INR in G.
  apply INR_eq in G. easy.
Qed.

Lemma ClosestFracUnique :
  forall (α : R) (p1 q1 p2 q2 N : nat),
    (0 < N)%nat ->
    (0 < q1 <= N)%nat ->
    (0 < q2 <= N)%nat ->
    Rabs (α - p1 / q1) < / (2 * N^2) ->
    Rabs (α - p2 / q2) < / (2 * N^2) ->
    p1 / q1 = p2 / q2.
Proof.
  intros. apply lt_INR in H. simpl in H.
  assert (Rabs (p1 / q1 - p2 / q2) < / N^2).
  { replace (/ N^2) with (/ (2 * N^2) + / (2 * N^2)) by (field; lra).
    apply Rabs_center with (x := α); easy.
  }
  apply ClosestFracUnique_aux with (N := N); easy.
Qed.

Local Close Scope R_scope.
Local Open Scope nat_scope.

Lemma Inc_Seq_Search :
  forall l n (f : nat -> nat) x,
    l <= n ->
    f l <= x ->
    x < f n ->
    (forall i, l <= i < n -> f i < f (S i)) ->
    (exists i, l <= i < n /\ f i <= x < f (S i)).
Proof.
  intros. induction n.
  - assert (l = 0) by lia. rewrite H3 in H0. lia.
  - bdestruct (x <? f n).
    + bdestruct (l <=? n).
      * assert (forall i : nat, l <= i < n -> f i < f (S i)) by (intros; apply H2; lia).
        destruct (IHn H4 H3 H5) as [i [Hl Hr]].
        exists i. split; lia.
      * assert (l = S n) by lia. subst. lia.
    + exists n.
      bdestruct (l <=? n). split; lia.
      assert (l = S n) by lia. subst. lia.
Qed.

Fixpoint modseq (n a b : nat) : list nat:=
  match n with
  | O => []
  | S n' => b :: modseq n' (b mod a) a
  end.

Lemma modseq_generate :
  forall i n m a b,
    i < n ->
    i < m ->
    nth i (modseq n a b) 0 = nth i (modseq m a b) 0.
Proof.
  intro i. induction i; intros.
  - destruct n. lia. destruct m. lia. easy.
  - destruct n. lia. destruct m. lia. simpl.
    destruct a. apply IHi; lia.
    apply IHi; lia.
Qed.

Definition nthmodseq n a b := nth n (modseq (S n) a b) 0.

Lemma nthmodseq_mod :
  forall n a b,
    a < b ->
    nthmodseq (S n) a b = nthmodseq n (b mod a) a.
Proof.
  intros. unfold nthmodseq. reflexivity.
Qed.

Lemma modseq_bound :
  forall m a b,
    a < b < m ->
    exists n,
      nthmodseq n a b <> 0 /\
      nthmodseq (S n) a b = 0.
Proof.
  intro m. induction m; intros. lia.
  bdestruct (b <? m). apply IHm; lia.
  assert (b = m) by lia.
  destruct a.
  - exists 0. split; unfold nthmodseq; simpl; lia.
  - assert (b mod (S a) < (S a) < m).
    { specialize (Nat.mod_upper_bound b (S a)) as G.
      assert (GT: S a <> 0) by lia. apply G in GT. lia.
    }
    apply IHm in H2. destruct H2 as [n0 H2].
    exists (S n0). apply H2. 
Qed.

Lemma modseq_pre :
  forall m a b,
    a < b < m ->
    exists n,
      (forall i, i < n -> nthmodseq i a b > nthmodseq (S i) a b) /\
      (forall i, i >= n -> nthmodseq i a b = 0).
Proof.
  intro m. induction m; intros. lia.
  bdestruct (b <? m). apply IHm; lia. assert (b = m) by lia. clear H0.
  destruct a.
  - exists 1. split; intros; unfold nthmodseq. assert (i = 0) by lia. simpl. rewrite H2. lia.
    simpl. induction i. lia. destruct i. simpl. lia. assert (S i >= 1) by lia. apply IHi in H2. simpl. apply H2.
  - rename a into a'. remember (S a') as a. remember (b mod a) as c.
    assert (c < a < m).
    { specialize (Nat.mod_upper_bound b a) as G.
      assert (GT: a <> 0) by lia. apply G in GT. lia.
    }
    apply IHm in H0. destruct H0 as [n [Hl Hr]].
    exists (S n). split. intros. destruct i. unfold nthmodseq. simpl. lia.
    do 2 rewrite nthmodseq_mod by lia. rewrite <- Heqc. apply Hl. lia.
    intros. destruct i. lia. rewrite nthmodseq_mod by lia. rewrite <- Heqc. apply Hr. lia.
Qed.

Lemma modseq_finite :
  forall a b,
    a < b ->
    exists n,
      (forall i, i < n -> nthmodseq i a b <> 0) /\
      (forall i, i >= n -> nthmodseq i a b = 0).
Proof.
  intros. specialize (modseq_pre (S b) a b) as G.
  assert (a < b < S b) by lia. apply G in H0. destruct H0 as [n [H1 H2]].
  exists n. split. intros. apply H1 in H0. lia. apply H2.
Qed.

Lemma nthmodseq_0_0 :
  forall n, nthmodseq n 0 0 = 0.
Proof.
  intros. induction n. easy.
  unfold nthmodseq. simpl. apply IHn.
Qed.


Fixpoint cfexp n a b :=
  match n with
  | O => []
  | S n => (b / a) :: cfexp n (b mod a) a
  end.

(*
Compute (cfexp 7 5 8).
*)

Definition nthcfexp n a b := nth n (cfexp (S n) a b) 0.

Lemma nthcfexp_mod :
  forall n a b,
    a < b ->
    nthcfexp (S n) a b = nthcfexp n (b mod a) a.
Proof.
  induction n; intros; easy.
Qed.

Lemma nthcfexp_0_0 :
  forall n, nthcfexp n 0 0 = 0.
Proof.
  induction n; intros. easy. unfold nthcfexp. simpl. apply IHn.
Qed.

Lemma nthcfexp_Sn0a :
  forall n a, nthcfexp (S n) 0 a = 0.
Proof.
  induction n; intros. easy. unfold nthcfexp. simpl. apply IHn with (a := a).
Qed.

Lemma nthcfexp_neq_0_nthmodseq :
  forall n a b,
    a < b ->
    nthcfexp n a b <> 0 ->
    nthmodseq (S n) a b <> 0.
Proof.
  induction n; intros. unfold nthcfexp in H0. simpl in H0.
  unfold nthmodseq. simpl.
  bdestruct (a =? 0). rewrite H1 in H0. Local Transparent Nat.div. simpl in H0. lia. lia.
  bdestruct (a =? 0). rewrite H1 in H0. rewrite nthcfexp_Sn0a in H0. lia.
  assert (a > 0) by lia.
  rewrite nthmodseq_mod by lia. apply IHn.
  apply Nat.mod_upper_bound. easy. easy.
Qed.

Lemma nthcfexp_neq_0_nthmodseq' :
  forall n a b,
    a < b ->
    nthcfexp n a b <> 0 ->
    nthmodseq n a b <> 0.
Proof.
  induction n; intros. unfold nthmodseq. simpl. lia. 
  bdestruct (a =? 0). rewrite H1 in H0. rewrite nthcfexp_Sn0a in H0. lia.
  assert (a > 0) by lia.
  rewrite nthmodseq_mod by lia. apply IHn.
  apply Nat.mod_upper_bound. easy. easy.
Qed.

Fixpoint CF_alt (cf : list nat) (al bl : nat) :=
  match cf with
  | [] => (al, bl)
  | a :: cf => match a with
             | O => (al, bl)
             | _ => let (p, q) := CF_alt cf al bl in
                   (q, a * q + p)
             end
  end.

(*
Compute (cfexp 5 2 3).

Compute (CF_alt (cfexp 3 2 3) 0 1).
*)

Lemma CF_alt_invariant :
  forall n a b,
    a < b ->
    let (p, q) := CF_alt (cfexp n a b) (nthmodseq (S n) a b) (nthmodseq n a b) in
    a * q = b * p.
Proof.
  intro n. induction n; intros.
  simpl. unfold nthmodseq. simpl. nia.
  rewrite nthmodseq_mod by lia. rewrite nthmodseq_mod with (a := a) by lia.
  simpl. destruct a. simpl. unfold nthmodseq. simpl. destruct n. lia. specialize (nthmodseq_0_0 n) as G. unfold nthmodseq in G. rewrite G. lia.
  rename a into a'. remember (S a') as a.
  destruct (b / a) eqn:E. assert (G: 0 < a <= b) by lia. specialize (Nat.div_str_pos b a G) as G'. lia. rewrite <- E.
  assert (b mod a < a).
  { specialize (Nat.mod_upper_bound b a) as G.
    apply G. lia.
  }
  apply IHn in H0.
  destruct (CF_alt (cfexp n (b mod a) a) (nthmodseq (S n) (b mod a) a) (nthmodseq n (b mod a) a)) eqn:Ecf.
  replace (a * (b / a * n2 + n1)) with ((a * (b / a) + b mod a) * n2) by nia. rewrite <- Nat.div_mod by lia. easy.
Qed.

Lemma rel_prime_linear :
  forall p q a,
    rel_prime p q ->
    rel_prime p (a * p + q).
Proof.
  intros. apply rel_prime_bezout in H. inversion H.
  apply bezout_rel_prime. apply Bezout_intro with (u := (u - a * v)%Z) (v := v). rewrite <- H0. nia.
Qed.

Lemma CF_alt_coprime :
  forall l (al bl : nat),
    rel_prime al bl ->
    ~ In 0 l ->
    let (p, q) := CF_alt l al bl in
    rel_prime p q.
Proof.
  induction l; intros. easy.
  destruct a. simpl in H0. lia.
  simpl in H0. apply Classical_Prop.not_or_and in H0. destruct H0 as [_ H0].
  specialize (IHl al bl H H0).
  simpl. destruct (CF_alt l al bl) as (p, q).
  replace (Z.of_nat (q + a * q + p)%nat) with ((a + 1) * q + p)%Z by lia.
  apply rel_prime_linear. apply rel_prime_sym. easy.
Qed.

Lemma nthcfexp_neq_0_In :
  forall n a b,
    (forall i, i < n -> nthcfexp i a b <> 0) ->
    ~ In 0 (cfexp n a b).
Proof.
  induction n; intros. simpl. easy.
  assert (nthcfexp 0 a b <> 0) by (apply H; lia).
  unfold nthcfexp in H0. simpl in H0.
  simpl. apply Classical_Prop.and_not_or. split. easy.
  apply IHn. intros. assert (S i < S n) by lia. apply H in H2. unfold nthcfexp in H2. simpl in H2. apply H2.
Qed.

Lemma CF_alt_cfexp_coprime :
  forall (n a b al bl : nat),
    rel_prime al bl ->
    (forall i, i < n -> nthcfexp i a b <> 0) ->
    let (p, q) := CF_alt (cfexp n a b) al bl in
    rel_prime p q.
Proof.
  intros. specialize (nthcfexp_neq_0_In n a b H0) as G.
  apply CF_alt_coprime; easy.
Qed.

Fixpoint CFq (n a b : nat) : nat :=
  match n with
  | O => 0
  | S O => 1
  | S (S n2 as n1) => if (nthcfexp n2 a b =? 0) then CFq n1 a b
                     else (nthcfexp n2 a b) * (CFq n1 a b) + CFq n2 a b
  end.

Fixpoint CFp (n a b : nat) : nat :=
  match n with
  | O => 1
  | S O => 0
  | S (S n2 as n1) => if (nthcfexp n2 a b =? 0) then CFp n1 a b
                     else (nthcfexp n2 a b) * (CFp n1 a b) + CFp n2 a b
  end.

Lemma CFp_mod :
  forall m n a b,
    n <= m ->
    0 < a < b ->
    CFp (S n) a b = CFq n (b mod a) a.
Proof.
  induction m; intros. assert (n = 0) by lia. subst. easy.
  destruct n. easy.
  simpl. rewrite <- IHm by lia. destruct n. unfold nthcfexp. simpl.
  destruct (b / a) eqn:Ebda. assert (G: 0 < a <= b) by lia. specialize (Nat.div_str_pos b a G) as G'. lia. simpl. nia.
  rewrite nthcfexp_mod by lia.
  rewrite <- IHm by lia. easy.
Qed.

Lemma CFq_mod :
  forall m n a b,
    n <= m ->
    0 < a < b ->
    CFq (S n) a b = b / a * CFq n (b mod a) a + CFp n (b mod a) a.
Proof.
  induction m; intros. assert (n = 0) by lia. subst. simpl. nia.
  destruct n. simpl. nia.
  simpl. destruct n. unfold nthcfexp. simpl.
  destruct (b / a) eqn:Ebda. assert (G: 0 < a <= b) by lia. specialize (Nat.div_str_pos b a G) as G'. lia. simpl. nia.
  rewrite nthcfexp_mod by lia.
  bdestruct (nthcfexp n (b mod a) a =? 0). rewrite <- IHm by lia. easy.
  replace (b / a * (nthcfexp n (b mod a) a * CFq (S n) (b mod a) a + CFq n (b mod a) a) + (nthcfexp n (b mod a) a * CFp (S n) (b mod a) a + CFp n (b mod a) a)) with (nthcfexp n (b mod a) a * (b / a * CFq (S n) (b mod a) a + CFp (S n) (b mod a) a) + (b / a * CFq n (b mod a) a + CFp n (b mod a) a)) by nia.
  do 2 rewrite <- IHm by lia. easy.
Qed.

Lemma CFp_SSn0a :
  forall n a,
    0 < a ->
    CFp (S (S n)) 0 a = 0.
Proof.
  induction n; intros. easy. remember (S (S n)) as l. simpl. rewrite IHn by lia. destruct l. lia.
  destruct l. easy. rewrite nthcfexp_mod by lia. simpl. rewrite nthcfexp_0_0. easy.
Qed.

Lemma CFq_SSn0a :
  forall n a,
    0 < a ->
    CFq (S (S n)) 0 a = 1.
Proof.
  induction n; intros. easy. remember (S (S n)) as l. simpl. rewrite IHn by lia. destruct l. lia.
  destruct l. easy. rewrite nthcfexp_mod by lia. simpl. rewrite nthcfexp_0_0. easy.
Qed.

Lemma CFq0a_upper_bound :
  forall m n b,
    n <= m ->
    0 < b ->
    CFq n 0 b <= b.
Proof.
  induction m; intros. assert (n = 0) by lia. rewrite H1. simpl. lia.
  bdestruct (n <=? m). apply IHm; easy.
  assert (n = S m) by lia. subst. simpl.
  destruct m. lia.
  destruct m. unfold nthcfexp. simpl. lia.
  rewrite nthcfexp_mod by lia. replace (b mod 0) with 0 by easy.
  rewrite nthcfexp_0_0. rewrite Nat.eqb_refl.
  apply IHm; lia.
Qed.

Lemma CFp0a_upper_bound :
  forall m n b,
    0 < n <= m ->
    0 < b ->
    CFp n 0 b = 0.
Proof.
  induction m; intros. lia.
  bdestruct (n <=? m). apply IHm; easy.
  assert (n = S m) by lia. subst. simpl.
  destruct m. easy.
  destruct m. unfold nthcfexp. simpl. easy.
  rewrite nthcfexp_mod by lia. replace (b mod 0) with 0 by easy.
  rewrite nthcfexp_0_0. rewrite Nat.eqb_refl.
  apply IHm; lia.
Qed.

Lemma pair_surject :
  forall {A B} (a1 a2 : A) (b1 b2 : B),
    a1 = a2 -> b1 = b2 -> (a1, b1) = (a2, b2).
Proof.
  intros. rewrite H, H0. easy.
Qed.

(*
Compute (cfexp 7 10 16).

Compute (let n := 5 in
         let (a, b) := (10, 16) in
         let (x, y) := (3, 6) in
         (CF_alt (cfexp n a b) x y, (x * CFp n a b + y * CFp (S n) a b, x * CFq n a b + y * CFq (S n) a b))).
*)

Lemma CF_alt_correct :
  forall n a b x,
    a < b ->
    CF_alt (cfexp n a b) 0 x = (x * CFp (S n) a b, x * CFq (S n) a b).
Proof.
  intro n. induction n; intros. simpl. apply pair_surject; lia.
  destruct a. rewrite CFp_SSn0a by lia. rewrite CFq_SSn0a by lia.
  simpl. apply pair_surject; lia.
  rename a into a'. remember (S a') as a.

  assert (b mod a < a).
  { specialize (Nat.mod_upper_bound b a) as G.
    apply G. lia.
  }
  assert (T:= H0).
  apply IHn with (x := x) in H0.
  remember (CFp (S (S n)) a b) as CFpt.
  remember (CFq (S (S n)) a b) as CFqt.
  simpl. rewrite H0.
  destruct (b / a) eqn:Ebda. assert (G: 0 < a <= b) by lia. specialize (Nat.div_str_pos b a G) as G'. lia. rewrite <- Ebda. clear Ebda n0.
  rewrite HeqCFpt, HeqCFqt. clear CFpt CFqt HeqCFpt HeqCFqt.

  apply pair_surject.
  - rewrite CFp_mod with (m := S n) (a := a) by lia. easy.
  - rewrite CFq_mod with (m := S n) (a := a) by lia. nia.
Qed.

Lemma nth_modseq_inc :
  forall n a b,
    nth (S (S n)) (modseq (S (S (S n))) a b) 0 = (nth n (modseq (S (S (S n))) a b) 0) mod (nth (S n) (modseq (S (S (S n))) a b) 0).
Proof.
  induction n; intros. easy.
  remember (S (S (S n))) as x. simpl. rewrite Heqx. rewrite Heqx in IHn. rewrite IHn. easy.
Qed.

Lemma modseq_length :
  forall n a b,
    length (modseq n a b) = n.
Proof.
  induction n; intros. easy. simpl. rewrite IHn. easy.
Qed.

Lemma nth_modseq_overflow :
  forall x n a b,
    n <= x ->
    nth x (modseq n a b) 0 = 0.
Proof.
  intros. apply nth_overflow. rewrite modseq_length. easy.
Qed.

Lemma nth_modseq_0_onestep :
  forall x n a b,
    a < b ->
    nth x (modseq n a b) 0 = 0 ->
    nth (S x) (modseq n a b) 0 = 0.
Proof.
  induction x; intros. destruct n. easy. simpl in H0. lia.
  bdestruct (n <=? S (S x)). apply nth_modseq_overflow; easy.
  rewrite modseq_generate with (m := (S (S (S x)))) by lia.
  rewrite modseq_generate with (m := (S (S (S x)))) in H0 by lia.
  rewrite nth_modseq_inc. rewrite H0. easy.
Qed.

Lemma nthmodseq_0_post :
  forall x n a b,
    nthmodseq n a b = 0 ->
    a < b ->
    nthmodseq (x + n) a b = 0.
Proof.
  induction x; intros. easy.
  apply IHx in H. 2:lia. unfold nthmodseq in H. unfold nthmodseq.
  rewrite modseq_generate with (m := (S (S x + n))) in H by lia.
  apply nth_modseq_0_onestep in H. 2:lia.
  replace (S x + n) with (S (x + n)) by lia.
  easy.
Qed.

Lemma nthcfexp_nthmodseq_eq :
  forall n a b,
    a < b ->
    nthcfexp n a b = (nthmodseq n a b) / (nthmodseq (S n) a b).
Proof.
  induction n; intros. easy.
  rewrite nthcfexp_mod by lia. do 2 rewrite nthmodseq_mod by lia.
  bdestruct (a =? 0). subst. simpl. rewrite nthcfexp_0_0. do 2 rewrite nthmodseq_0_0. simpl. easy.
  assert (b mod a < a) by (apply Nat.mod_upper_bound; easy).
  apply IHn in H1. easy.
Qed.

Lemma nthmodseq_0_nthcfexp :
  forall n a b,
    a < b ->
    nthmodseq (S n) a b = 0 ->
    nthcfexp n a b = 0.
Proof.
  intros. bdestruct (nthcfexp n a b =? 0). easy.
  apply nthcfexp_neq_0_nthmodseq in H1. 2:lia. lia.
Qed.

Lemma nthmodseq_dec :
  forall n a b,
    a < b ->
    nthmodseq n a b >= nthmodseq (S n) a b.
Proof.
  unfold nthmodseq.
  destruct n; intros. simpl. lia. rewrite nth_modseq_inc.
  rewrite modseq_generate with (n := S (S n)) (m := S (S (S n))) by lia.
  bdestruct (nth (S n) (modseq (S (S (S n))) a b) 0 =? 0). rewrite H0. simpl. lia.
  assert (forall p q, p < q -> q >= p) by (intros; lia).
  apply H1. apply Nat.mod_upper_bound. easy.
Qed.

Lemma nthmodseq_neq_0_nthcfexp :
  forall n a b,
    a < b ->
    nthmodseq (S n) a b <> 0 ->
    nthcfexp n a b <> 0.
Proof.
  induction n; intros. specialize (nthmodseq_dec 1 a b H) as G.
  unfold nthmodseq in H0, G. simpl in H0, G. unfold nthcfexp. simpl.
  assert (0 < a <= b) by lia. specialize (Nat.div_str_pos b a H1) as T. lia.
  rewrite nthmodseq_mod in H0 by lia.
  bdestruct (a =? 0). rewrite H1 in H0. simpl in H0. rewrite nthmodseq_0_0 in H0. lia.
  specialize (nthmodseq_dec (S n) a b H) as G. rewrite nthcfexp_mod by lia. 
  assert (b mod a < a) by (apply Nat.mod_upper_bound; easy).
  specialize (IHn (b mod a) a H2 H0). easy.
Qed.

Lemma nthmodseq_0_CFp :
  forall x n a b,
    a < b ->
    nthmodseq n a b = 0 ->
    CFp (x + n) a b = CFp n a b.
Proof.
  induction x; intros. easy. unfold nthmodseq in H0.
  assert (H1 := H0).
  rewrite modseq_generate with (m := (S (S n))) in H0 by lia.
  apply nth_modseq_0_onestep in H0. 2:lia.
  specialize (IHx (S n) a b H H0).
  replace (S x + n) with (x + S n) by lia.
  rewrite IHx. simpl. destruct n. simpl in H1. lia.
  specialize (nthmodseq_0_nthcfexp n a b H H1) as G.
  rewrite G. simpl. easy.
Qed.

Lemma nthmodseq_0_CFq :
  forall x n a b,
    a < b ->
    nthmodseq n a b = 0 ->
    CFq (x + n) a b = CFq n a b.
Proof.
  induction x; intros. easy. unfold nthmodseq in H0.
  assert (H1 := H0).
  rewrite modseq_generate with (m := (S (S n))) in H0 by lia.
  apply nth_modseq_0_onestep in H0. 2:lia.
  specialize (IHx (S n) a b H H0).
  replace (S x + n) with (x + S n) by lia.
  rewrite IHx. simpl. destruct n. simpl in H1. lia.
  specialize (nthmodseq_0_nthcfexp n a b H H1) as G.
  rewrite G. simpl. easy.
Qed.

Lemma CF_ite_CFpq :
  forall x n a b,
    a < b ->
    CF_ite x (nthmodseq (S n) a b) (nthmodseq n a b) (CFp (S n) a b) (CFq (S n) a b) (CFp n a b) (CFq n a b) = (CFp (x + S n) a b, CFq (x + S n) a b).
Proof.
  induction x; intros. easy.
  unfold CF_ite. fold CF_ite.
  bdestruct (nthmodseq (S n) a b =? 0).
  rewrite nthmodseq_0_CFp, nthmodseq_0_CFq by lia. easy.
  replace (S x + S n) with (x + S (S n)) by lia.
  rewrite <- IHx by lia.
  replace (nthmodseq n a b mod nthmodseq (S n) a b) with (nthmodseq (S (S n)) a b).
  2:{ unfold nthmodseq. rewrite modseq_generate with (n := S n) (m := (S (S (S n)))) by lia.
      rewrite modseq_generate with (n := S (S n)) (m := (S (S (S n)))) by lia.
      apply nth_modseq_inc.
  }
  replace (CFp (S (S n)) a b) with (nthmodseq n a b / nthmodseq (S n) a b * CFp (S n) a b + CFp n a b).
  2:{ simpl. apply nthmodseq_neq_0_nthcfexp in H0. 2:lia. apply Nat.eqb_neq in H0. rewrite H0.
      rewrite <- nthcfexp_nthmodseq_eq by lia. easy.
  } 
  replace (CFq (S (S n)) a b) with (nthmodseq n a b / nthmodseq (S n) a b * CFq (S n) a b + CFq n a b).
  2:{ simpl. apply nthmodseq_neq_0_nthcfexp in H0. 2:lia. apply Nat.eqb_neq in H0. rewrite H0.
      rewrite <- nthcfexp_nthmodseq_eq by lia. easy.
  }
  easy.
Qed.

Lemma CF_alt_correct_full :
  forall n a b x y,
    a < b ->
    (forall i, i < n -> nthcfexp i a b <> 0) ->
    CF_alt (cfexp n a b) x y = (x * CFp n a b + y * CFp (S n) a b, x * CFq n a b + y * CFq (S n) a b).
Proof.
  induction n; intros. simpl. apply pair_surject; lia.
  destruct a. specialize (H0 0). assert (0 < S n) by lia. apply H0 in H1. unfold nthcfexp in H1. simpl in H1. lia.
  rename a into a'. remember (S a') as a.

  assert (b mod a < a).
  { specialize (Nat.mod_upper_bound b a) as G.
    apply G. lia.
  }
  assert (T:= H1).
  apply IHn with (x := x) (y := y) in H1.
  2:{ intros. assert (nthcfexp (S i) a b <> 0). apply H0. lia.
      rewrite nthcfexp_mod in H3 by lia. easy.
  }
  
  remember (x * CFp (S n) a b + y * CFp (S (S n)) a b, x * CFq (S n) a b + y * CFq (S (S n)) a b) as CFtmp.
  simpl. rewrite H1.
  destruct (b / a) eqn:Ebda. assert (G: 0 < a <= b) by lia. specialize (Nat.div_str_pos b a G) as G'. lia. rewrite <- Ebda. clear Ebda n0.
  rewrite HeqCFtmp. clear CFtmp HeqCFtmp.

  apply pair_surject.
  - do 2 rewrite CFp_mod with (m := S n) (a := a) by lia. easy.
  - do 2 rewrite CFq_mod with (m := S n) (a := a) by lia. nia.
Qed.

Lemma CF_coprime :
  forall n a b,
    a < b ->
    (forall i, S i < n -> nthcfexp i a b <> 0) ->
    rel_prime (CFp n a b) (CFq n a b).
Proof.
  intros. destruct n. simpl. apply rel_prime_1.
  assert (forall i, i < n -> nthcfexp i a b <> 0) by (intros; apply H0; lia).
  specialize (CF_alt_correct_full n a b 0 1 H H1) as G.
  replace (0 * CFp n a b + 1 * CFp (S n) a b) with (CFp (S n) a b) in G by lia.
  replace (0 * CFq n a b + 1 * CFq (S n) a b) with (CFq (S n) a b) in G by lia.
  specialize (rel_prime_1 0) as T. apply rel_prime_sym in T.
  specialize (CF_alt_cfexp_coprime n a b 0 1 T H1) as T'.
  rewrite G in T'. easy.
Qed.

Lemma CF_converge_aux :
  forall n a b,
    (a < b) ->
    (forall i, i < n -> nthcfexp i a b <> 0) ->
    a * ((nthmodseq (S n) a b) * (CFq n a b) + (nthmodseq n a b) * (CFq (S n) a b)) =
    b * ((nthmodseq (S n) a b) * (CFp n a b) + (nthmodseq n a b) * (CFp (S n) a b)).
Proof.
  intros. specialize (CF_alt_invariant n a b H) as G.
  rewrite CF_alt_correct_full in G by easy. apply G.
Qed.

Lemma CF_finite :
  forall m a b,
    a < b < m ->
    (exists n,
        n >= 1 /\
        CFp n a b * b = CFq n a b * a /\  (* a.k.a., a / b = CFp n a b / CFq n a b *)
        (forall i, S i < n -> nthcfexp i a b <> 0) /\
        (forall i, S i >= n -> nthcfexp i a b = 0)
    ).
Proof.
  induction m; intros. lia.
  bdestruct (b <? m). apply IHm; easy. assert (b = m) by lia.
  destruct a.
  - destruct b. (* b = 0 *) lia.
    exists 1. split. lia. split. easy. split. intros. lia. intros.
    destruct i. easy. rewrite nthcfexp_mod by lia. simpl. apply nthcfexp_0_0.
  - rename a into a'. remember (S a') as a.
    assert (Ga: a <> 0) by lia. assert (Ga': a =? 0 = false) by (apply eqb_neq; apply Ga).
    assert (Gmod: b mod a < a < m) by (specialize (Nat.mod_upper_bound b a Ga) as G; lia).
    apply IHm in Gmod. destruct Gmod as [n [Hn [Hi [Hii Hiii]]]].
    exists (S n). split. lia. split. rewrite CFp_mod with (m := n) by lia. rewrite CFq_mod with (m := n) by lia.
    rewrite Nat.mul_add_distr_r. rewrite Hi.
    replace (b / a * CFq n (b mod a) a * a + CFq n (b mod a) a * (b mod a)) with ((a * (b / a) + b mod a) * CFq n (b mod a) a) by lia. rewrite <- Nat.div_mod by easy. lia.
    split. intros. destruct i. unfold nthcfexp. simpl.
    destruct (b / a) eqn:Ebda. assert (G: 0 < a <= b) by lia. specialize (Nat.div_str_pos b a G) as G'. lia. lia.
    rewrite nthcfexp_mod by lia. apply Hii. lia.
    intros. destruct i. lia. rewrite nthcfexp_mod by lia. apply Hiii. lia.
Qed.

Lemma CFq_pos :
  forall n a b,
    n > 0 ->
    CFq n a b > 0.
Proof.
  intro n. induction n; intros. lia. simpl.
  destruct n. lia.
  assert (S n > 0) by lia.
  specialize (IHn a b H0). 
  bdestruct (nthcfexp n a b =? 0). apply IHn. nia.
Qed.  

Lemma CFq_strict_inc :
  forall n a b,
    a < b ->
    n >= 1 ->
    (forall i, S i < n -> nthcfexp i a b <> 0) ->
    (exists l, l <= n /\
          1 <= l <= 2 /\
          CFq l a b = 1 /\
          (forall i, l <= i < n ->
                CFq i a b < CFq (S i) a b)).
Proof.
  destruct n. intros. lia.
  induction n; intros. exists 1. split. lia. split. lia. split. simpl. lia. intros. lia.
  destruct a.
  - specialize (H1 0). assert (T : 1 < S (S n)) by lia. apply H1 in T. unfold nthcfexp in T. simpl in T. lia.
  - rename a into a'. remember (S a') as a.
    bdestruct (b / a =? 1).
    + exists 2. split. lia. split. lia. split. simpl. unfold nthcfexp. simpl. rewrite H2. simpl. easy.
      intros. bdestruct (i <? S n).
      * assert (T: forall j, S j < S n -> nthcfexp j a b <> 0).
        { intros. apply H1. lia.
        }
        assert (T': S n >= 1) by lia.
        specialize (IHn a b H T' T). destruct IHn as [l [_ [Hl2 [_ Hi]]]]. apply Hi. lia.
      * assert (i = S n) by lia. rewrite H5.
        assert (S n < S (S n)) by lia. specialize (H1 n H6). assert (nthcfexp n a b > 0) by lia. apply Nat.eqb_neq in H1. simpl. rewrite H1.
        assert (n > 0) by lia.
        specialize (CFq_pos n a b H8) as G. nia.
    + destruct (b / a) eqn:Ebda. assert (G: 0 < a <= b) by lia. specialize (Nat.div_str_pos b a G) as G'. lia. rewrite <- Ebda in H2.
      assert (b / a > 1) by lia. 
      exists 1. split. lia. split. lia. split. simpl. lia.
      intros. bdestruct (i =? 1). rewrite H5. simpl. unfold nthcfexp. simpl. rewrite Ebda. simpl. nia.
      bdestruct (i <? S n).
      * assert (T: forall j, S j < S n -> nthcfexp j a b <> 0).
        { intros. apply H1. lia.
        }
        assert (T': S n >= 1) by lia.
        specialize (IHn a b H T' T). destruct IHn as [l [_ [Hl2 [_ Hi]]]]. apply Hi. lia.
      * assert (i = S n) by lia. rewrite H7.
        assert (S n < S (S n)) by lia. specialize (H1 n H8). assert (nthcfexp n a b > 0) by lia. apply Nat.eqb_neq in H1. simpl. rewrite H1.
        assert (n > 0) by lia.
        specialize (CFq_pos n a b H10) as G. nia.
Qed.

Lemma CFq_exp_inc :
  forall n a b,
    a < b ->
    nthcfexp n a b <> 0 ->
    CFq n a b + CFq (S n) a b <= CFq (S (S n)) a b.
Proof.
  intros. simpl. assert (nthcfexp n a b >= 1) by lia. apply Nat.eqb_neq in H0. rewrite H0. nia.
Qed.

Lemma CFq_inc :
  forall x n a b,
    a < b ->
    CFq (x + n) a b >= CFq n a b.
Proof.
  induction x; intros. simpl. lia.
  destruct x. simpl. destruct n. simpl. lia.
  bdestruct (nthcfexp n a b =? 0). lia. nia.
  replace (S (S x) + n) with (S (S (x + n))) by lia.  simpl.
  bdestruct (nthcfexp (x + n) a b =? 0). apply IHx. easy.
  specialize (IHx n a b H).
  simpl in IHx. nia.
Qed.  

Lemma CFq_lower_bound :
  forall n a b,
    a < b ->
    (forall i, i < 2*n -> nthcfexp i a b <> 0) ->
    CFq ((2*n) + 1) a b >= 2^n.
Proof.
  induction n; intros. simpl. lia.
  assert (nthcfexp (S (2*n)) a b <> 0) by (apply H0; lia).
  assert (nthcfexp (2*n) a b <> 0) by (apply H0; lia).
  specialize (CFq_exp_inc (S (2*n)) a b H H1) as G1.
  specialize (CFq_exp_inc (2*n) a b H H2) as G2.
  assert (CFq (S (2*n)) a b >= 2^n).
  { replace (S (2*n)) with (2*n+1) by lia. apply IHn. easy.
    intros. apply H0. lia.
  }
  replace (2 ^ S n) with (2^n + 2^n) by (simpl; lia).
  replace (2 * S n + 1) with (S (S (S (2 * n)))) by lia.
  lia.
Qed.

Lemma CF_upper_bound :
  forall n a b,
    0 < a < b ->
    CFq n a b <= b /\
    CFp n a b <= a.
Proof.
  induction n; intros. simpl. split; lia.
  rewrite CFq_mod with (m := n) by lia.
  rewrite CFp_mod with (m := n) by lia.
  bdestruct (b mod a =? 0).
  - rewrite H0. split.
    + destruct n. simpl. nia.
      rewrite CFp0a_upper_bound with (m := S n) by lia.
      assert (CFq (S n) 0 a <= a) by (apply CFq0a_upper_bound with (m := S n); lia).
      assert (a <> 0) by lia.
      specialize (Nat.mul_div_le b a H2) as G. nia.
    + apply CFq0a_upper_bound with (m := n); lia.
  - assert (0 < b mod a < a).
    { assert (a <> 0) by lia. specialize (Nat.mod_upper_bound b a H1) as G. lia.
    }
    apply IHn in H1. destruct H1 as [H1 H2]. split.
    + remember (b / a * CFq n (b mod a) a + CFp n (b mod a) a) as tmp.
      rewrite Nat.div_mod with (x := b) (y := a) by lia.
      rewrite Heqtmp. nia.
    + easy.
Qed.

Lemma CFq_upper_bound :
  forall n a b,
    a < b ->
    CFq n a b <= b.
Proof.
  intros. destruct a. apply CFq0a_upper_bound with (m := n); lia.
  assert (0 < S a < b) by lia.
  specialize (CF_upper_bound n (S a) b H0) as G. destruct G as [G _].
  apply G.
Qed.

Lemma CF_finite_aux :
  forall n a b,
    a < b ->
    (forall i, i < 2*n -> nthcfexp i a b <> 0) ->
    n <= Nat.log2 b.
Proof.
  intros. specialize (CFq_lower_bound n a b H H0) as G.
  specialize (CFq_upper_bound (2 * n + 1) a b H) as T.
  assert (2 ^ n <= b) by lia. apply Nat.log2_le_pow2; lia.
Qed.

Lemma CF_finite_bound :
  forall n a b,
    a < b ->
    (forall i, S i < n -> nthcfexp i a b <> 0) ->
    n <= 2 * (Nat.log2 b + 1).
Proof.
  intros. destruct (Stdlib.even_or_odd n) as [k [Hn | Hn]].
  - destruct k. lia.
    assert (forall i, i < 2*k -> nthcfexp i a b <> 0).
    { intros. apply H0. nia.
    }
    specialize (CF_finite_aux k a b H H1) as G. lia.
  - assert (forall i, i < 2*k -> nthcfexp i a b <> 0).
    { intros. apply H0. nia.
    }
    specialize (CF_finite_aux k a b H H1) as G. lia.
Qed.


Local Close Scope nat_scope.
Local Open Scope Z_scope.

Fixpoint signflip n : BinNums.Z :=
  match n with
  | O => 1
  | S n => - signflip n
  end.

Lemma signflip_abs :
  forall n, Z.abs (signflip n) = 1.
Proof.
  induction n; simpl; nia.
Qed.

Lemma signflip_cancel :
  forall n, signflip n * signflip n = 1.
Proof.
  induction n; simpl; nia.
Qed.

Lemma CF_tauto :
  forall n a b,
    (a < b)%nat ->
    (forall i, i < n -> nthcfexp i a b <> 0)%nat ->
    (CFp (S n) a b) * (CFq n a b) - (CFp n a b) * (CFq (S n) a b) = signflip (S n).
Proof.
  induction n; intros. simpl. lia.
  replace (Z.of_nat (CFp (S (S n)) a b)) with (nthcfexp n a b * CFp (S n) a b + CFp n a b).
  2:{ remember (CFp (S n) a b) as tmp.
      assert (nthcfexp n a b <> 0)%nat by (apply H0; lia).
      apply Nat.eqb_neq in H1.
      simpl. rewrite H1. rewrite Nat2Z.inj_add. rewrite Nat2Z.inj_mul. rewrite Heqtmp. simpl. lia.
  } 
  replace (Z.of_nat (CFq (S (S n)) a b)) with (nthcfexp n a b * CFq (S n) a b + CFq n a b).
  2:{ remember (CFq (S n) a b) as tmp.
      assert (nthcfexp n a b <> 0)%nat by (apply H0; lia).
      apply Nat.eqb_neq in H1.
      simpl. rewrite H1. rewrite Nat2Z.inj_add. rewrite Nat2Z.inj_mul. rewrite Heqtmp. simpl. lia.
  }
  replace (signflip (S (S n))) with (-signflip (S n)) by easy.
  rewrite <- (IHn a b H) by (intros; apply H0; lia).
  nia.
Qed.

Lemma CF_converge :
  forall n a b,
    (a < b)%nat ->
    (forall i, i < n -> nthcfexp i a b <> 0)%nat ->
    (a / b * CFq (S n) a b - CFp (S n) a b = (IZR (signflip n)) * ((nthmodseq (S n) a b) / (nthmodseq (S n) a b * CFq n a b + nthmodseq n a b * CFq (S n) a b)))%R.
Proof.
  intros n a b H0 H1.
  assert (H: 1 = 1) by lia.
  specialize (CF_converge_aux n a b H0 H1) as G.
  specialize (CF_tauto n a b H0 H1) as G'.
  assert (INR b <> 0)%R by (apply not_0_INR; lia).
  assert (nthmodseq (S n) a b * CFq n a b + nthmodseq n a b * CFq (S n) a b <> 0)%R.
  { destruct n. unfold nthmodseq. simpl. lra.
    assert (nthcfexp n a b <> 0)%nat by (apply H1; lia).
    apply nthcfexp_neq_0_nthmodseq in H3. 2 : lia.
    assert ((S (S n)) > 0)%nat by lia.
    apply CFq_pos with (a := a) (b := b) in H4.
    assert (forall x y c d : nat, (0 < c)%nat -> (0 < d)%nat -> (x * y + c * d <> 0)%R).
    { intros. assert (0 < x * y + c * d)%nat by nia. apply lt_INR in H7. simpl in H7. rewrite plus_INR in H7.
      do 2 rewrite mult_INR in H7. lra.
    }
    apply H5; lia.
  }
  assert (forall a b : nat, a = b -> INR a = INR b) by (intros; subst; easy).
  apply H4 in G.
  repeat rewrite mult_INR in G.
  repeat rewrite plus_INR in G.
  repeat rewrite mult_INR in G.
  remember (nthmodseq (S n) a b * CFp n a b + nthmodseq n a b * CFp (S n) a b)%R as d1.
  remember (nthmodseq (S n) a b * CFq n a b + nthmodseq n a b * CFq (S n) a b)%R as d2.
  assert (a / b = d1 / d2)%R.
  { apply Rmult_eq_reg_r with (r := b). 2 : easy.
    replace (a / b * b)%R with (INR a).
    2:{ unfold Rdiv. replace (a * / b * b)%R with (a * (/ b * b))%R by lra. rewrite <- Rinv_l_sym by easy. lra.
    }
    apply Rmult_eq_reg_r with (r := d2). 2 : easy.
    replace (d1 / d2 * b * d2)%R with (d1 * b * (/d2 * d2))%R by lra. rewrite <- Rinv_l_sym by easy. lra.
  }
  rewrite H5.
  replace (INR (CFp (S n) a b)) with (d2 / d2 * CFp (S n) a b)%R.
  2:{ unfold Rdiv. rewrite <- Rinv_r_sym by easy. lra.
  } 
  replace (d1 / d2 * CFq (S n) a b - d2 / d2 * CFp (S n) a b)%R with ((d1 * CFq (S n) a b - d2 * CFp (S n) a b) / d2)%R by lra.
  apply Rmult_eq_reg_r with (r := d2). 2: easy.
  remember (d1 * CFq (S n) a b - d2 * CFp (S n) a b)%R as x1.
  replace (IZR (signflip n) * (nthmodseq (S n) a b / d2))%R with ((IZR (signflip n) * nthmodseq (S n) a b) / d2)%R by lra.
  remember (IZR (signflip n) * nthmodseq (S n) a b)%R as x2.
  replace (x1 / d2 * d2)%R with (x1 * (/ d2 * d2))%R by lra.
  replace (x2 / d2 * d2)%R with (x2 * (/ d2 * d2))%R by lra.
  rewrite <- Rinv_l_sym by easy. do 2 rewrite Rmult_1_r.
  rewrite Heqx1, Heqx2. clear x1 Heqx1 x2 Heqx2.
  rewrite Heqd1, Heqd2. do 2 rewrite Rmult_plus_distr_r.
  replace (nthmodseq (S n) a b * CFp n a b * CFq (S n) a b + nthmodseq n a b * CFp (S n) a b * CFq (S n) a b - (nthmodseq (S n) a b * CFq n a b * CFp (S n) a b + nthmodseq n a b * CFq (S n) a b * CFp (S n) a b))%R with (- nthmodseq (S n) a b * (CFp (S n) a b * CFq n a b - CFq (S n) a b * CFp n a b))%R by lra.
  replace (IZR (signflip n))%R with (- IZR (signflip (S n)))%R by (simpl; rewrite opp_IZR; apply Ropp_involutive).
  rewrite <- G'.
  rewrite minus_IZR. repeat rewrite mult_IZR. repeat rewrite <- INR_IZR_INZ.
  lra.
Qed.

Lemma CF_converge' :
  forall n a b,
    (0 < n)%nat ->
    (a < b)%nat ->
    (forall i, i < n -> nthcfexp i a b <> 0)%nat ->
    (a / b * CFq n a b - CFp n a b = (IZR (signflip (S n))) * ((nthmodseq n a b) / (nthmodseq (S n) a b * CFq n a b + nthmodseq n a b * CFq (S n) a b)))%R.
Proof.
  intros.
  specialize (CF_converge_aux n a b H0 H1) as G.
  specialize (CF_tauto n a b H0 H1) as G'.
  assert (INR b <> 0)%R by (apply not_0_INR; lia).
  assert (nthmodseq (S n) a b * CFq n a b + nthmodseq n a b * CFq (S n) a b <> 0)%R.
  { destruct n. unfold nthmodseq. simpl. lra.
    assert (nthcfexp n a b <> 0)%nat by (apply H1; lia).
    apply nthcfexp_neq_0_nthmodseq in H3. 2 : lia.
    assert ((S (S n)) > 0)%nat by lia.
    apply CFq_pos with (a := a) (b := b) in H4.
    assert (forall x y c d : nat, (0 < c)%nat -> (0 < d)%nat -> (x * y + c * d <> 0)%R).
    { intros. assert (0 < x * y + c * d)%nat by nia. apply lt_INR in H7. simpl in H7. rewrite plus_INR in H7.
      do 2 rewrite mult_INR in H7. lra.
    }
    apply H5; lia.
  }
  assert (forall a b : nat, a = b -> INR a = INR b) by (intros; subst; easy).
  apply H4 in G.
  repeat rewrite mult_INR in G.
  repeat rewrite plus_INR in G.
  repeat rewrite mult_INR in G.
  remember (nthmodseq (S n) a b * CFp n a b + nthmodseq n a b * CFp (S n) a b)%R as d1.
  remember (nthmodseq (S n) a b * CFq n a b + nthmodseq n a b * CFq (S n) a b)%R as d2.
  assert (a / b = d1 / d2)%R.
  { apply Rmult_eq_reg_r with (r := b). 2 : easy.
    replace (a / b * b)%R with (INR a).
    2:{ unfold Rdiv. replace (a * / b * b)%R with (a * (/ b * b))%R by lra. rewrite <- Rinv_l_sym by easy. lra.
    }
    apply Rmult_eq_reg_r with (r := d2). 2 : easy.
    replace (d1 / d2 * b * d2)%R with (d1 * b * (/d2 * d2))%R by lra. rewrite <- Rinv_l_sym by easy. lra.
  }
  rewrite H5.
  replace (INR (CFp n a b)) with (d2 / d2 * CFp n a b)%R.
  2:{ unfold Rdiv. rewrite <- Rinv_r_sym by easy. lra.
  } 
  replace (d1 / d2 * CFq n a b - d2 / d2 * CFp n a b)%R with ((d1 * CFq n a b - d2 * CFp n a b) / d2)%R by lra.
  apply Rmult_eq_reg_r with (r := d2). 2: easy.
  remember (d1 * CFq n a b - d2 * CFp n a b)%R as x1.
  replace (IZR (signflip (S n)) * (nthmodseq n a b / d2))%R with ((IZR (signflip (S n)) * nthmodseq n a b) / d2)%R by lra.
  remember (IZR (signflip (S n)) * nthmodseq n a b)%R as x2.
  replace (x1 / d2 * d2)%R with (x1 * (/ d2 * d2))%R by lra.
  replace (x2 / d2 * d2)%R with (x2 * (/ d2 * d2))%R by lra.
  rewrite <- Rinv_l_sym by easy. do 2 rewrite Rmult_1_r.
  rewrite Heqx1, Heqx2. clear x1 Heqx1 x2 Heqx2.
  rewrite Heqd1, Heqd2. do 2 rewrite Rmult_plus_distr_r.
  replace (nthmodseq (S n) a b * CFp n a b * CFq n a b + nthmodseq n a b * CFp (S n) a b * CFq n a b - (nthmodseq (S n) a b * CFq n a b * CFp n a b + nthmodseq n a b * CFq (S n) a b * CFp n a b))%R with (nthmodseq n a b * (CFp (S n) a b * CFq n a b - CFq (S n) a b * CFp n a b))%R by lra.
  rewrite <- G'.
  rewrite minus_IZR. repeat rewrite mult_IZR. repeat rewrite <- INR_IZR_INZ.
  lra.
Qed.

Lemma Z_split :
  forall z : BinNums.Z,
    z = 0 \/ z < 0 \/ z > 0.
Proof.
  intros. lia.
Qed.

Lemma linear_opp_sign :
  forall (a b x : nat) (c d : BinNums.Z),
    (x < a)%nat ->
    Z.of_nat x = a * c + b * d ->
    c = 0 \/ c * d < 0.
Proof.
  intros. destruct (Z_split c) as [G | [G | G]]. left. easy.
  right. nia. right. assert (d < 0) by nia. nia.
Qed.

Lemma Zprod_non_zero :
  forall x y, x * y < 0 -> y <> 0.
Proof.
  intros. nia.
Qed.

Local Close Scope Z_scope.
Local Open Scope R_scope.

Lemma Rprod_same_sign :
  forall a b,
    a * b >= 0 ->
    Rabs (a + b) = Rabs a + Rabs b.
Proof.
  intros.
  destruct (total_order_T a 0) as [[G | G] | G].
  - destruct (total_order_T b 0) as [[T | T] | T].
    + do 3 rewrite Rabs_left by lra. lra.
    + rewrite T. rewrite Rabs_R0. do 2 rewrite Rplus_0_r. easy.
    + nra.
  - rewrite G. rewrite Rabs_R0. do 2 rewrite Rplus_0_l. easy.
  - destruct (total_order_T b 0) as [[T | T] | T].
    + nra. 
    + rewrite T. rewrite Rabs_R0. do 2 rewrite Rplus_0_r. easy.
    + do 3 rewrite Rabs_right by lra. lra.
Qed.

Lemma Rprod_opp_sign :
  forall a b c d,
    a * c <= 0 ->
    b * d <= 0 ->
    Rabs (a * b + c * d) = (Rabs a) * (Rabs b) + (Rabs c) * (Rabs d).
Proof.
  intros.
  assert ((a * c) * (b * d) >= 0) by nra.
  rewrite Rprod_same_sign by nra.
  do 2 rewrite Rabs_mult. easy.
Qed.

Lemma CF_opp_sign :
  forall (n a b : nat),
    (a < b)%nat ->
    (forall i, i < n -> nthcfexp i a b <> 0)%nat ->
    ((a / b * CFq n a b - CFp n a b) * (a / b * CFq (S n) a b - CFp (S n) a b)) <= 0.
Proof.
  intros. destruct n. subst. simpl.
  assert (0 <= a < b).
  { split. apply pos_INR. apply lt_INR. easy.
  }
  assert (0 <= a / b) by (apply Rcomplements.Rdiv_le_0_compat; lra). lra.
  
  assert (forall i, i < n -> nthcfexp i a b <> 0)%nat by (intros; apply H0; lia).
  specialize (CF_converge n a b H H1) as G1.
  specialize (CF_converge (S n) a b H H0) as G2.
  remember (nthmodseq (S n) a b / (nthmodseq (S n) a b * CFq n a b + nthmodseq n a b * CFq (S n) a b)) as x1.
  remember (nthmodseq (S (S n)) a b / (nthmodseq (S (S n)) a b * CFq (S n) a b + nthmodseq (S n) a b * CFq (S (S n)) a b)) as x2.
  rewrite G1. rewrite G2.
  assert (forall (x y z r : nat), (x * y + z * r > 0)%nat -> 0 <= x / (x * y + z * r)).
  { intros. assert (1 <= x * y + z * r)%nat by lia. apply le_INR in H3.
    rewrite plus_INR in H3. do 2 rewrite mult_INR in H3. simpl in H3.
    assert (0 < x * y + z * r) by lra.
    apply Stdlib.Rdiv_pos_compat. apply pos_INR. easy.
  }
  assert (0 <= x1).
  { rewrite Heqx1. apply H2.
    assert (nthcfexp n a b <> 0)%nat by (apply H0; lia). apply nthcfexp_neq_0_nthmodseq' in H3. 2: lia.
    assert (CFq (S n) a b > 0)%nat by (apply CFq_pos; lia). nia.
  }
  assert (0 <= x2).
  { rewrite Heqx2. apply H2.
    assert (nthcfexp n a b <> 0)%nat by (apply H0; lia). apply nthcfexp_neq_0_nthmodseq in H4. 2: lia.
    assert (CFq (S (S n)) a b > 0)%nat by (apply CFq_pos; lia). nia.
  }
  simpl. rewrite opp_IZR.
  replace (IZR (signflip n) * x1 * (- IZR (signflip n) * x2)) with (- (IZR (signflip n) * IZR (signflip n) * x1 * x2)) by lra.
  rewrite <- mult_IZR. rewrite signflip_cancel. nra.
Qed.

Lemma CF_distance_bound :
  forall n a b p q : nat,
    (a < b)%nat ->
    (forall i, i < n -> nthcfexp i a b <> 0)%nat ->
    (CFq n a b <= q < CFq (S n) a b)%nat ->
    (q <> 0)%nat ->
    Rabs (a / b * CFq n a b - CFp n a b) <= Rabs (a / b * q - p).
Proof.
  intros.
  remember ((signflip n) * (CFp n a b * q - CFq n a b * p))%Z as x.
  remember ((signflip n) * (- CFp (S n) a b * q + CFq (S n) a b * p))%Z as y.
  assert (Hq: (Z.of_nat q = CFq (S n) a b * x + CFq n a b * y)%Z).
  { rewrite Heqx, Heqy.
    replace (CFq (S n) a b * (signflip n * (CFp n a b * q - CFq n a b * p)) + CFq n a b * (signflip n * (- CFp (S n) a b * q + CFq (S n) a b * p)))%Z with (signflip n * -(CFp (S n) a b * CFq n a b - CFp n a b * CFq (S n) a b) * q)%Z by lia.
    rewrite CF_tauto by easy. simpl. rewrite Z.opp_involutive. rewrite signflip_cancel. lia.
  }
  assert (Hp: (Z.of_nat p = CFp (S n) a b * x + CFp n a b * y)%Z).
  { rewrite Heqx, Heqy.
    replace (CFp (S n) a b * (signflip n * (CFp n a b * q - CFq n a b * p)) + CFp n a b * (signflip n * (- CFp (S n) a b * q + CFq (S n) a b * p)))%Z with (signflip n * -(CFp (S n) a b * CFq n a b - CFp n a b * CFq (S n) a b) * p)%Z by lia.
    rewrite CF_tauto by easy. simpl. rewrite Z.opp_involutive. rewrite signflip_cancel. lia.
  }
  assert (Hxy := Hq). apply linear_opp_sign in Hxy. 2:easy.
  destruct Hxy as [Hxy | Hxy].
  - assert (y <> 0)%Z by nia.
    assert (Z.abs y >= 1)%Z by lia.
    assert (Hq': (Z.of_nat q = CFq n a b * y)%Z) by nia.
    assert (Hp': (Z.of_nat p = CFp n a b * y)%Z) by nia.
    repeat rewrite INR_IZR_INZ. rewrite Hq', Hp'.
    repeat rewrite mult_IZR.
    replace (IZR a / IZR b * (IZR (CFq n a b) * IZR y) - IZR (CFp n a b) * IZR y) with ((IZR a / IZR b * IZR (CFq n a b) - IZR (CFp n a b)) * IZR y) by lra.
    rewrite Rabs_mult. rewrite Rabs_Zabs.
    apply IZR_ge in H4.
    assert (0 <= Rabs (IZR a / IZR b * IZR (CFq n a b) - IZR (CFp n a b))) by apply Rabs_pos.
    nra.
  - assert (y <> 0)%Z by (apply Zprod_non_zero with (x := x); easy).
    assert (Z.abs y >= 1)%Z by lia.
    apply IZR_ge in H4. rewrite <- Rabs_Zabs in H4.
    repeat rewrite INR_IZR_INZ. rewrite Hq, Hp.
    repeat rewrite plus_IZR. repeat rewrite mult_IZR.
    replace (IZR a / IZR b * (IZR (CFq (S n) a b) * IZR x + IZR (CFq n a b) * IZR y) - (IZR (CFp (S n) a b) * IZR x + IZR (CFp n a b) * IZR y)) with ((IZR a / IZR b * (IZR (CFq (S n) a b)) - (IZR (CFp (S n) a b))) * IZR x + (IZR a / IZR b * (IZR (CFq n a b)) - (IZR (CFp n a b))) * IZR y) by lra.
    apply IZR_lt in Hxy. rewrite mult_IZR in Hxy.
    specialize (CF_opp_sign n a b H H0) as G.
    repeat rewrite INR_IZR_INZ in G.
    rewrite Rprod_opp_sign by nra.
    assert (forall u v z r, Rabs r >= 1 -> Rabs u <= Rabs v * Rabs z + Rabs u * Rabs r).
    { intros. assert (0 <= Rabs v * Rabs z) by (rewrite <- Rabs_mult; apply Rabs_pos).
      specialize (Rabs_pos u). nra.
    }
    apply H5; easy.
Qed.

Lemma Rabs_extract :
  forall x p q : R,
    0 < q ->
    Rabs (x - p / q) = / q * Rabs (x * q - p).
Proof.
  intros. replace (x - p / q) with (/q * (x * q - p)) by (field; lra).
  rewrite Rabs_mult. apply Rinv_0_lt_compat in H. assert (0 <= /q) by lra. apply Rabs_pos_eq in H0. rewrite H0. easy.
Qed.

Lemma Legendre_rational :
  forall a b p q : nat,
    (0 < q)%nat ->
    (a < b)%nat ->
    Rabs (a / b - p / q) < 1 / (2 * q^2) ->
    rel_prime p q ->
    exists step,
      (1 <= step <= CF_bound b)%nat /\
      CFq step a b = q.
Proof.
  intros a b p q Hq Hab Hdis Hpq. assert (T: (a < b < S b)%nat) by lia. specialize (CF_finite (S b) a b T) as G.
  destruct G as [n [Hn [Heq [Hl Hr]]]].
  bdestruct (CFq n a b <=? q)%nat.
  - exists n. split. specialize (CF_finite_bound n a b Hab Hl) as Gn. unfold CF_bound. lia.
    assert (a / b = CFp n a b / CFq n a b).
    { assert (Hb: (0 < b)%nat) by lia. apply lt_INR in Hb. simpl in Hb.
      assert (Hqn' : (CFq n a b > 0)%nat) by (apply CFq_pos; lia). assert (Hqn : (0 < CFq n a b)%nat) by lia. apply lt_INR in Hqn. simpl in Hqn. clear Hqn'.
      apply Rmult_eq_reg_r with (r := b). 2:lra.
      apply Rmult_eq_reg_r with (r := CFq n a b). 2:lra.
      replace (a / b * b * CFq n a b) with ((/ b * b) * CFq n a b * a) by lra.
      replace (CFp n a b / CFq n a b * b * CFq n a b) with ((/ CFq n a b * CFq n a b) * CFp n a b * b) by lra.
      do 2 rewrite <- Rinv_l_sym by lra. do 2 rewrite Rmult_1_l. do 2 rewrite <- mult_INR.
      rewrite Heq. easy.
    } 
    rewrite H0 in Hdis.
    assert (Hdiv2: 1 / (2 * q ^ 2) < / q^2).
    { apply lt_INR in Hq. simpl in Hq.
      unfold Rdiv. rewrite Rmult_1_l. apply Rinv_lt_contravar.
      simpl. replace (q * (q * 1) * (2 * (q * (q * 1)))) with (2 * (q * q) * (q * q)) by nra.
      assert (0 < q * q) by nra. nra.
      nra.
    }
    assert (Hdis': Rabs (CFp n a b / CFq n a b - p / q) < / q ^ 2) by lra.
    assert (Hqn : (CFq n a b > 0)%nat) by (apply CFq_pos; lia).
    assert (Hqn' : (0 < CFq n a b <= q)%nat) by lia.
    specialize (ClosestFracUnique_CF' (CFp n a b) (CFq n a b) p q Hqn' Hdis') as G.
    assert (Hcfpq : rel_prime (CFp n a b) (CFq n a b)) by (apply CF_coprime; easy).
    assert (HINZ : Z.of_nat (CFp n a b) = Z.of_nat p /\ Z.of_nat (CFq n a b) = Z.of_nat q) by (apply rel_prime_cross_prod; try easy; try lia).
    destruct HINZ as [_ HINZ]. apply Nat2Z.inj_iff. easy.
  - specialize (CFq_strict_inc n a b Hab Hn Hl) as G.
    destruct G as [l [Hln [Hl2 [Hstart Hinc]]]].
    assert (Hlup: (CFq l a b <= q)%nat) by lia.
    assert (H': (q < CFq n a b)%nat) by lia.
    specialize (Inc_Seq_Search l n (fun x => CFq x a b) q Hln Hlup H' Hinc) as U.
    destruct U as [i [Hi Hcfi]].
    exists i. split. specialize (CF_finite_bound n a b Hab Hl) as Gn. unfold CF_bound. lia.
    assert (G: Rabs (CFp i a b / CFq i a b - p / q) < / CFq i a b * / q).
    { specialize (Rabs_split (a / b) (CFp i a b / CFq i a b) (p / q)) as U.
      assert (Hqn' : (CFq i a b > 0)%nat) by (apply CFq_pos; lia). assert (Hqn : (0 < CFq i a b)%nat) by lia. apply lt_INR in Hqn. simpl in Hqn. clear Hqn'.
      assert (Hqn'' : (CFq i a b > 0)%nat) by (apply CFq_pos; lia). assert (Hqn' : (1 <= CFq i a b)%nat) by lia. apply le_INR in Hqn'. simpl in Hqn'. clear Hqn''.
      rewrite Rabs_extract with (x := a / b) in U by lra.
      assert (Hil : forall x : nat, (x < i -> nthcfexp x a b <> 0)%nat) by (intros; apply Hl; lia).
      assert (Hq' : q <> 0%nat) by lia.
      specialize (CF_distance_bound i a b p q Hab Hil Hcfi Hq') as U'.
      clear Hq'. assert (Hq' : (1 <= q)%nat) by lia. apply le_INR in Hq'. simpl in Hq'.
      replace (Rabs (a / b * q - p)) with (q * (/q * Rabs (a / b * q - p))) in U' by (field; lra).
      rewrite <- Rabs_extract with (p := INR p) in U' by lra.
      specialize (Rinv_0_lt_compat (CFq i a b) Hqn) as Hqn''.
      assert (0 <= Rabs (a / b * CFq i a b - CFp i a b)) by (apply Rabs_pos).
      assert (/ CFq i a b <= q * / CFq i a b) by nra.
      assert (U1: / CFq i a b * Rabs (a / b * CFq i a b - CFp i a b) <= q / CFq i a b * Rabs (a / b - p / q)) by nra. clear H0 H1.
      replace (Rabs (a / b - p / q)) with (q * / q * Rabs (a / b - p / q)) in U by (field; lra).
      assert (Hdisnn: 0 <= Rabs (a / b - p / q)) by apply Rabs_pos.
      assert (CFq i a b <= q)%nat by lia. apply le_INR in H0.
      assert (/q <= / CFq i a b) by (apply Rinv_le_contravar; lra).
      assert (0 < /q) by (apply Rinv_0_lt_compat; lra).
      assert (0 <= q * Rabs (a / b - p / q)) by nra.
      assert (q * Rabs (a / b - p / q) * /q <= q * Rabs (a / b - p / q) * / CFq i a b ) by nra.
      assert (U2: q * / q * Rabs (a / b - p / q) <= q / CFq i a b * Rabs (a / b - p / q)) by nra. clear H0 H1 H2 H3 H4.
      assert (Ufin: Rabs (CFp i a b / CFq i a b - p / q) <= 2 * q / CFq i a b * Rabs (a / b - p / q)) by lra.
      assert (0 < 2 * q / CFq i a b) by nra.
      assert (Ufin': Rabs (CFp i a b / CFq i a b - p / q) < 2 * q / CFq i a b * (1 / (2 * q^2))) by nra. clear H0.
      replace (2 * q / CFq i a b * (1 / (2 * q ^ 2))) with (/ CFq i a b * / q) in Ufin' by (field; lra).
      easy.
    }
    assert (Hqn' : (CFq i a b > 0)%nat) by (apply CFq_pos; lia).
    assert (Hqnq : (0 < CFq i a b <= q)%nat) by lia.
    specialize (ClosestFracUnique_CF (CFp i a b) (CFq i a b) p q Hqnq G) as F.
    assert (Hil : forall x : nat, (S x < i)%nat -> nthcfexp x a b <> 0%nat) by (intros; apply Hl; lia).
    assert (Hcfpq : rel_prime (CFp i a b) (CFq i a b)) by (apply CF_coprime; easy).
    assert (HINZ : Z.of_nat (CFp i a b) = Z.of_nat p /\ Z.of_nat (CFq i a b) = Z.of_nat q) by (apply rel_prime_cross_prod; try easy; try lia).
    destruct HINZ as [_ HINZ]. apply Nat2Z.inj_iff. easy.
Qed.

Lemma Legendre_ContinuedFraction :
  forall a b p q : nat,
    (0 < q)%nat ->
    (a < b)%nat ->
    Rabs (a / b - p / q) < 1 / (2 * q^2) ->
    rel_prime p q ->
    exists step,
      (step < CF_bound b)%nat /\
      snd (ContinuedFraction step a b) = q.
Proof.
  intros. specialize (Legendre_rational a b p q H H0 H1 H2) as G.
  destruct G as [n [Ha Hb]].
  destruct n. lia.
  exists n. split. lia.
  unfold ContinuedFraction. specialize (CF_ite_CFpq n 0 a b H0) as G.
  unfold nthmodseq in G. simpl in G. rewrite G.
  simpl. replace (n + 1)%nat with (S n) by lia. easy.
Qed.

