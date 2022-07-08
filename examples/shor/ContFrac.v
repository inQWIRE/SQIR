Require Import Psatz ZArith Znumtheory Reals QuantumLib.Prelim.
(* ============================== *)
(* = Continued Fraction Results = *)
(* ============================== *)

Local Open Scope nat_scope.
Local Coercion Z.of_nat : nat >-> BinNums.Z.
Local Coercion INR : nat >-> R.

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
  | S n' => if a =? 0
           then b :: modseq n' 0 0
           else b :: modseq n' (b mod a) a
  end.

Lemma modseq_generate :
  forall i n m a b,
    i < n ->
    i < m ->
    nth i (modseq n a b) 0 = nth i (modseq m a b) 0.
Proof.
  intro i. induction i; intros.
  - destruct n. lia. destruct m. lia. simpl.
    bdestruct (a =? 0); reflexivity.
  - destruct n. lia. destruct m. lia. simpl.
    bdestruct (a =? 0). 
    simpl. apply IHi; lia.
    simpl. apply IHi; lia.
Qed.

Definition nthmodseq n a b := nth n (modseq (S n) a b) 0.

Lemma nthmodseq_mod :
  forall n a b,
    0 < a < b ->
    nthmodseq (S n) a b = nthmodseq n (b mod a) a.
Proof.
  intros. unfold nthmodseq. simpl. bdestructΩ (a =? 0).
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

Lemma nthmodseq_0_0 :
  forall n, nthmodseq n 0 0 = 0.
Proof.
  intros. induction n. easy.
  unfold nthmodseq. simpl. apply IHn.
Qed.

Lemma nthmodseq_Sn0a :
  forall n a, nthmodseq (S n) 0 a = 0.
Proof.
  intros n a.
  induction n; unfold nthmodseq. 
  simpl. reflexivity.
  unfold nthmodseq in IHn.
  simpl in *. 
  apply IHn.
Qed.

Fixpoint cfexp n a b :=
  match n with
  | O => []
  | S n => if a =? 0
          then 0 :: cfexp n 0 0
          else (b / a) :: cfexp n (b mod a) a
  end.

(*
Compute (cfexp 7 5 8).
*)

Definition nthcfexp n a b := nth n (cfexp (S n) a b) 0.

Lemma nthcfexp_mod :
  forall n a b,
    0 < a < b ->
    nthcfexp (S n) a b = nthcfexp n (b mod a) a.
Proof.
  induction n; intros; unfold nthcfexp; simpl; bdestructΩ (a =? 0).
Qed.

Lemma nthcfexp_n0a :
  forall n a, nthcfexp n 0 a = 0.
Proof.
  intros n a.
  induction n; unfold nthcfexp. 
  simpl. reflexivity.
  unfold nthcfexp in IHn.
  simpl in *. 
  apply IHn.
Qed.

Lemma nthcfexp_neq_0_nthmodseq :
  forall n a b,
    a < b ->
    nthcfexp n a b <> 0 ->
    nthmodseq (S n) a b <> 0.
Proof.
  induction n; intros. 
  unfold nthcfexp in H0. simpl in H0.
  unfold nthmodseq. simpl.
  bdestruct (a =? 0). simpl in H0. lia.
  bdestruct (b mod a =? 0); simpl; assumption.
  bdestruct (a =? 0).
  subst. rewrite nthcfexp_n0a in H0. lia.
  rewrite nthmodseq_mod by lia.
  apply IHn.
  apply Nat.mod_upper_bound. assumption.
  rewrite nthcfexp_mod in H0 by lia. assumption.
Qed.

Lemma nthcfexp_neq_0_nthmodseq' :
  forall n a b,
    a < b ->
    nthcfexp n a b <> 0 ->
    nthmodseq n a b <> 0.
Proof.
  induction n; intros. unfold nthmodseq. simpl. 
  bdestructΩ (a =? 0).
  bdestruct (a =? 0). rewrite H1 in H0. rewrite nthcfexp_n0a in H0. lia.
  rewrite nthmodseq_mod by lia. apply IHn.
  apply Nat.mod_upper_bound. assumption.
  rewrite nthcfexp_mod in H0 by lia. assumption.
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

Lemma CF_alt_invariant :
  forall n a b,
    a < b ->
    let (p, q) := CF_alt (cfexp n a b) (nthmodseq (S n) a b) (nthmodseq n a b) in
    a * q = b * p.
Proof.
  induction n; intros.
  simpl. unfold nthmodseq. simpl. 
  bdestruct (a =? 0); simpl. nia.
  destruct (b mod a =? 0); simpl; lia.
  bdestruct (a =? 0). subst. simpl.  
  rewrite nthmodseq_Sn0a. lia. 
  simpl. 
  bdestruct (a =? 0). subst. simpl.
  rewrite nthmodseq_Sn0a. lia. 
  simpl.
  destruct (b / a) eqn:E.
  rewrite Nat.div_small_iff in E by assumption. lia.
  assert (b mod a < a).
  { specialize (Nat.mod_upper_bound b a) as G.
    apply G. lia.
  }
  apply IHn in H2.
  rewrite nthmodseq_mod by lia.
  rewrite (nthmodseq_mod _ a) by lia.
  destruct (CF_alt (cfexp n (b mod a) a) (nthmodseq (S n) (b mod a) a) (nthmodseq n (b mod a) a)) eqn:Ecf.
  rewrite <- E.
  replace (a * (b / a * n2 + n1)) with ((a * (b / a) + b mod a) * n2) by nia. 
  rewrite <- Nat.div_mod by lia. reflexivity.
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
  simpl. 
  bdestruct (a =? 0).
  simpl in H0. lia.
  apply Classical_Prop.and_not_or. split. easy.
  apply IHn. intros. assert (S i < S n) by lia. 
  apply H in H3. unfold nthcfexp in H3. simpl in H3.
  bdestruct (a =? 0). lia.
  simpl in H3. apply H3.
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
  bdestructΩ (a =? 0).
  destruct (b / a) eqn:Ebda. 
  assert (G: 0 < a <= b) by lia. specialize (Nat.div_str_pos b a G) as G'. lia. simpl. nia.
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
  bdestructΩ (a =? 0).
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
  induction n; intros. easy. 
  remember (S (S n)) as l. simpl. rewrite IHn by lia. destruct l. reflexivity.
  destruct l. easy.
  rewrite nthcfexp_n0a. simpl. reflexivity.
Qed.

Lemma CFq_SSn0a :
  forall n a,
    0 < a ->
    CFq (S (S n)) 0 a = 1.
Proof.
  induction n; intros. reflexivity. 
  remember (S (S n)) as l. simpl. rewrite IHn by lia. destruct l. reflexivity.
  destruct l. reflexivity.
  rewrite nthcfexp_n0a. simpl. reflexivity.
Qed.

Lemma CFq0a_upper_bound :
  forall m n b,
    n <= m ->
    0 < b ->
    CFq n 0 b <= b.
Proof.
  induction m; intros. assert (n = 0) by lia. rewrite H1. simpl. lia.
  bdestruct (n <=? m). apply IHm; assumption.
  assert (n = S m) by lia. subst. simpl.
  destruct m. lia.
  rewrite nthcfexp_n0a.
  rewrite Nat.eqb_refl.
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
  destruct m. reflexivity.
  rewrite nthcfexp_n0a.
  rewrite Nat.eqb_refl.
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
  simpl. bdestructΩ (a =? 0). rewrite H0.
  destruct (b / a) eqn:Ebda. assert (G: 0 < a <= b) by lia. specialize (Nat.div_str_pos b a G) as G'. lia. rewrite <- Ebda. clear Ebda n0.
  rewrite HeqCFpt, HeqCFqt. clear CFpt CFqt HeqCFpt HeqCFqt.

  apply pair_surject.
  - rewrite CFp_mod with (m := S n) (a := a) by lia. easy.
  - rewrite CFq_mod with (m := S n) (a := a) by lia. nia.
Qed.

Lemma modseq_length :
  forall n a b,
    length (modseq n a b) = n.
Proof.
  induction n; intros. easy. simpl. 
  bdestruct (a =? 0); simpl; rewrite IHn; reflexivity.
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
  induction x; intros. 
  destruct n. reflexivity.
  simpl in H0. destruct (a =? 0); simpl in H0; lia.
  bdestruct (n <=? S (S x)). apply nth_modseq_overflow; easy.
  rewrite modseq_generate with (m := (S (S (S x)))) by lia.
  rewrite modseq_generate with (m := (S (S (S x)))) in H0 by lia.
  remember (S (S x)) as x'.
  simpl in H0.
  bdestruct (a =? 0). subst.
  replace (nth (S (S x)) (modseq (S (S (S x))) 0 b) 0) with (nthmodseq (S (S x)) 0 b) by reflexivity.
  rewrite nthmodseq_Sn0a. reflexivity.
  simpl in H0.
  apply IHx in H0.
  rewrite Heqx' at 1.
  simpl.
  bdestructΩ (a =? 0).
  apply Nat.mod_upper_bound. assumption.
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
  induction n; intros.
  unfold nthmodseq. simpl.
  destruct (a =? 0). simpl. lia.
  destruct (b mod a =? 0); simpl; lia.
  bdestruct (a =? 0). subst.
  rewrite 2 nthmodseq_Sn0a. lia.
  rewrite 2 nthmodseq_mod by lia.
  apply IHn.
  apply Nat.mod_upper_bound. assumption.
Qed.

Lemma nthmodseq_neq_0_nthcfexp :
  forall n a b,
    a < b ->
    nthmodseq (S n) a b <> 0 ->
    nthcfexp n a b <> 0.
Proof.
  induction n; intros. 
  unfold nthmodseq in H0.
  unfold nthcfexp.
  simpl in *.
  bdestruct (a =? 0).
  simpl in H0. lia.
  simpl.
  intro contra.
  rewrite Nat.div_small_iff in contra; lia.
  unfold nthcfexp in *.
  remember (S n) as n'.
  simpl.
  bdestruct (a =? 0).
  rewrite H1 in H0.
  rewrite nthmodseq_Sn0a in H0. lia.
  subst n'.
  simpl.
  apply IHn.
  apply Nat.mod_upper_bound. assumption.
  rewrite nthmodseq_mod in H0 by lia.
  assumption.
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
  rewrite IHx. simpl. destruct n. simpl in H1.
  destruct (a =? 0); simpl in H1; lia.
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
  rewrite IHx. simpl. destruct n. simpl in H1. 
  destruct (a =? 0); simpl in H1; lia.
  specialize (nthmodseq_0_nthcfexp n a b H H1) as G.
  rewrite G. simpl. easy.
Qed.

Lemma nth_modseq_inc :
  forall n a b, a < b ->
  nthmodseq (S n) a b <> 0 ->
  nthmodseq (S (S n)) a b = nthmodseq n a b mod nthmodseq (S n) a b.
Proof.
  induction n; intros.
  unfold nthmodseq in *.
  simpl in *. 
  destruct (a =? 0); simpl in *.
  lia.
  bdestruct (b mod a =? 0); simpl in *.
  lia. 
  destruct (a mod (b mod a) =? 0); reflexivity.
  bdestruct (a =? 0). subst.
  rewrite nthmodseq_Sn0a in H0. lia.
  rewrite nthmodseq_mod in H0 by lia.
  apply IHn in H0.
  rewrite nthmodseq_mod by lia.
  rewrite 2 (nthmodseq_mod _ a b) by lia.
  assumption.
  apply Nat.mod_upper_bound.
  assumption.
Qed.

Lemma nthcfexp_nthmodseq_eq :
  forall n a b, a < b ->
  nthmodseq (S n) a b <> 0 ->
  nthcfexp n a b = nthmodseq n a b / nthmodseq (S n) a b.
Proof.
  induction n; intros. 
  unfold nthcfexp, nthmodseq in *.
  simpl in *. 
  bdestruct (a =? 0); simpl in *.
  lia.
  destruct (b mod a =? 0); reflexivity.
  bdestruct (a =? 0). subst.
  rewrite nthmodseq_Sn0a in H0. lia.
  rewrite nthmodseq_mod in H0 by lia.
  apply IHn in H0.
  rewrite 2 nthmodseq_mod by lia.
  rewrite nthcfexp_mod by lia.
  assumption.
  apply Nat.mod_upper_bound.
  assumption.
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
  clear IHx.
  bdestruct (a =? 0).
  subst. rewrite nthmodseq_Sn0a in H0. lia.
  rewrite <- nth_modseq_inc by assumption.
  assert (CFp (S (S n)) a b = nthmodseq n a b / nthmodseq (S n) a b * CFp (S n) a b + CFp n a b).
  { rewrite <- nthcfexp_nthmodseq_eq by lia. 
    simpl. apply nthmodseq_neq_0_nthcfexp in H0. 2: lia. 
    apply Nat.eqb_neq in H0. rewrite H0. reflexivity.
  } 
  rewrite H2.
  assert (CFq (S (S n)) a b = nthmodseq n a b / nthmodseq (S n) a b * CFq (S n) a b + CFq n a b).
  { rewrite <- nthcfexp_nthmodseq_eq by lia. 
    simpl. apply nthmodseq_neq_0_nthcfexp in H0. 2: lia. 
    apply Nat.eqb_neq in H0. rewrite H0. reflexivity.
  } 
  rewrite H3.
  reflexivity.
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
  simpl. 
  bdestruct (a =? 0). subst. lia.
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
    destruct i. easy. rewrite nthcfexp_n0a. reflexivity.
  - rename a into a'. remember (S a') as a.
    assert (Ga: a <> 0) by lia. assert (Ga': a =? 0 = false) by (apply Nat.eqb_neq; apply Ga).
    assert (Gmod: b mod a < a < m) by (specialize (Nat.mod_upper_bound b a Ga) as G; lia).
    apply IHm in Gmod. destruct Gmod as [n [Hn [Hi [Hii Hiii]]]].
    exists (S n). split. lia. split. rewrite CFp_mod with (m := n) by lia. rewrite CFq_mod with (m := n) by lia.
    rewrite Nat.mul_add_distr_r. rewrite Hi.
    replace (b / a * CFq n (b mod a) a * a + CFq n (b mod a) a * (b mod a)) with ((a * (b / a) + b mod a) * CFq n (b mod a) a) by lia. rewrite <- Nat.div_mod by easy. lia.
    split. intros. destruct i. unfold nthcfexp. simpl.
    destruct (b / a) eqn:Ebda. assert (G: 0 < a <= b) by lia. specialize (Nat.div_str_pos b a G) as G'. lia. destruct (a =? 0); simpl. easy. lia.
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
    + exists 2. split. lia. split. lia. split. simpl. unfold nthcfexp. simpl. rewrite H2. 
      bdestruct (a =? 0); simpl; reflexivity.
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
      intros. bdestruct (i =? 1). rewrite H5. simpl. unfold nthcfexp. simpl. rewrite Ebda. 
      bdestruct (a =? 0); simpl; lia.
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

Lemma even_or_odd :
  forall n : nat, exists k : nat, n = 2 * k \/ n = S (2 * k).
Proof.
  induction n. exists 0. lia.
  destruct IHn. destruct H.
  exists x. lia. exists (S x). lia.
Qed.

Lemma CF_finite_bound :
  forall n a b,
    a < b ->
    (forall i, S i < n -> nthcfexp i a b <> 0) ->
    n <= 2 * (Nat.log2 b + 1).
Proof.
  intros. destruct (even_or_odd n) as [k [Hn | Hn]].
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
  { destruct n. unfold nthmodseq. simpl. destruct (a =? 0)%nat; simpl; lra.
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
  { destruct n. unfold nthmodseq. simpl. 
    destruct (a =? 0)%nat; simpl. lra.
    destruct (b mod a =? 0)%nat; simpl; lra.
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

Lemma Rdiv_pos_compat :
  forall x y : R, 0 <= x -> 0 < y -> 0 <= x / y.
Proof.
  intros. unfold Rdiv. apply Rinv_0_lt_compat in H0. nra.
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
  assert (0 <= a / b) by (apply Rdiv_pos_compat; lra). lra.
  
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
    apply Rdiv_pos_compat. apply pos_INR. easy.
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
      assert (Hq' : q <> O) by lia.
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
    assert (Hil : forall x : nat, (S x < i)%nat -> nthcfexp x a b <> O) by (intros; apply Hl; lia).
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
  unfold nthmodseq in G. simpl in G. 
  bdestruct (a =? 0)%nat.
  simpl in G.
  subst a. rewrite G.
  simpl. replace (n + 1)%nat with (S n) by lia. assumption.
  simpl in G.
  bdestruct (b mod a =? 0)%nat.
  simpl in G.
  rewrite G.
  simpl. replace (n + 1)%nat with (S n) by lia. assumption.
  simpl in G.
  rewrite G.
  simpl. replace (n + 1)%nat with (S n) by lia. assumption.
Qed.
