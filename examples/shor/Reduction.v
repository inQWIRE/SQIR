Require Import Psatz ZArith Znumtheory Reals Prelim NumTheory Btauto Utilities.
Require Import euler.Asympt euler.Misc euler.Primes euler.Prod EulerTotient.

(* =================================================== *)
(* =  Reduction from Factorization to Order Finding  = *)
(* =================================================== *)

Local Open Scope nat_scope.
Local Coercion Z.of_nat : nat >-> BinNums.Z.
Local Coercion INR : nat >-> R.

Lemma sqr1_not_pm1 :
  forall x N,
    1 < N ->
    x ^ 2 mod N = 1 ->
    x mod N <> 1 ->
    x mod N <> N - 1 ->
    ((Nat.gcd N (x - 1) < N) /\ (Nat.gcd N (x - 1) > 1))
    \/ ((Nat.gcd N (x + 1) < N) /\ (Nat.gcd N (x + 1) > 1)).
Proof.
  intros.
  replace (x ^ 2) with (x * x) in H0 by (simpl; lia).
  rewrite <- Nat.mul_mod_idemp_l, <- Nat.mul_mod_idemp_r in H0 by lia.
  remember (x mod N) as y.
  assert (1 < y).
  { destruct y. rewrite Nat.mod_0_l in H0 by lia. easy.
    destruct y. lia. lia.
  }
  assert ((y * y - 1) mod N = 0).
  { apply Nat_eq_mod_sub_0. rewrite H0. rewrite Nat.mod_small; easy.
  }
  assert (y < N - 1).
  { assert (y < N). subst. apply Nat.mod_upper_bound. lia.
    lia.
  }
  replace (y * y - 1) with ((y + 1) * (y - 1)) in H4 by lia.
  apply Nat.mod_divide in H4. 2: lia.
  bdestruct (Nat.gcd N (y + 1) =? 1).
  - specialize (Nat.gauss _ _ _ H4 H6) as G.
    apply Nat.divide_gcd_iff' in G.
    assert (Nat.gcd N (y - 1) <= y - 1) by (apply Nat_gcd_le_r; lia).
    lia.
  - bdestruct (Nat.gcd N (y + 1) =? 0).
    apply Nat.gcd_eq_0 in H7. lia.
    right.
    assert (Nat.gcd N (x + 1) = Nat.gcd N (y + 1)). {
      rewrite <- Nat.gcd_mod by lia. rewrite Nat.gcd_comm.
      rewrite <- Nat.add_mod_idemp_l by lia. rewrite <- Heqy.
      rewrite Nat.mod_small by lia. easy.
    }
    rewrite H8.
    assert (Nat.gcd N (y + 1) <= y + 1) by (apply Nat_gcd_le_r; lia).
    split; lia.
Qed.

Lemma dec_search :
  forall (P : nat -> Prop),
    (forall i, {P i} + {~ P i}) ->
    (forall x, {exists i, i <= x /\ P i} + {forall i, i > x \/ ~ P i}).
Proof.
  intros. induction x.
  - destruct (H 0).
    + left. exists 0. split. lia. easy.
    + right. intros. bdestruct (0 =? i). right. subst. easy. left. lia.
  - destruct (H (S x)).
    + left. exists (S x). split. lia. easy.
    + destruct IHx.
      * left. destruct e. exists x0. split. lia. easy.
      * right. intros. bdestruct (i =? S x). right. subst. easy.
        destruct (o i). left. lia. right. easy.
Qed.

Lemma Minima_Exists_aux :
  forall n (P : nat -> Prop) x,
    (forall i, {P i} + {~ P i}) ->
    x <= n ->
    P x ->
    (exists m, P m /\
          (forall y, P y -> y >= m)).
Proof.
  induction n; intros. exists 0. assert (x = 0) by lia. subst. split. easy. intros. lia.
  destruct (dec_search _ H n).
  - destruct e. destruct H2. apply IHn with (x := x0); easy.
  - destruct (H (S n)).
    + exists (S n). split. easy. intros. destruct (o y). lia. easy.
    + bdestruct (x =? S n). subst. easy.
      assert (x <= n) by lia.
      apply IHn with (x := x); easy.
Qed.

Lemma Minima_Exists :
  forall (P : nat -> Prop) x,
    (forall i, {P i} + {~ P i}) ->
    P x ->
    (exists m, P m /\
          (forall y, P y -> y >= m)).
Proof.
  intros. apply Minima_Exists_aux with (n := x) (x := x). easy. lia. easy.
Qed.
  
Lemma Minima_Exists_non_zero :
  forall (P : nat -> Prop) x,
    (forall i, {P i} + {~ P i}) ->
    0 < x -> P x ->
    (exists m, 0 < m /\ P m /\
          (forall y, 0 < y /\ P y -> y >= m)).
Proof.
  intros. remember (fun x => 0 < x /\ P x) as U.
  assert (HU : forall i, {U i} + {~ U i}). {
    intros. subst. destruct i. right. intro. lia.
    destruct (H (S i)). left. split. lia. easy. right. intro. easy.
  }
  destruct x. lia.
  assert (HUSx : U (S x)) by (subst; easy).
  destruct (Minima_Exists _ _ HU HUSx) as [m [? ?]].
  subst. exists m. easy.
Qed.

Lemma φ_pos :
  forall n,
    2 <= n -> 0 < φ n.
Proof.
  intros.
  specialize (φ_lower_bound _ H) as G.
  apply INR_lt. simpl.
  assert (1 <= Nat.log2 n). {
    replace 1 with (Nat.log2 2) by easy.
    apply Nat.log2_le_mono. easy.
  }
  apply le_INR in H0. simpl in H0.
  assert (0 < exp (-2))%R by (apply exp_pos).
  assert (INR 0 < n)%R by (apply lt_INR; lia). simpl in H2.
  apply Rge_le in G. apply Rcomplements.Rle_div_r in G. 2: lra.
  unfold Rdiv in G.
  assert (0 < Nat.log2 n ^ 4)%R. {
    simpl. assert (0 < Nat.log2 n * Nat.log2 n)%R by nra. nra.
  }
  assert (0 < / Nat.log2 n ^ 4)%R by (apply Rinv_0_lt_compat; lra).
  assert (0 < exp (-2) * / Nat.log2 n ^ 4)%R by nra.
  assert (0 < exp (-2) * / Nat.log2 n ^ 4 * n)%R by nra.
  nra.
Qed.

Lemma Order_exists :
  forall a N,
    2 <= N ->
    Nat.gcd a N = 1 ->
    exists r, Order a r N.
Proof.
  intros. unfold Order. apply Minima_Exists_non_zero with (x := (φ N)).
  - intro. bdestruct (a ^ i mod N =? 1). left. easy. right. easy.
  - apply φ_pos. easy.
  - rewrite φ_φ' by easy.
    replace 1 with (1 mod N) by (apply Nat.mod_small; lia).
    apply PTotient.euler_fermat_little. lia.
    intro. subst. rewrite Nat.gcd_0_l_nonneg in H0. lia.
    lia. easy.
Qed.

Lemma Order_unique :
  forall a r1 r2 N,
    Order a r1 N ->
    Order a r2 N ->
    r1 = r2.
Proof.
  intros. destruct H as [? [? ?]]. destruct H0 as [? [? ?]].
  assert (r1 >= r2) by (apply H4; easy).
  assert (r2 >= r1) by (apply H2; easy).
  lia.
Qed.

Lemma Order_factor_mod1 :
  forall a r N x, 0 < N ->
    Order a r N ->
    a ^ x mod N = 1 ->
    Nat.divide r x.
Proof.
  intros. specialize (Order_rel_prime _ _ _ H H0) as G.
  assert (2 <= N) by (specialize (Order_N_lb _ _ _ H H0); lia).
  destruct H0 as [? [? ?]].
  bdestruct (x =? 0). subst. apply Nat.divide_0_r.
  assert (x >= r). {
    apply H4. split. lia. easy.
  }
  assert (x = r * (x / r) + x mod r) by (apply Nat.div_mod; lia).
  rewrite H7 in H1.
  rewrite Nat.pow_add_r in H1. rewrite Nat.pow_mul_r in H1.
  rewrite <- Nat.mul_mod_idemp_l in H1 by lia.
  rewrite pow_mod in H1. rewrite H3 in H1. rewrite Nat.pow_1_l in H1. rewrite Nat.mod_small with (a := 1) in H1 by lia. rewrite Nat.mul_1_l in H1.
  assert (x mod r < r) by (apply Nat.mod_upper_bound; lia).
  bdestruct (0 <? x mod r).
  assert (0 < x mod r /\ a ^ (x mod r) mod N = 1) by easy.
  apply H4 in H10. lia.
  apply Nat.mod_divide; lia.
Qed.

Lemma Order_factor_φ :
  forall a r N, 0 < N ->
    Order a r N ->
    Nat.divide r (φ N).
Proof.
  intros. apply Order_factor_mod1 with (a := a) (N := N); try easy.
  assert (2 <= N) by (specialize (Order_N_lb _ _ _ H H0); lia).
  rewrite φ_φ' by easy. replace 1 with (1 mod N) by (apply Nat.mod_small; lia).
  apply PTotient.euler_fermat_little. lia.
  intro. subst. destruct H0 as [T [H0 _]]. rewrite Nat.pow_0_l in H0 by lia. rewrite Nat.mod_small in H0 by lia. easy.
  apply Order_rel_prime with (r := r); easy.
Qed.

Lemma Order_mod :
  forall a r N,
    Order a r N ->
    Order (a mod N) r N.
Proof.
  intros. destruct H as [? [? ?]].
  split. easy.
  split. rewrite <- pow_mod. easy.
  intros. apply H1.
  split. easy.
  rewrite pow_mod. easy.
Qed.

Fixpoint ord' n a N :=
  match n with
  | O => O
  | S n' => match (ord' n' a N) with
           | O => (if (a ^ n mod N =? 1) then n else O)
           | _ => ord' n' a N
           end
  end.
Definition ord a N := ord' (φ N) a N.

Lemma ord'_upper_bound :
  forall n a N, ord' n a N <= n.
Proof.
  intros. induction n. easy.
  simpl. destruct (ord' n a N). bdestruct ((a * a ^ n) mod N =? 1); lia. lia.
Qed.

Lemma ord'_a_pow_mod :
  forall n a N, 2 <= N -> a ^ (ord' n a N) mod N = 1.
Proof.
  intros. induction n. simpl. rewrite Nat.mod_small; lia.
  simpl. destruct (ord' n a N).
  bdestruct ((a * a ^ n) mod N =? 1). simpl. rewrite H0. easy.
  simpl. rewrite Nat.mod_small; lia. easy.
Qed.

Lemma ord'_non_zero_increase :
  forall m n a N,
    n <= m ->
    ord' n a N <> 0 ->
    ord' m a N = ord' n a N.
Proof.
  induction m; intros. assert (n = 0) by lia. subst. easy.
  bdestruct (n =? S m). subst. easy.
  assert (n <= m) by lia. specialize (IHm _ _ _ H2 H0).
  simpl. rewrite IHm. destruct (ord' n a N). lia. easy.
Qed.

Lemma ord'_non_zero :
  forall n a N, n <> 0 -> a ^ n mod N = 1 -> ord' n a N <> 0.
Proof.
  intros. destruct n. lia.
  simpl. destruct (ord' n a N). simpl in H0. rewrite H0.
  rewrite Nat.eqb_refl. lia. lia.
Qed.

Lemma ord_non_zero :
  forall a N,
    2 <= N -> Nat.gcd a N = 1 ->
    ord a N <> 0.
Proof.
  intros. unfold ord.
  assert (a ^ (φ N) mod N = 1). {
    rewrite φ_φ' by easy. replace 1 with (1 mod N) by (apply Nat.mod_small; lia).
    apply PTotient.euler_fermat_little. lia.
    intro. rewrite H1 in H0. rewrite Nat.gcd_0_l in H0. lia.
    easy.
  }
  assert (0 < φ N) by (apply φ_pos; easy).
  apply ord'_non_zero; lia.
Qed.

Lemma ord'_lt_zero :
  forall n m a N,
    0 < m < ord' n a N ->
    a ^ m mod N <> 1.
Proof.
  intros. intro.
  assert (ord' m a N <> 0) by (apply ord'_non_zero; lia).
  assert (m <= n) by (specialize (ord'_upper_bound n a N); lia).
  assert (ord' m a N <= m) by (specialize (ord'_upper_bound m a N); lia).
  apply ord'_non_zero_increase with (a := a) (N := N) in H2.
  lia. easy.
Qed.

Lemma ord_Order :
  forall a N,
    2 <= N -> Nat.gcd a N = 1 ->
    Order a (ord a N) N.
Proof.
  intros. unfold Order.
  assert (ord a N <> 0) by (apply ord_non_zero; easy).
  split. lia.
  split. apply ord'_a_pow_mod. easy.
  intros. destruct H2. bdestruct (r' <? ord a N). unfold ord in H4.
  assert (a ^ r' mod N <> 1) by (apply ord'_lt_zero with (n := (φ N)); lia).
  easy. easy.
Qed.

Lemma ord_mod :
  forall a N,
    2 <= N ->
    Nat.gcd a N = 1 ->
    ord a N = ord (a mod N) N.
Proof.
  intros.
  assert (Nat.gcd (a mod N) N = 1) by (rewrite Nat.gcd_mod by flia H; rewrite Nat.gcd_comm; easy).
  apply ord_Order in H0. apply ord_Order in H1. 2, 3: easy.
  apply Order_mod in H0.
  apply Order_unique with (a := (a mod N)) (N := N); easy.
Qed.

Lemma Order_not_factor :
  forall a r N x, 0 < N ->
    Order a r N ->
    a ^ x mod N <> 1 ->
    ~ Nat.divide r x.
Proof.
  intros. intro. destruct H2 as [k ?]. subst.
  rewrite Nat.mul_comm in H1. rewrite Nat.pow_mul_r in H1. rewrite pow_mod in H1.
  assert (1 < N) by (eapply Order_N_lb; try apply H0; easy).
  destruct H0 as [_ [? _]]. rewrite H0 in H1. rewrite Nat.pow_1_l in H1.
  rewrite Nat.mod_small in H1 by easy.
  lia.
Qed.

Lemma CRT_1 :
  forall a p q,
    1 < p /\
    1 < q /\
    Nat.gcd p q = 1 ->
    a mod (p * q) = 1 <-> (a mod p = 1 /\ a mod q = 1).
Proof.
  intros. split.
  - intro. split.
    + rewrite (Nat.div_mod a (p * q)) by nia. rewrite H0.
      replace (p * q * (a / (p * q))) with (p * (q * (a / (p * q)))) by lia.
      rewrite Nat_mod_add_l_mul_l by lia.
      apply Nat.mod_small. lia.
    + rewrite (Nat.div_mod a (p * q)) by nia. rewrite H0.
      replace (p * q * (a / (p * q))) with (q * (p * (a / (p * q)))) by lia.
      rewrite Misc.Nat_mod_add_l_mul_l by lia.
      apply Nat.mod_small. lia.
  - intro. destruct H0.
    assert (a = p * (a / p) + 1) by (rewrite <- H0; apply Nat.div_mod; lia).
    assert (a = q * (a / q) + 1) by (rewrite <- H1; apply Nat.div_mod; lia).
    bdestruct (a =? 0). subst. lia.
    assert (a - 1 = (a / p) * p) by lia.
    assert (a - 1 = (a / q) * q) by lia.
    assert ((a / p) = q * ((a / p) / q)) by (apply Primisc.gcd_1_div_mul_exact with (m := a - 1) (p := p) (kq := a / q); try lia; try easy).
    rewrite H7 in H2.
    rewrite H2. replace (p * (q * (a / p / q))) with ((p * q) * (a / p / q)) by lia.
    rewrite Nat_mod_add_l_mul_l by nia.
    apply Nat.mod_small. nia.
Qed.

Tactic Notation "flia" hyp_list(Hs) := clear - Hs; intros; nia.

Lemma CRT_neg1 :
  forall a p q,
    1 < p /\
    1 < q /\
    Nat.gcd p q = 1 ->
    a mod (p * q) = p * q - 1 <-> (a mod p = p - 1 /\ a mod q = q - 1).
Proof.
  intros. split.
  - intro. split.
    + rewrite (Nat.div_mod a (p * q)) by nia. rewrite H0.
      replace (p * q * (a / (p * q))) with (p * (q * (a / (p * q)))) by lia.
      rewrite Nat_mod_add_l_mul_l by lia.
      replace ((p * q) - 1) with (p * (q - 1) + (p - 1)) by lia.
      rewrite Nat_mod_add_l_mul_l by lia.
      apply Nat.mod_small. lia.
    + rewrite (Nat.div_mod a (p * q)) by nia. rewrite H0.
      replace (p * q * (a / (p * q))) with (q * (p * (a / (p * q)))) by lia.
      rewrite Nat_mod_add_l_mul_l by lia.
      replace ((p * q) - 1) with (q * (p - 1) + (q - 1)) by lia.
      rewrite Nat_mod_add_l_mul_l by lia.
      apply Nat.mod_small. lia.
  - intro. destruct H0.
    assert (a = p * (a / p) + (p - 1)) by (rewrite <- H0; apply Nat.div_mod; lia).
    assert (a = q * (a / q) + (q - 1)) by (rewrite <- H1; apply Nat.div_mod; lia).
    bdestruct (a =? 0). subst. lia.
    assert (a + 1 = ((a / p) + 1) * p) by lia.
    assert (a + 1 = ((a / q) + 1) * q) by lia.
    assert ((a / p) + 1 = q * (((a / p) + 1) / q)) by (apply Primisc.gcd_1_div_mul_exact with (m := a + 1) (p := p) (kq := a / q + 1); try lia; try easy).
    replace (p * (a / p) + (p - 1)) with (p * (a / p + 1) - 1) in H2 by lia.
    assert ((a / p + 1) / q > 0). {
      bdestruct ((a / p + 1) / q =? 0). rewrite H8 in H7. lia. lia.
    }
    rewrite H7 in H2.
    rewrite H2.
    replace (p * (q * ((a / p + 1) / q)) - 1) with ((p * q) * (((a / p + 1) / q) - 1) + (p * q - 1)) by flia H H8.
    rewrite Nat_mod_add_l_mul_l by nia.
    apply Nat.mod_small. nia.
Qed.

Definition crt2 i j p q := (q * (modinv q p) * i + p * (modinv p q) * j) mod (p * q).

Lemma mod_mul :
  forall x p q,
    p <> 0 -> q <> 0 ->
    (x mod (p * q)) mod p = x mod p.
Proof.
  intros. rewrite Nat.mod_mul_r by easy.
  rewrite Nat_mod_add_r_mul_l. apply Nat.mod_mod. easy. easy.
Qed.

Lemma crt2_sur :
  forall x i j p q,
    i < p -> j < q ->
    Nat.gcd p q = 1 ->
    x = crt2 i j p q ->
    x mod p = i /\ x mod q = j.
Proof.
  intros. split; subst; unfold crt2.
  - rewrite mod_mul by flia H H0.
    replace (p * modinv p q * j) with (p * (modinv p q * j)) by flia.
    rewrite Nat_mod_add_r_mul_l by flia H.
    rewrite <- Nat.mul_mod_idemp_l by flia H.
    rewrite modinv_correct by flia H.
    rewrite Nat.gcd_comm, H1.
    bdestruct (p =? 1). assert (i = 0) by flia H H2. subst. easy.
    rewrite Nat.mod_small with (a := 1) by flia H H2.
    rewrite Nat.mod_small by flia H. flia.
  - replace (p * q) with (q * p) by flia.    
    rewrite mod_mul by flia H H0.
    replace (q * modinv q p * i) with (q * (modinv q p * i)) by flia.
    rewrite Nat_mod_add_l_mul_l by flia H0.
    rewrite <- Nat.mul_mod_idemp_l by flia H0.
    rewrite modinv_correct by flia H0.
    rewrite H1.
    bdestruct (q =? 1). assert (j = 0) by flia H0 H2. subst. easy.
    rewrite Nat.mod_small with (a := 1) by flia H0 H2.
    rewrite Nat.mod_small by flia H0. flia.
Qed.

Lemma crt2_upper_bound :
  forall i j p q, p <> 0 -> q <> 0 -> crt2 i j p q < p * q.
Proof.
  intros. unfold crt2. apply Nat.mod_upper_bound. nia.
Qed.

Lemma crt2_correct :
  forall x i j p q,
    i < p -> j < q -> x < p * q ->
    Nat.gcd p q = 1 ->
    x mod p = i /\ x mod q = j   <->   x = crt2 i j p q.
Proof.
  intros.
  assert (crt2 i j p q mod p = i /\ crt2 i j p q mod q = j) by (apply crt2_sur; easy).
  split. 2: intro; apply crt2_sur; easy.
  intros. destruct H3, H4.
  bdestruct (x =? crt2 i j p q). easy.
  bdestruct (x <? crt2 i j p q).
  - assert ((crt2 i j p q - x) mod p = 0) by (apply Nat_eq_mod_sub_0; rewrite H3, H4; easy).
    assert ((crt2 i j p q - x) mod q = 0) by (apply Nat_eq_mod_sub_0; rewrite H5, H6; easy).
    rewrite Nat.mod_divide in H9, H10 by flia H H0.
    assert (Nat.divide (p * q) (crt2 i j p q - x)) by (apply Primisc.Nat_gcd_1_mul_divide; easy).
    destruct H11.
    destruct x0. flia H8 H11.
    assert (crt2 i j p q < p * q) by (apply crt2_upper_bound; flia H H0).
    flia H11 H12.
  - assert ((x - crt2 i j p q) mod p = 0) by (apply Nat_eq_mod_sub_0; rewrite H3, H4; easy).
    assert ((x - crt2 i j p q) mod q = 0) by (apply Nat_eq_mod_sub_0; rewrite H5, H6; easy).
    rewrite Nat.mod_divide in H9, H10 by flia H H0.
    assert (Nat.divide (p * q) (x - crt2 i j p q)) by (apply Primisc.Nat_gcd_1_mul_divide; easy).
    destruct H11.
    destruct x0. flia H8 H11.
    flia H11 H1.
Qed.

Lemma gcd_crt2 :
  forall i j p q,
    1 < p -> 1 < q ->
    Nat.gcd p q = 1 ->
    Nat.gcd (crt2 i j p q) (p * q) = 1 <-> Nat.gcd i p = 1 /\ Nat.gcd j q = 1.
Proof.
  intros. split; intros.
  unfold crt2 in H2. rewrite Nat.gcd_mod in H2 by flia H H0.
  - split.
    + bdestruct (Nat.gcd i p =? 1). easy.
      destruct (Nat.gcd_divide i p). destruct H4, H5.
      replace (p * q) with ((x0 * q) * Nat.gcd i p) in H2 by flia H5.
      replace (q * modinv q p * i + p * modinv p q * j) with ((q * modinv q p * x + x0 * modinv p q * j) * Nat.gcd i p) in H2 by flia H4 H5.
      rewrite Nat.gcd_mul_mono_r in H2.
      apply natmul1 in H2; easy.
    + bdestruct (Nat.gcd j q =? 1). easy.
      destruct (Nat.gcd_divide j q). destruct H4, H5.
      replace (p * q) with ((x0 * p) * Nat.gcd j q) in H2 by flia H5.
      replace (q * modinv q p * i + p * modinv p q * j) with ((x0 * modinv q p * i + x * modinv p q * p) * Nat.gcd j q) in H2 by flia H4 H5.
      rewrite Nat.gcd_mul_mono_r in H2.
      apply natmul1 in H2; easy.
  - destruct H2.
    unfold crt2. rewrite Nat.gcd_mod by flia H H0.
    apply Nat_gcd_1_mul_l.
    rewrite <- Nat.gcd_mod by flia H.
    replace (p * modinv p q * j) with (p * (modinv p q * j)) by flia.
    rewrite Nat_mod_add_r_mul_l by flia H.
    rewrite Nat.gcd_mod by flia H.
    apply Nat_gcd_1_mul_r. apply Nat_gcd_1_mul_r.
    easy. rewrite Nat.gcd_comm. apply modinv_coprime; try easy; try flia H H0.
    rewrite Nat.gcd_comm. easy.
    rewrite <- Nat.gcd_mod by flia H0.
    replace (q * modinv q p * i) with (q * (modinv q p * i)) by flia.
    rewrite Nat_mod_add_l_mul_l by flia H0.
    rewrite Nat.gcd_mod by flia H0.
    apply Nat_gcd_1_mul_r. apply Nat_gcd_1_mul_r.
    rewrite Nat.gcd_comm. easy. rewrite Nat.gcd_comm. apply modinv_coprime; try easy; try flia H H0.
    rewrite Nat.gcd_comm. easy.
    rewrite Nat.gcd_comm. easy.
Qed.

Lemma Order_coprime_lcm :
  forall a rp rq p q,
    Nat.gcd p q = 1 ->
    Order a rp p ->
    Order a rq q ->
    Order a (Nat.lcm rp rq) (p * q).
Proof.
  intros. 
  assert (Hq : 0 < q).
  { bdestruct (q =? 0).
    subst. simpl in H.
    rewrite Nat.gcd_0_r in H. subst.
    destruct H0 as [_ [H0 _]]. simpl in H0. easy. 
    lia. }
  assert (Hp : 0 < p).
  { bdestruct (p =? 0).
    subst. simpl in H. subst.
    destruct H1 as [_ [H1 _]]. simpl in H1. easy. 
    lia. }
  assert (Hpod := H0). assert (Hqod := H1).
  destruct H0 as [Hrp0 [Hrp1 Hrp2]].
  destruct H1 as [Hrq0 [Hrq1 Hrq2]].
  split. bdestruct (Nat.lcm rp rq =? 0). rewrite Nat.lcm_eq_0 in H0. lia. lia.
  assert (1 < p) by (apply (Order_N_lb _ _ _ Hp Hpod)).
  assert (1 < q) by (apply (Order_N_lb _ _ _ Hq Hqod)).
  split.
  - rewrite CRT_1 by easy. split.
    unfold Nat.lcm. rewrite Nat.pow_mul_r. rewrite pow_mod. rewrite Hrp1.
    rewrite Nat.pow_1_l. apply Nat.mod_small. easy.
    rewrite Nat.lcm_comm.
    unfold Nat.lcm. rewrite Nat.pow_mul_r. rewrite pow_mod. rewrite Hrq1.
    rewrite Nat.pow_1_l. apply Nat.mod_small. easy.
  - intros. destruct H2.
    rewrite CRT_1 in H3 by easy. destruct H3.
    apply Order_factor_mod1 with (r := rp) in H3; try easy.
    apply Order_factor_mod1 with (r := rq) in H4; try easy.
    assert (Nat.divide (Nat.lcm rp rq) r') by (apply Nat.lcm_least; easy).
    apply Nat.divide_pos_le in H5; lia.
Qed.

Definition d2p n := pow_in_n n 2.

Local Opaque Nat.div Nat.modulo.
Lemma prime_decomp_double :
  forall a, a <> 0 -> prime_decomp (2 * a) = 2 :: prime_decomp a.
Proof.
  intros. unfold prime_decomp. destruct a. easy.
  replace (2 * S a) with (S (S (2 * a))) by lia.
  destruct a. easy.
  remember (S (2 * S a)) as a2_3.
  remember (S (S a)) as a1_2.
  simpl. replace (S a2_3) with ((S (S a)) * 2) by lia.
  rewrite Nat.mod_mul by easy.
  replace (S (S a) * 2 / 2) with (S (S a)) by (rewrite Nat.div_mul; easy).
  subst. symmetry. rewrite prime_decomp_aux_more_iter with (k := a + 1) by lia.
  replace (S (S a) + (a + 1)) with (S (2 * (S a))) by lia.
  easy.
Qed.
Local Transparent Nat.div Nat.modulo.

Lemma d2p_double :
  forall a, a <> 0 -> d2p (2 * a) = S (d2p a).
Proof.
  intros. unfold d2p, pow_in_n. rewrite prime_decomp_double by easy. easy.
Qed.

Lemma d2p_odd :
  forall a, d2p (2 * a + 1) = 0.
Proof.
  intros. unfold d2p, pow_in_n. apply count_occ_not_In.
  intro. apply in_prime_decomp_divide in H. destruct H. lia.
Qed.

Lemma parity_decomp_pos :
  forall n,
    n <> 0 ->
    exists k, k < n /\ (n = 2 * k \/ n = 2 * k + 1).
Proof.
  destruct n. easy.
  induction n; intros. exists 0. lia.
  assert (S n <> 0) by lia.
  destruct (IHn H0) as [k [U [G | G]]]. exists k. lia. exists (S k). lia.
Qed.

Lemma parity_decomp_pos_stronger :
  forall n,
    n <> 0 ->
    exists k, (0 < k < n /\ n = 2 * k) \/ (k < n /\ n = 2 * k + 1).
Proof.
  destruct n. easy.
  induction n; intros. exists 0. lia.
  assert (S n <> 0) by lia.
  destruct (IHn H0) as [k [? | ?]]. exists k. lia. exists (S k). lia.
Qed.

Lemma parity_pow_decomp_aux :
  forall m n,
    n <= m ->
    n <> 0 ->
    exists k d, n = 2 ^ d * (2 * k + 1).
Proof.
  induction m. intros. lia.
  intros. bdestruct (n <=? m). apply IHm; easy.
  assert (n = S m) by lia.
  destruct (parity_decomp_pos_stronger n) as [k [[? ?] | [? ?]]]. easy.
  - assert (k <= m) by lia. assert (k <> 0) by lia.
    destruct (IHm k H5 H6) as [k' [d ?]]. 
    exists k'. exists (S d). replace (2 ^ S d) with (2 * 2 ^ d) by (simpl; lia).
    lia.
  - exists k. exists 0. simpl. lia.
Qed.

Lemma parity_pow_decomp :
  forall n,
    n <> 0 ->
    exists k d, n = 2 ^ d * (2 * k + 1).
Proof.
  intros. apply parity_pow_decomp_aux with (m := n); lia.
Qed.

Lemma d2p_parity_pow :
  forall d k,
    d2p (2^d * (2 * k + 1)) = d.
Proof.
  induction d; intros. replace (2 ^ 0 * (2 * k + 1)) with (2 * k + 1) by (simpl; lia). apply d2p_odd.
  replace (2 ^ S d * (2 * k + 1)) with (2 * (2 ^ d * (2 * k + 1))) by (simpl; lia).
  rewrite d2p_double. rewrite IHd. easy.
  assert (2 * k + 1 <> 0) by lia.
  assert (2 ^ d <> 0) by (apply Nat.pow_nonzero; easy).
  nia.
Qed.    

Lemma d2p_mul_odd :
  forall a b, d2p (a * (2 * b + 1)) = d2p a.
Proof.
  intros. bdestruct (a =? 0). subst. easy.
  destruct (parity_pow_decomp _ H) as [k [d ?]].
  rewrite H0.
  replace (2 ^ d * (2 * k + 1) * (2 * b + 1)) with (2 ^ d * ((2 * k + 1) * (2 * b + 1))) by lia.
  replace ((2 * k + 1) * (2 * b + 1)) with (2 * (2 * k * b + k + b) + 1) by lia.
  do 2 rewrite d2p_parity_pow. easy.
Qed.

Lemma Natdivide_mul_mono :
  forall n m p,
    p <> 0 ->
    Nat.divide (p * n) (p * m) ->
    Nat.divide n m.
Proof.
  intros. destruct H0. exists x. rewrite <- (Nat.mul_cancel_l _ _ _ H). nia.
Qed.

Lemma d2p_factor_aux :
  forall n a b,
    b <= n ->
    b <> 0 ->
    Nat.divide a b ->
    d2p a <= d2p b.
Proof.
  induction n; intros. lia.
  assert (a <> 0). {
    destruct H1. intro. subst. lia.
  }
  destruct (parity_decomp_pos _ H0) as [b2 [Hb2n [Hbeven | Hbodd]]];
  destruct (parity_decomp_pos _ H2) as [a2 [Ha2n [Haeven | Haodd]]]; subst.
  - assert (a2 <> 0) by lia. assert (b2 <> 0) by lia. assert (b2 <= n) by lia.
    do 2 rewrite d2p_double by easy.
    assert (Nat.divide a2 b2) by (apply Natdivide_mul_mono with (p := 2); easy).
    specialize (IHn _ _ H5 H4 H6). lia.
  - rewrite d2p_odd. lia.
  - destruct H1. lia.
  - rewrite d2p_odd. lia.
Qed.

Lemma d2p_factor :
  forall a b,
    b <> 0 ->
    Nat.divide a b ->
    d2p a <= d2p b.
Proof.
  intros. apply d2p_factor_aux with (n := b); try easy; try lia.
Qed.

Lemma d2p_stuck :
  forall a b,
    Nat.divide a (2 * b) ->
    ~ Nat.divide a b ->
    d2p a = S (d2p b).
Proof.
  intros.
  bdestruct (b =? 0). subst. specialize (Nat.divide_0_r a) as G. easy.
  bdestruct (a =? 0). subst. destruct H. lia.
  specialize (Nat.div_mod b a H2) as G.
  remember (b mod a) as q. remember (b / a) as p.
  bdestruct (q =? 0). subst. rewrite Nat.mod_divide in H3; easy.
  assert (q < a) by (subst; apply Nat.mod_upper_bound; easy).
  assert (2 * q < 2 * a) by lia.
  rewrite <- Nat.mod_divide in H by easy.
  replace (2 * b) with (a * (2 * p) + 2 * q) in H by lia.
  rewrite Nat_mod_add_l_mul_l in H by lia.
  rewrite Nat.mod_divide in H by easy. destruct H.
  bdestruct (x =? 0). subst. flia H H3.
  bdestruct (2 <=? x). flia H H5 H7.
  assert (x = 1) by lia. rewrite H8 in H. rewrite Nat.mul_1_l in H.
  replace (a * p + q) with (q * (2 * p + 1)) in G by flia H G.
  rewrite <- H, G. rewrite d2p_double by easy. rewrite d2p_mul_odd. easy.
Qed.

Lemma d2p_pos :
  forall a, d2p a > 0 -> exists k, k > 0 /\ a = 2 * k.
Proof.
  intros. bdestruct (a =? 0). subst. unfold d2p, pow_in_n in H. simpl in H. lia.
  destruct (parity_decomp_pos _ H0) as [k [? [? | ?]]].
  - exists k. split. bdestructΩ (k =? 0). easy.
  - subst. rewrite d2p_odd in H. lia.
Qed.

Lemma Natgcd_pos :
  forall a b, 0 < a -> 0 < b -> 0 < Nat.gcd a b.
Proof.
  intros. destruct (Nat.gcd a b) eqn:E. rewrite Nat.gcd_eq_0 in E. lia. lia.
Qed.

Lemma Natlcm_pos :
  forall a b, 0 < a -> 0 < b -> 0 < Nat.lcm a b.
Proof.
  intros. unfold Nat.lcm.
  assert (Nat.gcd a b <= b) by (apply Nat_gcd_le_r; lia).
  assert (0 < Nat.gcd a b) by (apply Natgcd_pos; easy).
  assert (1 <= b / Nat.gcd a b) by (apply Nat.div_le_lower_bound; lia).
  nia.
Qed.

Lemma Natlcm_mono_l :
  forall a b c, Nat.divide a b -> Nat.divide a (Nat.lcm b c).
Proof.
  intros. destruct H. subst. unfold Nat.lcm. replace (x * a * (c / Nat.gcd (x * a) c)) with (a * (x * (c / Nat.gcd (x * a) c))) by lia. apply Nat.divide_factor_l.
Qed.

Lemma d2p_r_even :
  forall rp rq,
    0 < rp -> 0 < rq ->
    d2p rp <> d2p rq ->
    Nat.divide 2 (Nat.lcm rp rq).
Proof.
  intros.
  bdestruct (d2p rp =? 0).
  - bdestruct (d2p rq =? 0). lia.
    assert (exists rq2, rq2 > 0 /\ rq = 2 * rq2) by (apply d2p_pos; lia).
    rewrite Nat.lcm_comm. apply Natlcm_mono_l. destruct H4 as [rq2 [? ?]]. exists rq2. lia.
  - assert (exists rp2, rp2 > 0 /\ rp = 2 * rp2) by (apply d2p_pos; lia).
    apply Natlcm_mono_l. destruct H3 as [rp2 [? ?]]. exists rp2. lia.
Qed.

Lemma d2p_neq_sufficient_aux :
  forall a r rp rq p q,
    2 < p -> 2 < q ->
    Nat.gcd p q = 1 ->
    Order a rp p -> Order a rq q ->
    Order a r (p * q) ->
    d2p rp <> d2p rq ->
    a ^ (r / 2) mod (p * q) <> 1 /\ a ^ (r / 2) mod (p * q) <> p * q - 1.
Proof.
  intros ? ? ? ? ? ? Hp Hq Hgcd Hrp Hrq Hr Hd2p.
  assert (Hlcm: Order a (Nat.lcm rp rq) (p * q)) by (apply Order_coprime_lcm; easy).
  apply Order_unique with (r1 := r) in Hlcm. 2: easy.
  assert (N0rp: 0 < rp) by (destruct Hrp; easy).
  assert (N0rq: 0 < rq) by (destruct Hrq; easy).
  destruct (d2p_r_even _ _ N0rp N0rq Hd2p) as [k Hk].
  bdestruct (k =? 0). subst. rewrite Nat.mul_0_l in Hk.
  assert (0 < Nat.lcm rp rq) by (apply Natlcm_pos; easy). flia Hk H.
  rewrite Hk in Hlcm. rewrite Hlcm. rewrite Nat.div_mul by easy.
  split.
  - intro contra. apply Order_factor_mod1 with (r := r) in contra. 3: easy.
    destruct contra as [x Hx]. rewrite Hx in Hlcm.
    replace (x * r * 2) with (r * (x * 2)) in Hlcm by lia.
    symmetry in Hlcm. rewrite Nat.mul_id_r in Hlcm by flia H Hx.
    flia Hlcm. lia.
  - intro contra.
    apply CRT_neg1 in contra. 2: lia. destruct contra as [Cp Cq].
    assert (Hkp: a ^ k mod p <> 1) by flia Hp Cp.
    apply Order_not_factor with (r := rp) in Hkp. 3: easy.
    assert (Cp': a ^ (2 * k) mod p = 1). {
      rewrite Nat.mul_comm. rewrite Nat.pow_mul_r. rewrite pow_mod. rewrite Cp.
      replace ((p - 1) ^ 2) with (p * (p - 2) + 1) by (simpl; flia Hp).
      rewrite Nat_mod_add_l_mul_l by flia Hp.
      apply Nat.mod_small. flia Hp.
    }
    apply Order_factor_mod1 with (r := rp) in Cp'. 3: easy.
    assert (Hd2prp: d2p rp = S (d2p k)) by (apply d2p_stuck; easy).    
    assert (Hkq: a ^ k mod q <> 1) by flia Hq Cq.
    apply Order_not_factor with (r := rq) in Hkq. 3: easy.
    assert (Cq': a ^ (2 * k) mod q = 1). {
      rewrite Nat.mul_comm. rewrite Nat.pow_mul_r. rewrite pow_mod. rewrite Cq.
      replace ((q - 1) ^ 2) with (q * (q - 2) + 1) by (simpl; flia Hq).
      rewrite Nat_mod_add_l_mul_l by flia Hq.
      apply Nat.mod_small. flia Hq.
    }
    apply Order_factor_mod1 with (r := rq) in Cq'. 3: easy.
    assert (Hd2prq: d2p rq = S (d2p k)) by (apply d2p_stuck; easy).
    flia Hd2prp Hd2prq Hd2p.
    all: lia.
Qed.

Lemma d2p_neq_sufficient :
  forall a r rp rq p q,
    2 < p -> 2 < q ->
    Nat.gcd p q = 1 ->
    Order a rp p -> Order a rq q ->
    Order a r (p * q) ->
    d2p rp <> d2p rq ->
    ((Nat.gcd (p * q) (a ^ (r / 2) - 1) < p * q) /\ (Nat.gcd (p * q) (a ^ (r / 2) - 1) > 1))
    \/ ((Nat.gcd (p * q) (a ^ (r / 2) + 1) < p * q) /\ (Nat.gcd (p * q) (a ^ (r / 2) + 1) > 1)).
Proof.
  intros ? ? ? ? ? ? Hp Hq Hgcd Hrp Hrq Hr Hd2p.
  specialize (d2p_neq_sufficient_aux _ _ _ _ _ _ Hp Hq Hgcd Hrp Hrq Hr Hd2p) as G.
  assert (Hlcm: Order a (Nat.lcm rp rq) (p * q)) by (apply Order_coprime_lcm; easy).
  apply Order_unique with (r1 := r) in Hlcm. 2: easy.
  assert (N0rp: 0 < rp) by (destruct Hrp; easy).
  assert (N0rq: 0 < rq) by (destruct Hrq; easy).
  destruct (d2p_r_even _ _ N0rp N0rq Hd2p) as [k Hk].
  assert (Hrk: r = k * 2) by flia Hlcm Hk.
  apply sqr1_not_pm1; try easy. flia Hp Hq.
  replace ((a ^ (r / 2)) ^ 2) with (a ^ (r / 2) * a ^ (r / 2)) by (simpl; flia).
  rewrite <- Nat.pow_add_r. rewrite Hrk. rewrite Nat.div_mul by easy.
  replace (k + k) with r by flia Hrk. destruct Hr. easy.
Qed.

Lemma Nat_gcd_1_mul_r_rev :
  forall a b c : nat,
    Nat.gcd a (b * c) = 1 -> Nat.gcd a b = 1.
Proof.
  intros.
  destruct (Nat.gcd_divide a b). 
  remember (Nat.gcd a b) as g.
  bdestruct (g =? 1). easy.
  destruct H0 as [a' Ha']. destruct H1 as [b' Hb'].
  rewrite Ha', Hb' in H. replace (b' * g * c) with ((b' * c) * g) in H by lia.
  rewrite Nat.gcd_mul_mono_r in H.
  bdestruct (g =? 0). rewrite H0 in H. flia H.
  remember (Nat.gcd a' (b' * c)) as r.
  bdestruct (r =? 0). rewrite H1 in H. flia H.
  flia H H0 H1 H2.
Qed.

Lemma pow_coprime :
  forall a p k,
    Nat.gcd a p = 1 -> Nat.gcd a (p^k) = 1.
Proof.
  intros. induction k. simpl. apply Nat.gcd_1_r.
  simpl. apply Nat_gcd_1_mul_r; easy.
Qed.

Lemma pow_coprime_rev :
  forall a p k,
    k <> 0 ->
    Nat.gcd a (p^k) = 1 -> Nat.gcd a p = 1.
Proof.
  intros. destruct k. lia. simpl in H0.
  apply Nat_gcd_1_mul_r_rev in H0. easy.
Qed.

Lemma prime_mod_pos :
  forall x p,
    prime p ->
    x mod p <> 0 <-> Nat.gcd p x = 1.
Proof.
  intros.
  assert (p <> 0) by (apply prime_neq_0; easy).
  assert (2 <= p) by (apply prime_ge_2; easy).
  split; intro.
  - rewrite <- Nat.gcd_mod by easy. rewrite Nat.gcd_comm. 
    apply eq_gcd_prime_small_1. easy.
    split. lia. apply Nat.mod_upper_bound; lia.
  - intro. rewrite Nat.mod_divide in H3 by easy.
    destruct H3. rewrite H3 in H2. rewrite Nat.mul_comm in H2. rewrite Nat.gcd_mul_diag_l in H2; lia.
Qed.

Lemma mod_pow_twice :
  forall x p k,
    k <> 0 -> p <> 0 -> (x mod p ^ k) mod p = x mod p.
Proof.
  intros. destruct k. easy. simpl.
  rewrite Nat.mod_mul_r. rewrite Nat_mod_add_r_mul_l. apply Nat.mod_mod.
  1-3: easy.
  assert (1 <= p ^ k) by (apply pow_positive; easy).
  lia.
Qed.  

Lemma sqr_mod_prime_pow_pos :
  forall x p k,
    k <> 0 -> prime p ->
    Nat.gcd x (p ^ k) = 1 ->
    (x ^ 2) mod (p ^ k) <> 0.
Proof.
  intros. replace (x ^ 2) with (x * x) by (simpl; flia). intro.
  assert (2 <= p) by (apply prime_ge_2; easy).
  assert (2 <= p ^ k). {
    destruct k. easy. simpl.
    assert (p ^ k > 0) by (apply pow_positive; lia).
    flia H3 H4.
  }
  assert ((x * x * ((modinv x (p ^ k)) * (modinv x (p ^ k)))) mod (p ^ k) = 0). {
    rewrite <- Nat.mul_mod_idemp_l by lia. rewrite H2.
    rewrite Nat.mul_0_l. apply Nat.mod_small. lia.
  }
  replace (x * x * (modinv x (p ^ k) * modinv x (p ^ k))) with ((x * (modinv x (p ^ k))) * (x * (modinv x (p ^ k)))) in H5 by flia.
  rewrite <- Nat.mul_mod_idemp_l, <- Nat.mul_mod_idemp_r in H5 by lia.
  rewrite modinv_correct in H5 by lia.
  rewrite H1 in H5.
  rewrite Nat.mod_small with (a := 1) in H5 by lia.
  rewrite Nat.mod_small in H5 by lia.
  lia.
Qed.

Lemma Natgcd_sqr :
  forall a p,
    Nat.divide (Nat.gcd a p) (Nat.gcd (a ^ 2) p).
Proof.
  intros. apply Nat.gcd_greatest.
  destruct (Nat.gcd_divide_l a p). exists (a * x). simpl. lia.
  apply Nat.gcd_divide_r.
Qed.

Lemma sqr_gcd :
  forall a x p,
    Nat.gcd a p = 1 ->
    x ^ 2 mod p = a ->
    Nat.gcd x p = 1.
Proof.
  intros.
  bdestruct (p =? 0).
  subst. simpl in *. rewrite Nat.gcd_0_r in *. lia.
  rewrite <- H0 in H.
  rewrite Nat.gcd_mod in H by easy. rewrite Nat.gcd_comm in H.
  destruct (Natgcd_sqr x p). rewrite H in H2.
  bdestruct (Nat.gcd x p =? 0). flia H2 H3.
  bdestruct (x0 =? 0). flia H2 H4.
  nia.
Qed.

Lemma mod_add_mul_multiple :
  forall x p a b,
    p <> 0 ->
    x + a * p >= b * p ->
    (x + a * p - b * p) mod p = x mod p.
Proof.
  intros.
  bdestruct (b <=? a).
  - replace (x + a * p - b * p) with (x + p * (a - b)) by flia H1.
    apply Nat_mod_add_r_mul_l. easy.
  - replace (x + a * p - b * p) with (x - p * (b - a)) by flia H0 H1.
    replace x with ((x - p * (b - a)) + p * (b - a)) at 2 by flia H0 H1.
    rewrite Nat_mod_add_r_mul_l; easy.
Qed.

Lemma neg_sqr_mod :
  forall x p, p <> 0 -> x <= p -> x ^ 2 mod p = (p - x) ^ 2 mod p.
Proof.
  intros. replace ((p - x) ^ 2) with (x * x + p * p - (2 * x) * p) by (simpl; nia).
  symmetry. replace (x ^ 2) with (x * x) by (simpl; lia).
  apply mod_add_mul_multiple. easy. nia.
Qed.

Lemma Natdivide_mul :
  forall a b c,
    Nat.divide (a * b) c ->
    Nat.divide a c /\ Nat.divide b c.
Proof.
  intros. destruct H. split.
  exists (x * b). lia. exists (x * a). lia.
Qed.

Lemma prime_div_reduce :
  forall x p,
    prime p -> 2 < p ->
    Nat.divide p (2 * x) ->
    Nat.divide p x.
Proof.
  intros. 
  apply Nat.gauss with (m := 2). easy.
  apply eq_gcd_prime_small_1. easy. lia.
Qed.

Lemma prime_power_lb :
  forall p k,
    k <> 0 -> prime p -> 2 < p ->
    p ^ k > 2.
Proof.
  intros. destruct k. easy. simpl.
  assert (p ^ k > 0) by (apply pow_positive; flia H1).
  flia H1 H2.
Qed.

Lemma mod_sqr_sol_aux :
  forall x y a p k,
    k <> 0 -> prime p -> 2 < p ->
    Nat.gcd a p = 1 ->
    0 < a < p^k -> 0 < x < p^k -> 0 < y < p^k -> y <= x ->
    x ^ 2 mod p^k = a -> y ^ 2 mod p^k = a ->
    y = x \/ y = p^k - x.
Proof.
  intros ? ? ? ? ? Hk Hprime Hp Hgcd Ha Hx Hy Hxy Hx2 Hy2.
  assert (Hdif: (x^2 - y^2) mod p^k = 0) by (apply Nat_eq_mod_sub_0; lia).
  replace (x ^ 2 - y ^ 2) with ((x + y) * (x - y)) in Hdif by (simpl; nia).
  bdestruct ((x + y) mod p =? 0); bdestruct ((x - y) mod p =? 0).
  - rewrite Nat.mod_divide in H, H0 by flia Hp. destruct H, H0.
    assert (Nat.divide p (2 * x)) by (exists (x0 + x1); flia H H0 Hxy).
    apply prime_div_reduce in H1. 2, 3: easy.
    rewrite <- Nat.mod_divide in H1 by flia Hp.
    apply pow_coprime with (k := k) in Hgcd.
    assert (Nat.gcd x (p ^ k) = 1) by (apply sqr_gcd with (a := a); easy).
    apply pow_coprime_rev with (k := k) in H2. 2: easy.
    rewrite Nat.gcd_comm in H2. rewrite <- prime_mod_pos in H2 by easy.
    flia H1 H2.
  - rewrite prime_mod_pos in H0 by easy.
    rewrite Nat.gcd_comm in H0.
    apply pow_coprime with (k := k) in H0.
    assert (p ^ k > 2) by (apply prime_power_lb; easy).
    assert (((x + y) * ((x - y) * (modinv (x - y) (p^k)))) mod p ^ k = 0). {
      replace ((x + y) * ((x - y) * (modinv (x - y) (p^k)))) with ((x + y) * (x - y) * (modinv (x - y) (p^k))) by flia.
      rewrite <- Nat.mul_mod_idemp_l by flia H1. rewrite Hdif.
      simpl. rewrite Nat.mod_0_l; flia H1.
    }
    rewrite <- Nat.mul_mod_idemp_r in H2 by flia H1.
    rewrite modinv_correct in H2 by flia H1.
    rewrite H0 in H2. rewrite Nat.mod_small with (a := 1) in H2 by flia H1.
    rewrite Nat.mul_1_r in H2.
    assert (x + y = (p ^ k * ((x + y) / p ^ k)) + (x + y) mod p ^ k) by (apply Nat.div_mod; flia H1).
    rewrite H2 in H3. rewrite Nat.add_0_r in H3.
    assert ((x + y) / p ^ k < 2) by (apply Nat.Private_NZDiv.div_lt_upper_bound; flia Hx Hy).
    bdestruct ((x + y) / p ^ k =? 0). rewrite H5 in H3. flia H3 Hx Hy.
    right. flia H3 H4 H5.
  - rewrite prime_mod_pos in H by easy.
    rewrite Nat.gcd_comm in H.
    apply pow_coprime with (k := k) in H.
    assert (p ^ k > 2) by (apply prime_power_lb; easy).
    assert (((x - y) * ((x + y) * (modinv (x + y) (p^k)))) mod p ^ k = 0). {
      replace ((x - y) * ((x + y) * (modinv (x + y) (p^k)))) with ((x + y) * (x - y) * (modinv (x + y) (p^k))) by flia.
      rewrite <- Nat.mul_mod_idemp_l by flia H1. rewrite Hdif.
      simpl. rewrite Nat.mod_0_l; flia H1.
    }
    rewrite <- Nat.mul_mod_idemp_r in H2 by flia H1.
    rewrite modinv_correct in H2 by flia H1.
    rewrite H in H2. rewrite Nat.mod_small with (a := 1) in H2 by flia H1.
    rewrite Nat.mul_1_r in H2.
    assert (x - y = (p ^ k * ((x - y) / p ^ k)) + (x - y) mod p ^ k) by (apply Nat.div_mod; flia H1).
    rewrite H2 in H3. rewrite Nat.add_0_r in H3.
    assert ((x - y) / p ^ k < 1) by (apply Nat.Private_NZDiv.div_lt_upper_bound; flia Hx Hy).
    assert ((x - y) / p ^ k = 0) by flia H4.
    rewrite H5 in H3. rewrite Nat.mul_0_r in H3.
    left. flia H3 Hxy.
  - rewrite prime_mod_pos in H, H0 by easy.
    rewrite Nat.gcd_comm in H, H0.
    apply pow_coprime with (k := k) in H. apply pow_coprime with (k := k) in H0.
    assert (p ^ k > 2) by (apply prime_power_lb; easy).
    assert ((((x + y) * (modinv (x + y) (p^k))) * ((x - y) * (modinv (x - y) (p^k)))) mod p ^ k = 0). {
      replace (((x + y) * (modinv (x + y) (p^k))) * ((x - y) * (modinv (x - y) (p^k)))) with ((x + y) * (x - y) * ((modinv (x + y) (p^k)) * (modinv (x - y) (p^k)))) by flia.
      rewrite <- Nat.mul_mod_idemp_l by flia H1. rewrite Hdif.
      simpl. rewrite Nat.mod_0_l; flia H1.
    }
    rewrite <- Nat.mul_mod_idemp_l, <- Nat.mul_mod_idemp_r in H2 by flia H1.
    do 2 rewrite modinv_correct in H2 by flia H1.
    rewrite H, H0 in H2. rewrite Nat.mod_small with (a := 1) in H2 by flia H1.
    rewrite Nat.mul_1_r in H2.
    rewrite Nat.mod_small in H2 by flia H1. easy.
Qed.

Lemma mod_sqr_sol :
  forall x y a p k,
    k <> 0 -> prime p -> 2 < p ->
    Nat.gcd a p = 1 ->
    0 < a < p^k -> 0 < x < p^k -> 0 < y < p^k ->
    x ^ 2 mod p^k = a -> y ^ 2 mod p^k = a ->
    y = x \/ y = p^k - x.
Proof.
  intros. bdestruct (y <=? x). apply mod_sqr_sol_aux with (a := a); easy.
  assert (x <= y) by flia H8.
  apply mod_sqr_sol_aux with (a := a) (p := p) (k := k) in H9. 2-10: easy.
  nia.
Qed.

Lemma mod_neg_neq :
  forall x p k,
    k <> 0 -> prime p -> 2 < p ->
    x < p ^ k ->
    x <> p ^ k - x.
Proof.
  intros. intro.
  assert (Nat.divide 2 (p ^ k)) by (exists x; flia H2 H3).
  destruct k. easy. simpl in H4. rewrite Nat.mul_comm in H4. apply Nat.gauss in H4.
  assert (~ Nat.divide 2 p). {
    apply prime_prop. easy. lia.
  }
  easy.
  rewrite pow_coprime. easy. rewrite Nat.gcd_comm.
  apply eq_gcd_prime_small_1. easy. lia.
Qed.

Fixpoint modmul n (f : nat -> bool) N :=
  match n with
  | O => 1
  | S n' => if (f n) then (n * (modmul n' f N)) mod N
           else modmul n' f N
end.

Lemma exists_pos_dec :
  forall n f,
    {forall x, 0 < x <= n -> f x = false} + {exists x, 0 < x <= n /\ f x = true}.
Proof.
  induction n; intros. left. intros. lia.
  destruct (f (S n)) eqn:E.
  - right. exists (S n). split. lia. easy.
  - destruct (IHn f).
    + left. intros. bdestruct (x =? S n). subst. easy. apply e. lia.
    + right. destruct e. exists x. split. lia. easy.
Qed.

Ltac iauto := try lia; auto.

Lemma modmul_same :
  forall n f g N,
    (forall x, 0 < x <= n -> f x = g x) ->
    modmul n f N = modmul n g N.
Proof.
  induction n; intros. easy.
  assert (f (S n) = g (S n)) by (apply H; lia).
  simpl. rewrite H0. rewrite IHn with (g := g). easy.
  intros. apply H. lia.
Qed.

Lemma modmul_coprime :
  forall n f N, 1 < N -> (forall x, 0 < x <= n -> f x = true -> Nat.gcd x N = 1) -> 
    Nat.gcd (modmul n f N) N = 1.
Proof.
  induction n; intros.
  reflexivity.
  simpl. destruct (f (S n)) eqn: H1.
  replace (modmul n f N + n * modmul n f N) with (S n * modmul n f N) by reflexivity.
  rewrite Nat.gcd_mod by lia. rewrite Nat_gcd_1_mul_r. reflexivity.
  rewrite Nat.gcd_comm. apply H0; iauto.
  rewrite Nat.gcd_comm. apply IHn. lia. intros. apply H0; iauto.
  apply IHn. lia. intros. apply H0; iauto.
Qed.

Lemma modmul_update :
  forall n t N x, 0 < N ->
    0 < x <= n -> t x = true -> 
    modmul n t N = (x * modmul n (update t x false) N) mod N.
Proof.
  induction n; intros.
  - lia.
  - bdestruct (x =? S n).
    subst. simpl. rewrite H1. rewrite update_index_eq.
    erewrite modmul_same. reflexivity.
    intros. rewrite update_index_neq; iauto.

    simpl. rewrite update_index_neq by easy. destruct (t (S n)).
    + rewrite IHn with _ _ x; iauto.
      remember (modmul n (update t x false) N) as s.
      rewrite <- Nat.add_mod_idemp_r by lia.
      rewrite Nat.mul_mod_idemp_r by lia.
      rewrite Nat.mul_mod_idemp_r by lia.
      replace (x * (s + n * s)) with (x * s + n * (x * s)) by lia.
      rewrite <- Nat.add_mod by lia.
      reflexivity.
    + rewrite IHn with _ _ x; iauto.
Qed.

Lemma update_false_true :
  forall f x y, (update f x false) y = true <-> (f y = true /\ y <> x).
Proof.
  intros. split. intro. split.
  rewrite <- H. rewrite update_index_neq. reflexivity. intro. subst.
  rewrite update_index_eq in H. discriminate.
  intro. subst.
  rewrite update_index_eq in H. discriminate.
  intro. rewrite update_index_neq. easy. lia. 
Qed.

Lemma two2one_modmul :
  forall n t f a N, (1 < N) ->
    (forall x, 0 < x <= n -> t x = true -> 0 < (f x) <= n) ->
    (forall x, 0 < x <= n -> t x = true -> t (f x) = true) ->
    (forall y, 0 < y <= n -> t y = true -> (exists x, 0 < x <= n /\ t x = true /\ f x = y)) ->
    (forall x, 0 < x <= n -> t x = true -> f (f x) = x) ->
    (forall x, 0 < x <= n -> t x = true -> x <> f x) ->
    (forall x y, 0 < x <= n -> 0 < y <= n -> t x = true -> t y = true -> f x = f y -> y = x) ->
    (forall x, 0 < x <= n -> t x = true -> (x * f x) mod N = a mod N) ->
    modmul n t N = a ^ ((count1 t n) / 2) mod N.
Proof.
  unfold count1.
  induction n; intros.
  { simpl. rewrite Nat.mod_small. reflexivity. apply H. }
  Local Opaque Nat.div.
  simpl. destruct (t (S n)) eqn: HtSn.
  {
    replace (modmul n t N + n * modmul n t N) with ((S n) * modmul n t N) by lia.
    assert (0 < f (S n) <= n).
    { apply H0 in HtSn as H7; try lia. assert (S n <> f (S n)). apply H4; auto. lia. lia.  }
    assert (t (f (S n)) = true).
    { apply H1; try flia; auto.  }
    rewrite modmul_update with _ _ _ (f (S n)) by iauto.
    rewrite <- count_update_false with _ _ (f (S n)) _ by iauto.
    remember (update t (f (S n)) false) as t'.
    simpl Nat.add.
    replace (S (S (count t' 1 n)) / 2) with (1 + count t' 1 n / 2) by now rewrite <- Nat.div_add_l by flia.
    rewrite Nat.pow_add_r. rewrite Nat.pow_1_r.
    rewrite Nat.mul_mod_idemp_r by lia.
    rewrite Nat.mul_assoc.
    rewrite <- Nat.mul_mod_idemp_l by lia.
    rewrite H6 by now try lia.
    rewrite IHn with t' f a _; auto; intros; clear IHn; subst.
    rewrite Nat.mul_mod_idemp_r by lia.
    rewrite Nat.mul_mod_idemp_l by lia. reflexivity.
    {
      assert (H11 := H10).
      rewrite update_index_neq in H10.
      assert (f x <> S n).
      { unfold not. intro. replace (f (S n)) with x in *. rewrite update_index_eq in H11. discriminate.
        rewrite <- H12. symmetry. apply H3. lia. easy. }
      assert (0 < f x ≤ S n).
      { apply H0. lia. easy. }
      lia. unfold not. intro. subst. rewrite update_index_eq in H11. discriminate.
    }
    {
      rewrite update_index_neq.
      apply H1. lia. rewrite update_index_neq in H10. easy. 
      unfold not. intro. subst. rewrite update_index_eq in H10. discriminate.
      unfold not. intro. assert (S n = x). apply H5; iauto.
      rewrite update_index_neq in H10. easy. intro. subst. rewrite update_index_eq in H10. discriminate.
      subst. lia.
    }
    {
      assert (y <> f (S n)).
      { intro. subst. rewrite update_index_eq in H10. discriminate. }
      rewrite update_index_neq in H10 by auto. assert (0 < y ≤ S n) by lia.
      apply H2 in H12. destruct H12 as (x & Hx0 & Hx1 & Hx2). exists x.
      split. assert (x <> S n).
      { intro. subst. auto. } lia.
      split. rewrite update_index_neq. easy.
      intro. subst. rewrite H3 in H9. lia. lia. easy. easy. easy.
    }
    {
     apply H3. lia. assert (x <> f (S n)).
     { intro. subst. rewrite update_index_eq in H10. discriminate. }
     rewrite update_index_neq in H10 by auto. easy.
    }
    {
      apply H4. lia. assert (x <> f (S n)).
      { intro. subst. rewrite update_index_eq in H10. discriminate. }
      rewrite update_index_neq in H10 by auto. easy.
    }
    {
      apply H5; try lia. assert (x <> f (S n)).
      { intro. subst. rewrite update_index_eq in H11. discriminate. }
      rewrite update_index_neq in H11 by auto. easy.
      assert (y <> f (S n)).
      { intro. subst. rewrite update_index_eq in H12. discriminate. }
      rewrite update_index_neq in H12 by auto. easy.
    }
    {
      apply H6. lia. assert (x <> f (S n)).
      { intro. subst. rewrite update_index_eq in H10. discriminate. }
      rewrite update_index_neq in H10 by auto. easy.
    }
  }
  {
    apply IHn with f; clear IHn; auto; intros.
    + assert (0 < x <= S n) by lia. assert (H8i := H8). apply H0 in H8; auto.
      assert (f x <> S n).
      { unfold not. intro. rewrite <- H10 in HtSn. rewrite H1 in HtSn. easy. lia. easy. } lia.
    + apply H1; auto. lia.
    + assert (0 < y <= S n) by flia H7. apply H2 in H9; [| apply H8].
      destruct H9 as (x & Hx1 & Hx2 & Hx3). exists x.
      split; [| split]; iauto.
      assert (x <> S n). { unfold not. intro. subst. contradict Hx2. rewrite HtSn. auto. }
      lia.
    + apply H3; iauto.
    + apply H4; iauto.
    + apply H5; iauto.
    + apply H6; iauto.
  }
Qed. 

(* facts about modinv *)

Lemma modinv_correct_coprime :
  forall a N, 1 < N -> Nat.gcd a N = 1 -> (a * modinv a N) mod N = 1.
Proof.
  intros.
  rewrite modinv_correct by lia. rewrite H0.
  rewrite Nat.mod_small by lia. reflexivity.
Qed.

Lemma modinv_range :
  forall a N, 1 < N -> Nat.gcd a N = 1 -> 0 < modinv a N < N.
Proof.
  intros. split.
  assert (modinv a N <> 0). intro. 
  assert (a <> 0). intro. subst. rewrite Nat.gcd_0_l in H0. lia.
  specialize (modinv_correct_coprime a N H H0) as H3. rewrite H1 in H3. rewrite Nat.mul_0_r in H3.
  rewrite Nat.mod_small in H3 by lia. lia. lia. apply modinv_upper_bound. lia.
Qed.

Lemma modinv_coprime_swap :
  forall a N, 1 < N -> Nat.gcd a N = 1 -> Nat.gcd (modinv a N) N = 1.
Proof.
  intros.
  rewrite Nat.gcd_comm.
  eapply Nat_gcd_1_mul_r_rev.
  rewrite Nat.mul_comm. rewrite <- Nat.gcd_mod by lia.
  rewrite modinv_correct_coprime by now try lia.
  apply Nat.gcd_1_l.
Qed.

Lemma modinv_modinv :
  forall a N, 1 < N -> Nat.gcd a N = 1 -> 0 < a < N -> a = modinv (modinv a N) N.
Proof.
  intros. transitivity (a mod N).
  now rewrite Nat.mod_small by lia.
  transitivity (a * 1 mod N).
  now rewrite Nat.mul_1_r.
  transitivity (a * (modinv a N * modinv (modinv a N) N) mod N).
  rewrite Nat.mul_mod with _ (modinv a N * modinv (modinv a N) N) _ by lia.
  rewrite modinv_correct_coprime. repeat rewrite Nat.mul_1_r. rewrite Nat.mod_mod by lia.
  now rewrite Nat.mod_small by lia. lia.
  now rewrite modinv_coprime_swap by now try lia.
  replace ((a * (modinv a N * modinv (modinv a N) N))) with (modinv (modinv a N) N * (a * modinv a N)) by lia.
  rewrite Nat.mul_mod by lia. rewrite modinv_correct_coprime by now try lia.
  rewrite Nat.mul_1_r. rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small. reflexivity.
  apply modinv_upper_bound. lia.
Qed.

Lemma modinv_injective :
  forall a b N, 1 < N -> Nat.gcd a N = 1 -> Nat.gcd b N = 1 -> 0 < a < N -> 0 < b < N ->
    modinv a N = modinv b N -> a = b.
Proof.
  intros.  transitivity (a mod N).
  now rewrite Nat.mod_small by lia.
  transitivity (a * 1 mod N).
  now rewrite Nat.mul_1_r.
  replace 1 with ((modinv b N * b) mod N).
  rewrite <- H4. rewrite Nat.mul_mod_idemp_r by lia.
  rewrite Nat.mul_assoc. rewrite <- Nat.mul_mod_idemp_l by lia.
  rewrite modinv_correct_coprime by iauto.
  rewrite Nat.mod_small; lia. rewrite Nat.mul_comm.
  rewrite modinv_correct_coprime by iauto.
  reflexivity.
Qed.

Lemma modinv_unique :
  forall a b N, 1 < N -> Nat.gcd a N = 1 -> 0 < b < N -> (a * b) mod N = 1 ->
    b = modinv a N.
Proof.
  intros.
  transitivity (b * (a * modinv a N mod N) mod N).
  rewrite modinv_correct_coprime. rewrite Nat.mod_small. lia. lia. lia. easy.
  rewrite Nat.mul_mod_idemp_r by lia.
  replace (b * (a * modinv a N)) with (a * b * modinv a N) by lia.
  rewrite <- Nat.mul_mod_idemp_l by lia. rewrite H2.
  rewrite Nat.mul_1_l. rewrite Nat.mod_small. reflexivity.
  specialize modinv_range with a N. lia.
Qed.

Lemma modinv_self :
    forall a p k, 2 < p -> prime p -> k <> 0 -> Nat.gcd a (p ^ k) = 1 ->  a = modinv a (p ^ k) -> 
      a = 1 \/ a = (p ^ k) - 1.
Proof.
  intros. 
  assert (2 < p ^ k) by now apply prime_power_lb.
  apply mod_sqr_sol with 1; iauto.
  rewrite H3. apply modinv_range. lia. easy.
  rewrite Nat.pow_1_l. rewrite Nat.mod_small by lia. easy.
  simpl. rewrite H3 at 2. rewrite Nat.mul_1_r. rewrite modinv_correct_coprime.
  reflexivity. lia. easy.
Qed.

Lemma modinv_mul :
  forall a b N, 1 < N -> Nat.gcd a N = 1 -> Nat.gcd b N = 1 ->
    modinv (a*b) N = (modinv a N * modinv b N) mod N.
Proof.
  intros. symmetry. apply modinv_unique. lia.
  apply Nat_gcd_1_mul_l; easy.
  split. assert ((modinv a N * modinv b N) mod N <> 0).
  intro. apply Nat.mod_divide in H2. 
  apply Nat.gauss in H2. apply Nat.divide_pos_le in H2.
  assert (0 < modinv b N < N). apply modinv_range. lia. lia. lia.
  assert (0 < modinv b N < N). apply modinv_range. lia. lia. lia.
  rewrite Nat.gcd_comm.
  apply modinv_coprime_swap. lia. easy. lia. lia.
  apply Nat.mod_upper_bound. lia.
  rewrite Nat.mul_mod_idemp_r by lia.
  replace (a * b * (modinv a N * modinv b N)) with ((a * modinv a N) * (b * modinv b N)) by lia.
  rewrite Nat.mul_mod. rewrite modinv_correct_coprime. rewrite modinv_correct_coprime.
  simpl. rewrite Nat.mod_small. reflexivity. lia. lia. easy. lia. easy. lia.
Qed.

Lemma modinv_mod :
  forall a N, 1 < N -> Nat.gcd a N = 1 -> modinv a N = modinv (a mod N) N.
Proof.
  intros. apply modinv_unique. lia.
  rewrite Nat.gcd_mod. rewrite Nat.gcd_comm. easy. lia.
  apply modinv_range. lia. easy.
  rewrite Nat.mul_mod_idemp_l. apply modinv_correct_coprime. lia. easy. lia.
Qed.

Lemma Wilson_on_prime_power :
  forall p k, k <> 0 -> prime p -> 2 < p ->
  modmul (p ^ k) (fun d : nat => Nat.gcd (p ^ k) d =? 1) (p ^ k) = p ^ k - 1.
Proof.
  intros.
  assert (2 < p ^ k) by now apply prime_power_lb.
  rewrite modmul_update with _ _ _ 1; try lia.
  rewrite modmul_update with _ _ _ (p ^ k - 1); try lia.
  rewrite Nat.mul_mod_idemp_r by lia.
  rewrite Nat.mul_1_l.
  replace (modmul (p ^ k) (update (update (fun d : nat => Nat.gcd (p ^ k) d =? 1) 1 false) (p ^ k - 1) false) (p ^ k)) with 1.
  rewrite Nat.mul_1_r. apply Nat.mod_small. lia.
  rewrite two2one_modmul with _ _ (fun x => modinv x (p ^ k)) 1 _; try lia; intros.
  rewrite Nat.pow_1_l. symmetry. apply Nat.mod_small. lia.

  assert (Nat.gcd x (p ^ k) = 1) as Hxcoprime.
  { apply update_false_true in H4 as (H4 & H5).
    apply update_false_true in H4 as (H4 & H6).
    apply Nat.eqb_eq in H4. rewrite Nat.gcd_comm. easy.
  }
  assert (0 < modinv x (p ^ k) < p ^ k).
  { apply modinv_range. lia. easy. } lia.
  
  apply update_false_true in H4 as (H4 & H5).
  apply update_false_true in H4 as (H4 & H6).
  apply Nat.eqb_eq in H4.
  apply update_false_true. split. apply update_false_true. split.
  rewrite Nat.eqb_eq. rewrite Nat.gcd_comm. rewrite modinv_coprime_swap.
  easy. lia. rewrite Nat.gcd_comm. easy.
  intro. contradict H6. replace x with (x * modinv x (p ^ k)) by lia.
  rewrite <- Nat.mod_small with (x * modinv x (p ^ k)) (p ^ k).
  rewrite modinv_correct_coprime. lia. lia. rewrite Nat.gcd_comm. easy.
  rewrite H7.
  assert (x <> p ^ k). {  intro. subst. rewrite Nat.gcd_diag_nonneg in H4 by lia. lia. }
  lia.
  intro. contradict H5. apply modinv_injective with (p ^ k); try lia.
  rewrite Nat.gcd_comm. easy. rewrite Nat.gcd_comm. rewrite Nat_gcd_sub_diag_l by lia.
  now rewrite Nat.gcd_1_r.  
  assert (x <> p ^ k). {  intro. subst. rewrite Nat.gcd_diag_nonneg in H4 by lia. lia. }
  lia. rewrite H7. apply modinv_unique; try lia. rewrite Nat.gcd_comm. rewrite Nat_gcd_sub_diag_l by lia.
  now rewrite Nat.gcd_1_r.
  replace ((p ^ k - 1) * (p ^ k - 1)) with ((p ^ k - 2) * p ^ k + 1) by lia.
  rewrite Nat.add_mod by lia. rewrite Nat.mod_mul by lia.
  rewrite Nat.add_0_l. rewrite Nat.mod_mod by lia. rewrite Nat.mod_small by lia. reflexivity.

  apply update_false_true in H4 as (H4 & H5).
  apply update_false_true in H4 as (H4 & H6).
  apply Nat.eqb_eq in H4. exists (modinv y (p ^ k)).
  split. assert (0 < modinv y (p^k) < p^k). apply modinv_range. lia.
  rewrite Nat.gcd_comm. easy. lia. split.
  apply update_false_true. split. apply update_false_true. split.
  rewrite Nat.eqb_eq. rewrite Nat.gcd_comm. apply modinv_coprime_swap. lia.
  rewrite Nat.gcd_comm. easy. intro. contradict H6. 
  apply modinv_injective with (p^k). lia. rewrite Nat.gcd_comm. easy.
  rewrite Nat.gcd_1_l. reflexivity.
  assert (y <> p ^ k). {  intro. subst. rewrite Nat.gcd_diag_nonneg in H4 by lia. lia. }
  lia. lia. rewrite H7. apply modinv_unique. lia. rewrite Nat.gcd_1_l. easy. lia.
  rewrite Nat.mod_small by lia. lia.
  intro. contradict H5. apply modinv_injective with (p^k). lia.
  rewrite Nat.gcd_comm. easy. rewrite Nat.gcd_comm. rewrite Nat_gcd_sub_diag_l.
  rewrite Nat.gcd_1_r by lia. easy. lia.
  assert (y <> p ^ k). {  intro. subst. rewrite Nat.gcd_diag_nonneg in H4 by lia. lia. }
  lia. lia. rewrite H7. apply modinv_unique. lia.  rewrite Nat.gcd_comm. rewrite Nat_gcd_sub_diag_l.
  rewrite Nat.gcd_1_r by lia. easy. lia. lia.
  replace ((p ^ k - 1) * (p ^ k - 1)) with ((p ^ k - 2) * p ^ k + 1) by lia.
  rewrite Nat.add_mod by lia. rewrite Nat.mod_mul by lia.
  rewrite Nat.add_0_l. rewrite Nat.mod_mod by lia. rewrite Nat.mod_small by lia. reflexivity.
  rewrite <- modinv_modinv with _ (p^k). easy. lia.
  rewrite Nat.gcd_comm. easy.
  assert (y <> p ^ k). {  intro. subst. rewrite Nat.gcd_diag_nonneg in H4 by lia. lia. } lia.

  apply update_false_true in H4 as (H4 & H5).
  apply update_false_true in H4 as (H4 & H6).
  apply Nat.eqb_eq in H4.
  rewrite <- modinv_modinv with _ (p^k). easy. lia.
  rewrite Nat.gcd_comm. easy.
  assert (x <> p ^ k). {  intro. subst. rewrite Nat.gcd_diag_nonneg in H4 by lia. lia. } lia.

  apply update_false_true in H4 as (H4 & H5).
  apply update_false_true in H4 as (H4 & H6).
  apply Nat.eqb_eq in H4.
  intro. apply modinv_self in H7; iauto.
  rewrite Nat.gcd_comm. easy.

  apply update_false_true in H5 as (H5 & H5a).
  apply update_false_true in H5 as (H5 & H5b).
  apply Nat.eqb_eq in H5.
  apply update_false_true in H6 as (H6 & H6a).
  apply update_false_true in H6 as (H6 & H6b).
  apply Nat.eqb_eq in H6.
  apply modinv_injective with (p^k); iauto.
  rewrite Nat.gcd_comm. easy. rewrite Nat.gcd_comm. easy.
  assert (y <> p ^ k). {  intro. subst. rewrite Nat.gcd_diag_nonneg in H6 by lia. lia. } lia.
  assert (x <> p ^ k). {  intro. subst. rewrite Nat.gcd_diag_nonneg in H5 by lia. lia. } lia.

  apply update_false_true in H4 as (H4 & H5).
  apply update_false_true in H4 as (H4 & H6).
  apply Nat.eqb_eq in H4.
  rewrite modinv_correct_coprime. symmetry. apply Nat.mod_small. lia. lia.
  rewrite Nat.gcd_comm. easy.

  apply update_false_true. split. rewrite Nat.eqb_eq. rewrite Nat_gcd_sub_diag_l.
  rewrite Nat.gcd_1_r. easy. lia. lia.

  rewrite Nat.eqb_eq. apply Nat.gcd_1_r.
Qed.

Definition moddiv x a N := (a * modinv x N) mod N.

Lemma moddiv_correct :
  forall x a N, 1 < N -> Nat.gcd a N = 1 -> Nat.gcd x N = 1 -> (x * moddiv x a N) mod N = a mod N.
Proof.
  intros. unfold moddiv.
  rewrite Nat.mul_mod_idemp_r by lia.
  replace (x * (a * modinv x N)) with (x * modinv x N * a) by lia.
  rewrite <- Nat.mul_mod_idemp_l by lia. rewrite modinv_correct_coprime by now try lia.
  rewrite Nat.mul_1_l. reflexivity.
Qed.

Lemma moddiv_range :
  forall x a N, 1 < N -> Nat.gcd a N = 1 -> Nat.gcd x N = 1 ->
    0 < moddiv x a N < N.
Proof.
  intros. split.
  unfold moddiv. 
  assert ((a * modinv x N) mod N <> 0).
  intro. rewrite Nat.mod_divide in H2.
  apply Nat.gauss in H2.
  apply Nat.divide_pos_le in H2.
  assert (0 < modinv x N < N). apply modinv_range. lia. easy. lia.
  assert (0 < modinv x N < N). apply modinv_range. lia. easy. lia.
  rewrite Nat.gcd_comm. easy. lia. lia.
  unfold moddiv. apply Nat.mod_upper_bound. lia.
Qed.

Lemma moddiv_coprime :
  forall x a N, 1 < N ->  Nat.gcd a N = 1 -> Nat.gcd x N = 1 ->
    Nat.gcd (moddiv x a N) N = 1.
Proof.
  intros. unfold moddiv.
  rewrite Nat.gcd_mod. apply Nat_gcd_1_mul_r.
  rewrite Nat.gcd_comm. easy.
  rewrite Nat.gcd_comm. apply modinv_coprime_swap. lia. easy. lia.
Qed.

Lemma moddiv_moddiv :
  forall x a N, 1 < N ->  Nat.gcd a N = 1 -> Nat.gcd x N = 1 -> 0 < x < N ->
    x = moddiv (moddiv x a N) a N.
Proof.
  intros. unfold moddiv.
  rewrite <- modinv_mod; try lia.
  rewrite modinv_mul; iauto.
  rewrite <- modinv_modinv; iauto.
  rewrite Nat.mul_mod_idemp_r by lia.
  rewrite Nat.mul_assoc.
  rewrite <- Nat.mul_mod_idemp_l by lia.
  rewrite modinv_correct_coprime; iauto.
  rewrite Nat.mul_1_l. rewrite Nat.mod_small. easy. lia.
  apply modinv_coprime_swap. lia. easy.
  apply Nat_gcd_1_mul_l. easy. apply modinv_coprime. lia. rewrite Nat.gcd_comm. easy.
Qed.

Lemma mul_coprime_equal :
    forall x y a N, 1 < N -> Nat.gcd a N = 1 -> 
      0 < x < N -> 0 < y < N -> a * x mod N = a * y mod N -> x = y.
Proof.
  intros.
  eapply Nat_mul_mod_cancel_l with x y _ _ in H0.
  repeat rewrite Nat.mod_small in H0 by lia. easy. easy.
Qed.

Lemma moddiv_injective :
  forall x y a N, 1 < N -> Nat.gcd a N = 1 -> Nat.gcd x N = 1 -> 
    Nat.gcd y N = 1 -> 0 < x < N -> 0 < y < N ->
    moddiv x a N = moddiv y a N -> x = y.
Proof.
  intros. rewrite moddiv_moddiv with x a N; iauto.
  rewrite moddiv_moddiv with y a N; iauto.
  rewrite H5. reflexivity.
Qed.

Lemma moddiv_unique :
  forall x y a N, 1 < N -> Nat.gcd a N = 1 -> Nat.gcd x N = 1 ->
    (x * y) mod N = a mod N -> 0 < y < N -> y = moddiv x a N.
Proof.
  intros. apply mul_coprime_equal with a N; iauto.
  apply moddiv_range; iauto.
  rewrite <- Nat.mul_mod_idemp_l by lia.
  rewrite <- Nat.mul_mod_idemp_l with _ (moddiv x a N) _ by lia.
  rewrite <- (moddiv_correct x a N) at 1 by iauto. rewrite <- H2.
  rewrite Nat.mul_mod_idemp_l by lia. rewrite Nat.mul_mod_idemp_l by lia.
  replace (x * moddiv x a N * y) with (x * y * moddiv x a N) by lia. reflexivity.
Qed.

Lemma moddiv_self_qr :
forall x y a p k, 2 < p -> prime p -> k <> 0 -> Nat.gcd a (p ^ k) = 1 -> Nat.gcd x (p ^ k) = 1 ->
  0 < a < p ^ k -> 0 < x < p ^ k -> 0 < y < p ^ k ->
  y * y mod (p^k) = a mod (p^k) ->  x = moddiv x a (p ^ k) -> 
  x = y \/ x = (p ^ k) - y.
Proof.
  intros.
  apply mod_sqr_sol with a; iauto.
  eapply pow_coprime_rev. apply H1. auto.
  simpl. rewrite Nat.mul_1_r. rewrite H7. rewrite Nat.mod_small. easy. lia.
  simpl. rewrite H8 at 2. rewrite Nat.mul_1_r. rewrite moddiv_correct; iauto.
  rewrite Nat.mod_small by lia. easy.
Qed.

Lemma moddiv_self_not_qr :
forall x a p k, 2 < p -> prime p -> k <> 0 -> Nat.gcd a (p ^ k) = 1 -> Nat.gcd x (p ^ k) = 1 ->
  0 < a < p^k -> 0 < x < p^k -> (forall x, 0 < x < p^k -> x^2 mod p^k <> a) ->
  x <> moddiv x a (p ^ k).
Proof.
  intros. intro.
  apply H6 in H5 as H5x. contradict H5x.
  simpl. rewrite Nat.mul_1_r. rewrite H7 at 2. rewrite moddiv_correct by iauto.
  apply Nat.mod_small. lia.
Qed.

Lemma Euler_criterion_not_qr :
  forall a p k,
    k <> 0 -> prime p -> 2 < p -> a < p^k -> (Nat.gcd a p = 1) ->
    (forall x, 0 < x < p^k -> x^2 mod p^k <> a) ->
    a ^ (φ (p^k) / 2) mod p^k = p^k - 1.
Proof.
  intros. unfold φ, coprimes.
  assert (2 < p ^ k) by now apply prime_power_lb.
  assert (Nat.gcd a (p ^ k) = 1) by now apply pow_coprime.
  rewrite <- count_filter_seq.
  replace (count (fun d : nat => Nat.gcd (p ^ k) d =? 1) 1 (p ^ k)) with (count1 (fun d : nat => Nat.gcd (p ^ k) d =? 1) (p ^ k)) by reflexivity.
  rewrite <- two2one_modmul with _ _ (fun x => moddiv x a (p ^ k)) _ _; intros. 
  rewrite Wilson_on_prime_power; iauto.
  lia.

  rewrite Nat.eqb_eq in H8.
  assert (0 < moddiv x a (p ^ k) < p ^ k). apply moddiv_range; iauto. rewrite Nat.gcd_comm. easy. lia.
  
  rewrite Nat.eqb_eq in H8.
  rewrite Nat.eqb_eq. rewrite Nat.gcd_comm. apply moddiv_coprime; iauto.
  rewrite Nat.gcd_comm. easy.

  rewrite Nat.eqb_eq in H8. exists (moddiv y a (p^k)).
  split. assert (0 < moddiv y a (p ^ k) < p ^ k). apply moddiv_range; iauto.
  rewrite Nat.gcd_comm. easy. lia. split.
  rewrite Nat.eqb_eq. rewrite Nat.gcd_comm. apply moddiv_coprime; iauto.
  rewrite Nat.gcd_comm. easy. rewrite <- moddiv_moddiv; iauto.
  rewrite Nat.gcd_comm. easy.
  assert (y <> p^k). { intro. subst. rewrite Nat.gcd_diag_nonneg in H8 by lia. lia. } lia.

  rewrite Nat.eqb_eq in H8.
  rewrite <- moddiv_moddiv; iauto.
  rewrite Nat.gcd_comm. easy.
  assert (x <> p^k). { intro. subst. rewrite Nat.gcd_diag_nonneg in H8 by lia. lia. } lia.

  rewrite Nat.eqb_eq in H8.
  apply moddiv_self_not_qr; iauto.
  rewrite Nat.gcd_comm. easy.
  assert (a <> p^k). { intro. subst. rewrite Nat.gcd_diag_nonneg in H6 by lia. lia. }
  assert (a <> 0). { intro. subst. rewrite Nat.gcd_0_l in H6. lia. } lia.
  assert (x <> p^k). { intro. subst. rewrite Nat.gcd_diag_nonneg in H8 by lia. lia. } lia.

  rewrite Nat.eqb_eq in H9.
  rewrite Nat.eqb_eq in H10.
  apply moddiv_injective with a (p ^ k); iauto.
  now rewrite Nat.gcd_comm. now rewrite Nat.gcd_comm.
  assert (y <> p^k). { intro. subst. rewrite Nat.gcd_diag_nonneg in H10 by lia. lia. } lia.
  assert (x <> p^k). { intro. subst. rewrite Nat.gcd_diag_nonneg in H9 by lia. lia. } lia.

  rewrite Nat.eqb_eq in H8.
  apply moddiv_correct; iauto. rewrite Nat.gcd_comm. easy.
Qed.

Lemma Euler_criterion_qr :
  forall a p k,
    k <> 0 -> prime p -> 2 < p -> a < p^k -> Nat.gcd a p = 1 ->
    (exists x, 0 < x < p^k /\ x^2 mod p^k = a) ->
    a ^ (φ (p^k) / 2) mod p^k = 1.
Proof.
  intros. assert (2 < p ^ k) by now apply prime_power_lb.
  assert (Nat.gcd a (p ^ k) = 1) by now apply pow_coprime.
  unfold φ, coprimes. rewrite <- count_filter_seq.
  destruct H4 as (x0 & ? & ?).
  rewrite <- count_update_false with _ _ x0 _; iauto.
  rewrite <- count_update_false with _ _ (p ^ k - x0) _; iauto.
  remember (update (update (fun d : nat => Nat.gcd (p ^ k) d =? 1) x0 false) (p ^ k - x0) false) as t'.
  replace (S (S (count t' 1 (p ^ k))) / 2) with (1 + count t' 1 (p ^ k) / 2) by now rewrite <- Nat.div_add_l by flia.
  rewrite Nat.pow_add_r. simpl. rewrite Nat.mul_1_r.
  rewrite <- Nat.mul_mod_idemp_r by lia.
  replace (count t' 1 (p ^ k)) with (count1 t' (p ^ k)) by reflexivity.
  rewrite <- two2one_modmul with _ _ (fun x => moddiv x a (p ^ k)) _ _; intros.
  apply mul_coprime_equal with (p ^ k - 1) (p ^ k). lia.
  rewrite Nat.gcd_comm. rewrite Nat_gcd_sub_diag_l. apply Nat.gcd_1_r. lia.
  split. assert (a * modmul (p ^ k) t' (p ^ k) mod (p ^ k) <> 0).
  intro. apply Nat.mod_divide in H8; try lia. apply Nat.divide_gcd_iff' in H8.
  assert (1 <> p ^ k) by lia. contradict H9. rewrite <- H8. symmetry.
  apply Nat_gcd_1_mul_r. rewrite Nat.gcd_comm. easy. rewrite Nat.gcd_comm. apply modmul_coprime; iauto.
  intros. subst. rewrite update_false_true in H10. rewrite update_false_true in H10. destruct H10.
  destruct H7. rewrite <- Nat.eqb_eq. rewrite Nat.gcd_comm. easy. lia.
  apply Nat.mod_upper_bound. lia. lia.
  rewrite Nat.mul_1_r. rewrite Nat.mul_mod_idemp_r by lia.
  rewrite Nat.mul_assoc. rewrite Nat.mul_mod by lia.
  replace ((p ^ k - 1) * a mod p ^ k) with (x0 * (p ^ k - x0) mod p ^ k).
  rewrite <- Nat.mul_mod by lia.
  rewrite <- Nat.mul_assoc. rewrite <- Nat.mul_mod_idemp_r by lia. rewrite Heqt'. clear Heqt' t'.
  rewrite <- modmul_update. rewrite <- modmul_update.
  rewrite Wilson_on_prime_power by iauto. rewrite Nat.mod_small by lia. easy.
  lia. lia. rewrite Nat.eqb_eq. rewrite Nat_gcd_1_mul_r_rev with _ _ x0. easy.
  rewrite <- Nat.gcd_mod by lia. replace (x0 * x0) with (x0 ^ 2) by (simpl; lia).
  rewrite H7. easy. lia. lia.
  rewrite update_false_true. rewrite Nat_gcd_sub_diag_l by lia. split.
  rewrite Nat.eqb_eq. 
  (* Nat.gcd (p ^ k) x0 = 1 *)
  rewrite Nat_gcd_1_mul_r_rev with _ _ x0. easy.
  rewrite <- Nat.gcd_mod by lia. replace (x0 * x0) with (x0 ^ 2) by (simpl; lia).
  rewrite H7. easy.
  (* p ^ k - x0 <> x0 *)
  intro. apply Nat.add_sub_eq_nz in H8; iauto. replace (x0 + x0) with (2 * x0) in H8 by lia.
  assert (Nat.gcd 2 (p ^ k) = 1). apply pow_coprime. apply eq_primes_gcd_1; iauto. reflexivity.
  rewrite <- H8 in H9. apply Nat_gcd_1_mul_r_rev in H9. rewrite Nat.gcd_diag_nonneg in H9; iauto.

  rewrite Nat.mul_sub_distr_r. rewrite Nat.mul_sub_distr_l. rewrite Nat.mul_1_l.
  
  rewrite Nat.div_mod with (x0 * x0) (p ^ k) by lia.
  assert (x0 * p ^ k >= (p ^ k * (x0 * x0 / p ^ k) + (x0 * x0) mod p ^ k)).
  rewrite <- Nat.div_mod by lia. apply Nat.mul_le_mono_pos_l; lia.
  assert ((x0 * p ^ k >= (p ^ k * (x0 * x0 / p ^ k)))) by lia.
  rewrite Nat.sub_add_distr. rewrite <- Nat_mod_add_r_mul_l with _ _ 1 by lia.
  rewrite <- Nat_mod_add_r_mul_l with (p ^ k * a - a) _ 1 by lia.
  repeat rewrite Nat.mul_1_r. rewrite <- Nat.add_sub_swap by nia.
  rewrite <- Nat.add_sub_swap with _ _ a by nia.
  rewrite <- Nat.add_sub_assoc. rewrite <- Nat.add_sub_assoc by lia.
  replace (x0 * p ^ k - p ^ k * (x0 * x0 / p ^ k)) with ((x0 - x0 * x0 / p ^ k) * p ^ k) by nia.
  rewrite Nat_mod_add_l_mul_r by lia. rewrite Nat_mod_add_l_mul_l by lia.
  replace (x0 * x0) with (x0 ^ 2) by (simpl; lia). rewrite H7. reflexivity.
  assert ((x0 * x0) mod p ^ k < p ^ k). apply Nat.mod_upper_bound. lia. lia.

  lia. assert (0 < moddiv x a (p ^ k) < p ^ k). apply moddiv_range; iauto.
  rewrite Heqt' in *. rewrite Nat.gcd_comm. rewrite update_false_true in H9. 
  rewrite update_false_true in H9. destruct H9. destruct H9. rewrite Nat.eqb_eq in H9. easy. lia.
  
  rewrite Heqt' in *.
  rewrite update_false_true in H9. 
  rewrite update_false_true in H9. destruct H9. destruct H9. rewrite Nat.eqb_eq in H9.
  rewrite update_false_true. rewrite update_false_true. split. split.
  rewrite Nat.eqb_eq. rewrite Nat.gcd_comm. rewrite moddiv_coprime; iauto. rewrite Nat.gcd_comm.
  easy. 
  (* moddiv x a (p ^ k) <> x0 *)
  intro. contradict H11. apply moddiv_injective with a (p ^ k); iauto.
  rewrite Nat.gcd_comm. easy. rewrite Nat.gcd_comm.
  rewrite Nat_gcd_1_mul_r_rev with _ _ x0. easy.
  rewrite <- Nat.gcd_mod by lia. replace (x0 * x0) with (x0 ^ 2) by (simpl; lia). rewrite H7. easy.
  assert (x <> p ^ k). { intro. subst. rewrite Nat.gcd_diag_nonneg in H9 by lia. lia. } lia.
  rewrite H12. apply moddiv_unique; iauto.
  rewrite Nat.gcd_comm.
  rewrite Nat_gcd_1_mul_r_rev with _ _ x0. easy.
  rewrite <- Nat.gcd_mod by lia. replace (x0 * x0) with (x0 ^ 2) by (simpl; lia). rewrite H7. easy.
  replace (x0 * x0) with (x0 ^ 2) by (simpl; lia). rewrite H7. rewrite Nat.mod_small. easy. lia.
  (* moddiv x a (p ^ k) <> p ^ k - x0 *)
  intro. contradict H10. apply moddiv_injective with a (p ^ k); iauto.
  rewrite Nat.gcd_comm. easy.
  rewrite Nat.gcd_comm. rewrite Nat_gcd_sub_diag_l by lia.
  rewrite Nat_gcd_1_mul_r_rev with _ _ x0. easy.
  rewrite <- Nat.gcd_mod by lia. replace (x0 * x0) with (x0 ^ 2) by (simpl; lia). rewrite H7. easy.
  assert (x <> p ^ k). { intro. subst. rewrite Nat.gcd_diag_nonneg in H9 by lia. lia. } lia.
  rewrite H12. apply moddiv_unique; iauto. rewrite Nat.gcd_comm. rewrite Nat_gcd_sub_diag_l by lia.
  rewrite Nat_gcd_1_mul_r_rev with _ _ x0. easy.
  rewrite <- Nat.gcd_mod by lia. replace (x0 * x0) with (x0 ^ 2) by (simpl; lia).
  rewrite H7. easy.
  replace ((p ^ k - x0) * (p ^ k - x0)) with ((p ^ k - x0) ^ 2) by (simpl; lia).
  rewrite <- neg_sqr_mod by lia. rewrite H7. rewrite Nat.mod_small; iauto.
  
  exists (moddiv y a (p ^ k)).
  rewrite Heqt' in *.
  rewrite update_false_true in H9. 
  rewrite update_false_true in H9. destruct H9. destruct H9. rewrite Nat.eqb_eq in H9.
  split. assert (0 < moddiv y a (p ^ k) < p ^ k). apply moddiv_range; iauto.
  rewrite Nat.gcd_comm. easy. lia. split.
  rewrite update_false_true. rewrite update_false_true. split. split.
  rewrite Nat.eqb_eq. rewrite Nat.gcd_comm. apply moddiv_coprime; iauto. rewrite Nat.gcd_comm.
  easy.
  intro. contradict H11. apply moddiv_injective with a (p ^ k); iauto.
  rewrite Nat.gcd_comm. easy. rewrite Nat.gcd_comm.
  rewrite Nat_gcd_1_mul_r_rev with _ _ x0. easy.
  rewrite <- Nat.gcd_mod by lia. replace (x0 * x0) with (x0 ^ 2) by (simpl; lia). rewrite H7. easy.
  assert (y <> p ^ k). { intro. subst. rewrite Nat.gcd_diag_nonneg in H9 by lia. lia. } lia.
  rewrite H12. apply moddiv_unique; iauto.
  rewrite Nat.gcd_comm.
  rewrite Nat_gcd_1_mul_r_rev with _ _ x0. easy.
  rewrite <- Nat.gcd_mod by lia. replace (x0 * x0) with (x0 ^ 2) by (simpl; lia). rewrite H7. easy.
  replace (x0 * x0) with (x0 ^ 2) by (simpl; lia). rewrite H7. rewrite Nat.mod_small. easy. lia.
  intro. contradict H10. apply moddiv_injective with a (p ^ k); iauto.
  rewrite Nat.gcd_comm. easy.
  rewrite Nat.gcd_comm. rewrite Nat_gcd_sub_diag_l by lia.
  rewrite Nat_gcd_1_mul_r_rev with _ _ x0. easy.
  rewrite <- Nat.gcd_mod by lia. replace (x0 * x0) with (x0 ^ 2) by (simpl; lia). rewrite H7. easy.
  assert (y <> p ^ k). { intro. subst. rewrite Nat.gcd_diag_nonneg in H9 by lia. lia. } lia.
  rewrite H12. apply moddiv_unique; iauto. rewrite Nat.gcd_comm. rewrite Nat_gcd_sub_diag_l by lia.
  rewrite Nat_gcd_1_mul_r_rev with _ _ x0. easy.
  rewrite <- Nat.gcd_mod by lia. replace (x0 * x0) with (x0 ^ 2) by (simpl; lia).
  rewrite H7. easy.
  replace ((p ^ k - x0) * (p ^ k - x0)) with ((p ^ k - x0) ^ 2) by (simpl; lia).
  rewrite <- neg_sqr_mod by lia. rewrite H7. rewrite Nat.mod_small; iauto.
  rewrite <- moddiv_moddiv; iauto. rewrite Nat.gcd_comm. easy.
  assert (y <> p ^ k). { intro. subst. rewrite Nat.gcd_diag_nonneg in H9 by lia. lia. } lia.

  rewrite Heqt' in *.
  rewrite update_false_true in H9. 
  rewrite update_false_true in H9. destruct H9. destruct H9. rewrite Nat.eqb_eq in H9.
  rewrite <- moddiv_moddiv; iauto. rewrite Nat.gcd_comm. easy.
  assert (x <> p ^ k). { intro. subst. rewrite Nat.gcd_diag_nonneg in H9 by lia. lia. } lia.

  rewrite Heqt' in *.
  rewrite update_false_true in H9. 
  rewrite update_false_true in H9. destruct H9. destruct H9. rewrite Nat.eqb_eq in H9.
  intro.
  assert (x = x0 \/ x = p ^ k - x0). apply moddiv_self_qr with a; iauto.
  rewrite Nat.gcd_comm. easy.
  assert (a <> p ^ k). { intro. rewrite H13 in *. rewrite Nat.gcd_diag_nonneg in H6 by lia. lia. }
  assert (a <> 0).  { intro. rewrite H14 in *. rewrite Nat.gcd_0_l in H6. lia. } lia.
  assert (x <> p ^ k). { intro. subst. rewrite Nat.gcd_diag_nonneg in H9 by lia. lia. } lia.
  replace (x0 * x0) with (x0 ^ 2) by (simpl; lia). rewrite H7. rewrite Nat.mod_small by lia. easy.
  destruct H13. easy. easy.
  
  rewrite Heqt' in *.
  rewrite update_false_true in *. 
  rewrite update_false_true in *. destruct H10. destruct H10. 
  destruct H11. destruct H11. rewrite Nat.eqb_eq in H10, H11.
  apply moddiv_injective with a (p ^ k); iauto.
  now rewrite Nat.gcd_comm. now rewrite Nat.gcd_comm.
  assert (y <> p ^ k). { intro. subst. rewrite Nat.gcd_diag_nonneg in H11 by lia. lia. } lia.
  assert (x <> p ^ k). { intro. subst. rewrite Nat.gcd_diag_nonneg in H10 by lia. lia. } lia.

  rewrite Heqt' in *.
  rewrite update_false_true in H9. 
  rewrite update_false_true in H9. destruct H9. destruct H9. rewrite Nat.eqb_eq in H9.
  rewrite moddiv_correct; iauto. now rewrite Nat.gcd_comm.

  rewrite update_false_true. split. rewrite Nat.eqb_eq. rewrite Nat_gcd_sub_diag_l by lia.
  rewrite Nat_gcd_1_mul_r_rev with _ _ x0. easy.
  rewrite <- Nat.gcd_mod by lia. replace (x0 * x0) with (x0 ^ 2) by (simpl; lia).
  rewrite H7. easy.
  intro. apply Nat.add_sub_eq_nz in H8; iauto. replace (x0 + x0) with (2 * x0) in H8 by lia.
  assert (Nat.gcd 2 (p ^ k) = 1). apply pow_coprime. apply eq_primes_gcd_1; iauto. reflexivity.
  rewrite <- H8 in H9. apply Nat_gcd_1_mul_r_rev in H9. rewrite Nat.gcd_diag_nonneg in H9; iauto.
  
  rewrite Nat.eqb_eq. rewrite Nat_gcd_1_mul_r_rev with _ _ x0. easy.
  rewrite <- Nat.gcd_mod by lia. replace (x0 * x0) with (x0 ^ 2) by (simpl; lia).
  rewrite H7. easy.
Qed.

Lemma φ_odd_prime_pow :
  forall p k,
    k <> 0 -> prime p -> 2 < p ->
    φ (p ^ k) = 2 * (φ (p ^ k) / 2)   /\   φ (p ^ k) / 2 <> 0.
Proof.
  intros.
  specialize (prime_pow_φ _ H0 _ H) as T.
  rewrite prime_φ with (p := p) in T by easy.
  assert (p mod 2 = 1) by (apply odd_prime; try easy; try lia).
  remember 2 as tmp. replace 1 with (1 mod 2) in H2 by easy. subst.
  apply Nat_eq_mod_sub_0 in H2.
  assert (φ (p ^ k) mod 2 = 0). {
    rewrite T. rewrite <- Nat.mul_mod_idemp_r by easy. rewrite H2.
    rewrite Nat.mul_0_r. easy.
  }
  apply Nat.mod_divide in H3. 2: easy.
  destruct H3.
  assert (φ (p ^ k) / 2 = x) by (rewrite H3; apply Nat.div_mul; easy).
  assert (0 < φ (p ^ k)). {
    apply φ_pos. specialize (prime_power_lb p k H H0 H1). flia.
  }
  rewrite H4. flia H3 H5.
Qed.

Lemma qr_d2p_lt :
  forall a r p k,
    k <> 0 -> prime p -> 2 < p -> a < p^k ->
    (exists x, 0 < x < p^k /\ x^2 mod p^k = a) ->
    Order a r (p ^ k) ->
    d2p r < d2p (φ (p ^ k)).
Proof.
  intros.
  assert (Nat.gcd a p = 1) as Ha. apply pow_coprime_rev with k. lia. apply Order_rel_prime with r. lia. easy.
  specialize (Euler_criterion_qr _ _ _ H H0 H1 H2 Ha H3) as G.
  apply Order_factor_mod1 with (r := r) in G.
  assert (φ (p ^ k) = 2 * (φ (p ^ k) / 2) /\ (φ (p ^ k) / 2 <> 0)) by (apply φ_odd_prime_pow; easy).
  destruct H5. rewrite H5. rewrite d2p_double. 2: easy.
  specialize (d2p_factor _ _ H6 G). flia.
  lia. easy.
Qed.

Lemma not_qr_d2p_eq :
  forall a r p k,
    k <> 0 -> prime p -> 2 < p -> a < p^k ->
    (forall x, 0 < x < p^k -> x^2 mod p^k <> a) ->
    Order a r (p ^ k) ->
    d2p r = d2p (φ (p ^ k)).
Proof.
  intros.
  assert (Nat.gcd a p = 1) as Ha. apply pow_coprime_rev with k. lia. apply Order_rel_prime with r. lia. easy.
  specialize (Euler_criterion_not_qr _ _ _ H H0 H1 H2 Ha H3) as G.
  assert (φ (p ^ k) = 2 * (φ (p ^ k) / 2) /\ (φ (p ^ k) / 2 <> 0)) by (apply φ_odd_prime_pow; easy).
  destruct H5.
  assert (p ^ k > 2) by (apply prime_power_lb; easy).
  assert (a ^ (φ (p ^ k) / 2) mod p ^ k <> 1) by flia G H7.
  assert (0 < p ^ k) by lia.
  specialize (Order_not_factor  _ _ _ _ H9 H4 H8) as T.
  specialize (Order_factor_φ _ _ _ H9 H4) as T2.
  rewrite H5 in T2.
  apply d2p_stuck in T2. 2: easy.
  rewrite H5. rewrite d2p_double. 2: easy.
  easy.
Qed.

Lemma qr_dec :
  forall a p, {forall x, 0 < x <= p -> x ^ 2 mod p <> a} + {exists x, 0 < x <= p /\ x ^ 2 mod p = a}.
Proof.
  intros. destruct (exists_pos_dec p (fun x => x ^ 2 mod p =? a)).
  - left. intros. specialize (e x H). apply Nat.eqb_neq in e. easy.
  - right. intros. destruct e as [x [? ?]]. exists x. split. apply H. apply Nat.eqb_eq in H0. easy.
Qed.

Definition qr_dec_b a p := if (qr_dec a p) then false else true.

Lemma two2one_mapping_img :
  forall n m t1 t2 f g,
    (forall x, 0 < x <= n -> t1 x = true -> 0 < (f x) <= m) ->
    (forall x, 0 < x <= n -> t1 x = true -> t2 (f x) = true) ->
    (forall a, 0 < a <= m -> t2 a = true -> (exists x, 0 < x <= n /\ t1 x = true /\ f x = a)) ->
    (forall x, 0 < x <= n -> t1 x = true -> 0 < (g x) <= n) ->
    (forall x, 0 < x <= n -> t1 x = true -> t1 (g x) = true) ->
    (forall x, 0 < x <= n -> t1 x = true -> g (g x) = x) ->
    (forall x, 0 < x <= n -> t1 x = true -> f x = f (g x)) ->
    (forall x, 0 < x <= n -> t1 x = true -> x <> g x) ->
    (forall x y, 0 < x <= n -> 0 < y <= n -> t1 x = true -> t1 y = true -> f x = f y -> y = x \/ y = g x) ->
    count1 t1 n = 2 * count1 t2 m.
Proof.
  unfold count1.
  induction n; intros.
  - rewrite count_eq with (f := t2) (g := (fun i => false)).
    rewrite count_all_false. reflexivity.
    destruct (exists_pos_dec m t2). 
    intros. apply e. lia.
    destruct e as [a [Ha Ha']]. specialize (H1 a Ha Ha').
    destruct H1. flia H1.
  - simpl. destruct (t1 (S n)) eqn:ESn.
    + remember (update t1 (g (S n)) false) as t3.
      assert (0 < g (S n) <= S n) by (apply H2; try easy; try flia).
      assert (S n <> g (S n)) by (apply H6; try easy; try flia).
      assert (t1 (g (S n)) = true) by (apply H3; try easy; try flia).
      assert (count t3 1 n + 1 = count t1 1 n). {
        assert (count t1 1 n <> 0). {
          apply count_nonzero. exists (g (S n)). split; try lia. easy.
        }
        rewrite Heqt3. rewrite count_update. flia H11.
        flia H8 H9. easy.
      }
      rewrite <- H11.
      remember (update t2 (f (S n)) false) as t4.
      assert (0 < f (S n) <= m) by (apply H; try easy; try flia).
      assert (t2 (f (S n)) = true) by (apply H0; try easy; try flia).
      assert (count t4 1 m + 1 = count t2 1 m). {
        assert (count t2 1 m <> 0). 
        { apply count_nonzero. exists (f (S n)). split; try lia. easy. }
        rewrite Heqt4. rewrite count_update. flia H14.
        lia. easy.
      }
      rewrite <- H14.
      rewrite (IHn m t3 t4 f g). simpl. flia.
      * intros. apply H. flia H15.
        assert (x <> (g (S n))) by (intro; rewrite H17, Heqt3, update_index_eq in H16; easy).
        rewrite Heqt3, update_index_neq in H16. easy. flia H17.
      * intros. rewrite Heqt4.
        assert (x <> (g (S n))) by (intro; rewrite H17, Heqt3, update_index_eq in H16; easy).
        assert (t1 x = true) by (rewrite Heqt3, update_index_neq in H16; try easy; try flia H17).
        assert (f x <> f (S n)). {
          intro. apply H7 in H19; try easy; try flia H15.
          destruct H19. flia H15 H19.
          assert (g (S n) = g (g x)) by (rewrite H19; easy).
          rewrite H4 in H20 by (try easy; try flia H15). flia H17 H20.
        }
        rewrite update_index_neq by flia H19.
        apply H0; try easy; try flia H15.
      * intros.
        assert (a <> f (S n)) by (intro; rewrite H17, Heqt4, update_index_eq in H16; easy).
        assert (t2 a = true) by (rewrite Heqt4, update_index_neq in H16; try easy; try flia H17).
        destruct H1 with (a := a) as [x [Hx1 [Hx2 Hx3]]]. easy. easy.
        assert (x <> S n) by (intro; subst; easy).
        assert (x <> g (S n)). {
          intro. rewrite H20 in Hx3. rewrite <- Hx3 in H17.
          rewrite <- H5 in H17. easy. flia. easy.
        }
        exists x. split. flia Hx1 H19.
        split. rewrite Heqt3. rewrite update_index_neq. easy. flia H20. easy.
      * intros.
        assert (x <> (g (S n))) by (intro; rewrite H17, Heqt3, update_index_eq in H16; easy).
        assert (t1 x = true) by (rewrite Heqt3, update_index_neq in H16; try easy; try flia H17).
        assert (0 < g x <= S n) by (apply H2; try easy; try flia H15).
        assert (g x <> S n). {
          intro.
          assert (g (S n) = g (g x)) by (rewrite H20; easy).
          rewrite H4 in H21 by (try easy; try flia H15). flia H17 H21.
        }
        flia H19 H20.
      * intros.
        assert (x <> (g (S n))) by (intro; rewrite H17, Heqt3, update_index_eq in H16; easy).
        assert (t1 x = true) by (rewrite Heqt3, update_index_neq in H16; try easy; try flia H17).
        assert (t1 (g x) = true) by (apply H3; try easy; try flia H15).
        assert (g x <> g (S n)). {
          intro. assert (g (g x) = g (g (S n))) by (rewrite H20; easy).
          do 2 rewrite H4 in H21 by (try easy; try flia H15). flia H15 H21.
        }
        rewrite Heqt3. rewrite update_index_neq. easy. flia H20.
      * intros.
        assert (x <> (g (S n))) by (intro; rewrite H17, Heqt3, update_index_eq in H16; easy).
        assert (t1 x = true) by (rewrite Heqt3, update_index_neq in H16; try easy; try flia H17).
        apply H4. flia H15. easy.
      * intros.
        assert (x <> (g (S n))) by (intro; rewrite H17, Heqt3, update_index_eq in H16; easy).
        assert (t1 x = true) by (rewrite Heqt3, update_index_neq in H16; try easy; try flia H17).
        apply H5. flia H15. easy.
      * intros.
        assert (x <> (g (S n))) by (intro; rewrite H17, Heqt3, update_index_eq in H16; easy).
        assert (t1 x = true) by (rewrite Heqt3, update_index_neq in H16; try easy; try flia H17).
        apply H6. flia H15. easy.
      * intros.
        assert (x <> (g (S n))) by (intro; rewrite H20, Heqt3, update_index_eq in H17; easy).
        assert (y <> (g (S n))) by (intro; rewrite H21, Heqt3, update_index_eq in H18; easy).
        assert (t1 x = true) by (rewrite Heqt3, update_index_neq in H17; try easy; try flia H20).
        assert (t1 y = true) by (rewrite Heqt3, update_index_neq in H18; try easy; try flia H21).
        apply H7. flia H15. flia H16. easy. easy. easy.
    + rewrite (IHn m t1 t2 f g). simpl. flia.
      * intros; apply H; try easy; try flia H8.
      * intros; apply H0; try easy; try flia H8.
      * intros. destruct (H1 a) as [x [Hx1 [Hx2 Hx3]]]. easy. easy.
        assert (x <> S n). {
          intro. rewrite H10 in Hx2. rewrite Hx2 in ESn. easy.
        }
        exists x. split. flia H10 Hx1. easy.
      * intros.
        assert (0 < g x <= S n) by (apply H2; try easy; try flia H8).
        assert (g x <> S n). {
          intro.
          assert (t1 (g x) = true) by (apply H3; try easy; try flia H8).
          rewrite H11, ESn in H12. easy.
        }
        flia H10 H11.
      * intros; apply H3; try easy; try flia H8.
      * intros; apply H4; try easy; try flia H8.
      * intros; apply H5; try easy; try flia H8.
      * intros; apply H6; try easy; try flia H8.
      * intros; apply H7; try easy; try flia H8 H9.
Qed.

Lemma qr_half :
  forall p k,
    k <> 0 -> prime p -> 2 < p ->
    count1 (fun x => Nat.gcd x (p^k) =? 1) (p^k) =
      2 * count1 (fun x => (Nat.gcd x (p^k) =? 1) && qr_dec_b x (p^k)) (p^k).
Proof.
  intros.
  remember (fun x => x ^ 2 mod (p^k)) as f.
  remember (fun x => p ^ k - x) as g.
  assert (2 < p ^ k) by (apply prime_power_lb; easy).
  apply two2one_mapping_img with (f := f) (g := g); intros.
  - rewrite Heqf. split.
    rewrite Nat.eqb_eq in H4.
    assert ((x ^ 2) mod (p ^ k) <> 0) by (apply sqr_mod_prime_pow_pos; easy).
    flia H5.
    assert (x ^ 2 mod (p ^ k) < p ^ k) by (apply Nat.mod_upper_bound; lia).
    flia H5.
  - rewrite andb_true_iff. rewrite Nat.eqb_eq in H4. split.
    + rewrite Heqf. rewrite Nat.eqb_eq.
      rewrite Nat.gcd_mod by flia H2.
      rewrite Nat.gcd_comm. apply Nat_gcd_1_pow_l. apply H4.
    + unfold qr_dec_b. destruct (qr_dec (f x) (p ^ k)).
      specialize (n x H3). rewrite Heqf in n. easy.
      easy.
  - rewrite andb_true_iff in H4. destruct H4. rewrite Nat.eqb_eq in H4.
    unfold qr_dec_b in H5. destruct (qr_dec a (p ^ k)). easy.
    destruct e as [x [? ?]]. exists x. split. easy.
    split. rewrite Nat.eqb_eq. apply sqr_gcd with (a := a); easy.
    rewrite Heqf. easy.
  - rewrite Heqg.
    assert (x <> p ^ k). {
      intro. rewrite H5 in H4. rewrite Nat.eqb_eq in H4. rewrite Nat.gcd_diag_nonneg in H4 by flia.
      flia H2 H4.
    }
    flia H3 H5.
  - rewrite Nat.eqb_eq in *. rewrite Heqg.
    rewrite Nat.gcd_comm. rewrite Nat_gcd_sub_diag_l by flia H3.
    rewrite Nat.gcd_comm. easy.
  - rewrite Heqg. flia H3.
  - rewrite Heqf. rewrite Heqg.
    apply neg_sqr_mod; flia H2 H3.
  - rewrite Heqg.
    assert (x <> p ^ k). {
      intro. rewrite H5 in H4. rewrite Nat.eqb_eq in H4. rewrite Nat.gcd_diag_nonneg in H4 by flia.
      flia H2 H4.
    }
    apply mod_neg_neq; try easy; flia H3 H5.
  - rewrite Heqg. apply mod_sqr_sol with (a := f x); try easy.
    + rewrite Nat.eqb_eq in H5, H6.
      apply pow_coprime_rev in H5. 2: easy.
      rewrite Heqf.
      rewrite Nat.gcd_comm. rewrite <- prime_mod_pos by easy.
      rewrite mod_pow_twice by flia H H1.
      replace (x ^ 2) with (x * x) by (simpl; flia).
      intro.
      assert ((x * x * ((modinv x p) * (modinv x p))) mod p = 0). {
        rewrite <- Nat.mul_mod_idemp_l by lia. rewrite H8.
        rewrite Nat.mul_0_l. apply Nat.mod_small. lia.
      }
      replace (x * x * (modinv x p * modinv x p)) with ((x * (modinv x p)) * (x * (modinv x p))) in H9 by flia.
      rewrite <- Nat.mul_mod_idemp_l, <- Nat.mul_mod_idemp_r in H9 by flia H1.
      rewrite modinv_correct in H9 by flia H1.
      rewrite H5 in H9.
      rewrite Nat.mod_small with (a := 1) in H9 by flia H1.
      rewrite Nat.mod_small in H9 by flia H1. flia H9.
    + rewrite Heqf. rewrite Nat.eqb_eq in *. split.
      assert (x ^ 2 mod p ^ k <> 0) by (apply sqr_mod_prime_pow_pos; easy).
      flia H8.
      apply Nat.mod_upper_bound. flia H2.
    + rewrite Nat.eqb_eq in *.
      assert (x <> p ^ k). {
        intro. rewrite H8 in H5. rewrite Nat.gcd_diag_nonneg in H5 by flia.
        flia H2 H5.
      }
      flia H3 H8.
    + rewrite Nat.eqb_eq in *.
      assert (y <> p ^ k). {
        intro. rewrite H8 in H6. rewrite Nat.gcd_diag_nonneg in H6 by flia.
        flia H2 H6.
      }
      flia H4 H8.
    + rewrite Heqf. easy.
    + rewrite H7. rewrite Heqf. easy.
Qed.

Lemma not_qr_half :
  forall p k,
    k <> 0 -> prime p -> 2 < p ->
    count1 (fun x => Nat.gcd x (p^k) =? 1) (p^k) =
      2 * count1 (fun x => (Nat.gcd x (p^k) =? 1) && ¬ (qr_dec_b x (p^k))) (p^k).
Proof.
  intros.
  assert (count1 (fun x => Nat.gcd x (p^k) =? 1) (p^k) = 2 * count1 (fun x => (Nat.gcd x (p^k) =? 1) && qr_dec_b x (p^k)) (p^k)) by (apply qr_half; easy).
  assert (count1 (fun x : nat => (Nat.gcd x (p ^ k) =? 1) && qr_dec_b x (p ^ k)) (p^k) + count1 (fun x : nat => (Nat.gcd x (p ^ k) =? 1) && ¬ (qr_dec_b x (p ^ k))) (p^k) = count1 (fun x => Nat.gcd x (p^k) =? 1) (p^k)) by apply count_complement.
  lia.
Qed.

Lemma d2p_half :
  forall p k d,
    k <> 0 -> prime p -> 2 < p ->
    count1 (fun x => Nat.gcd x (p^k) =? 1) (p^k) <= 
      2 * count1 (fun x => (Nat.gcd x (p^k) =? 1) && ¬ (d2p (ord x (p^k)) =? d)) (p^k).
Proof.
  intros.
  assert (2 < p ^ k) by (apply prime_power_lb; easy).
  assert (forall a b, a <= b -> 2 * a <= 2 * b) by (intros; lia).
  bdestruct (d =? d2p (φ (p ^ k))).
  - rewrite qr_half by easy. apply H3.
    apply count_implies. intros.
    rewrite andb_true_iff in *. destruct H6.
    split; rewrite Nat.eqb_eq in *. easy.
    rewrite <- negb_false_iff, negb_involutive.
    apply Nat.eqb_neq. intro. subst.
    unfold qr_dec_b in H7. destruct qr_dec in H7. easy.
    assert (Order x (ord x (p ^ k)) (p ^ k)) by (apply ord_Order; lia).
    apply qr_d2p_lt in H4; try easy. flia H4 H8.
    bdestruct (x =? p^k). subst. rewrite Nat.gcd_diag_nonneg in H6 by flia H2.
    flia H2 H6. flia H5 H9.
    destruct e as [y [? ?]]. exists y. split.
    bdestruct (y =? p ^ k). rewrite H11 in H10.
    replace ((p ^ k) ^ 2) with ((p ^ k) * (p ^ k)) in H10 by (simpl; flia).
    rewrite <- Nat.mul_mod_idemp_l in H10 by flia H2.
    rewrite Nat.mod_same in H10 by flia H2. rewrite Nat.mul_0_l in H10.
    rewrite Nat.mod_small in H10 by flia H2. flia H5 H10.
    flia H9 H11.
    easy.
  - rewrite not_qr_half by easy. apply H3.
    apply count_implies. intros.
    rewrite andb_true_iff in *. destruct H6.
    split; rewrite Nat.eqb_eq in *. easy.
    rewrite <- negb_false_iff, negb_involutive.
    apply Nat.eqb_neq. intro. subst.
    unfold qr_dec_b in H7. destruct qr_dec in H7. 2: easy.
    assert (Order x (ord x (p ^ k)) (p ^ k)) by (apply ord_Order; lia).
    apply not_qr_d2p_eq in H8; try easy. 
    bdestruct (x =? p^k). subst. rewrite Nat.gcd_diag_nonneg in H6 by flia H2.
    flia H2 H6. flia H5 H9.
    intros. apply n. flia H9.
Qed.

Local Opaque Nat.div.
Lemma reduction_factor_order_finding_aux :
  forall p k q,
    k <> 0 -> prime p -> 2 < p -> 2 < q ->
    Nat.gcd (p ^ k) q = 1 ->
    count1 (fun a => Nat.gcd a (p^k * q) =? 1) (p^k * q) <= 
      2 * count1 (fun a => (Nat.gcd a (p^k * q) =? 1) && (((Nat.gcd (a ^ ((ord a (p^k * q)) / 2) - 1) (p^k * q) <? p^k * q) && (1 <? Nat.gcd (a ^ ((ord a (p^k * q)) / 2) - 1) (p^k * q)))  ||  ((Nat.gcd (a ^ ((ord a (p^k * q)) / 2) + 1) (p^k * q) <? p^k * q) && (1 <? Nat.gcd (a ^ ((ord a (p^k * q)) / 2) + 1) (p^k * q))))) (p^k * q).
Proof.
  intros.
  assert (pk_lb : 2 < p ^ k) by (apply prime_power_lb; easy).
  assert (count1 (fun a => (Nat.gcd a (p^k * q) =? 1) && ¬ (d2p (ord (a mod p^k) (p^k)) =? d2p (ord (a mod q) q))) (p^k * q) 
          <= count1 (fun a => (Nat.gcd a (p^k * q) =? 1) && (((Nat.gcd (a ^ ((ord a (p^k * q)) / 2) - 1) (p^k * q) <? p^k * q) && (1 <? Nat.gcd (a ^ ((ord a (p^k * q)) / 2) - 1) (p^k * q)))  ||  ((Nat.gcd (a ^ ((ord a (p^k * q)) / 2) + 1) (p^k * q) <? p^k * q) && (1 <? Nat.gcd (a ^ ((ord a (p^k * q)) / 2) + 1) (p^k * q))))) (p^k * q)). {
    apply count_implies. intros a ? ?.
    rewrite andb_true_iff in H5. destruct H5.
    rewrite H5. simpl.
    rewrite negb_true_iff in H6.
    rewrite Nat.eqb_eq in H5. rewrite Nat.eqb_neq in H6.
    assert (Nat.gcd a (p ^ k) = 1) by (apply Nat_gcd_1_mul_r_rev with (c := q); easy).
    rewrite Nat.mul_comm in H5.
    assert (Nat.gcd a q = 1) by (apply Nat_gcd_1_mul_r_rev with (c := p^k); easy).
    rewrite Nat.mul_comm in H5.
    assert (((Nat.gcd (p ^ k * q) (a ^ (ord a (p ^ k * q) / 2) - 1) < p ^ k * q) /\ (Nat.gcd (p ^ k * q) (a ^ (ord a (p ^ k * q) / 2) - 1) > 1)) \/ ((Nat.gcd (p ^ k * q) (a ^ (ord a (p ^ k * q) / 2) + 1) < p ^ k * q) /\ (Nat.gcd (p ^ k * q) (a ^ (ord a (p ^ k * q) / 2) + 1) > 1))). {
      apply d2p_neq_sufficient with (rp := ord a (p ^ k)) (rq := ord a q); try apply ord_Order; try easy; try flia H1 H2 pk_lb.
      rewrite ord_mod by (try easy; try flia pk_lb).
      rewrite ord_mod with (N := q) by (try easy; try flia H2).
      easy.
    }
    destruct H9.
    bdestruct (1 <? Nat.gcd (a ^ (ord a (p ^ k * q) / 2) - 1) (p ^ k * q)).
    bdestruct (Nat.gcd (a ^ (ord a (p ^ k * q) / 2) - 1) (p ^ k * q) <? p ^ k * q).
    easy.
    rewrite Nat.gcd_comm in H9. flia H9 H11.
    rewrite Nat.gcd_comm in H9. flia H9 H10.
    bdestruct (1 <? Nat.gcd (a ^ (ord a (p ^ k * q) / 2) + 1) (p ^ k * q)).
    bdestruct (Nat.gcd (a ^ (ord a (p ^ k * q) / 2) + 1) (p ^ k * q) <? p ^ k * q).
    rewrite orb_true_r. easy.
    rewrite Nat.gcd_comm in H9. flia H9 H11.
    rewrite Nat.gcd_comm in H9. flia H9 H10.
  }
  assert (count1 (fun a : nat => Nat.gcd a (p ^ k * q) =? 1) (p^k * q)
          <= 2 * count1 (fun a : nat => (Nat.gcd a (p ^ k * q) =? 1) && ¬ (d2p (ord (a mod p ^ k) (p ^ k)) =? d2p (ord (a mod q) q))) (p^k * q)). {
    clear H4.
    assert (G0: Nat.gcd 0 (p ^ k * q) =? 1 = false) by (rewrite Nat.eqb_neq; rewrite Nat.gcd_0_l; flia H2 pk_lb).
    assert (G1: Nat.gcd (p ^ k * q) (p ^ k * q) =? 1 = false) by (rewrite Nat.eqb_neq; rewrite Nat.gcd_diag_nonneg; flia H2 pk_lb).
    rewrite count1_Nsum by easy. rewrite count1_Nsum.
    2 : rewrite G0; tauto. 2 : rewrite G1; tauto.
    assert (T1 : forall x : nat, x < p ^ k * q -> true = true) by (intros; easy).
    assert (T2 : forall i j : nat, i < p ^ k -> j < q -> true = true -> exists x : nat, x < p ^ k * q /\ (x mod p ^ k, x mod q) = (i, j)). {
      intros.
      assert (crt2 i j (p ^ k) q < p ^ k * q) by (apply crt2_upper_bound; flia pk_lb H2).
      exists (crt2 i j (p ^ k) q). split. easy.
      rewrite pair_equal_spec. apply crt2_correct; try easy.
    }
    assert (T3 : forall x : nat, x < p ^ k * q -> x mod p ^ k < p ^ k /\ x mod q < q) by (intros; split; apply Nat.mod_upper_bound; flia H2 pk_lb).
    assert (T4 : forall x : nat,
               x < p ^ k * q ->
               (if Nat.gcd x (p ^ k * q) =? 1 then 1 else 0) = (if Nat.gcd (crt2 (x mod p ^ k) (x mod q) (p ^ k) q) (p ^ k * q) =? 1 then 1 else 0)). {
      intros.
      assert (x = crt2 (x mod p ^ k) (x mod q) (p ^ k) q) by (apply crt2_correct; try easy; try (apply Nat.mod_upper_bound; flia H2 pk_lb)).
      rewrite <- H5. easy.
    }
    assert (T5 : forall x y : nat, x < p ^ k * q -> y < p ^ k * q -> x <> y ->
                            (x mod p ^ k, x mod q) <> (y mod p ^ k, y mod q)). {
      intros. intro. rewrite pair_equal_spec in H7. destruct H7.
      assert (x = crt2 (x mod p ^ k) (x mod q) (p ^ k) q) by (apply crt2_correct; try easy; try (apply Nat.mod_upper_bound; flia H2 pk_lb)).
      assert (y = crt2 (y mod p ^ k) (y mod q) (p ^ k) q) by (apply crt2_correct; try easy; try (apply Nat.mod_upper_bound; flia H2 pk_lb)).
      rewrite H7, H8 in H9. flia H6 H9 H10.
    }
    assert (T6 :  forall x : nat, x < p ^ k * q ->
                           (if (Nat.gcd x (p ^ k * q) =? 1) && ¬ (d2p (ord (x mod p ^ k) (p ^ k)) =? d2p (ord (x mod q) q)) then 1 else 0) =
                           (if (Nat.gcd (crt2 (x mod p ^ k) (x mod q) (p ^ k) q) (p ^ k * q) =? 1) && ¬ (d2p (ord (x mod p ^ k) (p ^ k)) =? d2p (ord (x mod q) q)) then 1 else 0)). {
      intros.
      assert (x = crt2 (x mod p ^ k) (x mod q) (p ^ k) q) by (apply crt2_correct; try easy; try (apply Nat.mod_upper_bound; flia H2 pk_lb)).
      rewrite <- H5. easy.
    }
    rewrite (Nsum2dmask_bijection (p ^ k * q) _ (p ^ k) q (fun i j => if (Nat.gcd (crt2 i j (p^k) q) (p^k * q) =? 1) then 1 else 0) (fun _ _ => true) (fun x => (x mod (p ^ k), x mod q))) by easy.
    rewrite <- Nsum2d_Nsum2dmask by easy. rewrite Nsum2d_swap_order.
    rewrite (Nsum2dmask_bijection (p ^ k * q) _ (p ^ k) q (fun i j => if (Nat.gcd (crt2 i j (p^k) q) (p^k * q) =? 1) && ¬ (d2p (ord i (p ^ k)) =? d2p (ord j q)) then 1 else 0) (fun _ _ => true) (fun x => (x mod (p ^ k), x mod q))) by easy.
    rewrite <- Nsum2d_Nsum2dmask by easy. rewrite Nsum2d_swap_order with (m := q).
    do 2 rewrite <- Nsum2d'_Nsum2d. unfold Nsum2d'.
    rewrite <- Nsum_scale.
    apply Nsum_le. intros.
    assert ((Nat.gcd (crt2 0 x (p ^ k) q) (p ^ k * q) =? 1) = false). {
      unfold crt2. rewrite Nat.gcd_mod by flia H2 pk_lb.
      rewrite Nat.eqb_neq.
      replace (q * modinv q (p ^ k) * 0 + p ^ k * modinv (p ^ k) q * x) with (p ^ k * (modinv (p ^ k) q * x)) by flia.
      rewrite Nat.gcd_mul_mono_l. rewrite Nat.mul_comm.
      apply natmul1. flia pk_lb.
    }
    assert ((Nat.gcd (crt2 (p ^ k) x (p ^ k) q) (p ^ k * q) =? 1) = false). {
      unfold crt2. rewrite Nat.gcd_mod by flia H2 pk_lb.
      rewrite Nat.eqb_neq.
      replace (q * modinv q (p ^ k) * p ^ k + p ^ k * modinv (p ^ k) q * x) with (p ^ k * (q * modinv q (p ^ k) + modinv (p ^ k) q * x)) by flia.
      rewrite Nat.gcd_mul_mono_l. rewrite Nat.mul_comm.
      apply natmul1. flia pk_lb.
    }
    rewrite <- count1_Nsum by easy. rewrite <- count1_Nsum by (try rewrite H5; try rewrite H6; easy).
    bdestruct (Nat.gcd x q =? 1).
    - unfold count1.
      rewrite count_eq with (g := fun a : nat => Nat.gcd a (p ^ k) =? 1) at 1.
      2:{ intros.
          bdestruct (Nat.gcd x0 (p ^ k) =? 1).
          rewrite Nat.eqb_eq. apply gcd_crt2; try easy; try flia pk_lb H2.
          rewrite Nat.eqb_neq. intro. rewrite gcd_crt2 in H10; try easy; try flia pk_lb H2.
      }
      pattern count at 1.
      rewrite count_eq with (g := fun a : nat => (Nat.gcd a (p ^ k) =? 1) && ¬ (d2p (ord a (p ^ k)) =? (d2p (ord x q)))).
      2:{ intros.
          assert (forall a b c, a = b -> a && c = b && c) by (intros a b c Hab; rewrite Hab; easy).
          apply H9.
          bdestruct (Nat.gcd x0 (p ^ k) =? 1).
          rewrite Nat.eqb_eq. apply gcd_crt2; try easy; try flia pk_lb H2.
          rewrite Nat.eqb_neq. intro. rewrite gcd_crt2 in H11; try easy; try flia pk_lb H2.
      }
      apply d2p_half; easy.
    - unfold count1.
      rewrite count_eq with (g := fun _ => false) at 1.
      2:{ intros. rewrite Nat.eqb_neq. intro. rewrite gcd_crt2 in H9; try easy; try flia pk_lb H2.
      }
      pattern count at 1.
      rewrite count_eq with (g := fun _ => false).
      2:{ intros.
          assert (forall a b, a = false -> a && b = false) by (intros a b Ha; rewrite Ha; easy).
          apply H9.
          rewrite Nat.eqb_neq. intro. rewrite gcd_crt2 in H10; try easy; try flia pk_lb H2.
      }
      rewrite count_all_false. easy.
  }
  flia H4 H5.
Qed.

Definition nontriv a N := (1 <? a) && (a <? N).

Definition nontrivgcd a N := nontriv (Nat.gcd a N) N.

Lemma count_ltn :
  forall n, 1 < n -> 
  count1 (fun a => nontrivgcd a n) n + count1 (fun a => Nat.gcd a n =? 1) n = n - 1.
Proof.
  intros.
  replace (n - 1) with (count1 (fun a => a <? n) n).
  2:{
    destruct n. easy.
    unfold count1. simpl. rewrite Nat.ltb_irrefl.
    replace (count (fun a => a <? S n) 1 n) with (count (fun a => true) 1 n).
    rewrite count_all_true. simpl. lia.
    apply count_eq. intros.
    symmetry. apply Nat.ltb_lt. lia.
  }
  replace (count1 (fun a : nat => a <? n) n) with (count1 (fun a : nat => (a <? n) && (Nat.gcd a n =? 1)) n + count1 (fun a : nat => (a <? n) && ¬ (Nat.gcd a n =? 1)) n) by apply count_complement.
  assert (forall n1 n2 n3 n4, n1 = n3 -> n2 = n4 -> n1 + n2 = n4 + n3) by (intros; lia).
  apply H0; apply count_eq; unfold nontrivgcd, nontriv; intros.
  - bdestruct (x =? n).
    + subst. rewrite Nat.gcd_diag, Nat.ltb_irrefl. btauto.
    + bdestruct (Nat.gcd x n =? 1).
      * rewrite H3. rewrite Nat.ltb_irrefl. btauto.
      * bdestruct (x <? n); try lia.
        assert (0 < Nat.gcd x n) by (apply Natgcd_pos; lia).
        bdestruct (1 <? Nat.gcd x n); try lia.
        bdestruct (Nat.gcd x n <? n); try btauto.
        assert (Nat.gcd x n <= x).
        { rewrite Nat.gcd_comm. apply Nat_gcd_le_r. lia.
        }
        lia.
  - bdestruct (x <? n). btauto.
    replace x with n by lia.
    rewrite Nat.gcd_diag. bdestruct (n =? 1); try easy; lia.
Qed.
    
Lemma reduction_factor_order_finding :
  forall p k q,
    k <> 0 -> prime p -> 2 < p -> 2 < q ->
    Nat.gcd (p ^ k) q = 1 ->
    (p^k * q) - 1 <= 2 * count1 (fun a => (nontrivgcd a (p^k * q)) || ((nontrivgcd (a ^ ((ord a (p^k * q)) / 2) - 1) (p^k * q)) || nontrivgcd (a ^ ((ord a (p^k * q)) / 2) + 1) (p^k * q))) (p^k * q - 1).
Proof.
  intros.
  assert (p ^ k > 0) by (apply pow_positive; lia).
  unfold count1.
  rewrite count_orb. rewrite <- count_ltn at 1 by lia.
  specialize (reduction_factor_order_finding_aux p k q H H0 H1 H2 H3) as G.
  assert (count1 (fun a : nat => (Nat.gcd a (p ^ k * q) =? 1) && ((Nat.gcd (a ^ (ord a (p ^ k * q) / 2) - 1) (p ^ k * q) <? p ^ k * q) && (1 <? Nat.gcd (a ^ (ord a (p ^ k * q) / 2) - 1) (p ^ k * q)) || (Nat.gcd (a ^ (ord a (p ^ k * q) / 2) + 1) (p ^ k * q) <? p ^ k * q) && (1 <? Nat.gcd (a ^ (ord a (p ^ k * q) / 2) + 1) (p ^ k * q)))) (p^k * q) = count1 (fun a : nat => ¬ (nontrivgcd a (p ^ k * q)) && (nontrivgcd (a ^ (ord a (p ^ k * q) / 2) - 1) (p ^ k * q) || nontrivgcd (a ^ (ord a (p ^ k * q) / 2) + 1) (p ^ k * q))) (p^k * q - 1)).
  { replace (p^k * q) with (S (p^k * q - 1)) at 1 by lia.
    unfold count1. rewrite count_extend.
    simpl Nat.add. 
    replace (S (p^k * q - 1)) with (p^k * q) by lia.
    rewrite Nat.gcd_diag. bdestruct (p^k * q =? 1); try lia.
    simpl. apply count_eq. intros.
    assert (¬ (nontrivgcd x (p^k * q)) = (Nat.gcd x (p^k * q) =? 1)).
    { unfold nontrivgcd, nontriv.
      bdestruct (Nat.gcd x (p^k * q) =? 1). rewrite H7, Nat.ltb_irrefl. btauto.
      assert (0 < Nat.gcd x (p^k * q)) by (apply Natgcd_pos; lia).
      assert (Nat.gcd x (p^k * q) <= x) by (rewrite Nat.gcd_comm; apply Nat_gcd_le_r; lia).
      bdestruct (1 <? Nat.gcd x (p^k*q)); try lia.
      bdestruct (Nat.gcd x (p^k * q) <? p^k * q); try easy; lia.
    }
    rewrite H7. unfold nontrivgcd, nontriv. btauto.
  }
  rewrite H5 in G. clear H5.
  unfold count1 in *.
  replace (count (fun a : nat => nontrivgcd a (p^k * q)) 1 (p^k * q)) with (count (fun a : nat => nontrivgcd a (p^k * q)) 1 (p^k * q - 1)). lia.
  replace (p^k * q) with (S (p^k * q - 1)) at 2 by lia.
  rewrite count_extend. simpl Nat.add.
  replace (S (p^k * q - 1)) with (p^k * q) by lia.
  unfold nontrivgcd, nontriv. 
  rewrite Nat.gcd_diag, Nat.ltb_irrefl, andb_false_r. easy.
Qed.

Local Transparent Nat.div.
