Require Import Reals Psatz ZArith Znumtheory Btauto Interval.Tactic.
Require Import euler.Asympt euler.Misc euler.Primes euler.Prod.
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

Lemma natmul1 :
  forall a b,
    b <> 1 ->
    ~(a * b = 1).
Proof.
  intros. intro. destruct a; destruct b; try lia.
  destruct b. lia. assert (S a >= 1) by lia. assert (S (S b) >= 2) by lia.
  assert (S a * S (S b) >= 2) by nia. lia.
Qed.

Lemma mul_mod_1_gcd :
  forall a b p,
    a * b mod p = 1 ->
    Nat.gcd a p = 1.
Proof.
  intros. bdestruct (p =? 0). subst. easy.
  bdestruct (p =? 1). subst. easy.
  bdestruct (Nat.gcd a p =? 1). easy.
  destruct (Nat.gcd_divide a p). destruct H4, H3.
  rewrite H3 in H. rewrite H4 in H at 2.
  replace (x0 * Nat.gcd a p * b) with (Nat.gcd a p * (x0 * b)) in H by flia.
  replace (x * Nat.gcd a p) with (Nat.gcd a p * x) in H by flia.
  rewrite Nat.mul_mod_distr_l in H.
  rewrite Nat.mul_comm in H. apply natmul1 in H; easy.
  intro. subst. flia H4 H0.
  intro. rewrite H5 in H4. flia H4 H0.
Qed.

Fixpoint Nsum (n : nat) (f : nat -> nat) :=
  match n with
  | O => O
  | S n' => Nsum n' f + f n'
  end.

Lemma Nsum_eq :
  forall n f g,
    (forall x, x < n -> f x = g x) ->
    Nsum n f = Nsum n g.
Proof.
  intros. induction n. easy.
  simpl. rewrite IHn. rewrite H. easy.
  flia. intros. apply H. flia H0.
Qed.

Lemma Nsum_scale :
  forall n f d,
    Nsum n (fun i => d * f i) = d * Nsum n f.
Proof.
  intros. induction n. simpl. flia. 
  simpl. rewrite IHn. flia.
Qed.

Lemma Nsum_le :
  forall n f g,
    (forall x, x < n -> f x <= g x) ->
    Nsum n f <= Nsum n g.
Proof.
  intros. induction n. simpl. easy.
  simpl.
  assert (f n <= g n) by (apply H; flia).
  assert (Nsum n f <= Nsum n g). {
    apply IHn. intros. apply H. lia.
  }
  lia.
Qed.

Lemma Nsum_add :
  forall n f g,
    Nsum n (fun i => f i + g i) = Nsum n f + Nsum n g.
Proof.
  intros. induction n. easy.
  simpl. rewrite IHn. flia.
Qed.

Lemma Nsum_delete :
  forall n x f,
    x < n ->
    Nsum n (update f x 0) + f x = Nsum n f.
Proof.
  induction n; intros. lia.
  simpl. bdestruct (x =? n). subst. rewrite update_index_eq.
  rewrite Nsum_eq with (g := f). lia.
  intros. rewrite update_index_neq. easy. lia.
  assert (x < n) by lia. apply IHn with (f := f) in H1. rewrite <- H1.
  rewrite update_index_neq. lia. easy.
Qed.

Lemma Nsum_zero :
  forall n, Nsum n (fun _ => 0) = 0.
Proof.
  induction n. easy.
  simpl. rewrite IHn. easy.
Qed.

Fixpoint Nsum2d (n m : nat) (f : nat -> nat -> nat) :=
  match n with
  | O => O
  | S n' => Nsum2d n' m f + Nsum m (fun i => f n' i)
  end.

Lemma Nsum2d_eq :
  forall n m f g,
    (forall x y, x < n -> y < m -> f x y = g x y) ->
    Nsum2d n m f = Nsum2d n m g.
Proof.
  intros. induction n. easy.
  simpl. rewrite Nsum_eq with (g := (fun i : nat => g n i)).
  rewrite IHn. lia.
  intros. apply H; lia.
  intros. apply H; lia.
Qed.

Lemma Nsum2d_allzero :
  forall n m f,
    (forall x y, x < n -> y < m -> f x y = 0) ->
    Nsum2d n m f = 0.
Proof.
  intros. induction n. easy.
  simpl. rewrite IHn. rewrite Nsum_eq with (g := (fun _ => 0)).
  rewrite Nsum_zero. lia.
  intros. apply H; lia.
  intros. apply H; lia.
Qed.

Lemma Nsum2d_scale :
  forall n m f d,
    Nsum2d n m (fun i j => d * f i j) = d * Nsum2d n m f.
Proof.
  intros. induction n. simpl. flia.
  simpl. rewrite IHn. rewrite Nsum_scale. flia.
Qed.

Lemma Nsum2d_eq_d2 :
  forall n m f d,
    (forall x, Nsum m (fun i => f x i) = d) ->
    Nsum2d n m f = n * d.
Proof.
  induction n; intros. easy.
  simpl. rewrite IHn with (d := d). rewrite H. flia.
  apply H.
Qed.

Lemma Nsum2d_le :
  forall n m f g,
    (forall x y, x < n -> y < m -> f x y <= g x y) ->
    Nsum2d n m f <= Nsum2d n m g.
Proof.
  intros. induction n. easy.
  simpl.
  assert (Nsum2d n m f <= Nsum2d n m g). {
    apply IHn. intros. apply H; lia.
  }
  assert (Nsum m (f n) <= Nsum m (g n)). {
    apply Nsum_le. intros. apply H; lia.
  }
  lia.
Qed.

Definition Nsum2d' n m f := Nsum n (fun i => Nsum m (fun j => f i j)).

Lemma Nsum2d'_Nsum2d :
  forall n m f,
    Nsum2d' n m f = Nsum2d n m f.
Proof.
  intros. induction n; unfold Nsum2d' in *. easy.
  simpl. rewrite IHn. easy.
Qed.

Lemma Nsum2d_swap_order :
  forall n m f,
    Nsum2d n m f = Nsum2d m n (fun i j => f j i).
Proof.
  intros. do 2 rewrite <- Nsum2d'_Nsum2d.
  induction n; unfold Nsum2d' in *. simpl. rewrite Nsum_zero. easy.
  simpl. rewrite IHn. rewrite Nsum_add. lia.
Qed.

Definition Nsum2dmask n m f (t : nat -> nat -> bool) := Nsum2d n m (fun i j => if t i j then f i j else 0).

Definition upd2d {A} f x y (a : A) := fun i j => if ((i =? x) && (j =? y)) then a else f i j.

Lemma upd2d_eq :
  forall A x y f a,
    @upd2d A f x y a x y = a.
Proof.
  intros. unfold upd2d. do 2 rewrite Nat.eqb_refl. easy.
Qed.

Lemma upd2d_neq :
  forall A x y f a i j,
    i <> x \/ j <> y ->
    @upd2d A f x y a i j = f i j.
Proof.
  intros. unfold upd2d.
  destruct H. apply Nat.eqb_neq in H. rewrite H. easy.
  apply Nat.eqb_neq in H. rewrite H, andb_false_r. easy.
Qed.

Lemma upd2d_update :
  forall A x y f a, @upd2d A f x y a x = update (f x) y a.
Proof.
  intros. unfold upd2d. rewrite Nat.eqb_refl. easy.
Qed.

Lemma Nsum2dmask_delete_d2 :
  forall m n f t y,
    y < m ->
    Nsum2dmask (S n) m f (upd2d t n y false) + (if (t n y) then f n y else 0) = Nsum2dmask (S n) m f t.
Proof.
  intros. unfold Nsum2dmask. simpl.
  rewrite Nsum2d_eq with (g := (fun i j : nat => if t i j then f i j else 0)).
  rewrite Nsum_eq with (f := (fun i : nat => if upd2d t n y false n i then f n i else 0)) (g := update (fun i : nat => if t n i then f n i else 0) y 0).
  rewrite plus_assoc_reverse. rewrite Nsum_delete. easy.
  easy.
  intros. bdestruct (y =? x). subst. rewrite upd2d_eq. rewrite update_index_eq. easy.
  rewrite upd2d_neq by lia. rewrite update_index_neq by lia. easy.
  intros. rewrite upd2d_neq by lia. easy.
Qed.

Lemma Nsum2dmask_delete :
  forall n m f t x y,
    x < n -> y < m ->
    Nsum2dmask n m f (upd2d t x y false) + (if (t x y) then f x y else 0) = Nsum2dmask n m f t.
Proof.
  induction n. easy.
  intros. bdestruct (x =? n). subst. apply Nsum2dmask_delete_d2. easy.
  assert (x < n) by lia.
  unfold Nsum2dmask in *. simpl.
  assert (forall a b c, a + b + c = (a + c) + b) by (intros; lia).
  rewrite H3. rewrite IHn by easy. rewrite Nsum_eq with (g := (fun i : nat => if t n i then f n i else 0)).
  easy.
  intros. rewrite upd2d_neq by lia. easy.
Qed.

Lemma Nsum2dmask_allfalse :
  forall n m f t,
    (forall x y, x < n -> y < m -> t x y = false) ->
    Nsum2dmask n m f t = 0.
Proof.
  intros. unfold Nsum2dmask. induction n. easy.
  simpl. rewrite IHn. rewrite Nsum_eq with (g := fun _ => 0). rewrite Nsum_zero. easy.
  intros. rewrite H. easy. lia. easy.
  intros. apply H. lia. easy.
Qed.

Lemma pair_neq :
  forall x y i j : nat, (x, y) <> (i, j) -> x <> i \/ y <> j.
Proof.
  intros. bdestruct (x =? i); bdestruct (y =? j); subst; try easy.
  right. easy. left. easy. left. easy.
Qed.

Lemma Nsum2dmask_bijection :
  forall n f p q g (t : nat -> nat -> bool) (map : nat -> nat * nat),
    (forall x, x < n -> let (i, j) := map x in t i j = true) ->
    (forall i j, i < p -> j < q -> t i j = true -> exists x, x < n /\ map x = (i, j)) ->
    (forall x, x < n -> let (i, j) := map x in i < p /\ j < q) ->
    (forall x, x < n -> let (i, j) := map x in f x = g i j) ->
    (forall x y, x < n -> y < n -> x <> y -> map x <> map y) ->
    Nsum n f = Nsum2dmask p q g t.
Proof.
  induction n; intros.
  - assert (forall x y, x < p -> y < q -> t x y = false). {
      intros. specialize (H0 _ _ H4 H5).
      destruct (t x y).
      destruct H0. easy. destruct H0. lia. easy.
    }
    rewrite Nsum2dmask_allfalse by easy. easy.
  - simpl. destruct (map n) as (i, j) eqn:E.
    remember (upd2d t i j false) as u.
    assert (t i j = true). {
      specialize (H n). rewrite E in H. apply H. flia.
    }
    assert (i < p /\ j < q). {
      specialize (H1 n). rewrite E in H1. apply H1. flia.
    }
    assert (f n = g i j). {
      specialize (H2 n). rewrite E in H2. apply H2. flia.
    }
    assert (forall x, x < n -> map n <> map x). {
      intros. specialize (H3 n x). apply H3; flia H7.
    }
    rewrite (IHn f p q g u map). subst. symmetry. rewrite <- Nsum2dmask_delete with (x := i) (y := j).
    rewrite H4, H6. easy. easy. easy.
    + intros. specialize (H7 _ H8). destruct (map x) eqn:E'.
      rewrite E in H7. apply pair_neq in H7. rewrite Hequ.
      rewrite upd2d_neq by flia H7.
      specialize (H x). rewrite E' in H. apply H. flia H8.
    + intros.
      assert (t i0 j0 = true). {
        rewrite Hequ in H10. destruct (t i0 j0) eqn:Et. easy.
        bdestruct (i =? i0).
        - bdestruct (j =? j0). subst. rewrite upd2d_eq in H10. easy.
          rewrite upd2d_neq in H10. rewrite H10 in Et. easy. right. flia H12.
        - rewrite upd2d_neq in H10. rewrite H10 in Et. easy. left. flia H11.
      }
      apply H0 in H11. destruct H11 as [x [? ?]].
      bdestruct (x =? n). subst. rewrite E in H12.
      apply pair_equal_spec in H12. destruct H12.
      subst. rewrite upd2d_eq in H10. easy.
      exists x. split. flia H11 H13. easy. easy. easy.
    + intros. apply H1. flia H8.
    + intros. apply H2. flia H8.
    + intros. apply H3. flia H8. flia H9. easy.
Qed.

Lemma Nsum2d_Nsum2dmask :
  forall n m f t,
    (forall x y, x < n -> y < m -> t x y = true) ->
    Nsum2d n m f = Nsum2dmask n m f t.
Proof.
  induction n; intros. easy.
  unfold Nsum2dmask in *. simpl. rewrite IHn with (t := t).
  symmetry. rewrite Nsum_eq with (g := (fun i : nat => f n i)). easy.
  intros. rewrite H by lia. easy.
  intros. apply H; lia.
Qed.

Lemma Nsum_Nsum2d :
  forall n f,
    Nsum n f = Nsum2d 1 n (fun _ i => f i).
Proof.
  intros. easy.
Qed.

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

Lemma modinv_coprime' :
  forall p q,
    1 < p -> 0 < q ->
    Nat.gcd p q = 1 ->
    Nat.gcd (modinv q p) p = 1.
Proof.
  intros.
  assert ((q * modinv q p) mod p = 1). {
    rewrite modinv_correct, Nat.gcd_comm, H1.
    apply Nat.mod_small. easy. lia.
  }
  rewrite Nat.mul_comm in H2.
  apply mul_mod_1_gcd with (b := q). easy.
Qed.

Lemma modinv_coprime :
  forall p q,
    1 < p ->
    Nat.gcd p q = 1 ->
    Nat.gcd (modinv q p) p = 1.
Proof.
  intros.
  bdestruct (0 <? q). apply modinv_coprime'; easy.
  assert (q = 0) by lia. subst. rewrite Nat.gcd_0_r in H0. lia.
Qed.

Lemma Nsum_coprime_linear :
  forall p f a b,
    a < p -> b < p -> 1 < p ->
    Nat.gcd a p = 1 ->
    Nsum p (fun i => f ((i * a + b) mod p)) = Nsum p f.
Proof.
  intros. rewrite Nsum_Nsum2d, Nsum2d_Nsum2dmask with (t := (fun _ _ => true)).
  2: intros; easy.
  symmetry. apply Nsum2dmask_bijection with (map := fun i => (0, ((i + (p - b)) * modinv a p) mod p)).
  - intros. easy.
  - intros. assert (i = 0) by flia H3. subst.
    exists ((j * a + b) mod p).
    split. apply Nat.mod_upper_bound. flia H.
    rewrite pair_equal_spec. split. easy.
    rewrite <- Nat.mul_mod_idemp_l by flia H.
    rewrite Nat.add_mod_idemp_l by flia H.
    replace (j * a + b + (p - b)) with (j * a + p) by flia H0.
    rewrite <- Nat.add_mod_idemp_r by flia H.
    rewrite Nat.mod_same by flia H. rewrite Nat.add_0_r.
    rewrite Nat.mul_mod_idemp_l by flia H.
    replace (j * a * modinv a p) with (j * (a * modinv a p)) by flia.
    rewrite <- Nat.mul_mod_idemp_r by flia H.
    rewrite modinv_correct by flia H. rewrite H2. rewrite Nat.mod_small with (a := 1) by flia H1.
    rewrite Nat.mul_1_r.
    apply Nat.mod_small. easy.
  - intros. split. flia. apply Nat.mod_upper_bound. flia H.
  - intros.
    rewrite <- Nat.add_mod_idemp_l by flia H.
    rewrite Nat.mul_mod_idemp_l by flia H.
    replace ((x + (p - b)) * modinv a p * a) with ((x + (p - b)) * (a * modinv a p)) by flia.
    rewrite <- Nat.mul_mod_idemp_r by flia H.
    rewrite modinv_correct by flia H. rewrite H2. rewrite Nat.mod_small with (a := 1) by flia H1.
    rewrite Nat.mul_1_r. rewrite Nat.add_mod_idemp_l by flia H.
    replace (x + (p - b) + b) with (x + p) by flia H0.
    rewrite <- Nat.add_mod_idemp_r by flia H.
    rewrite Nat.mod_same by flia H. rewrite Nat.add_0_r.
    rewrite Nat.mod_small; easy.
  - intros. intro. apply pair_equal_spec in H6.
    destruct H6.
    assert (((x + (p - b)) * modinv a p * a + b) mod p = ((y + (p - b)) * modinv a p * a + b) mod p). {
      rewrite <- Nat.add_mod_idemp_l, <- Nat.mul_mod_idemp_l by flia H.
      rewrite H7.
      rewrite Nat.mul_mod_idemp_l, Nat.add_mod_idemp_l by flia H.
      easy.
    }
    replace ((x + (p - b)) * modinv a p * a) with ((x + (p - b)) * (a * modinv a p)) in H8 by flia.
    replace ((y + (p - b)) * modinv a p * a) with ((y + (p - b)) * (a * modinv a p)) in H8 by flia.
    rewrite <- Nat.add_mod_idemp_l, <- Nat.mul_mod_idemp_r, modinv_correct in H8 by flia H.
    rewrite H2, Nat.mod_small with (a := 1), Nat.mul_1_r in H8 by flia H1.
    rewrite Nat.add_mod_idemp_l in H8 by flia H.
    replace (x + (p - b) + b) with (x + p) in H8 by flia H0.
    rewrite <- Nat.add_mod_idemp_r, Nat.mod_same, Nat.add_0_r, Nat.mod_small in H8 by flia H H3.
    symmetry in H8.
    rewrite <- Nat.add_mod_idemp_l, <- Nat.mul_mod_idemp_r, modinv_correct in H8 by flia H.
    rewrite H2, Nat.mod_small with (a := 1), Nat.mul_1_r in H8 by flia H1.
    rewrite Nat.add_mod_idemp_l in H8 by flia H.
    replace (y + (p - b) + b) with (y + p) in H8 by flia H0.
    rewrite <- Nat.add_mod_idemp_r, Nat.mod_same, Nat.add_0_r, Nat.mod_small in H8 by flia H H4.
    flia H5 H8.
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


(* =================================================== *)
(* =  Reduction from Factorization to Order Finding  = *)
(* =================================================== *)

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
  bdestruct (Nat.gcd N (y + 1) =? 0).
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
  forall a r N x,
    Order a r N ->
    a ^ x mod N = 1 ->
    Nat.divide r x.
Proof.
  intros. specialize (Order_rel_prime _ _ _ H) as G.
  assert (2 <= N) by (specialize (Order_N_lb _ _ _ H); lia).
  destruct H as [? [? ?]].
  bdestruct (x =? 0). subst. apply Nat.divide_0_r.
  assert (x >= r). {
    apply H3. split. lia. easy.
  }
  assert (x = r * (x / r) + x mod r) by (apply Nat.div_mod; lia).
  rewrite H6 in H0.
  rewrite Nat.pow_add_r in H0. rewrite Nat.pow_mul_r in H0.
  rewrite <- Nat.mul_mod_idemp_l in H0 by lia.
  rewrite pow_mod in H0. rewrite H2 in H0. rewrite Nat.pow_1_l in H0. rewrite Nat.mod_small with (a := 1) in H0 by lia. rewrite Nat.mul_1_l in H0.
  assert (x mod r < r) by (apply Nat.mod_upper_bound; lia).
  bdestruct (0 <? x mod r).
  assert (0 < x mod r /\ a ^ (x mod r) mod N = 1) by easy.
  apply H3 in H9. lia.
  apply Nat.mod_divide; lia.
Qed.

Lemma Order_factor_φ :
  forall a r N,
    Order a r N ->
    Nat.divide r (φ N).
Proof.
  intros. apply Order_factor_mod1 with (a := a) (N := N). easy.
  assert (2 <= N) by (specialize (Order_N_lb _ _ _ H); lia).
  rewrite φ_φ' by easy. replace 1 with (1 mod N) by (apply Nat.mod_small; lia).
  apply PTotient.euler_fermat_little. lia.
  intro. subst. destruct H as [T [H _]]. rewrite Nat.pow_0_l in H by lia. rewrite Nat.mod_small in H by lia. easy.
  apply Order_rel_prime with (r := r). easy.
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
  forall a r N x,
    Order a r N ->
    a ^ x mod N <> 1 ->
    ~ Nat.divide r x.
Proof.
  intros. intro. destruct H1 as [k ?]. subst.
  rewrite Nat.mul_comm in H0. rewrite Nat.pow_mul_r in H0. rewrite pow_mod in H0.
  assert (1 < N) by (eapply Order_N_lb; apply H).
  destruct H as [_ [? _]]. rewrite H in H0. rewrite Nat.pow_1_l in H0.
  rewrite Nat.mod_small in H0 by easy.
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
  intros. assert (Hpod := H0). assert (Hqod := H1).
  destruct H0 as [Hrp0 [Hrp1 Hrp2]].
  destruct H1 as [Hrq0 [Hrq1 Hrq2]].
  split. bdestruct (Nat.lcm rp rq =? 0). rewrite Nat.lcm_eq_0 in H0. lia. lia.
  assert (1 < p) by (apply (Order_N_lb _ _ _ Hpod)).
  assert (1 < q) by (apply (Order_N_lb _ _ _ Hqod)).
  split.
  - rewrite CRT_1 by easy. split.
    unfold Nat.lcm. rewrite Nat.pow_mul_r. rewrite pow_mod. rewrite Hrp1.
    rewrite Nat.pow_1_l. apply Nat.mod_small. easy.
    rewrite Nat.lcm_comm.
    unfold Nat.lcm. rewrite Nat.pow_mul_r. rewrite pow_mod. rewrite Hrq1.
    rewrite Nat.pow_1_l. apply Nat.mod_small. easy.
  - intros. destruct H2.
    rewrite CRT_1 in H3 by easy. destruct H3.
    apply Order_factor_mod1 with (r := rp) in H3. 2: easy.
    apply Order_factor_mod1 with (r := rq) in H4. 2: easy.
    assert (Nat.divide (Nat.lcm rp rq) r') by (apply Nat.lcm_least; easy).
    apply Nat.divide_pos_le in H5; lia.
Qed.

Definition d2p n := pow_in_n n 2.

Local Opaque Nat.modulo.
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
Local Transparent Nat.modulo.

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
  - intro contra. apply Order_factor_mod1 with (r := r) in contra. 2: easy.
    destruct contra as [x Hx]. rewrite Hx in Hlcm.
    replace (x * r * 2) with (r * (x * 2)) in Hlcm by lia.
    symmetry in Hlcm. rewrite Nat.mul_id_r in Hlcm by flia H Hx.
    flia Hlcm.
  - intro contra.
    apply CRT_neg1 in contra. 2: lia. destruct contra as [Cp Cq].
    assert (Hkp: a ^ k mod p <> 1) by flia Hp Cp.
    apply Order_not_factor with (r := rp) in Hkp. 2: easy.
    assert (Cp': a ^ (2 * k) mod p = 1). {
      rewrite Nat.mul_comm. rewrite Nat.pow_mul_r. rewrite pow_mod. rewrite Cp.
      replace ((p - 1) ^ 2) with (p * (p - 2) + 1) by (simpl; flia Hp).
      rewrite Nat_mod_add_l_mul_l by flia Hp.
      apply Nat.mod_small. flia Hp.
    }
    apply Order_factor_mod1 with (r := rp) in Cp'. 2: easy.
    assert (Hd2prp: d2p rp = S (d2p k)) by (apply d2p_stuck; easy).    
    assert (Hkq: a ^ k mod q <> 1) by flia Hq Cq.
    apply Order_not_factor with (r := rq) in Hkq. 2: easy.
    assert (Cq': a ^ (2 * k) mod q = 1). {
      rewrite Nat.mul_comm. rewrite Nat.pow_mul_r. rewrite pow_mod. rewrite Cq.
      replace ((q - 1) ^ 2) with (q * (q - 2) + 1) by (simpl; flia Hq).
      rewrite Nat_mod_add_l_mul_l by flia Hq.
      apply Nat.mod_small. flia Hq.
    }
    apply Order_factor_mod1 with (r := rq) in Cq'. 2: easy.
    assert (Hd2prq: d2p rq = S (d2p k)) by (apply d2p_stuck; easy).
    flia Hd2prp Hd2prq Hd2p.
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
  assert (p <> 0). {
    intro. subst. simpl in H. easy.
  }
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

Fixpoint cnttrue n (f : nat -> bool) :=
  match n with
  | O => O
  | S n' => if (f n) then S (cnttrue n' f)
           else cnttrue n' f
  end.

Lemma cnttrue_extend :
  forall n f, cnttrue (S n) f = if (f (S n)) then S (cnttrue n f) else cnttrue n f.
Proof.
  intros. easy.
Qed.

Lemma cnttrue_extend_more :
  forall m n f, cnttrue (n + m) f = cnttrue n f + cnttrue m (fun x => f (n + x)).
Proof.
  induction m; intros. simpl. do 2 rewrite Nat.add_0_r. easy.
  simpl.
  replace (n + S m) with (S (n + m)) by flia. simpl.
  destruct (f (S (n + m))). rewrite IHm. lia.
  apply IHm.
Qed.

Lemma cnttrue_allfalse :
  forall n, cnttrue n (fun _ => false) = O.
Proof.
  induction n; intros; simpl; try apply IHn; easy.
Qed.

Lemma cnttrue_same :
  forall n f g,
    (forall x, 0 < x <= n -> f x = g x) ->
    cnttrue n f = cnttrue n g.
Proof.
  induction n; intros. easy.
  assert (f (S n) = g (S n)) by (apply H; lia).
  simpl. rewrite H0. rewrite IHn with (g := g). easy.
  intros. apply H. lia.
Qed.

Lemma cnttrue_over_n_update :
  forall n x f b, x > n -> cnttrue n f = cnttrue n (update f x b).
Proof.
  intros. apply cnttrue_same. intros.
  rewrite update_index_neq. easy. lia.
Qed.

Lemma cnttrue_pos :
  forall n x f, 0 < x <= n -> f x = true -> cnttrue n f > 0.
Proof.
  induction n; intros. lia.
  bdestruct (x =? S n). subst. simpl. rewrite H0. lia.
  assert (cnttrue n f > 0) by (apply IHn with (x := x); try easy; try lia).
  simpl. destruct (f (S n)); lia.
Qed.

Lemma cnttrue_update_t :
  forall n x f b, 0 < x <= n -> f x = true -> cnttrue n (update f x b) = if b then cnttrue n f else (cnttrue n f) - 1.
Proof.
  induction n; intros. lia.
  destruct b. rewrite update_same. easy. easy.
  bdestruct (x =? S n). subst. simpl. rewrite update_index_eq. rewrite H0.
  rewrite <- cnttrue_over_n_update; lia.
  simpl. rewrite update_index_neq by easy. destruct (f (S n)). rewrite IHn by (try easy; try lia).
  assert (cnttrue n f > 0) by (apply cnttrue_pos with (x := x); try easy; try lia).
  lia.
  rewrite IHn. easy. lia. easy.
Qed.

Lemma cnttrue_filter_seq :
  forall n f, cnttrue n f = length (filter f (List.seq 1 n)).
Proof.
  induction n; intros. easy.
  rewrite seq_extend. rewrite filter_app. rewrite app_length.
  rewrite <- IHn. simpl.
  destruct (f (S n)). simpl. lia.
  simpl. lia.
Qed.

Lemma cnttrue_Nsum_aux :
  forall n f,
    f 0 = false ->
    cnttrue n f = Nsum (S n) (fun i => if f i then 1 else 0).
Proof.
  intros. induction n. simpl. rewrite H. easy.
  simpl. rewrite IHn. destruct (f (S n)); simpl; lia.
Qed.

Lemma cnttrue_Nsum :
  forall n f,
    f 0 = false -> f n = false ->
    cnttrue n f = Nsum n (fun i => if f i then 1 else 0).
Proof.
  intros. destruct n. easy.
  simpl. rewrite H0. rewrite cnttrue_Nsum_aux; easy.
Qed.

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

Lemma cnttrue_update_t_false :
  forall n x f, 0 < x <= n -> f x = true -> S (cnttrue n (update f x false)) = cnttrue n f.
Proof.
  intros. 
  assert (cnttrue n f > 0) by now apply cnttrue_pos with x.
  rewrite cnttrue_update_t; iauto.
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
    modmul n t N = a ^ ((cnttrue n t) / 2) mod N.
Proof.
  induction n; intros.
  {
    simpl. replace (0/2) with 0. simpl. rewrite Nat.mod_small. reflexivity.
    apply H. rewrite Nat.div_small; lia.
  }
  Local Opaque Nat.div.
  simpl. destruct (t (S n)) eqn: HtSn.
  {
    replace (modmul n t N + n * modmul n t N) with ((S n) * modmul n t N) by lia.
    assert (0 < f (S n) <= n).
    { apply H0 in HtSn as H7; try lia. assert (S n <> f (S n)). apply H4; auto. lia. lia.  }
    assert (t (f (S n)) = true).
    { apply H1; try flia; auto.  }
    rewrite modmul_update with _ _ _ (f (S n)) by iauto.
    rewrite <- cnttrue_update_t_false with _ (f (S n)) _ by iauto.
    remember (update t (f (S n)) false) as t'.
    replace (S (S (cnttrue n t')) / 2) with (1 + cnttrue n t' / 2) by now rewrite <- Nat.div_add_l by flia.
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
  rewrite <- cnttrue_filter_seq.
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
  unfold φ, coprimes. rewrite <- cnttrue_filter_seq.
  destruct H4 as (x0 & ? & ?).
  rewrite <- cnttrue_update_t_false with _ x0 _; iauto.
  rewrite <- cnttrue_update_t_false with _ (p ^ k - x0) _; iauto.
  remember (update (update (fun d : nat => Nat.gcd (p ^ k) d =? 1) x0 false) (p ^ k - x0) false) as t'.
  replace (S (S (cnttrue (p ^ k) t')) / 2) with (1 + cnttrue (p ^ k) t' / 2) by now rewrite <- Nat.div_add_l by flia.
  rewrite Nat.pow_add_r. simpl. rewrite Nat.mul_1_r.
  rewrite <- Nat.mul_mod_idemp_r by lia.
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
  assert (Nat.gcd a p = 1) as Ha. apply pow_coprime_rev with k. lia. apply Order_rel_prime with r. easy.
  specialize (Euler_criterion_qr _ _ _ H H0 H1 H2 Ha H3) as G.
  apply Order_factor_mod1 with (r := r) in G.
  assert (φ (p ^ k) = 2 * (φ (p ^ k) / 2) /\ (φ (p ^ k) / 2 <> 0)) by (apply φ_odd_prime_pow; easy).
  destruct H5. rewrite H5. rewrite d2p_double. 2: easy.
  specialize (d2p_factor _ _ H6 G). flia.
  easy.
Qed.
  
  
Lemma not_qr_d2p_eq :
  forall a r p k,
    k <> 0 -> prime p -> 2 < p -> a < p^k ->
    (forall x, 0 < x < p^k -> x^2 mod p^k <> a) ->
    Order a r (p ^ k) ->
    d2p r = d2p (φ (p ^ k)).
Proof.
  intros.
  assert (Nat.gcd a p = 1) as Ha. apply pow_coprime_rev with k. lia. apply Order_rel_prime with r. easy.
  specialize (Euler_criterion_not_qr _ _ _ H H0 H1 H2 Ha H3) as G.
  assert (φ (p ^ k) = 2 * (φ (p ^ k) / 2) /\ (φ (p ^ k) / 2 <> 0)) by (apply φ_odd_prime_pow; easy).
  destruct H5.
  assert (p ^ k > 2) by (apply prime_power_lb; easy).
  assert (a ^ (φ (p ^ k) / 2) mod p ^ k <> 1) by flia G H7.
  specialize (Order_not_factor  _ _ _ _ H4 H8) as T.
  specialize (Order_factor_φ _ _ _ H4) as T2.
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
    cnttrue n t1 = 2 * cnttrue m t2.
Proof.
  induction n; intros.
  - rewrite cnttrue_same with (f := t2) (g := (fun i => false)).
    rewrite cnttrue_allfalse. easy.
    destruct (exists_pos_dec m t2). easy.
    destruct e as [a [Ha Ha']]. specialize (H1 a Ha Ha').
    destruct H1. flia H1.
  - simpl. destruct (t1 (S n)) eqn:ESn.
    + remember (update t1 (g (S n)) false) as t3.
      assert (0 < g (S n) <= S n) by (apply H2; try easy; try flia).
      assert (S n <> g (S n)) by (apply H6; try easy; try flia).
      assert (t1 (g (S n)) = true) by (apply H3; try easy; try flia).
      assert (cnttrue n t3 + 1 = cnttrue n t1). {
        assert (cnttrue n t1 > 0). {
          apply cnttrue_pos with (x := g (S n)). flia H8 H9. easy.
        }
        rewrite Heqt3. rewrite cnttrue_update_t. flia H11.
        flia H8 H9. easy.
      }
      rewrite <- H11.
      remember (update t2 (f (S n)) false) as t4.
      assert (0 < f (S n) <= m) by (apply H; try easy; try flia).
      assert (t2 (f (S n)) = true) by (apply H0; try easy; try flia).
      assert (cnttrue m t4 + 1 = cnttrue m t2). {
        assert (cnttrue m t2 > 0) by (apply cnttrue_pos with (x := f (S n)); easy).
        rewrite Heqt4. rewrite cnttrue_update_t. flia H14.
        easy. easy.
      }
      rewrite <- H14.
      rewrite (IHn m t3 t4 f g). flia.
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
    + rewrite (IHn m t1 t2 f g). flia.
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
    cnttrue (p^k) (fun x => Nat.gcd x (p^k) =? 1) =
    2 * cnttrue (p^k) (fun x => (Nat.gcd x (p^k) =? 1) && qr_dec_b x (p^k)).
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

Lemma cnttrue_upper_bound :
  forall n f, cnttrue n f <= n.
Proof.
  induction n; intros. easy.
  simpl. destruct (f (S n)); specialize (IHn f); lia.
Qed.

Lemma cnttrue_complement :
  forall n f g, cnttrue n (fun i => f i && g i) + cnttrue n (fun i => f i && ¬ (g i)) = cnttrue n f.
Proof.
  intros. induction n. easy.
  simpl. destruct (f (S n)); simpl; destruct (g (S n)); simpl; lia.
Qed.

Lemma cnttrue_indicate :
  forall n f g,
    (forall x, 0 < x <= n -> f x = true -> g x = true) ->
    cnttrue n f <= cnttrue n g.
Proof.
  intros. induction n. easy.
  assert (cnttrue n f <= cnttrue n g). {
    apply IHn. intros. apply H. lia. easy.
  }
  simpl. destruct (f (S n)) eqn:Efsn. apply H in Efsn. 2: lia.
  rewrite Efsn. lia.
  destruct (g (S n)); lia.
Qed.

Lemma not_qr_half :
  forall p k,
    k <> 0 -> prime p -> 2 < p ->
    cnttrue (p^k) (fun x => Nat.gcd x (p^k) =? 1) =
    2 * cnttrue (p^k) (fun x => (Nat.gcd x (p^k) =? 1) && ¬ (qr_dec_b x (p^k))).
Proof.
  intros.
  assert (cnttrue (p^k) (fun x => Nat.gcd x (p^k) =? 1) = 2 * cnttrue (p^k) (fun x => (Nat.gcd x (p^k) =? 1) && qr_dec_b x (p^k))) by (apply qr_half; easy).
  assert (cnttrue (p ^ k) (fun x : nat => (Nat.gcd x (p ^ k) =? 1) && qr_dec_b x (p ^ k)) + cnttrue (p ^ k) (fun x : nat => (Nat.gcd x (p ^ k) =? 1) && ¬ (qr_dec_b x (p ^ k))) = cnttrue (p^k) (fun x => Nat.gcd x (p^k) =? 1)) by apply cnttrue_complement.
  lia.
Qed.

Lemma d2p_half :
  forall p k d,
    k <> 0 -> prime p -> 2 < p ->
    cnttrue (p^k) (fun x => Nat.gcd x (p^k) =? 1) <= 2 * cnttrue (p^k) (fun x => (Nat.gcd x (p^k) =? 1) && ¬ (d2p (ord x (p^k)) =? d)).
Proof.
  intros.
  assert (2 < p ^ k) by (apply prime_power_lb; easy).
  assert (forall a b, a <= b -> 2 * a <= 2 * b) by (intros; lia).
  bdestruct (d =? d2p (φ (p ^ k))).
  - rewrite qr_half by easy. apply H3.
    apply cnttrue_indicate. intros.
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
    apply cnttrue_indicate. intros.
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
Lemma reduction_factor_order_finding :
  forall p k q,
    k <> 0 -> prime p -> 2 < p -> 2 < q ->
    Nat.gcd (p ^ k) q = 1 ->
    cnttrue (p^k * q) (fun a => Nat.gcd a (p^k * q) =? 1) <= 2 * cnttrue (p^k * q) (fun a => (Nat.gcd a (p^k * q) =? 1) && (((Nat.gcd (a ^ ((ord a (p^k * q)) / 2) - 1) (p^k * q) <? p^k * q) && (1 <? Nat.gcd (a ^ ((ord a (p^k * q)) / 2) - 1) (p^k * q)))  ||  ((Nat.gcd (a ^ ((ord a (p^k * q)) / 2) + 1) (p^k * q) <? p^k * q) && (1 <? Nat.gcd (a ^ ((ord a (p^k * q)) / 2) + 1) (p^k * q))))).
Proof.
  intros.
  assert (pk_lb : 2 < p ^ k) by (apply prime_power_lb; easy).
  assert (cnttrue (p ^ k * q) (fun a => (Nat.gcd a (p^k * q) =? 1) && ¬ (d2p (ord (a mod p^k) (p^k)) =? d2p (ord (a mod q) q)))
          <= cnttrue (p ^ k * q) (fun a => (Nat.gcd a (p^k * q) =? 1) && (((Nat.gcd (a ^ ((ord a (p^k * q)) / 2) - 1) (p^k * q) <? p^k * q) && (1 <? Nat.gcd (a ^ ((ord a (p^k * q)) / 2) - 1) (p^k * q)))  ||  ((Nat.gcd (a ^ ((ord a (p^k * q)) / 2) + 1) (p^k * q) <? p^k * q) && (1 <? Nat.gcd (a ^ ((ord a (p^k * q)) / 2) + 1) (p^k * q)))))). {
    apply cnttrue_indicate. intros a ? ?.
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
  assert (cnttrue (p ^ k * q) (fun a : nat => Nat.gcd a (p ^ k * q) =? 1)
          <= 2 * cnttrue (p ^ k * q) (fun a : nat => (Nat.gcd a (p ^ k * q) =? 1) && ¬ (d2p (ord (a mod p ^ k) (p ^ k)) =? d2p (ord (a mod q) q)))). {
    clear H4.
    assert (G0: Nat.gcd 0 (p ^ k * q) =? 1 = false) by (rewrite Nat.eqb_neq; rewrite Nat.gcd_0_l; flia H2 pk_lb).
    assert (G1: Nat.gcd (p ^ k * q) (p ^ k * q) =? 1 = false) by (rewrite Nat.eqb_neq; rewrite Nat.gcd_diag_nonneg; flia H2 pk_lb).
    rewrite cnttrue_Nsum by easy. rewrite cnttrue_Nsum.
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
    rewrite <- cnttrue_Nsum by easy. rewrite <- cnttrue_Nsum by (try rewrite H5; try rewrite H6; easy).
    bdestruct (Nat.gcd x q =? 1).
    - rewrite cnttrue_same with (g := fun a : nat => Nat.gcd a (p ^ k) =? 1) at 1.
      2:{ intros.
          bdestruct (Nat.gcd x0 (p ^ k) =? 1).
          rewrite Nat.eqb_eq. apply gcd_crt2; try easy; try flia pk_lb H2.
          rewrite Nat.eqb_neq. intro. rewrite gcd_crt2 in H10; try easy; try flia pk_lb H2.
      }
      pattern cnttrue at 1.
      rewrite cnttrue_same with (g := fun a : nat => (Nat.gcd a (p ^ k) =? 1) && ¬ (d2p (ord a (p ^ k)) =? (d2p (ord x q)))).
      2:{ intros.
          assert (forall a b c, a = b -> a && c = b && c) by (intros a b c Hab; rewrite Hab; easy).
          apply H9.
          bdestruct (Nat.gcd x0 (p ^ k) =? 1).
          rewrite Nat.eqb_eq. apply gcd_crt2; try easy; try flia pk_lb H2.
          rewrite Nat.eqb_neq. intro. rewrite gcd_crt2 in H11; try easy; try flia pk_lb H2.
      }
      apply d2p_half; easy.
    - rewrite cnttrue_same with (g := fun _ => false) at 1.
      2:{ intros. rewrite Nat.eqb_neq. intro. rewrite gcd_crt2 in H9; try easy; try flia pk_lb H2.
      }
      pattern cnttrue at 1.
      rewrite cnttrue_same with (g := fun _ => false).
      2:{ intros.
          assert (forall a b, a = false -> a && b = false) by (intros a b Ha; rewrite Ha; easy).
          apply H9.
          rewrite Nat.eqb_neq. intro. rewrite gcd_crt2 in H10; try easy; try flia pk_lb H2.
      }
      rewrite cnttrue_allfalse. easy.
  }
  flia H4 H5.
Qed.
Local Transparent Nat.div.

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
  rewrite Rsum_extend. rewrite IHl by easy. rewrite seq_extend. rewrite filter_app. rewrite app_length.
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
  forall (n : nat),
    (2 <= n)%nat ->
    (ϕ n) / n >= exp(-2) / (Nat.log2 n ^ 4).
Proof.
  intros. rewrite ϕ_φ_equal by lia. apply φ_lower_bound. easy.
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

