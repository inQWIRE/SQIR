Require Import Psatz ZArith Znumtheory Btauto.
Require Import QuantumLib.Prelim QuantumLib.VectorStates.
Require Import Examples.Utilities.

(* ============================= *)
(* =   Number theory results   = *)
(* ============================= *)

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> BinNums.Z.
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; intros; nia.

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

Local Opaque Nat.modulo Nat.div Z.mul.
Lemma exteuc_correct :
  forall (t a b : nat),
    (a < t)%nat ->
    let (n, m) := exteuc a b in
    a * n + b * m = Nat.gcd a b.
Proof.
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
Local Transparent Nat.modulo Nat.div Z.mul.

Local Close Scope Z_scope.
Local Open Scope nat_scope.

Lemma natmul1 :
  forall a b,
    b <> 1 ->
    ~(a * b = 1).
Proof.
  intros. intro. destruct a; destruct b; lia.
Qed.

Lemma mul_mod_1_gcd :
  forall a b p,
    a * b mod p = 1 ->
    Nat.gcd a p = 1.
Proof.
  intros. bdestruct (p =? 0). 
  subst. rewrite Nat.gcd_0_r. simpl in H. 
  try lia. (* versions < 8.14 *)
  try (apply mult_is_one in H as [? ?]; assumption). (* version 8.14 *)
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

Lemma Nsum_delete : forall n x f,
  (x < n)%nat ->
  (big_sum (update f x 0) n + f x = big_sum f n)%nat.
Proof.
  induction n; intros. lia.
  simpl. bdestruct (x =? n). subst. rewrite update_index_eq.
  rewrite (big_sum_eq_bounded _ f). lia.
  intros. rewrite update_index_neq. easy. lia.
  assert (x < n)%nat by lia. apply IHn with (f := f) in H1. rewrite <- H1.
  rewrite update_index_neq. lia. easy.
Qed.

(* The main use of Nsum2d (and Nsum2dmask) is the "Nsum2dmask_bijection" lemma. *)
Fixpoint Nsum2d (n m : nat) (f : nat -> nat -> nat) :=
  match n with
  | O => O
  | S n' => Nsum2d n' m f + big_sum (fun i => f n' i) m
  end.

Lemma Nsum2d_eq :
  forall n m f g,
    (forall x y, x < n -> y < m -> f x y = g x y) ->
    Nsum2d n m f = Nsum2d n m g.
Proof.
  intros. induction n. easy.
  simpl. rewrite (big_sum_eq_bounded _ (fun i : nat => g n i)).
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
  simpl. rewrite IHn. rewrite (big_sum_eq_bounded _ (fun _ => 0)).
  rewrite big_sum_0; auto.
  intros. apply H; lia.
  intros. apply H; lia.
Qed.

Lemma Nsum2d_scale :
  forall n m f d,
    Nsum2d n m (fun i j => d * f i j) = d * Nsum2d n m f.
Proof.
  intros. induction n. simpl. flia.
  simpl. rewrite IHn. 
  rewrite Nat.mul_add_distr_l.
  rewrite Nsum_scale. 
  reflexivity.
Qed.

Lemma Nsum2d_eq_d2 :
  forall n m f d,
    (forall x, big_sum (fun i => f x i) m = d) ->
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
  assert (big_sum (f n) m <= big_sum (g n) m). {
    apply Nsum_le. intros. apply H; lia.
  }
  apply Nat.add_le_mono; assumption.
Qed.

Definition Nsum2d' n m (f : nat -> nat -> nat) := big_sum (fun i => big_sum (fun j => f i j) m) n.

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
  induction n; unfold Nsum2d' in *. simpl. rewrite big_sum_0; easy.
  simpl. rewrite IHn. symmetry. apply Nsum_add.
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
  rewrite (big_sum_eq_bounded (fun i : nat => if upd2d t n y false n i then f n i else 0) (update (fun i : nat => if t n i then f n i else 0) y 0)).
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
  rewrite H3. rewrite IHn by easy. 
  rewrite (big_sum_eq_bounded _ (fun i : nat => if t n i then f n i else 0)); auto.
  intros. rewrite upd2d_neq by lia. easy.
Qed.

Lemma Nsum2dmask_allfalse :
  forall n m f t,
    (forall x y, x < n -> y < m -> t x y = false) ->
    Nsum2dmask n m f t = 0.
Proof.
  intros. unfold Nsum2dmask. induction n. easy.
  simpl. rewrite IHn. 
  rewrite (big_sum_eq_bounded _ (fun _ => 0)). 
  rewrite big_sum_constant. rewrite times_n_nat. easy.
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
    big_sum f n = Nsum2dmask p q g t.
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
  symmetry. rewrite (big_sum_eq_bounded _ (fun i : nat => f n i)). easy.
  intros. rewrite H by lia. easy.
  intros. apply H; lia.
Qed.

Lemma Nsum_Nsum2d :
  forall n f,
    big_sum f n = Nsum2d 1 n (fun _ i => f i).
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
  forall p (f : nat -> nat) a b,
    a < p -> b < p -> 1 < p ->
    Nat.gcd a p = 1 ->
    big_sum (fun i => f ((i * a + b) mod p)%nat) p = big_sum f p.
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




(* ============================= *)
(* =   Multiplicative Order    = *)
(* ============================= *)



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
  forall a r N, 0 < N ->
    Order a r N ->
    1 < N.
Proof.
  intros a r N E H.
  destruct (1 <? N)%nat eqn:S.
  - apply Nat.ltb_lt in S; easy.
  - apply Nat.ltb_ge in S. destruct H as [_ [? _]].
    replace N with 1%nat in H by lia. simpl in H. discriminate H.
Qed.

Lemma Order_a_nonzero :
  forall a r N, 0 < N ->
    Order a r N ->
    0 < a.
Proof.
  intros a r n ? H. assert (HN := H). apply Order_N_lb in HN.
  destruct (0 <? a)%nat eqn:E.
  - apply Nat.ltb_lt in E; easy.
  - apply Nat.ltb_ge in E. assert (a=0) by lia. destruct H as [? [? _]]. rewrite H1 in H2. rewrite Nat.pow_0_l in H2. rewrite Nat.mod_0_l in H2 by lia. lia. lia.
  - assumption.
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
  forall a r N, 0 < N ->
    Order a r N ->
    Nat.gcd a N = 1.
Proof.
  intros. destruct (Order_a_inv_ex _ _ _ H0) as [ainv G].
  specialize (Nat.gcd_divide a N) as [[a' Ha] [N' HN]].
  remember (Nat.gcd a N) as g. bdestruct (g =? 1). easy.
  rewrite Ha, HN in G. replace (a' * g * ainv) with (a' * ainv * g) in G by lia.
  rewrite Nat.mul_mod_distr_r in G. specialize (natmul1 ((a' * ainv) mod N') g H1) as T. easy.
  apply Order_N_lb in H0. lia. assumption.
  apply Order_N_lb in H0. lia. assumption.
Qed.

Lemma Order_modinv_correct :
  forall a r N, 0 < N ->
    Order a r N ->
    (a * (modinv a N)) mod N = 1.
Proof.
  intros. specialize (Order_rel_prime _ _ _ H H0) as G.
  apply Order_N_lb in H0.
  rewrite modinv_correct by lia. rewrite G.
  rewrite Nat.mod_small; easy.
  assumption.
Qed.

Lemma inv_pow :
  forall a r N a_inv x, 0 < N ->
    Order a r N ->
    (a * a_inv) mod N = 1 ->
    (a^x * a_inv^x) mod N = 1.
Proof.
  intros. assert (HN := H0). apply Order_N_lb in HN. induction x.
  - simpl. apply Nat.mod_1_l. easy.
  - simpl. rewrite Nat.mul_assoc. rewrite (Nat.mul_shuffle0 a (a^x)%nat a_inv).
    rewrite mult_assoc_reverse with (n:=(a * a_inv)%nat). rewrite <- Nat.mul_mod_idemp_l with (a:=(a * a_inv)%nat); try lia. rewrite H1. rewrite Nat.mul_1_l. apply IHx.
  - assumption.
Qed.

Lemma Pow_minus_aux :
  forall a r N a_inv x d, 0 < N ->
    Order a r N ->
    (a * a_inv) mod N = 1 ->
    a^d mod N = (a^(x + d) * a_inv^x) mod N.
Proof.
  intros. replace (x + d)%nat with (d + x)%nat by lia. rewrite Nat.pow_add_r.
  assert (HN := H0). apply Order_N_lb in HN.
  rewrite <- Nat.mul_assoc. rewrite <- Nat.mul_mod_idemp_r; try lia. rewrite inv_pow with (r:=r); auto. rewrite Nat.mul_1_r. easy.
  assumption.
Qed.

Lemma Pow_minus :
  forall a r N a_inv x1 x2, 0 < N ->
    Order a r N ->
    x1 <= x2 ->
    (a * a_inv) mod N = 1 ->
    a^(x2-x1) mod N = (a^x2 * a_inv^x1) mod N.
Proof.
  intros. rewrite Pow_minus_aux with (r:=r) (a:=a) (x:=x1) (a_inv:=a_inv); try easy. replace (x1 + (x2 - x1))%nat with (x2 - x1 + x1)%nat by lia. rewrite Nat.sub_add; easy.
Qed.

Lemma Pow_diff :
  forall a r N x1 x2, 0 < N ->
    Order a r N ->
    0 <= x1 < r ->
    0 <= x2 < r ->
    x1 < x2 ->
    a^x1 mod N <> a^x2 mod N.
Proof.
  intros. intro.
  assert (Ha_inv := H0). apply Order_a_inv_ex in Ha_inv. destruct Ha_inv as [a_inv Ha_inv].
  assert (HN := H0). apply Order_N_lb in HN.
  assert (a^(x2-x1) mod N = 1).
  rewrite Pow_minus with (r:=r) (a_inv:=a_inv); try lia; try easy.
  rewrite <- Nat.mul_mod_idemp_l; try lia.
  rewrite <- H4. rewrite Nat.mul_mod_idemp_l; try lia.
  rewrite <- Pow_minus with (r:=r); try lia; try easy.
  rewrite Nat.sub_diag. simpl. apply Nat.mod_1_l; easy.
  destruct H0 as [_ [_ Hminimal]].
  specialize (Hminimal (x2 - x1)%nat) as Hcounter.
  assert (0 < x2 - x1 /\ a ^ (x2 - x1) mod N = 1)%nat by lia.
  apply Hcounter in H0. lia.
  assumption.
Qed.

Lemma Pow_diff_neq :
  forall a r N x1 x2, 0 < N ->
    Order a r N ->
    0 <= x1 < r ->
    0 <= x2 < r ->
    x1 <> x2 ->
    a^x1 mod N <> a^x2 mod N.
Proof.
  intros. apply not_eq in H3. destruct H3.
  - apply Pow_diff with (r:=r); easy.
  - apply not_eq_sym. apply Pow_diff with (r:=r); easy.
Qed.

Lemma Pow_pos :
  forall (a r N i : nat), 0 < N ->
    Order a r N ->
    a^i mod N > 0.
Proof.
  intros. unfold gt. destruct (Nat.lt_ge_cases 0 (a ^ i mod N)). easy.
  inversion H1.  exfalso. cut (a^r mod N = 0).
  intros. destruct H0 as (Ha & Hb & Hc). lia.
  assert (N <> 0).
  { assert (1 < N). { apply (Order_N_lb a r _); easy. } lia. }
  destruct (Nat.lt_ge_cases i r).
  - assert (r = (i + (r - i))%nat) by lia.
    rewrite H5. rewrite -> Nat.pow_add_r. rewrite Nat.mul_mod. rewrite H3. simpl.
    apply Nat.mod_0_l.
    easy. easy.
  - assert (r = (i - (i - r))%nat) by lia.
    rewrite H5. specialize (Order_a_inv_ex a r N H0) as e. destruct e.
    rewrite (Pow_minus _ r _ x _ _); try easy; try lia.
    rewrite Nat.mul_mod. rewrite H3. simpl.
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
        contradict H_fk.
          apply (nex_to_forall k n x f H_nex H_lt).
        rewrite <- H_eq; assumption.
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
  forall a r N, 0 < N ->
    Order a r N ->
    r < N.
Proof.
  intros.
  destruct (Nat.lt_ge_cases r N). easy.
  remember (fun i => pred (a^i mod N))%nat as f.
  cut (exists i j, i <= pred r /\ j < i /\ f i = f j).
  - intros. destruct H2 as (i & j & H2 & H3 & H4).
    cut (f i <> f j). easy.
    rewrite Heqf.
    assert (forall (a b : nat), a > 0 -> b > 0 -> a <> b -> pred a <> pred b).
    { intros. lia. }
    apply H5.
    + apply (Pow_pos _ r _ _); easy.
    + apply (Pow_pos _ r _ _); easy.
    + assert (forall T (x y : T), x <> y -> y <> x) by auto.
      apply H6. apply (Pow_diff _ r _ j i); try lia. easy.
  - apply pigeonhole. intros. subst. 
    assert (forall (a b : nat), a > 0 -> b > 0 -> a < b -> pred a < pred b) by (intros; lia).
    apply H3. apply (Pow_pos _ r _ _); easy. destruct H0. auto.
    cut (a^i mod N < N). lia.
    apply Nat.mod_upper_bound. 
    assert (1 < N). { apply (Order_N_lb a r _); easy. } lia.
Qed.
