Require Import Coq.btauto.Btauto Coq.NArith.Nnat Bool. 
Require Import Dirac.
Require Import BasicUtility.
Local Open Scope nat_scope.

(* Here we defined the specification of carry value for each bit. *)
(* fb_push is to take a qubit and then push it to the zero position 
        in the bool function representation of a number. *)
Lemma mod_sum_lt :
  forall x y M,
    x < M ->
    y < M ->
    (x + y) mod M < x <-> x + y >= M.
Proof.
  intros. split; intros.
  - assert ((x + y) mod M < x + y) by lia.
    rewrite Nat.div_mod with (y := M) in H2 by lia.
    assert (0 < (x + y) / M) by nia.
    rewrite Nat.div_str_pos_iff in H3 by lia. lia.
  - rewrite Nat.mod_eq by lia.
    assert (1 <= (x + y) / M < 2).
    { split.
      apply Nat.div_le_lower_bound; lia.
      apply Nat.div_lt_upper_bound; lia.
    }
    replace (M * ((x + y) / M)) with M by nia.
    lia.
Qed.


Lemma mod_sum_lt_bool :
  forall x y M,
    x < M ->
    y < M ->
    ¬ (M <=? x + y) = (x <=? (x + y) mod M).
Proof.
  intros. bdestruct (M <=? x + y); bdestruct (x <=? (x + y) mod M); try easy.
  assert ((x + y) mod M < x) by (apply mod_sum_lt; lia). lia.
  assert (x + y >= M) by (apply mod_sum_lt; lia). lia.
Qed.


Definition allfalse := fun (_:nat) => false.

Definition majb a b c := (a && b) ⊕ (b && c) ⊕ (a && c).

Definition fb_push b f : nat -> bool :=
  fun x => match x with
        | O => b
        | S n => f n
        end.

Lemma fb_push_right:
  forall n b f, 0 < n -> fb_push b f n = f (n-1).
Proof.
  intros. induction n. lia.
  simpl. assert ((n - 0) = n) by lia.
  rewrite H0. reflexivity.
Qed.

Lemma fb_push_same : forall b f g, (forall i, fb_push b f i = fb_push b g i) -> f = g.
Proof.
intros.
apply functional_extensionality; intros.
specialize (H (S x)).
rewrite fb_push_right in H; try lia.
rewrite fb_push_right in H; try lia.
simpl in H.
assert (x-0 = x) by lia. rewrite H0 in H. easy. 
Qed.

(* fb_push_n is the n repeatation of fb_push.
Definition fb_push_n n f g : nat -> bool :=
  fun i => if (i <? n) then f i else g (i - n).
*)

(* A function to compile positive to a bool function. *)
Fixpoint pos2fb p : nat -> bool :=
  match p with
  | xH => fb_push true allfalse
  | xI p' => fb_push true (pos2fb p')
  | xO p' => fb_push false (pos2fb p')
  end.

(* A function to compile N to a bool function. *)
Definition N2fb n : nat -> bool :=
  match n with
  | 0%N => allfalse
  | Npos p => pos2fb p
  end.

Definition nat2fb n := N2fb (N.of_nat n).

Definition add_c b x y :=
  match b with
  | false => Pos.add x y
  | true => Pos.add_carry x y
  end.

Fixpoint carry b n f g :=
  match n with
  | 0 => b
  | S n' => let c := carry b n' f g in
           let a := f n' in
           let b := g n' in
           (a && b) ⊕ (b && c) ⊕ (a && c)
  end.

Lemma carry_1 : forall b f g, carry b 1 f g = majb (f 0) (g 0) b.
Proof.
 intros. simpl. unfold majb. easy.
Qed.

Lemma carry_n : forall n b f g, carry b (S n) f g = majb (f n) (g n) (carry b n f g).
Proof.
 intros. simpl. unfold majb. easy.
Qed.

Lemma carry_sym :
  forall b n f g,
    carry b n f g = carry b n g f.
Proof.
  intros. induction n. reflexivity.
  simpl. rewrite IHn. btauto.
Qed.

Lemma carry_false_0_l: forall n f, 
    carry false n allfalse f = false.
Proof.
  unfold allfalse.
  induction n.
  simpl.
  reflexivity.
  intros. simpl.
  rewrite IHn. rewrite andb_false_r.
  reflexivity.
Qed.

Lemma carry_false_0_r: forall n f, 
    carry false n f allfalse = false.
Proof.
  unfold allfalse.
  induction n.
  simpl.
  reflexivity.
  intros. simpl.
  rewrite IHn. rewrite andb_false_r.
  reflexivity.
Qed.

Lemma carry_fbpush :
  forall n a ax ay fx fy,
    carry a (S n) (fb_push ax fx) (fb_push ay fy) = carry (majb a ax ay) n fx fy.
Proof.
  induction n; intros.
  simpl. unfold majb. btauto.
  remember (S n) as Sn. simpl. rewrite IHn. unfold fb_push. subst.
  simpl. easy.
Qed.

Lemma carry_succ :
  forall m p,
    carry true m (pos2fb p) allfalse = pos2fb (Pos.succ p) m ⊕ (pos2fb p) m.
Proof.
  induction m; intros. simpl. destruct p; reflexivity.
  replace allfalse with (fb_push false allfalse).
  2:{ unfold fb_push, allfalse. apply functional_extensionality. intros. destruct x; reflexivity.
  }
  Local Opaque fb_push carry.
  destruct p; simpl.
  rewrite carry_fbpush; unfold majb; simpl. rewrite IHm. reflexivity.
  rewrite carry_fbpush; unfold majb; simpl. rewrite carry_false_0_r. Local Transparent fb_push. simpl. btauto.
  rewrite carry_fbpush; unfold majb; simpl. Local Transparent carry. destruct m; reflexivity.
Qed.

Lemma carry_succ' :
  forall m p,
    carry true m allfalse (pos2fb p) = pos2fb (Pos.succ p) m ⊕ (pos2fb p) m.
Proof.
  intros. rewrite carry_sym. apply carry_succ.
Qed.

Lemma carry_succ0 :
  forall m, carry true m allfalse allfalse = pos2fb xH m.
Proof.
  induction m. easy. 
  replace allfalse with (fb_push false allfalse).
  2:{ unfold fb_push, allfalse. apply functional_extensionality. intros. destruct x; reflexivity.
  }
  rewrite carry_fbpush. unfold majb. simpl. rewrite carry_false_0_l. easy.
Qed.

Lemma carry_add_pos_eq :
  forall m b p q,
    carry b m (pos2fb p) (pos2fb q) ⊕ (pos2fb p) m ⊕ (pos2fb q) m = pos2fb (add_c b p q) m.
Proof.
  induction m; intros. simpl. destruct p, q, b; reflexivity.
  Local Opaque carry.
  destruct p, q, b; simpl; rewrite carry_fbpush; 
    try (rewrite IHm; reflexivity);
    try (unfold majb; simpl; 
         try rewrite carry_succ; try rewrite carry_succ'; 
         try rewrite carry_succ0; try rewrite carry_false_0_l;
         try rewrite carry_false_0_r;
         unfold allfalse; try btauto; try (destruct m; reflexivity)).
Qed.

Lemma carry_add_eq_carry0 :
  forall m x y,
    carry false m (N2fb x) (N2fb y) ⊕ (N2fb x) m ⊕ (N2fb y) m = (N2fb (x + y)) m.
Proof.
  intros.
  destruct x as [|p]; destruct y as [|q]; simpl; unfold allfalse.
  rewrite carry_false_0_l. easy.
  rewrite carry_false_0_l. btauto.
  rewrite carry_false_0_r. btauto.
  apply carry_add_pos_eq.
Qed.

Lemma carry_add_eq_carry1 :
  forall m x y,
    carry true m (N2fb x) (N2fb y) ⊕ (N2fb x) m ⊕ (N2fb y) m = (N2fb (x + y + 1)) m.
Proof.
  intros. 
  destruct x as [|p]; destruct y as [|q]; simpl; unfold allfalse.
  rewrite carry_succ0. destruct m; easy.
  rewrite carry_succ'. replace (q + 1)%positive with (Pos.succ q) by lia. btauto.
  rewrite carry_succ. replace (p + 1)%positive with (Pos.succ p) by lia. btauto.
  rewrite carry_add_pos_eq. unfold add_c. rewrite Pos.add_carry_spec.
  replace (p + q + 1)%positive with (Pos.succ (p + q)) by lia. easy.
Qed.

Definition fbxor f g := fun (i : nat) => f i ⊕ g i.

Definition msma i b f g := fun (x : nat) => if (x <? i) then 
        (carry b (S x) f g ⊕ (f (S x))) else (if (x =? i) then carry b (S x) f g else f x).

Definition msmb i (b : bool) f g := fun (x : nat) => if (x <=? i) then (f x ⊕ g x) else g x.

Definition msmc i b f g := fun (x : nat) => if (x <=? i) then (f x ⊕ g x) else (carry b x f g ⊕ f x ⊕ g x).

Definition sumfb b f g := fun (x : nat) => carry b x f g ⊕ f x ⊕ g x.

Definition negatem i (f : nat -> bool) := fun (x : nat) => if (x <? i) then ¬ (f x) else f x.

Lemma sumfb_correct_carry0 :
  forall x y,
    sumfb false (nat2fb x) (nat2fb y) = nat2fb (x + y).
Proof.
  intros. unfold nat2fb. rewrite Nnat.Nat2N.inj_add.
  apply functional_extensionality. intros. unfold sumfb. rewrite carry_add_eq_carry0. easy.
Qed.

Lemma sumfb_correct_carry1 :
  forall x y,
    sumfb true (nat2fb x) (nat2fb y) = nat2fb (x + y + 1).
Proof.
  intros. unfold nat2fb. do 2 rewrite Nnat.Nat2N.inj_add.
  apply functional_extensionality. intros. unfold sumfb. rewrite carry_add_eq_carry1. easy.
Qed.

Lemma sumfb_correct_N_carry0 :
  forall x y,
    sumfb false (N2fb x) (N2fb y) = N2fb (x + y).
Proof.
  intros. apply functional_extensionality. intros. unfold sumfb. rewrite carry_add_eq_carry0. easy.
Qed.

Lemma pos2fb_Postestbit :
  forall n i,
    (pos2fb n) i = Pos.testbit n (N.of_nat i).
Proof.
  induction n; intros.
  - destruct i; simpl. easy. rewrite IHn. destruct i; simpl. easy. rewrite Pos.pred_N_succ. easy.
  - destruct i; simpl. easy. rewrite IHn. destruct i; simpl. easy. rewrite Pos.pred_N_succ. easy.
  - destruct i; simpl. easy. easy.
Qed.

Lemma N2fb_Ntestbit :
  forall n i,
    (N2fb n) i = N.testbit n (N.of_nat i).
Proof.
  intros. destruct n. easy.
  simpl. apply pos2fb_Postestbit.
Qed.

Lemma Z2N_Nat2Z_Nat2N :
  forall x,
    Z.to_N (Z.of_nat x) = N.of_nat x.
Proof.
  destruct x; easy.
Qed.

Lemma Nofnat_mod :
  forall x y,
    y <> 0 ->
    N.of_nat (x mod y) = ((N.of_nat x) mod (N.of_nat y))%N.
Proof.
  intros. specialize (Zdiv.mod_Zmod x y H) as G.
  repeat rewrite <- Z2N_Nat2Z_Nat2N. rewrite G. rewrite Z2N.inj_mod; lia.
Qed.

Lemma Nofnat_pow :
  forall x y,
    N.of_nat (x ^ y) = ((N.of_nat x) ^ (N.of_nat y))%N.
Proof.
  intros. induction y. easy.
  Local Opaque N.pow. replace (N.of_nat (S y)) with ((N.of_nat y) + 1)%N by lia.
 simpl. rewrite N.pow_add_r. rewrite N.pow_1_r. rewrite Nnat.Nat2N.inj_mul. rewrite IHy. lia.
Qed.

Lemma Ntestbit_lt_pow2n :
  forall x n,
    (x < 2^n)%N ->
    N.testbit x n = false.
Proof.
  intros. apply N.mod_small in H. rewrite <- H. apply N.mod_pow2_bits_high. lia.
Qed.

Lemma Ntestbit_in_pow2n_pow2Sn :
  forall x n,
    (2^n <= x < 2^(N.succ n))%N ->
    N.testbit x n = true.
Proof.
  intros. assert (N.log2 x = n) by (apply N.log2_unique; lia).
  rewrite <- H0. apply N.bit_log2.
  assert (2^n <> 0)%N by (apply N.pow_nonzero; easy).
  lia.
Qed.

Lemma negatem_Nlnot :
  forall (n : nat) (x : N) i,
    negatem n (N2fb x) i = N.testbit (N.lnot x (N.of_nat n)) (N.of_nat i).
Proof.
  intros. unfold negatem. rewrite N2fb_Ntestbit. symmetry.
  bdestruct (i <? n). apply N.lnot_spec_low. lia.
  apply N.lnot_spec_high. lia.
Qed.

Lemma negatem_arith :
  forall n x,
    x < 2^n ->
    negatem n (nat2fb x) = nat2fb (2^n - 1 - x).
Proof.
  intros. unfold nat2fb. apply functional_extensionality; intro i.
  rewrite negatem_Nlnot. rewrite N2fb_Ntestbit.
  do 2 rewrite Nnat.Nat2N.inj_sub. rewrite Nofnat_pow. simpl.
  bdestruct (x =? 0). subst. simpl. rewrite N.ones_equiv. rewrite N.pred_sub. rewrite N.sub_0_r. easy.
  rewrite N.lnot_sub_low. rewrite N.ones_equiv. rewrite N.pred_sub. easy.
  apply N.log2_lt_pow2. assert (0 < x) by lia. lia.
  replace 2%N with (N.of_nat 2) by lia. rewrite <- Nofnat_pow. lia.
Qed.


(* Here, we define the addto / addto_n functions for angle rotation. *)
Definition cut_n (f:nat -> bool) (n:nat) := fun i => if i <? n then f i else allfalse i.
 
Definition fbrev' i n (f : nat -> bool) := fun (x : nat) => 
            if (x <=? i) then f (n - 1 - x) else if (x <? n - 1 - i) 
                         then f x else if (x <? n) then f (n - 1 - x) else f x.
Definition fbrev {A} n (f : nat -> A) := fun (x : nat) => if (x <? n) then f (n - 1 - x) else f x.

Lemma fbrev'_fbrev :
  forall n f,
    0 < n ->
    fbrev n f = fbrev' ((n - 1) / 2) n f.
Proof.
  intros. unfold fbrev, fbrev'. apply functional_extensionality; intro.
  assert ((n - 1) / 2 < n) by (apply Nat.div_lt_upper_bound; lia).
  assert (2 * ((n - 1) / 2) <= n - 1) by (apply Nat.mul_div_le; easy).
  assert (n - 1 - (n - 1) / 2 <= (n - 1) / 2 + 1).
  { assert (n - 1 <= 2 * ((n - 1) / 2) + 1).
    { assert (2 <> 0) by easy.
      specialize (Nat.mul_succ_div_gt (n - 1) 2 H2) as G.
      lia.
    }
    lia.
  }
  IfExpSimpl; easy.
Qed.

Lemma allfalse_0 : forall n, cut_n allfalse n = nat2fb 0.
Proof.
  intros. unfold nat2fb. simpl.
  unfold cut_n.
  apply functional_extensionality; intro.
  bdestruct (x <? n).
  easy. easy.
Qed.

Lemma f_num_aux_0: forall n f x, cut_n f n = nat2fb x 
                -> f n = false -> cut_n f (S n) = nat2fb x.
Proof.
  intros.
  rewrite <- H.
  unfold cut_n.
  apply functional_extensionality.
  intros.
  bdestruct (x0 <? n).
  bdestruct (x0 <? S n).
  easy.
  lia.
  bdestruct (x0 <? S n).
  assert (x0 = n) by lia.
  subst. rewrite H0. easy.
  easy.
Qed.

Definition twoton_fun (n:nat) := fun i => if i <? n then false else if i=? n then true else false.


Definition times_two_spec (f:nat -> bool) :=  fun i => if i =? 0 then false else f (i-1).

(* Showing the times_two spec is correct. *)

Lemma nat2fb_even_0:
  forall x, nat2fb (2 * x) 0 = false.
Proof.
  intros.
  unfold nat2fb.
  rewrite Nat2N.inj_double.
  unfold N.double.
  destruct (N.of_nat x).
  unfold N2fb,allfalse.
  reflexivity.
  unfold N2fb.
  simpl.
  reflexivity.
Qed.

Lemma pos2fb_times_two_eq:
  forall p x, x <> 0 -> pos2fb p (x - 1) = pos2fb p~0 x.
Proof.
  intros.
  induction p.
  simpl.
  assert ((fb_push false (fb_push true (pos2fb p))) x = (fb_push true (pos2fb p)) (x - 1)).
  rewrite fb_push_right.
  reflexivity. lia.
  rewrite H0.
  reflexivity.
  simpl.
  rewrite (fb_push_right x).
  reflexivity. lia.
  simpl.
  rewrite (fb_push_right x).
  reflexivity. lia.
Qed.

Lemma times_two_correct:
   forall x, (times_two_spec (nat2fb x)) = (nat2fb (2*x)).
Proof.
  intros.
  unfold times_two_spec.
  apply functional_extensionality; intros.
  unfold nat2fb.
  bdestruct (x0 =? 0).
  rewrite H.
  specialize (nat2fb_even_0 x) as H3.
  unfold nat2fb in H3.
  rewrite H3.
  reflexivity.
  rewrite Nat2N.inj_double.
  unfold N.double,N2fb.
  destruct (N.of_nat x).
  unfold allfalse.
  reflexivity.
  rewrite pos2fb_times_two_eq.
  reflexivity. lia.
Qed.


Lemma f_twoton_eq : forall n, twoton_fun n = nat2fb (2^n).
Proof.
  intros.
  induction n.
  simpl.
  unfold twoton_fun.
  apply functional_extensionality.
  intros. 
  IfExpSimpl.
  unfold fb_push. destruct x. easy. lia.
  unfold fb_push. destruct x. lia. easy.
  assert ((2 ^ S n) = 2 * (2^n)). simpl. lia.
  rewrite H.
  rewrite <- times_two_correct.
  rewrite <- IHn.
  unfold twoton_fun,times_two_spec.
  apply functional_extensionality; intros.
  bdestruct (x =? 0).
  subst.
  bdestruct (0 <? S n).
  easy. lia.
  bdestruct (x <? S n).
  bdestruct (x - 1 <? n).
  easy. lia.
  bdestruct (x =? S n).
  bdestruct (x - 1 <? n). lia.
  bdestruct (x - 1 =? n). easy.
  lia.
  bdestruct (x-1<? n). easy.
  bdestruct (x-1 =? n). lia.
  easy.
Qed.

Local Transparent carry.

Lemma carry_cut_n_false : forall i n f, carry false i (cut_n f n) (twoton_fun n) = false.
Proof.
  intros.
  induction i.
  simpl. easy.
  simpl. rewrite IHi.
  unfold cut_n,twoton_fun.
  IfExpSimpl. btauto.
  simpl.
  btauto.
  simpl. easy.
Qed.

Lemma carry_lt_same : forall m n f g h b, m < n -> (forall i, i < n -> f i = g i)
                          -> carry b m f h = carry b m g h.
Proof.
 induction m; intros; simpl. easy.
 rewrite H0. rewrite (IHm n) with (g:= g); try lia. easy.
 easy. lia.
Qed.

Lemma carry_lt_same_1 : forall m n f g h h' b, m < n -> (forall i, i < n -> f i = g i)
                 -> (forall i, i < n -> h i = h' i) -> carry b m f h = carry b m g h'.
Proof.
 induction m; intros; simpl. easy.
 rewrite H1. rewrite H0. rewrite (IHm n) with (g:= g) (h' := h'); try lia. easy.
 easy. easy. lia. lia.
Qed.

Local Opaque carry.

Lemma sumfb_cut_n : forall n f, f n = true -> sumfb false (cut_n f n) (twoton_fun n)  = cut_n f (S n).
Proof.
  intros.
  unfold sumfb.
  apply functional_extensionality; intros.
  rewrite carry_cut_n_false.
  unfold cut_n, twoton_fun.
  IfExpSimpl. btauto.
  subst. rewrite H. simpl.  easy.
  simpl. easy.
Qed.

Lemma f_num_aux_1: forall n f x, cut_n f n = nat2fb x -> f n = true 
                  -> cut_n f (S n) = nat2fb (x + 2^n).
Proof.
  intros.
  rewrite <- sumfb_correct_carry0.
  rewrite <- H.
  rewrite <- f_twoton_eq.
  rewrite sumfb_cut_n.
  easy. easy.
Qed.

Lemma f_num_0 : forall f n, (exists x, cut_n f n = nat2fb x).
Proof.
  intros.
  induction n.
  exists 0.
  rewrite <- (allfalse_0 0).
  unfold cut_n.
  apply functional_extensionality.
  intros.
  bdestruct (x <? 0).
  inv H. easy.
  destruct (bool_dec (f n) true).
  destruct IHn.
  exists (x + 2^n).
  rewrite (f_num_aux_1 n f x).
  easy. easy. easy.
  destruct IHn.
  exists x. rewrite (f_num_aux_0 n f x).
  easy. easy.
  apply not_true_is_false in n0. easy.
Qed.

Lemma cut_n_1_1: forall (r:rz_val), r 0 = true -> cut_n r 1 = nat2fb 1.
Proof.
  intros. unfold cut_n.
  apply functional_extensionality. intros.
  bdestruct (x <? 1).
  assert (x = 0) by lia. subst.
  unfold nat2fb. simpl. rewrite H. easy.
  unfold nat2fb. simpl. 
  rewrite fb_push_right. easy. lia.
Qed.

Lemma cut_n_1_0: forall (r:rz_val), r 0 = false -> cut_n r 1 = nat2fb 0.
Proof.
  intros. unfold cut_n.
  apply functional_extensionality. intros.
  bdestruct (x <? 1).
  assert (x = 0) by lia. subst.
  unfold nat2fb. simpl. rewrite H. easy.
  unfold nat2fb. simpl. easy.
Qed.

Lemma nat2fb_0: nat2fb 0 = allfalse.
Proof.
 unfold nat2fb. simpl. easy.
Qed.

Lemma pos2fb_no_zero : forall p, (exists i, pos2fb p i = true).
Proof.
  intros. induction p.
  simpl. exists 0.
  simpl. easy.
  simpl. destruct IHp.
  exists (S x).
  simpl. easy. simpl.
  exists 0. simpl. easy.
Qed.

Lemma cut_n_eq : forall n f, (forall i, i >= n -> f i = false) -> cut_n f n = f.
Proof.
 intros. unfold cut_n.
 apply functional_extensionality; intro.
 bdestruct (x <? n). easy. rewrite H. easy. lia. 
Qed.

Lemma cut_n_twice_same : forall n f, cut_n (cut_n f n) n = cut_n f n.
Proof.
 intros. unfold cut_n.
  apply functional_extensionality.
  intros. bdestruct (x <? n). easy. easy.
Qed.

Lemma nat2fb_bound : forall n x, x < 2^n -> (forall i, i >= n -> nat2fb x i = false).
Proof.
 intros. 
 unfold nat2fb in *. 
 assert ((N.of_nat x < (N.of_nat 2)^ (N.of_nat n))%N).
 rewrite <- Nofnat_pow. lia.
 apply N.mod_small in H1.
 rewrite N2fb_Ntestbit.
 rewrite <- H1.
 apply N.mod_pow2_bits_high. lia.
Qed.

Lemma pos2fb_sem : forall x y, pos2fb x = pos2fb y -> x = y.
Proof.
 induction x; intros.
 simpl in *.
 destruct y. simpl in H.
 assert (forall i, fb_push true (pos2fb x) i = fb_push true (pos2fb y) i).
 intros. rewrite H. easy.
 apply fb_push_same in H0. apply IHx in H0. subst. easy.
 simpl in H.
 assert (forall i, fb_push true (pos2fb x) i = fb_push false (pos2fb y) i).
 intros. rewrite H. easy.
 specialize (H0 0). simpl in H0. inv H0.
 simpl in H.
 assert (forall i, fb_push true (pos2fb x) i = fb_push true allfalse i).
 intros. rewrite H. easy.
 apply fb_push_same in H0.
 specialize (pos2fb_no_zero x) as eq1.
 destruct eq1. rewrite H0 in H1. unfold allfalse in H1. inv H1.
 destruct y. simpl in *.
 assert (forall i, fb_push false (pos2fb x) i = fb_push true (pos2fb y) i).
 intros. rewrite H. easy.
 specialize (H0 0). simpl in H0. inv H0.
 simpl in *.
 assert (forall i, fb_push false (pos2fb x) i = fb_push false (pos2fb y) i).
 intros. rewrite H. easy.
 apply fb_push_same in H0. apply IHx in H0. subst. easy.
 simpl in *.
 assert (forall i, fb_push false (pos2fb x) i = fb_push true allfalse i).
 intros. rewrite H. easy.
 specialize (H0 0). simpl in H0. inv H0.
 destruct y. simpl in *.
 assert (forall i, fb_push true allfalse i = fb_push true (pos2fb y) i).
 intros. rewrite H. easy.
 apply fb_push_same in H0. 
 specialize (pos2fb_no_zero y) as eq1. destruct eq1.
 rewrite <- H0 in H1. unfold allfalse in H1. inv H1.
 simpl in *. 
 assert (forall i, fb_push true allfalse i = fb_push false (pos2fb y) i).
 intros. rewrite H. easy.
 specialize (H0 0). simpl in H0. inv H0. easy.
Qed.

Lemma nat2fb_sem : forall x y, nat2fb x = nat2fb y -> x = y.
Proof.
  intros. unfold nat2fb,N2fb in H.
  destruct (N.of_nat x) eqn:eq1.
  destruct (N.of_nat y) eqn:eq2.
  simpl in eq1. lia.
  specialize (pos2fb_no_zero p) as eq3.
  destruct eq3.
  rewrite <- H in H0. unfold allfalse in H0. inv H0.
  destruct (N.of_nat y) eqn:eq2.
  specialize (pos2fb_no_zero p) as eq3.
  destruct eq3.
  rewrite H in H0. unfold allfalse in H0. inv H0.
  apply pos2fb_sem in H. subst.
  rewrite <- eq1 in eq2. lia.
Qed.

Lemma f_num_small : forall f n x, cut_n f n = nat2fb x -> x < 2^n.
Proof.
  induction n; intros. simpl in *.
  assert (cut_n f 0 = allfalse).
  unfold cut_n.
  apply functional_extensionality.
  intros. bdestruct (x0 <? 0). lia. easy.
  rewrite H0 in H.
  unfold nat2fb in H.
  unfold N2fb in H.
  destruct (N.of_nat x) eqn:eq1. lia.
  specialize (pos2fb_no_zero p) as eq2.
  destruct eq2. rewrite <- H in H1. unfold allfalse in H1.
  inv H1.
  specialize (f_num_0 f n) as eq1.
  destruct eq1.
  destruct (f n) eqn:eq2.
  rewrite f_num_aux_1 with (x := x0) in H; try easy.
  apply IHn in H0. simpl.
  apply nat2fb_sem in H. subst. lia.
  rewrite f_num_aux_0 with (x := x0) in H; try easy.
  apply nat2fb_sem in H. subst.
  apply IHn in H0. simpl. lia.
Qed.

Definition addto (r : nat -> bool) (n:nat) : nat -> bool := fun i => if i <? n 
                    then (cut_n (fbrev n (sumfb false (cut_n (fbrev n r) n) (nat2fb 1))) n) i else r i.

Definition addto_n (r:nat -> bool) n := fun i => if i <? n
               then (cut_n (fbrev n (sumfb false (cut_n (fbrev n r) n) (negatem n (nat2fb 0)))) n) i else r i.

Lemma addto_n_0 : forall r, addto_n r 0 = r.
Proof.
  intros.
  unfold addto_n.
  apply functional_extensionality.
  intros.
  IfExpSimpl. easy.
Qed.

Lemma addto_0 : forall r, addto r 0 = r.
Proof.
  intros.
  unfold addto.
  apply functional_extensionality.
  intros.
  IfExpSimpl. easy.
Qed.

Lemma cut_n_fbrev_flip : forall n f, cut_n (fbrev n f) n = fbrev n (cut_n f n).
Proof.
  intros.
  unfold cut_n, fbrev.
  apply functional_extensionality.
  intros.
  bdestruct (x <? n).
  bdestruct (n - 1 - x <? n).
  easy. lia. easy.
Qed.

Lemma cut_n_if_cut : forall n f g, cut_n (fun i => if i <? n then f i else g i) n = cut_n f n.
Proof.
  intros.
  unfold cut_n.
  apply functional_extensionality; intros.
  bdestruct (x <? n).
  easy. easy.
Qed.

Lemma fbrev_twice_same {A}: forall n f, @fbrev A n (fbrev n f) = f.
Proof.
  intros.
  unfold fbrev.
  apply functional_extensionality.
  intros.
  bdestruct (x <? n).
  bdestruct (n - 1 - x <? n).
  assert ((n - 1 - (n - 1 - x)) = x) by lia.
  rewrite H1. easy.
  lia. easy.
Qed.

Lemma cut_n_mod : forall n x, cut_n (nat2fb x) n = (nat2fb (x mod 2^n)).
Proof.
  intros.
  bdestruct (x <? 2^n).
  rewrite Nat.mod_small by lia.
  unfold cut_n.
  apply functional_extensionality; intros.
  bdestruct (x0 <? n). easy.
  specialize (nat2fb_bound n x H x0) as eq1.
  rewrite eq1. easy. lia.
  unfold cut_n.
  apply functional_extensionality; intros.
  bdestruct (x0 <? n).
  unfold nat2fb.
  rewrite N2fb_Ntestbit.
  rewrite N2fb_Ntestbit.
  rewrite <- N.mod_pow2_bits_low with (n := N.of_nat n).
  rewrite Nofnat_mod.
  rewrite Nofnat_pow. simpl. easy.
  apply Nat.pow_nonzero. lia. lia.
  assert (x mod 2 ^ n < 2^n).
  apply Nat.mod_small_iff.
  apply Nat.pow_nonzero. lia.
  rewrite Nat.mod_mod. easy.
  apply Nat.pow_nonzero. lia.  
  specialize (nat2fb_bound n (x mod 2^n) H1 x0 H0) as eq1.
  rewrite eq1. easy.
Qed.

Lemma add_to_r_same : forall q r, addto (addto_n r q) q = r.
Proof.
  intros.
  destruct q eqn:eq1.
  rewrite addto_n_0.
  rewrite addto_0. easy.
  unfold addto_n.
  specialize (f_num_0 (fbrev (S n) r) (S n)) as eq2.
  destruct eq2.
  rewrite negatem_arith.
  rewrite H.
  rewrite sumfb_correct_carry0.
  assert (1 < 2 ^ (S n)).
  apply Nat.pow_gt_1. lia. lia.
  assert (((2 ^ S n - 1 - 0)) = 2^ S n -1) by lia.
  rewrite H1.
  unfold addto.
  rewrite (cut_n_fbrev_flip (S n) (fun i0 : nat =>
                 if i0 <? S n
                 then
                  cut_n
                    (fbrev (S n)
                       (nat2fb
                          (x + (2 ^ S n - 1))))
                    (S n) i0
                 else r i0)).
  rewrite cut_n_if_cut.
  rewrite (cut_n_fbrev_flip (S n)
                      (nat2fb
                         (x + (2 ^ S n - 1)))).
  rewrite cut_n_mod.
  rewrite <- cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  rewrite cut_n_mod.
  rewrite Nat.mod_mod by lia.
  rewrite sumfb_correct_carry0.
  assert (((x + (2 ^ S n - 1)) mod 2 ^ S n + 1) = ((x + (2 ^ S n - 1)) mod 2 ^ S n + (1 mod 2^ S n))).
  assert (1 mod 2^ S n = 1).
  rewrite Nat.mod_small. easy. easy.
  rewrite H2. easy.
  rewrite H2.
  rewrite cut_n_fbrev_flip.
  rewrite cut_n_mod.
  rewrite <- Nat.add_mod by lia.
  assert ((x + (2 ^ S n - 1) + 1) = x + 2 ^ S n) by lia.
  rewrite H3.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  assert (x mod 2 ^ S n = x).
  rewrite Nat.mod_small. easy.
  apply (f_num_small (fbrev (S n) r)). easy.
  rewrite H4.
  rewrite plus_0_r.
  rewrite H4.
  rewrite <- H.
  rewrite <- cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  apply functional_extensionality.
  intros.
  bdestruct (x0 <? S n).
  unfold cut_n.
  bdestruct (x0 <? S n).
  easy. lia. easy.
  specialize (Nat.pow_nonzero 2 (S n)) as eq2.
  assert (2 <> 0) by lia. apply eq2 in H0. lia.
Qed.

Lemma add_to_same : forall q r, addto_n (addto r q) q = r.
Proof.
  intros.
  destruct q eqn:eq1.
  rewrite addto_n_0.
  rewrite addto_0. easy.
  unfold addto.
  specialize (f_num_0 (fbrev (S n) r) (S n)) as eq2.
  destruct eq2.
  rewrite H.
  rewrite sumfb_correct_carry0.
  unfold addto_n.
  assert (0 < 2^ (S n)).
  specialize (Nat.pow_nonzero 2 (S n)) as eq2.
  assert (2 <> 0) by lia. apply eq2 in H0. lia.
  rewrite negatem_arith by lia.
  rewrite (cut_n_fbrev_flip (S n) (fun i0 : nat =>
                 if i0 <? S n
                 then
                  cut_n
                    (fbrev (S n)
                       (nat2fb (x + 1))) 
                    (S n) i0
                 else r i0)).
  rewrite cut_n_if_cut.
  rewrite (cut_n_fbrev_flip (S n)
                      (nat2fb (x+1))).
  rewrite cut_n_mod.
  rewrite <- cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  rewrite cut_n_mod.
  rewrite Nat.mod_mod by lia.
  assert ((2 ^ S n - 1) = (2 ^ S n - 1) mod (2^ S n)).
  rewrite Nat.mod_small by lia.
  easy.
  rewrite H1.
  rewrite sumfb_correct_carry0.
  rewrite cut_n_fbrev_flip.
  rewrite cut_n_mod.
  assert ((x + 1) mod 2 ^ S n + ((2 ^ S n - 1) mod 2 ^ S n - 0)
           = ((x + 1) mod 2 ^ S n + ((2 ^ S n - 1) mod 2 ^ S n))) by lia.
  rewrite H2.
  rewrite <- Nat.add_mod by lia.
  assert ((x + 1 + (2 ^ S n - 1))  = x + 2 ^ S n) by lia.
  rewrite H3.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small.
  rewrite <- H.
  rewrite cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  apply functional_extensionality.
  intros.
  bdestruct (x0 <? S n).
  unfold cut_n.
  bdestruct (x0 <? S n).
  easy. lia. easy.
  apply (f_num_small (fbrev (S n) r)). easy.
Qed.


Lemma posi_neq_f : forall (p p' : posi), p <> p' -> fst p <> fst p' \/ snd p <> snd p'.
Proof.
 intros. destruct p. destruct p'.
 simpl in *.
 bdestruct (v =? v0).
 subst. right.
 intros R. subst. contradiction.
 bdestruct (n =? n0).
 subst.
 left.
 intros R. subst. contradiction.
 left. lia.
Qed.

Lemma posi_neq_b : forall (p p' : posi), fst p <> fst p' \/ snd p <> snd p' -> p <> p'.
Proof.
 intros. destruct p. destruct p'.
 simpl in *.
 intros R. inv R.
 destruct H.
 lia.
 lia.
Qed.

Lemma xorb_andb_distr_l : forall x y z, (x ⊕ y) && z = (x && z) ⊕ (y && z).
Proof.
 intros. btauto.
Qed.

Lemma xorb_andb_distr_r : forall x y z, z && (x ⊕ y) = (z && x) ⊕ (z && y).
Proof.
 intros. btauto.
Qed.


Ltac bt_simpl := repeat (try rewrite xorb_false_r; try rewrite xorb_false_l;
            try rewrite xorb_true_r; try rewrite xorb_true_r; 
            try rewrite andb_false_r; try rewrite andb_false_l;
            try rewrite andb_true_r; try rewrite andb_true_l;
            try rewrite xorb_andb_distr_l; try rewrite xorb_andb_distr_r;
            try rewrite andb_diag).

Lemma msm_eq1 :
  forall n i c f g,
    S i < n ->
    msma i c f g i ⊕ msma i c f g (S i) = msma (S i) c f g i.
Proof.
  intros. unfold msma. IfExpSimpl. easy.
Qed.

Lemma msm_eq2 :
  forall n i c f g,
    S i < n ->
    msmb i c f g (S i) ⊕ msma i c f g (S i) = msmb (S i) c f g (S i).
Proof.
  intros. unfold msma. unfold msmb. IfExpSimpl. btauto.
Qed.
       

Lemma msm_eq3 :
  forall n i c f g,
    S i < n ->
    majb (msma i c f g (S i)) (msmb i c f g (S i)) (msma i c f g i) = msma (S i) c f g (S i).
Proof.
  intros. unfold msma. unfold msmb. IfExpSimpl.
  simpl. unfold majb. easy.
Qed.


Lemma pow2_predn :
  forall n x,
    x < 2^(n-1) -> x < 2^n.
Proof.
  intros. destruct n. simpl in *. lia.
  simpl in *. rewrite Nat.sub_0_r in H. lia.
Qed.

Lemma carry_leb_equiv_true :
  forall n x y,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    x <= y ->
    carry true n (nat2fb (2^n - 1 - x)) (nat2fb y) = true.
Proof.
  intros. unfold nat2fb. specialize (carry_add_eq_carry1 n (N.of_nat (2 ^ n - 1 - x)) (N.of_nat y)) as G.
  do 2 apply xorb_move_l_r_2 in G. rewrite G.
  do 2 (pattern N2fb at 1; rewrite N2fb_Ntestbit).
  rewrite Ntestbit_lt_pow2n.
  2:{ replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow. apply pow2_predn in H1. lia.
  }
  rewrite Ntestbit_lt_pow2n.
  2:{ replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
      assert (0 < 2^n) by (apply pow_positive; easy). lia.
  }
  replace 1%N with (N.of_nat 1) by easy. do 2 rewrite <- Nnat.Nat2N.inj_add.
  rewrite N2fb_Ntestbit. rewrite Ntestbit_in_pow2n_pow2Sn. btauto.
  split.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
  replace (2^n) with (2^(n-1) + 2^(n-1)). lia.
  destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
  rewrite <- Nnat.Nat2N.inj_succ.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
  replace (2^(S n)) with (2^n + 2^n) by (simpl; lia).
  replace (2^n) with (2^(n-1) + 2^(n-1)). lia.
  destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
Qed.

Lemma carry_leb_equiv_false :
  forall n x y,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    x > y ->
    carry true n (nat2fb (2^n - 1 - x)) (nat2fb y) = false.
Proof.
  intros. unfold nat2fb. specialize (carry_add_eq_carry1 n (N.of_nat (2 ^ n - 1 - x)) (N.of_nat y)) as G.
  do 2 apply xorb_move_l_r_2 in G. rewrite G.
  do 2 (pattern N2fb at 1; rewrite N2fb_Ntestbit).
  rewrite Ntestbit_lt_pow2n.
  2:{ replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow. apply pow2_predn in H1. lia.
  }
  rewrite Ntestbit_lt_pow2n.
  2:{ replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
      assert (0 < 2^n) by (apply pow_positive; easy). lia.
  }
  replace 1%N with (N.of_nat 1) by easy. do 2 rewrite <- Nnat.Nat2N.inj_add.
  rewrite N2fb_Ntestbit. rewrite Ntestbit_lt_pow2n. btauto.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
  replace (2^n) with (2^(n-1) + 2^(n-1)). lia.
  destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
Qed.

Lemma carry_leb_equiv :
  forall n x y,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    carry true n (nat2fb (2^n - 1 - x)) (nat2fb y) = (x <=? y).
Proof.
  intros. bdestruct (x <=? y). apply carry_leb_equiv_true; easy. apply carry_leb_equiv_false; easy.
Qed.

Lemma pow2_low_bit_false : forall n i, i < n -> nat2fb (2^n) i = false.
Proof.
 intros. unfold nat2fb.
 rewrite N2fb_Ntestbit.
 assert (N.of_nat i < N.of_nat n)%N.
 lia.
 specialize (N.mul_pow2_bits_low 1 (N.of_nat n) (N.of_nat i) H0) as eq1.
 assert (1 * 2 ^ N.of_nat n = 2 ^ N.of_nat n)%N by lia.
 rewrite H1 in eq1.
 assert (2%N = (N.of_nat 2)) by easy. rewrite H2 in eq1.
 rewrite Nofnat_pow.
 rewrite eq1. easy.
Qed.

Local Transparent carry.
Lemma carry_false_lt: forall n f g,
    (forall i, i <= n -> g i = false) -> 
    carry false n f g = false.
Proof.
  induction n;intros.
  simpl. easy.
  simpl.
  rewrite IHn.
  rewrite H by lia. btauto.
  intros. rewrite H. easy. lia.
Qed.


Lemma low_bit_same : forall n x, 0 < n -> x < 2^n -> 
    (forall i, i < n -> nat2fb (x + 2^n) i = nat2fb x i).
Proof.
  intros.
  rewrite <- sumfb_correct_carry0.
  unfold sumfb.
  rewrite pow2_low_bit_false by easy. bt_simpl.
  rewrite carry_false_lt. btauto.
  intros.
  apply pow2_low_bit_false. lia.
Qed.

Lemma carry_low_bit_same : forall m b n x g, m <= n -> 0 < n -> x < 2^n -> 
    carry b m (nat2fb (x + 2^n)) g = carry b m (nat2fb x) g.
Proof.
  induction m;intros. simpl. easy.
  simpl.
  rewrite IHm by lia.
  rewrite low_bit_same by lia. easy.
Qed.



Lemma majb_carry_s_eq : forall n x y, 0 < n -> x < 2^n -> y < 2^n ->
      majb true false (carry true n (nat2fb (2^n - 1 - x)) (nat2fb y)) 
       = carry true (S n) (nat2fb ((2^n - 1 - x) + 2^n)) (nat2fb y).
Proof.
  intros. simpl. unfold majb.
  assert (nat2fb (2 ^ n - 1 - x + 2 ^ n) n = true).
  unfold nat2fb. rewrite N2fb_Ntestbit.
  rewrite Ntestbit_in_pow2n_pow2Sn. easy.
  split. 
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow. lia.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nnat.Nat2N.inj_succ. 
  rewrite <- Nofnat_pow.
  rewrite Nat.pow_succ_r. lia. lia.
  rewrite H2.
  assert (nat2fb y n = false).
  unfold nat2fb. rewrite N2fb_Ntestbit.
  rewrite Ntestbit_lt_pow2n. easy.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow. lia.
  rewrite H3. rewrite carry_low_bit_same. easy.
  easy. lia. lia.
Qed.

Local Opaque carry.



Fixpoint natsum n (f : nat -> nat) :=
  match n with
  | 0 => 0
  | S n' => f n' + natsum n' f
  end.

Lemma natsum_mod :
  forall n f M,
    M <> 0 ->
    (natsum n f) mod M = natsum n (fun i => f i mod M) mod M.
Proof.
  induction n; intros. easy.
  simpl. rewrite Nat.add_mod by easy. rewrite IHn by easy. 
  rewrite <- Nat.add_mod by easy. rewrite Nat.add_mod_idemp_l by easy. easy.
Qed.

Lemma parity_decompose :
  forall n, exists k, n = 2 * k \/ n = 2 * k + 1.
Proof.
  induction n. exists 0. lia. 
  destruct IHn as [k [H | H]]. exists k. lia. exists (S k). lia.
Qed.

Lemma Natodd_Ntestbit_even :
  forall k, Nat.odd (2 * k) = N.testbit (N.of_nat (2 * k)) 0.
Proof.
  induction k. easy.
  replace (2 * (S k)) with (S (S (2 * k))) by lia.
  rewrite Nat.odd_succ_succ. rewrite IHk.
  do 2 rewrite N.bit0_odd.
  replace (N.of_nat (S (S (2 * k)))) 
   with (N.succ (N.succ (N.of_nat (2 * k)))) by lia.
   rewrite N.odd_succ_succ. easy.
Qed.

Lemma Natodd_Ntestbit_odd :
  forall k, Nat.odd (2 * k + 1) = N.testbit (N.of_nat (2 * k + 1)) 0.
Proof.
  induction k. easy.
  replace (2 * (S k) + 1) with (S (S (2 * k + 1))) by lia.
  rewrite Nat.odd_succ_succ. rewrite IHk.
  do 2 rewrite N.bit0_odd.
  replace (N.of_nat (S (S (2 * k + 1)))) 
     with (N.succ (N.succ (N.of_nat (2 * k + 1)))) by lia.
  rewrite N.odd_succ_succ. easy.
Qed.

Lemma nat_is_odd_testbit:
  forall n, N.testbit (N.of_nat n) 0 = true -> Nat.odd n = true.
Proof.
  intros.
  specialize (parity_decompose n) as [k [Hk | Hk]]; subst.
  rewrite Natodd_Ntestbit_even.
  assumption.
  rewrite Natodd_Ntestbit_odd.
  assumption.
Qed.

Lemma nat_is_even_testbit:
  forall n, N.testbit (N.of_nat n) 0 = false -> Nat.even n = true.
Proof.
  intros.
  assert (Nat.odd n = false).
  specialize (parity_decompose n) as [k [Hk | Hk]]; subst.
  rewrite Natodd_Ntestbit_even.
  assumption.
  rewrite Natodd_Ntestbit_odd.
  assumption.
  unfold Nat.odd in H0.
  apply negb_false_iff in H0.
  assumption.
Qed.

Lemma Nattestbit_Ntestbit :
  forall m n,
    Nat.testbit n m = N.testbit (N.of_nat n) (N.of_nat m).
Proof.
  induction m; intros. simpl. specialize (parity_decompose n) as [k [Hk | Hk]]; subst.
   apply Natodd_Ntestbit_even. apply Natodd_Ntestbit_odd.
  remember (N.of_nat (S m)) as NSm. simpl. rewrite IHm. rewrite Nnat.Nat2N.inj_div2.
   rewrite <- N.testbit_succ_r_div2 by lia. subst. rewrite Nnat.Nat2N.inj_succ. easy.
Qed.  

Definition bindecomp n x := natsum n (fun i => Nat.b2n ((nat2fb x) i) * 2^i).

Lemma bindecomp_spec :
  forall n x,
    bindecomp n x = x mod 2^n.
Proof.
  unfold bindecomp. induction n; intros. easy.
  simpl. rewrite IHn. unfold nat2fb. rewrite N2fb_Ntestbit. rewrite <- Nattestbit_Ntestbit.
  rewrite Nat.testbit_spec'. replace (2 ^ n + (2 ^ n + 0)) with ((2 ^ n) * 2) by lia. 
  rewrite Nat.mod_mul_r. lia. apply Nat.pow_nonzero. easy. easy.
Qed.

Lemma bindecomp_seq :
  forall n x, bindecomp (S n) x = bindecomp n x + Nat.b2n ((nat2fb x) n) * 2^n.
Proof.
 intros.
 unfold bindecomp.
 simpl. lia.
Qed.

Lemma f_num_nat2fb : forall n f, (forall i, i >= n -> f i = false) -> (exists x, f = nat2fb x).
Proof.
  intros.
  specialize (f_num_0 f n) as eq1.
  destruct eq1.
  assert (f = cut_n f n).
  unfold cut_n.
  apply functional_extensionality; intro.
  bdestruct (x0 <? n). easy.
  rewrite H. easy. easy.
  exists x. rewrite H1. easy.
Qed.

Lemma add_to_sem : forall n q r, 0 < q <= n ->
                 (forall i , i >= n -> r i = false) ->
                 (addto r q) = cut_n (fbrev n (sumfb false (fbrev n r) (nat2fb (2^(n-q))))) n.
Proof.
  intros. unfold cut_n,addto,fbrev.
  apply functional_extensionality; intro.
  bdestruct (x <? q).
  bdestruct (x <? n).
Admitted. 

Lemma add_to_n_sem : forall n q r, 0 < q <= n ->
                 (forall i , i >= n -> r i = false) ->
                 (addto_n r q) = cut_n (fbrev n (sumfb false (fbrev n r) (nat2fb (2^n - 2^(n-q))))) n.
Proof.
  intros. unfold addto_n.
  apply functional_extensionality; intro.
  bdestruct (x <? q).
  rewrite negatem_arith.
  assert ((forall i : nat, i >= n -> fbrev q r i = false)).
  intros. unfold fbrev.
  bdestruct (i <? q). lia. rewrite H0. easy. lia.
  specialize (f_num_nat2fb n (fbrev q r) H2) as eq1.
  destruct eq1.
  rewrite H3.
  rewrite cut_n_mod.
  assert (2 ^ q <> 0).
  apply Nat.pow_nonzero. lia.
  rewrite sumfb_correct_carry0.
  assert ((2 ^ q - 1 - 0) = ((2 ^ q -1) mod 2^q)).
  rewrite Nat.mod_small by lia.
  lia. rewrite H5.
  rewrite cut_n_fbrev_flip.
  rewrite cut_n_mod.
  rewrite <- Nat.add_mod by lia.
  assert (forall i : nat, i >= n -> fbrev n r i = false).
  intros. unfold fbrev.
  bdestruct (i <? n). lia. rewrite H0. easy. lia.
  specialize (f_num_nat2fb n (fbrev n r) H6) as eq2.
  destruct eq2.
  rewrite H7.
  rewrite sumfb_correct_carry0.
  rewrite cut_n_fbrev_flip.
  rewrite cut_n_mod.
  Check Nat.add_mod.
Admitted. 

Lemma sumfb_assoc : forall f g h n, 
          (forall i, i >= n -> f i = false) -> (forall i, i >= n -> g i = false) 
             -> (forall i, i >= n -> h i = false) ->
         sumfb false f (sumfb false g h) = sumfb false (sumfb false f g) h. 
Proof.
  intros.
  rewrite <- (cut_n_eq n f).
  rewrite <- (cut_n_eq n g).
  rewrite <- (cut_n_eq n h).
  specialize (f_num_0 f n) as eq1.
  specialize (f_num_0 g n) as eq2.
  specialize (f_num_0 h n) as eq3.
  destruct eq1. destruct eq2. destruct eq3.
  rewrite H2. rewrite H3. rewrite H4.
  repeat rewrite sumfb_correct_carry0.
  rewrite plus_assoc. easy.
  easy. easy. easy.
Qed.


Lemma highbit_means_lt : forall size X M, X < 2^ S size -> M < 2^size -> X < 2 * M 
         -> fbrev (S size) (nat2fb ((X + 2^S size - M) mod 2^S size)) 0 = (X <? M).
Proof.
  intros. unfold fbrev.
  bdestruct (0 <? size). simpl.
  assert ((size - 0 - 0) = size) by lia. rewrite H3.
  unfold nat2fb.
  rewrite N2fb_Ntestbit.
  bdestruct (X <? M).
  apply Ntestbit_in_pow2n_pow2Sn.
  assert ((2 ^ size + (2 ^ size + 0)) = 2^ S size). simpl. easy.
  rewrite H5.
  split.
  assert (2^size <= (X + 2 ^ S size - M) mod 2 ^ S size).
  assert ((X + 2 ^ S size - M) = 2^S size - (M - X)) by lia.
  rewrite H6.
  assert ((2 ^ S size - (M - X)) < 2 ^ S size) by lia.
  rewrite Nat.mod_small by lia.
  assert (M - X < 2^size) by lia. lia.
  assert (N.of_nat(2 ^ size) <= N.of_nat ((X + 2 ^ S size - M) mod 2 ^ S size))%N by lia.
  simpl in *. rewrite Nofnat_pow in H7. simpl in H7. lia.
  assert ((X + 2 ^ S size - M) mod 2 ^ S size < 2 ^ S size).
  apply Nat.mod_upper_bound. lia.
  assert (N.of_nat ((X + 2 ^ S size - M) mod 2 ^ S size) < N.of_nat (2 ^ S size))%N by lia.
  rewrite Nofnat_pow in H7. 
  assert (N.of_nat (S size) = N.succ (N.of_nat size)) by lia.
  rewrite H8 in H7. simpl in *. lia.
  apply Ntestbit_lt_pow2n.
  assert ((2 ^ size + (2 ^ size + 0)) = 2^ S size). simpl. easy.
  rewrite H5. clear H5.
  assert ((X + 2 ^ S size - M) mod 2 ^ S size < 2 ^ size).
  assert ((X + 2 ^ S size - M) = 2 ^ S size + (X - M)) by lia.
  rewrite H5. clear H5.
  assert (2^ size <> 0).
  apply Nat.pow_nonzero. lia.
  rewrite Nat.add_mod by (simpl;lia).
  rewrite Nat.mod_same by (simpl;lia).
  rewrite plus_0_l.
  rewrite Nat.mod_mod by (simpl;lia).
  rewrite Nat.mod_small by (simpl;lia).
  simpl. lia.
  assert (N.of_nat ((X + 2 ^ S size - M) mod 2 ^ S size) < N.of_nat (2 ^ size))%N by lia.
  rewrite Nofnat_pow in H6. 
  simpl in *. lia. 
  bdestruct (0 <? S size).
  assert (size = 0) by lia. subst. simpl in *. lia.
  lia.
Qed.
