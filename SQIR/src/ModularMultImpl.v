Require Import VectorStates UnitaryOps Coq.btauto.Btauto RCIR ModularMultSpec.


Local Open Scope nat_scope.
Local Open Scope bccom_scope.

(**********************)
(** Unitary Programs - Modular Multiplier. **)
(**********************)

(* First, we need to define a function to grab three fbools out of a single uniformed fbools. 
   The structure of the fbool is like
     from 0 to 2n+2 are bits messing around for f and g and extra c bit and high bit for comparator. *)
Definition get_f n (fb:nat -> bool) := fun i => if i <? n then fb (2 * i + 1) else false.

Definition get_g n (fb:nat -> bool) := fun i => if i <? n then fb (2 * i + 2) else false.

Definition get_fold base (fb:nat -> bool) := fun i => fb (base + i).

Fixpoint insert_f n f (fb:nat -> bool) :=
     match n with 
          | 0 => fb
          | S m => insert_f m f (fb[2 * m + 1 |-> f m])
     end.

Lemma get_insert_f_same':
  forall n f m, n <= m -> insert_f n (get_f m f) f = f.
Proof.
  intros n f.
  unfold get_f.
  induction n.
  simpl.
  reflexivity.
  intros.
  simpl in *.
  rewrite update_same.
  rewrite IHn.
  reflexivity.
  lia.
  destruct (n <? m) eqn:eq.
  reflexivity.
specialize (Nat.ltb_lt n m) as eq1.
apply not_iff_compat in eq1.
apply not_true_iff_false in eq.
apply eq1 in eq.
lia.
Qed.


Lemma get_insert_f_same:
  forall n f, insert_f n (get_f n f) f = f.
Proof.
  intros.
  rewrite get_insert_f_same'.
  reflexivity. lia.
Qed.

(* The following contains the implementation of the Modular Multiplier circuit that meets the specification. *)
(* Maj and UMA circuits. *)
Definition MAJ a b c := bccnot c b ; bccnot c a ; bcccnot a b c.
Definition MAJ_neg a b c := bcinv (MAJ a b c).
Definition UMA a b c := bcccnot a b c ; bccnot c a ; bccnot a b.

Lemma MAJ_correct :
  forall a b c f,
    a <> b -> b <> c -> a <> c ->
    bcexec (MAJ c b a) f = ((f[a |-> 
    ((f a && f b) ⊕ (f a && f c) ⊕ (f b && f c))])
          [b |-> (f b ⊕ f a)])[c |-> (f c ⊕ f a)].
Proof.
  intros ? ? ? ? Hab' Hbc' Hac'. apply functional_extensionality; intro i. simpl.
  unfold update. bnauto.
Qed.

Lemma UMA_correct_partial :
  forall a b c f f',
    a <> b -> b <> c -> a <> c ->
    f' a = ((f a && f b) ⊕ (f a && f c) ⊕ (f b && f c)) ->
    f' b = (f b ⊕ f a) -> f' c = (f c ⊕ f a) ->
    bcexec (UMA c b a) f' = ((f'[a |-> (f a)])[b |-> (f a ⊕ f b ⊕ f c)])[c |-> (f c)].
Proof.
  intros ? ? ? ? ? Hab' Hbc' Hac' Hf'1 Hf'2 Hf'3. apply functional_extensionality; intro i. simpl.
  unfold update. bnauto_expand (f' a :: f' b :: f' c :: []).
Qed.


Fixpoint MAJseq n : bccom :=
  match n with
  | 0 => MAJ 0 1 2
  | S n' => MAJseq n'; MAJ (2 * n) (2 * n + 1) (2 * n + 2)
  end.

Definition carry n f := carry_spec (f 0) n (get_f n f) (get_g n f).

Lemma carry_extend_aux :
   forall n t m f, n <= t -> t < m -> 
    carry_spec (f 0) n (get_f m f) (get_g m f)
   = carry_spec (f 0) n (get_f t f) (get_g t f).
Proof.
  intros.
  unfold get_f,get_g.
  induction n.
  simpl. reflexivity.
  simpl in *.
  destruct (n <? m) eqn:eq.
  destruct (n <? t) eqn:eq1.
  rewrite IHn.
  reflexivity.
  lia.
  specialize (Nat.ltb_lt n t) as eq2.
  apply not_iff_compat in eq2.
  apply not_true_iff_false in eq1.
  apply eq2 in eq1.
  lia.
  specialize (Nat.ltb_lt n m) as eq2.
  apply not_iff_compat in eq2.
  apply not_true_iff_false in eq.
  apply eq2 in eq.
  lia.
Qed.

Lemma carry_extend :
  forall n f,
    carry (S n) f = (f (2 * n + 1) && f (2 * n + 2)) ⊕ 
  (f (2 * n + 2) && carry n f) ⊕ (f (2 * n + 1) && carry n f).
Proof.
  intros. unfold carry.
  simpl.
  assert (get_f (S n) f n = f (n + (n + 0) + 1)).
  unfold get_f.
  destruct (n <? S n) eqn:eq. easy.
  specialize (Nat.ltb_lt n (S n)) as eq1.
  apply not_iff_compat in eq1.
  apply not_true_iff_false in eq.
  apply eq1 in eq.
  lia.
  rewrite H.
  assert (get_g (S n) f n = f (n + (n + 0) + 2)).
  unfold get_g.
  destruct (n <? S n) eqn:eq. easy.
  specialize (Nat.ltb_lt n (S n)) as eq1.
  apply not_iff_compat in eq1.
  apply not_true_iff_false in eq.
  apply eq1 in eq.
  lia.
  rewrite H0.
  rewrite (carry_extend_aux n n (S n)).
  reflexivity.
  lia. lia.
Qed.

Fixpoint msb n f : nat -> bool :=
  match n with
  | 0 => f[0 |-> carry 0 f ⊕ f 2][1 |-> f 1 ⊕ f 2][2 |-> carry 1 f]
  | S n' => (msb n' f)[2 * n
          |-> carry n f ⊕ f (2 * n + 2)][2 * n + 1 |-> f (2 * n + 1) ⊕ f (2 * n + 2)]
                    [2 * n + 2 |-> carry (S n) f]
  end.

Lemma msb_end2 :
  forall n f,
    msb n f (2 * n + 2) = carry (S n) f.
Proof.
  destruct n; intros. simpl. unfold update. bnauto.
  simpl. repeat rewrite update_index_neq by lia. repeat rewrite update_index_eq. easy.
Qed.

Lemma msb_end_gt :
  forall n m f,
    2 * n + 2 < m ->
    msb n f m = f m.
Proof.
  induction n; intros. simpl. repeat rewrite update_index_neq by lia. easy.
  simpl. repeat rewrite update_index_neq by lia. apply IHn. lia.
Qed.

Lemma MAJseq_correct :
  forall n f,
    bcexec (MAJseq n) f = msb n f.
Proof.
  Local Opaque MAJ.
  induction n; intros. simpl. 
  rewrite MAJ_correct by lia. 
  rewrite (update_twice_neq f).
  rewrite update_twice_neq.
  rewrite (update_twice_neq f).
  assert ((f 2 && f 1) = (f 1 && f 2)). apply andb_comm.
  rewrite H. reflexivity.
  1 - 3: lia.
  Local Opaque msb. simpl. rewrite IHn. 
  rewrite MAJ_correct by lia. 
  Local Transparent msb.
  assert (msb (S n) f = (msb n f)[2 * (S n)
          |-> carry (S n) f ⊕ f (2 * (S n) + 2)][2 * (S n) + 1 |-> f (2 * (S n) + 1) ⊕ f (2 * (S n) + 2)]
                    [2 * (S n) + 2 |-> carry (S (S n)) f]). easy.
  rewrite H.
  rewrite <- msb_end2.
  rewrite <- msb_end2.
  assert (S (n + S (n + 0) + 2) = 2 * S n + 2) by lia. rewrite H0. clear H0.
  assert ((S (n + S (n + 0) + 1)) = 2 * S n + 1) by lia. rewrite H0. clear H0.
  assert (S (n + S (n + 0)) = 2 * S n) by lia. rewrite H0. clear H0.
  assert ((2 * n + 2) = 2 * S n) by lia. rewrite H0. clear H0.
  rewrite -> (msb_end_gt n (2 * S n + 1) f). 
  rewrite -> (msb_end_gt n (2 * S n + 2) f). 
  assert (((f (2 * S n + 2) && f (2 * S n + 1))
       ⊕ (f (2 * S n + 2) && msb n f (2 * S n)))
      ⊕ (f (2 * S n + 1) && msb n f (2 * S n)) = msb (S n) f (2 * S n + 2)).
  rewrite msb_end2.
  rewrite carry_extend.
  rewrite andb_comm.
  rewrite <- msb_end2.
  assert ((2 * n + 2) = 2 * S n) by lia. rewrite H0. clear H0.
  reflexivity.
  rewrite H0.
  rewrite (update_twice_neq (msb n f)).
  rewrite (update_twice_neq ((msb n f) [2 * S n + 1 |-> f (2 * S n + 1) ⊕ f (2 * S n + 2)])).
  rewrite (update_twice_neq (msb n f)).
  reflexivity.
  1 - 5 : lia.
  Qed.

Definition MAJ_sign n : bccom := MAJseq n; bccnot (2 * n + 2) (2 * n + 3).


Lemma MAJ_sign_correct_1 :   
  forall m n f, m <= 2 * n + 2 -> 
    (bcexec (MAJ_sign n) f) m = (msb n f) m.
Proof.
intros.
unfold MAJ_sign.
rewrite bcseq_correct.
rewrite MAJseq_correct.
rewrite bccnot_correct.
rewrite (update_index_neq (msb n f) (2 * n + 3)).
reflexivity. lia. lia.
Qed.


Lemma MAJ_sign_correct_2 :   
  forall n f,
    (bcexec (MAJ_sign n) f) (2 * n + 3) = ((msb n f) (2 * n + 2)) ⊕ f (2 * n + 3).
Proof.
intros.
unfold MAJ_sign.
rewrite bcseq_correct.
rewrite MAJseq_correct.
rewrite bccnot_correct.
rewrite update_index_eq.
rewrite xorb_comm.
rewrite (msb_end_gt n (2 * n + 3)).
reflexivity.
lia. lia.
Qed.

Definition msbs n f : nat -> bool := (msb n f)[2 * n + 3 |-> ((msb n f) (2 * n + 2)) ⊕ f (2 * n + 3)].

Lemma msbs_end_gt : 
  forall n m f,
    2 * n + 3 < m ->
    msbs n f m = f m.
Proof.
  intros.
  unfold msbs.
  rewrite <- (msb_end_gt n m f).
  rewrite update_index_neq.
  reflexivity. lia. lia.
Qed. 

Lemma MAJ_sign_correct :   
  forall n f,
    (bcexec (MAJ_sign n) f) = (msbs n f).
Proof.
intros.
  apply functional_extensionality.
  intros.
  destruct (x <=? 2 * n + 2) eqn:eq.
  apply Nat.leb_le in eq.
  rewrite MAJ_sign_correct_1.
  unfold msbs.
  rewrite update_index_neq.
  reflexivity. lia.
  assumption.
  apply Compare_dec.leb_iff_conv in eq.
  destruct (x =? 2 * n + 3) eqn:eq1.
  apply Nat.eqb_eq in eq1.
  unfold msbs.
  rewrite eq1.
  rewrite MAJ_sign_correct_2.
  rewrite update_index_eq.
  reflexivity.
  apply EqNat.beq_nat_false in eq1.
  assert (2 * n + 3 < x) by lia.
  rewrite msbs_end_gt.
  unfold MAJ_sign.
  rewrite bcseq_correct.
  rewrite MAJseq_correct.
  rewrite bccnot_correct.
  rewrite (update_index_neq (msb n f) (2 * n + 3)).
  rewrite msb_end_gt.
  reflexivity. 
  1 - 4: lia.
Qed.

Fixpoint UMAseq len n : bccom :=
  match n with
  | 0 => UMA len (len + 1) (len + 2)
  | S n' => UMAseq len n'; UMA (2 * (len - n)) (2 * (len - n) + 1) (2 * (len - n) + 2)
  end.

Lemma uma_end_gt' :
   forall n len t f, 
        n <= len ->  2 * len + 2 < t ->
        (bcexec (UMAseq len n) f) t = f t.
Proof.
  induction n; intros.
  simpl.
  destruct (f len) eqn:eq1.
  destruct (f (len+1)) eqn:eq2.
  destruct ((f [(len + 2) |-> ¬ (f (len + 2))]) (len + 2)) eqn:eq3.
  destruct (((f [(len + 2) |-> ¬ (f (len + 2))])
                 [len |-> ¬ ((f [(len + 2) |-> ¬ (f (len + 2))]) len)]) len) eqn:eq4.
  repeat rewrite update_index_neq by lia.
  reflexivity. 
  repeat rewrite update_index_neq by lia.
  reflexivity. 
  destruct ((f [(len + 2) |-> ¬ (f (len + 2))]) len) eqn:eq4.
  repeat rewrite update_index_neq by lia.
  reflexivity. 
  rewrite update_index_neq by lia.
  reflexivity. 
  destruct (f (len + 2)) eqn:eq3.
  destruct ((f [len |-> ¬ (f len)]) len) eqn:eq4.
  repeat rewrite update_index_neq by lia.
  reflexivity. 
  rewrite update_index_neq by lia.
  reflexivity. 
  destruct (f len) eqn:eq4.
  rewrite update_index_neq by lia.
  1 - 2: reflexivity.
  destruct (f (len + 2)) eqn:eq2.
  destruct ((f [len |-> ¬ (f len)]) len) eqn:eq3.
  repeat rewrite update_index_neq by lia.
  reflexivity. 
  rewrite update_index_neq by lia.
  reflexivity.
  destruct (f len) eqn:eq3.
  rewrite update_index_neq by lia.
  1 - 2: reflexivity.
  simpl.
  destruct (bcexec (UMAseq len n) f (len - S n + (len - S n + 0))) eqn:eq1.
  destruct (bcexec (UMAseq len n) f (len - S n + (len - S n + 0) + 1)) eqn:eq2.
  destruct (((bcexec (UMAseq len n) f) [len - S n + (len - S n + 0) + 2
     |-> ¬ (bcexec (UMAseq len n) f
              (len - S n + (len - S n + 0) + 2))])
      (len - S n + (len - S n + 0) + 2)) eqn:eq3.
  destruct ((((bcexec (UMAseq len n) f) [len - S n + (len - S n + 0) + 2
    |-> ¬ (bcexec (UMAseq len n) f
             (len - S n + (len - S n + 0) + 2))])
   [len - S n + (len - S n + 0)
   |-> ¬ (((bcexec (UMAseq len n) f)
           [len - S n + (len - S n + 0) + 2
           |-> ¬ (bcexec (UMAseq len n) f
                    (len - S n + (len - S n + 0) + 2))])
            (len - S n + (len - S n + 0)))])
    (len - S n + (len - S n + 0))) eqn:eq4.
  repeat rewrite update_index_neq by lia.
  rewrite (IHn len t f) by lia.
  reflexivity.
  repeat rewrite update_index_neq by lia.
  rewrite (IHn len t f) by lia.
  reflexivity.
  destruct (((bcexec (UMAseq len n) f) [len - S n + (len - S n + 0) + 2
   |-> ¬ (bcexec (UMAseq len n) f
            (len - S n + (len - S n + 0) + 2))])
    (len - S n + (len - S n + 0))) eqn:eq4.
  repeat rewrite update_index_neq by lia.
  rewrite IHn by lia. reflexivity.
  repeat rewrite update_index_neq by lia.
  rewrite IHn by lia. reflexivity.
  destruct (bcexec (UMAseq len n) f (len - S n + (len - S n + 0) + 2)) eqn:eq4.
  destruct (((bcexec (UMAseq len n) f) [len - S n + (len - S n + 0)
   |-> ¬ (bcexec (UMAseq len n) f (len - S n + (len - S n + 0)))])
    (len - S n + (len - S n + 0))) eqn:eq5.
  repeat rewrite update_index_neq by lia.
  rewrite IHn by lia.
  reflexivity.
  repeat rewrite update_index_neq by lia.
  rewrite IHn by lia.
  reflexivity.
  destruct (bcexec (UMAseq len n) f (len - S n + (len - S n + 0))) eqn:eq5.
  repeat rewrite update_index_neq by lia.
  rewrite IHn by lia.
  reflexivity.
  rewrite IHn by lia.
  reflexivity.
  destruct (bcexec (UMAseq len n) f (len - S n + (len - S n + 0) + 2)) eqn:eq2.
  destruct (((bcexec (UMAseq len n) f) [len - S n + (len - S n + 0)
   |-> ¬ (bcexec (UMAseq len n) f (len - S n + (len - S n + 0)))])
    (len - S n + (len - S n + 0))).
  repeat rewrite update_index_neq by lia.
  rewrite IHn by lia.
  reflexivity.
  repeat rewrite update_index_neq by lia.
  rewrite IHn by lia.
  reflexivity.
  destruct (bcexec (UMAseq len n) f (len - S n + (len - S n + 0))) eqn:eq3.
  repeat rewrite update_index_neq by lia.
  rewrite IHn by lia.
  reflexivity.
  rewrite IHn by lia.
  reflexivity.
Qed.

Lemma uma_end_gt :
  forall n m f,
    2 * n + 2 < m ->
    (bcexec (UMAseq n n) f) m = f m.
Proof.
  intros.
  rewrite uma_end_gt'.
  reflexivity.
  lia.
  assumption.
Qed.

Lemma Single_MAJ_UMA_correct :
  forall a b c f,
    a <> b -> b <> c -> a <> c ->
    bcexec ((MAJ c b a); (UMA c b a)) f = ((f[a |-> (f a)])[b |-> (f a ⊕ f b ⊕ f c)])[c |-> (f c)].
Proof.
  intros.
  rewrite bcseq_correct.
  rewrite MAJ_correct.
  remember (((f [a
     |-> ((f a && f b) ⊕ (f a && f c))
         ⊕ (f b && f c)]) [b |-> 
    f b ⊕ f a]) [c |-> f c ⊕ f a]) as g.
  rewrite (UMA_correct_partial a b c f g).
  rewrite update_twice_neq.
  rewrite (update_twice_neq g).
  rewrite Heqg.
  rewrite update_twice_eq.
  rewrite (update_twice_neq ((f [a
    |-> ((f a && f b) ⊕ (f a && f c))
        ⊕ (f b && f c)]) [b |-> 
   f b ⊕ f a])).
  rewrite (update_twice_neq (f [a
    |-> ((f a && f b) ⊕ (f a && f c))
        ⊕ (f b && f c)])).
  rewrite update_twice_eq.
  rewrite (update_twice_neq ((f [a |-> f a]) [b |-> f b ⊕ f a])).
  rewrite update_twice_eq.
  reflexivity.
  1 - 8 : lia.
  rewrite Heqg.
  rewrite (update_twice_neq f).
  rewrite (update_twice_neq (f [b |-> f b ⊕ f a])).
  rewrite update_index_eq.
  reflexivity.
  1 - 2 : lia.
  rewrite Heqg.
  rewrite update_twice_neq.
  rewrite update_index_eq. 
  reflexivity. lia.
  rewrite Heqg.
  rewrite update_index_eq. 
  reflexivity.
  1 - 3 : assumption.
Qed.

Lemma uma_msb_hbit_eq :
   forall n m f, f 0 = false -> m < 2 * n + 3 ->
     bcexec (UMAseq n n) ((msb n f) [2 * n + 2 |-> f (2 * n + 2)]) m =
              bcexec (UMAseq n n) (msb n f) m.
Proof.
  induction n.
  intros.
  simpl.
  rewrite update_index_neq by lia.
  destruct ((((f [0 |-> f 0 ⊕ f 2]) [1 |-> f 1 ⊕ f 2]) [2
       |-> ((f 1 && f 2) ⊕ (f 2 && f 0)) ⊕ (f 1 && f 0)]) 0) eqn:eq.
  rewrite update_index_neq by lia.
  destruct ((((f [0 |-> f 0 ⊕ f 2]) [1 |-> f 1 ⊕ f 2]) [2
       |-> ((f 1 && f 2) ⊕ (f 2 && f 0)) ⊕ (f 1 && f 0)]) 1) eqn:eq1.
  rewrite update_index_eq by lia.
  rewrite update_index_eq by lia.
(*
  rewrite (update_index_eq (((f [0 |-> f 0 ⊕ f 2]) [1 |-> f 1 ⊕ f 2]) [2
      |-> ((f 1 && f 2) ⊕ (f 2 && f 0)) ⊕ (f 1 && f 0)])) by lia.
  rewrite (update_index_eq ((f [0 |-> f 0 ⊕ f 2]) [1 |-> f 1 ⊕ f 2])) by lia.
  rewrite (update_twice_neq f) in eq by lia.
  rewrite (update_twice_neq (f [1 |-> f 1 ⊕ f 2])) in eq by lia.
  rewrite update_index_eq in eq by lia.
  rewrite (update_twice_neq (f [0 |-> f 0 ⊕ f 2])) in eq1 by lia.
  rewrite update_index_eq in eq1 by lia.
  destruct ((f 2)) eqn:eq2.
  assert (¬ true = false) by easy. rewrite H1.
  rewrite xorb_true_r in eq.
  rewrite xorb_true_r in eq1.
  apply negb_true_iff in eq1.
  rewrite eq1. rewrite H.
  rewrite xorb_false_l.
  rewrite andb_false_l.
  rewrite andb_true_l.
  rewrite andb_false_l.
  rewrite xorb_false_l.
  unfold negb.
  rewrite update_index_eq by lia.
  repeat rewrite update_index_neq by lia.
  rewrite update_index_eq by lia.
  destruct (m =? 0) eqn:eq3.
  apply Nat.eqb_eq in eq3.
  rewrite eq3.
  repeat rewrite update_index_neq by lia.
*)
Admitted.

(* Defining the adder implementation based on series of MAJ + UMA. *)



Definition adder n : bccom := MAJseq n; UMAseq n n.



Lemma adder_correct :
   forall n fb, (bcexec (adder n) fb) = insert_f n (adder_spec (get_f n fb) (get_g n fb)) fb.
Proof.
 intros.
 unfold adder,adder_spec,add_bit.
 rewrite bcseq_correct.
 rewrite MAJseq_correct.
Admitted.

(* Defining the comparator implementation.
   The comparator is based on computing x - y, which is computing (x' + y)'. *)
Fixpoint flip_snd n : bccom :=
      match n with 
       | 0 => bcskip
       | S m => flip_snd m; bcx (2 * m + 1)
      end.

Definition comparator n := flip_snd n ; MAJ_sign n ; UMAseq n n ; flip_snd n.

Lemma comparator_correct : 
   forall n fb m, m <= n -> 
         get_f n (bcexec (comparator n) fb) m = compare_spec (get_f n fb) (get_g n fb) m.
Proof.
intros.
Admitted.


Definition times_two n := bcswap 1 (2 * n - 1).

Lemma times_two_correct :
   forall n i fb, 0 < n -> i < n -> 
         fb (2 * n - 1) = false -> get_f n (bcexec (times_two n) fb) i = times_two_spec (get_f n fb) i.
Proof.
intros.
Admitted.

(* first, swap M with zeros. 
   These are the steps before starting one_step. 
   assume the input is x M 0000000 *)
Fixpoint suffle_1 base len n :=
  match n with 0 => bcswap base (len + 1)
             | S m => suffle_1 base len m ;bcswap (base + m) (len + n)
  end.

(* second swap x => x_1 0 x_2 0 ..... x_n 0 *)
Fixpoint suffle_2 n :=
  match n with 0 => bcskip
           | S m => if 1 <? n then bcswap n (2*n-1) ; suffle_2 m else suffle_2 m
  end.

(* move M back to swap *)
Fixpoint suffle_3 base n :=
   match n with 0  => bcskip
            | S m => bcswap (base + m) (2*m+2);suffle_3 base m
   end.

Definition suffle n := suffle_1 (n^3 + 2*n+2) n n ; suffle_2 n ; suffle_3 (n^3 + 2*n+2) n.

(* get the x,M before the code. *)
Definition get_of n f := fun i => if i <? n then f i else false.

Definition get_og n f := fun i => if i <? n then f (n + i) else false.

Definition get_bf b n f := fun i => if i <? n then f (b + i) else false. 

Lemma suffle_correct_1_aux :
    forall n m len fb, n <= len -> n + len < m ->
                 get_f n (bcexec (suffle_1 m len n ; suffle_2 n; suffle_3 m n) fb) = get_of n fb. 
Proof.
intros.
unfold get_f,get_of.
induction n.
simpl. reflexivity.
Admitted.

Lemma suffle_correct_1 :
    forall n fb, 0 < n -> get_f n (bcexec (suffle n) fb) = get_of n fb. 
Proof.
intros.
unfold suffle.
rewrite suffle_correct_1_aux.
reflexivity. lia.
assert (2 * n = n + n ) by lia.
rewrite H0.
assert (n ^ 3 = n * n * n).
unfold Nat.pow. lia.
rewrite H1.
lia.
Qed.


Lemma suffle_correct_2_aux :
    forall n m len fb, n <= len -> n + len < m ->
                 get_g n (bcexec (suffle_1 m len n ; suffle_2 n; suffle_3 m n) fb) = get_og n fb. 
Proof.
intros.
unfold get_f,get_of.
induction n.
simpl. reflexivity.
Admitted.

Lemma suffle_correct_2 :
    forall n fb, 0 < n -> get_g n (bcexec (suffle n) fb) = get_og n fb. 
Proof.
intros.
unfold suffle.
rewrite suffle_correct_2_aux.
reflexivity. lia.
assert (2 * n = n + n ) by lia.
rewrite H0.
assert (n ^ 3 = n * n * n).
unfold Nat.pow. lia.
rewrite H1.
lia.
Qed.


Fixpoint copy_x_low base len n :=
     match n with 0 => bcskip
               | S m => bccont (2 * m + 1) (bcx (2*len+ m + 2); bcx (base + m)); copy_x_low base len m
     end.

Lemma copy_x_low_correct_1 : 
   forall n m base fb, n <= m -> 2 * m + n + 2 < base ->
     get_bf (2 * m + n + 2) n (bcexec (copy_x_low base m n) fb) = get_f n fb.
Proof.
  intros.
  unfold get_f,get_bf.
  induction n.
  simpl. reflexivity.
  simpl.
Admitted.

Lemma copy_x_low_correct_2 : 
   forall n m base fb, n <= m -> 2 * m + n + 2 < base ->
     get_bf base n (bcexec (copy_x_low base m n) fb) = get_f n fb.
Proof.
  intros.
  unfold get_f,get_bf.
  induction n.
  simpl. reflexivity.
  simpl.
Admitted.

Definition init n := suffle n ; copy_x_low (n^3 + n+2) n n.

Lemma init_correct_1 :
   forall n fb, get_f n (bcexec (init n) fb) = get_of n fb.
Proof.
 intros.
 unfold init.
 rewrite bcseq_correct.
 rewrite <- suffle_correct_1.
Admitted.

Lemma init_correct_2 :
   forall n fb, get_g n (bcexec (init n) fb) = get_og n fb.
Proof.
 intros.
 unfold init.
 rewrite bcseq_correct.
 rewrite <- suffle_correct_2.
Admitted.

Lemma init_correct_3 :
   forall n fb, get_bf ((n^3 + n+2)) n (bcexec (init n) fb) = get_of n fb.
Proof.
 intros.
 unfold init.
 rewrite bcseq_correct.
Admitted.

Lemma init_correct_4 :
   forall n fb, get_bf (2 * n + n + 2) n (bcexec (init n) fb) = get_of n fb.
Proof.
 intros.
 unfold init.
 rewrite bcseq_correct.
Admitted.


(* This is the one_step_impl. *)
Definition first_half n := times_two n; (comparator n);bccont (2 * n + 1) (adder n).

Lemma first_half_correct_1:
  forall n fb, get_f n (bcexec (first_half n) fb) = one_step_sepc n (get_f n fb) (get_g n fb).
Proof.
  intros.
Admitted.

Lemma first_half_correct_2:
  forall n fb, get_g n (bcexec (first_half n) fb) = (get_g n fb).
Proof.
  intros.
Admitted.

Fixpoint swap_x len n :=
   match n with 0 => bcskip
            | S m => bcswap (2*len + m + 2) (2*m+1);swap_x len m
   end.

Fixpoint swap_M n :=
   match n with 0 => bcskip
            | S m => bcswap (2*m+1) (2*m+2);swap_M m
   end.


(* If you want to add x back, please add here. It does not affect 
   the result of 2x%M *)
Definition second_half n := swap_M n ; swap_x n n; comparator n.

Lemma second_half_correct:
  forall n fb, (bcexec (first_half n; second_half n) fb) (2*n+1) = false.
Proof.
  intros.
Admitted.

(* remove x - (2x %M) to other place, and then move 2x%M there for further calculation. *)
Fixpoint swap_clean_1 base n := 
   match n with 0 => bcskip
             | S m => bcswap (base + m) (2*m+1);swap_clean_1 base m
   end.

Fixpoint copy_r len n := 
     match n with 0 => bcskip
            | S m => bccont (2 * m + 1) (bcx (2*len+m + 2)); copy_r len m
     end.

Definition one_step_clean base n := swap_clean_1 base n; swap_x n n; swap_M n; copy_r n n.

Definition one_step base n := first_half n ; second_half n; one_step_clean base n.

Lemma one_step_correct_1:
 forall n base fb, 0 < n -> 3 * n + 2 < base ->
      get_f n (bcexec (one_step base n) fb) = one_step_sepc n (get_f n fb) (get_g n fb).
Proof.
 intros.
Admitted.

Lemma one_step_correct_2:
 forall n base fb, 0 < n -> 3 * n + 2 < base ->
      get_g n (bcexec (one_step base n) fb) = get_g n fb.
Proof.
  intros.
Admitted.

Lemma one_step_correct_3:
 forall n base fb, 0 < n -> 3 * n + 2 < base ->
      get_bf (2*n+2) n (bcexec (one_step base n) fb) = one_step_sepc n (get_f n fb) (get_g n fb).
Proof.
  intros.
Admitted.

Lemma one_step_correct_4:
 forall n base fb, 0 < n -> 3 * n + 2 < base ->
      get_bf base n (bcexec (one_step base n) fb) = get_f n fb.
Proof.
  intros.
Admitted.


Fixpoint swap_high_x base n :=
  match n with 0 => bcskip
            | S m => bcswap (2*m+2) (base + m);swap_high_x base m
  end.

Fixpoint suffle_back n :=
    match n with 0 => bcskip
              | S m => suffle_back m ; bcswap m (2 * m + 1)
    end.

Fixpoint suffle_M base len n :=
    match n with 0 => bcskip
              | S m => bcswap (base + m) (len + m); suffle_M base len m
    end.

Definition basis_step_impl high_base n :=
       swap_high_x high_base n; adder n; swap_high_x high_base n
         ;  comparator n; bccont (2 * n + 1) (adder n)
         ; swap_high_x high_base n; swap_M n
         ; comparator n; adder n; swap_high_x high_base n
         ; suffle_3 (high_base + n) n; suffle_back n ; suffle_M (high_base + n) n n.

Lemma basis_step_impl_correct_1:
  forall n base fb, 0 < n -> 2 * n + 1 < base ->
    get_bf (base + n) n (bcexec (basis_step_impl base n) fb) = basis_step_spec n (get_bf base n fb) (get_f n fb) (get_g n fb).
Proof.
  intros.
Admitted.

Lemma basis_step_impl_correct_2:
  forall n base fb, 0 < n -> 2 * n + 1 < base ->
    get_of n (bcexec (basis_step_impl base n) fb) = (get_bf base n fb).
Proof.
  intros.
Admitted.

Lemma basis_step_impl_correct_3:
  forall n base fb, 0 < n -> 2 * n + 1 < base ->
    get_og n (bcexec (basis_step_impl base n) fb) = (get_g n fb).
Proof.
  intros.
Admitted.

Definition basis_step_no_step high_base n :=
       swap_M n ; swap_high_x high_base n ; swap_M n ;
               suffle_3 (high_base + n) n; suffle_back n ; suffle_M (high_base + n) n n.


Lemma basis_step_no_step_correct_1:
  forall n base fb, 0 < n -> 2 * n + 1 < base ->
    get_bf (base + n) n (bcexec (basis_step_no_step base n) fb) = (get_f n fb).
Proof.
  intros.
Admitted.

Lemma basis_step_no_step_correct_2:
  forall n base fb, 0 < n -> 2 * n + 1 < base ->
    get_of n (bcexec (basis_step_no_step base n) fb) = (get_bf base n fb).
Proof.
  intros.
Admitted.

Lemma basis_step_no_step_correct_3:
  forall n base fb, 0 < n -> 2 * n + 1 < base ->
    get_og n (bcexec (basis_step_no_step base n) fb) = (get_g n fb).
Proof.
  intros.
Admitted.


Fixpoint repeat_step_impl base dim n :=
   match n with 
    | 0 => bcskip
    | S m => one_step base dim ; repeat_step_impl (base+dim) dim m
   end.

Lemma repeat_step_impl_correct_1 :
   forall n len base fb, 0 < n -> n <= len -> 2 * n + 1 < base ->
     get_f n (bcexec (repeat_step_impl base len n) fb) = repeat_step_spec n len (get_f n fb) (get_g n fb).
Proof.
 intros.
Admitted.

(* I guess we will need a repeat step correctness 2 here to state that what happen to the bits in base + n each time
   but I don't know how to state here. *)

Fixpoint all_step' n fold_base base dim (c: nat -> bool) : bccom :=
   match n with 
    | 0 => if c 0 then basis_step_impl fold_base dim else basis_step_no_step fold_base dim 
    | S m => if c n then (repeat_step_impl base dim n) ; all_step' m fold_base (base+dim^2) dim c
                    else all_step' m fold_base base dim c
   end.


Definition all_step n (c: nat -> bool) := init n; all_step' (n - 1) (n^3 + n+2) (3*n+2) n c.

Definition fb_wf n f := (0 < n) /\ (forall i, 2 * n < i -> f i = false).

Lemma all_step_correct_1 :
      forall n c fb, fb_wf n fb ->
            get_bf (n^3 + 2*n+2) n (bcexec (all_step n c) fb) = all_step_spec n c (get_of n fb) (get_og n fb).
Proof.
 intros.
Admitted.

Lemma all_step_correct_2 :
      forall n c fb, fb_wf n fb ->
            get_of n (bcexec (all_step n c) fb) = (get_of n fb).
Proof.
 intros.
Admitted.


Lemma all_step_correct_3 :
      forall n c fb, fb_wf n fb ->
            get_og n (bcexec (all_step n c) fb) = (get_og n fb).
Proof.
 intros.
Admitted.



