Require Import VectorStates UnitaryOps Coq.btauto.Btauto RCIR ModularMultSpec.


Local Open Scope nat_scope.
Local Open Scope bccom_scope.

(**********************)
(** Unitary Programs - Modular Multiplier. **)
(**********************)


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

Fixpoint carry n f :=
  match n with
  | 0 => f 0
  | S n' => let c := carry n' f in
           let a := f (2 * n' + 1) in
           let b := f (2 * n' + 2) in
           (a && b) ⊕ (b && c) ⊕ (a && c)
  end.

Lemma carry_extend :
  forall n f,
    carry (S n) f = (f (2 * n + 1) && f (2 * n + 2)) ⊕ 
  (f (2 * n + 2) && carry n f) ⊕ (f (2 * n + 1) && carry n f).
Proof.
  intros. easy.
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

Fixpoint UMAseq n : bccom :=
  match n with
  | 0 => UMA 0 1 2
  | S n' => UMA (2 * n) (2 * n + 1) (2 * n + 2) ; UMAseq n'
  end.

Lemma uma_end_gt :
  forall n m f,
    2 * n + 2 < m ->
    (bcexec (UMAseq n) f) m = f m.
Proof.
  induction n; intros. simpl.
  destruct (f 0) eqn:eq1.
  destruct (f 1) eqn:eq2.
  destruct ((f [2 |-> ¬ (f 2)]) 2) eqn:eq3.
  destruct (((f [2 |-> ¬ (f 2)]) [0 |-> ¬ ((f [2 |-> ¬ (f 2)]) 0)]) 0) eqn:eq4.
  repeat rewrite update_index_neq by lia.
  reflexivity. 
  repeat rewrite update_index_neq by lia.
  reflexivity. 
  destruct ((f [2 |-> ¬ (f 2)]) 0) eqn:eq4.
  repeat rewrite update_index_neq by lia.
  reflexivity. 
  rewrite update_index_neq by lia.
  reflexivity. 
  destruct (f 2) eqn:eq3.
  destruct ((f [0 |-> ¬ (f 0)]) 0) eqn:eq4.
  repeat rewrite update_index_neq by lia.
  reflexivity. 
  rewrite update_index_neq by lia.
  reflexivity. 
  destruct (f 0) eqn:eq4.
  rewrite update_index_neq by lia.
  1 - 2: reflexivity.
  destruct (f 2) eqn:eq2.
  destruct ((f [0 |-> ¬ (f 0)]) 0) eqn:eq3.
  repeat rewrite update_index_neq by lia.
  reflexivity. 
  rewrite update_index_neq by lia.
  reflexivity.
  destruct (f 0) eqn:eq3.
  rewrite update_index_neq by lia.
  1 - 2: reflexivity.
  simpl.
  destruct (f (S (n + S (n + 0)))) eqn:eq1.
  destruct (f (S (n + S (n + 0) + 1))) eqn:eq2.
  destruct ((f [S (n + S (n + 0) + 2)
       |-> ¬ (f (S (n + S (n + 0) + 2)))])
        (S (n + S (n + 0) + 2))) eqn:eq3.
  destruct (((f [S (n + S (n + 0) + 2)
      |-> ¬ (f (S (n + S (n + 0) + 2)))]) [
     S (n + S (n + 0))
     |-> ¬ ((f [S (n + S (n + 0) + 2)
             |-> ¬ (f (S (n + S (n + 0) + 2)))])
              (S (n + S (n + 0))))]) (S (n + S (n + 0)))) eqn:eq4.
  rewrite (IHn m (((f [S (n + S (n + 0) + 2)
     |-> ¬ (f (S (n + S (n + 0) + 2)))]) [
    S (n + S (n + 0))
    |-> ¬ ((f [S (n + S (n + 0) + 2)
            |-> ¬ (f (S (n + S (n + 0) + 2)))])
             (S (n + S (n + 0))))]) [S (n + S (n + 0) + 1)
   |-> ¬ (((f [S (n + S (n + 0) + 2)
            |-> ¬ (f (S (n + S (n + 0) + 2)))])
           [S (n + S (n + 0))
           |-> ¬ ((f [S (n + S (n + 0) + 2)
                   |-> ¬ (f (S (n + S (n + 0) + 2)))])
                    (S (n + S (n + 0))))])
            (S (n + S (n + 0) + 1)))])) by lia.
  repeat rewrite update_index_neq by lia.
  reflexivity.
  rewrite IHn by lia.
  repeat rewrite update_index_neq by lia.
  reflexivity.
  destruct ((f [S (n + S (n + 0) + 2)
     |-> ¬ (f (S (n + S (n + 0) + 2)))]) 
      (S (n + S (n + 0)))) eqn:eq4.
  rewrite IHn by lia.
  repeat rewrite update_index_neq by lia.
  reflexivity.
  rewrite IHn by lia.
  repeat rewrite update_index_neq by lia.
  reflexivity.
  destruct (f (S (n + S (n + 0) + 2))) eqn:eq3.
  destruct ((f [S (n + S (n + 0)) |-> ¬ (f (S (n + S (n + 0))))])) eqn:eq4.
  rewrite IHn by lia.
  repeat rewrite update_index_neq by lia.
  reflexivity.
  rewrite IHn by lia.
  rewrite update_index_neq by lia.
  reflexivity.
  destruct (f (S (n + S (n + 0)))) eqn:eq4.
  rewrite IHn by lia.
  rewrite update_index_neq by lia.
  reflexivity.
  rewrite IHn by lia.
  reflexivity.
  destruct (f (S (n + S (n + 0) + 2))) eqn:eq2.
  destruct ((f [S (n + S (n + 0)) |-> ¬ (f (S (n + S (n + 0))))])
      (S (n + S (n + 0)))) eqn:eq3.
  rewrite IHn by lia.
  repeat rewrite update_index_neq by lia.
  reflexivity.
  rewrite IHn by lia.
  rewrite update_index_neq by lia.
  reflexivity.
  destruct (f (S (n + S (n + 0)))) eqn:eq3.
  rewrite IHn by lia.
  rewrite update_index_neq by lia.
  reflexivity.
  rewrite IHn by lia.
  reflexivity.
Qed.

(* Defining the adder implementation based on series of MAJ + UMA. *)

(* First, we need to define a function to grab three fbools out of a single uniformed fbools. 
   The structure of the fbool is like
     from 0 to 2n+2 are bits messing around for f and g and extra c bit and high bit for comparator. *)
Definition get_f (fb:nat -> bool) := fun i => fb (2 * i + 1).

Definition get_g (fb:nat -> bool) := fun i => fb (2 * i + 2).

Definition get_fold base (fb:nat -> bool) := fun i => fb (base + i).

Fixpoint insert_f n f (fb:nat -> bool) :=
     match n with 
          | 0 => fb
          | S m => insert_f m f (fb[2 * m + 1 |-> f m])
     end.

Lemma get_insert_f_same:
  forall n f, insert_f n (get_f f) f = f.
Proof.
  intros.
  unfold get_f.
  induction n.
  simpl.
  reflexivity.
  simpl in *.
  rewrite update_same.
  rewrite IHn.
  reflexivity.
  reflexivity.
Qed.


Definition adder n : bccom := MAJ_sign n; UMAseq n.

Lemma adder_correct :
   forall n fb m, m < n -> get_f (bcexec (adder n) fb) m = adder_spec (get_f fb) (get_g fb) m.
Proof.
intros.
Admitted.

(* Defining the comparator implementation.
   The comparator is based on computing x - y, which is computing (x' + y)'. *)
Fixpoint flip_snd n : bccom :=
      match n with 
       | 0 => bcskip
       | S m => flip_snd m; bcx (2 * m + 1)
      end.

Definition comparator n := flip_snd n ; adder n ; flip_snd n.

Lemma comparator_correct : 
   forall n fb m, m <= n -> get_f (bcexec (comparator n) fb) m = compare_spec (get_f fb) (get_g fb) m.
Proof.
intros.
Admitted.


Definition times_two n := bcswap 1 (2 * n - 1).

Lemma times_two_correct :
   forall n i fb, 0 < n -> i < n -> 
         fb (2 * n - 1) = false -> get_f (bcexec (times_two n) fb) i = times_two_spec (get_f fb) i.
Proof.
intros.
Admitted.


Definition one_step n := times_two n; (comparator n) ; bccont (2 * n + 1) (adder n).

Lemma one_step_correct_f :
   forall n m i fb, 0 < n -> 2 * n + 1 < m -> i <= n -> fb m = false ->
        get_f (bcexec (one_step n) fb) i = one_step_sepc n (get_f fb) (get_g fb) i.
Proof.
intros.
Admitted.

Lemma one_step_correct_g :
   forall n m i fb, 0 < n -> 2 * n + 1 < m -> i < n -> fb m = false ->
        get_g (bcexec (one_step n) fb) i = (get_g fb) i.
Proof.
intros.
Admitted.

Definition clean_impl n m := bcswap (2 * n + 1) m.

Lemma clean_correct :
   forall n m fb, 0 < n -> 2 * n + 1 < m  -> fb m = false -> 
         (bcexec (clean_impl n m) fb) (2 * n + 1) = false.
Proof.
  intros.
  unfold clean_impl.
  rewrite bcswap_correct.
  destruct (2 * n + 1 =? 2 * n + 1) eqn:eq.
  rewrite H1. reflexivity.
  apply EqNat.beq_nat_false  in eq.
  lia. lia.
Qed.

Fixpoint repeat_step_impl base dim len :=
   match len with 
    | 0 => bcskip
    | S m => one_step dim ; clean_impl dim (base + m) ; repeat_step_impl base dim m
   end.

Lemma repeat_step_correct :
   forall dim base len fb i, 0 < dim -> 2 * dim + 1 < base + len -> i < dim -> fb (base + len) = false ->
        get_f (bcexec (repeat_step_impl base dim len) fb) = repeat_step_spec len dim (get_f fb) (get_g fb).
Proof.
intros.
Admitted.

Fixpoint switch_fold base n := 
    match n with 
         | 0 => bcskip
         | S m => bcswap (2 * m + 2) (base + m); switch_fold base m
    end.

Definition basis_step_impl n fold_base := 
           switch_fold fold_base n ; adder n; switch_fold fold_base n;
                comparator n; bccont (2 * n + 1) (adder n).

Lemma basis_step_correct :
   forall n base fb, 0 < n -> 2 * n + 1 < base -> fb (2 * n + 1) = false ->
           get_f (bcexec (basis_step_impl n base) fb) = basis_step_spec n (get_fold base fb) (get_f fb) (get_g fb).
Proof.
  intros.
Admitted.

(* Defining the all step for the fb. The whole structure of fb is:
    the bits from 0 to 2 * n + 1 are combining f and g and the c bit and the high bit. 
    from 2 * n + 2 to n^2 + 2 * n + 2 are zero ancilla bits for cleaning the 2*n+1 bit for futher calculation. 
    The bits from n^2 + 2*n + 2 to n^2 + 2*n + n + 1 are to store the fold value of f bits (1 to 2 * n + 1 bits.
    The fold value is useful to compute the addition at f 0. *)
Fixpoint all_step' n fold_base base dim (c: nat -> bool) : bccom :=
   match n with 
    | 0 => if c 0 then basis_step_impl dim fold_base else bcskip 
    | S m => if c n then (repeat_step_impl base dim n) ; all_step' m fold_base (base+dim) dim c
                    else all_step' m fold_base base dim c
   end.
Definition all_step n (c: nat -> bool) := all_step' (n - 1) (n^2 + 2*n + 2) (2*n+2) n c.

Definition fb_wf n f := (0 > n) /\ (forall i, 2 * n < i < n ^ 2 + 2 * n + 2 -> f i = false).

Lemma all_step_correct :
      forall n c fb, fb_wf n fb ->
            get_f (bcexec (all_step n c) fb) = all_step_spec n c (get_f fb) (get_g fb).
Proof.
 intros.
Admitted.


