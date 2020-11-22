Require Import VectorStates UnitaryOps Coq.btauto.Btauto.

Inductive bccom :=
| bcskip
| bcx (n : nat)
(*| bcnot (x y : nat)*)
| bccont (n : nat) (p : bccom)
| bcseq (p1 p2 : bccom)
.

Declare Scope bccom_scope.
Delimit Scope bccom_scope with bccom.
Local Open Scope bccom.
Notation "p1 ; p2" := (bcseq p1 p2) (at level 50) : bccom_scope.
Notation "f '[' i '|->' x ']'" := (update f i x) (at level 10).
Local Open Scope nat_scope.

Definition bccnot (x y : nat) := bccont x (bcx y).
Definition bcswap (x y : nat) := bccnot x y; bccnot y x; bccnot x y.
Definition bcccnot (x y z : nat) := bccont x (bccnot y z).

Fixpoint bcexec (p : bccom) (f : nat -> bool) :=
  match p with
  | bcskip => f
  | bcx n => f [n |-> (¬ (f n))]
  (*  | bccnot x y => update f y ((f y) ⊕ (f x)) *)
  | bccont n p => if f n then bcexec p f else f
  | bcseq p1 p2 => bcexec p2 (bcexec p1 f)
  end.

Ltac BreakIf :=
  match goal with
  | [ |- context[if ?X then _ else _] ] => destruct X eqn:?
  | [ H : context[if ?X then _ else _] |- _ ] => destruct X eqn:?
  end.

Ltac gen_if_no T P :=
  match goal with
  | [ H : T |- _ ] => idtac
  | _ => assert (T) by P
  end.

Lemma neq_sym :
  forall {T} (x y : T),
    x <> y -> y <> x.
Proof.
  intros. intro. rewrite H0 in H. easy.
Qed.

Ltac GenNeq :=
  match goal with
  | [ H : ?x <> ?y |- _ ] => gen_if_no (y <> x) (apply (neq_sym x y H))
  end.

Ltac EqbEq :=
  match goal with
  | [ H : (?x =? ?y) = true |- _ ] => repeat rewrite H; rewrite Nat.eqb_eq in H; subst
  end.

Ltac EqbRefl :=
  match goal with
  | [ |- context[?x =? ?x] ] => repeat rewrite Nat.eqb_refl; simpl
  end.

Ltac EqbNeq :=
  match goal with
  | [ H : ?x =? ?y = false |- _ ] => repeat rewrite H; rewrite Nat.eqb_neq in H; GenNeq
  end.

Ltac EqEqb :=
  match goal with
  | [ H : ?x = ?y |- context[?x =? ?y] ] => rewrite <- (Nat.eqb_eq x y H); simpl
  | [ H : ?x <> ?y |- context[?x =? ?y] ] => rewrite <- (Nat.eqb_neq x y H); simpl
  end.

Ltac Negb :=
  match goal with
  | [ H : ¬ ?b = false |- _ ] => rewrite negb_false_iff in H
  | [ H : ¬ ?b = true |- _ ] => rewrite negb_true_iff in H
  end.

Ltac boolsub :=
  match goal with
  | [ H : ?b = true |- context[?b] ] => rewrite H
  | [ H : ?b = false |- context[?b] ] => rewrite H
  | [ H1 : ?b = true, H2 : ?b = false |- _ ] => rewrite H1 in H2; discriminate H2
  | [ H1 : ?b = true, H2 : context[?b] |- _ ] => rewrite H1 in H2; simpl in H2
  | [ H1 : ?b = false, H2 : context[?b] |- _ ] => rewrite H1 in H2; simpl in H2
  end.

Ltac bdes exp :=
  match exp with
  | ?a ⊕ ?b => bdes a; bdes b
  | ?a && ?b => bdes a; bdes b
  | ?a || ?b => bdes a; bdes b
  | ¬ ?a => bdes a
  | true => idtac
  | false => idtac
  | ?a => destruct a eqn:?; repeat boolsub; try easy
  end.

Ltac bsimpl :=
  simpl in *;
  match goal with
  | [ |- true = false ] => match goal with
                         | [ H : context[?a ⊕ ?b] |- _ ] => bdes a; bdes b
                         | [ H : context[?a && ?b] |- _ ] => bdes a; bdes b
                         | [ H : context[?a || ?b] |- _ ] => bdes a; bdes b
                         | [ H : context[¬ ?a] |- _ ] => bdes a
                         end
  | [ |- false = true ] => match goal with
                         | [ H : context[?a ⊕ ?b] |- _ ] => bdes a; bdes b
                         | [ H : context[?a && ?b] |- _ ] => bdes a; bdes b
                         | [ H : context[?a || ?b] |- _ ] => bdes a; bdes b
                         | [ H : context[¬ ?a] |- _ ] => bdes a
                         end
  | [ |- ?a = ?b ] => bdes a; bdes b
  end.

Ltac Expand fl :=
  match fl with
  | [] => idtac
  | ?x :: ?fl' => match goal with
                | [ H : x = ?b |- _ ] => repeat (rewrite H; simpl)
                | _ => idtac
                end;
                Expand fl'
  end.

Ltac bnauto_expand fl :=
  try btauto;
  repeat (BreakIf; repeat EqbEq; repeat EqbRefl; 
     repeat EqbNeq; repeat Negb; repeat boolsub; try (Expand fl); try easy; try btauto);
  repeat bsimpl.  

Ltac bnauto := bnauto_expand (@List.nil bool).

Lemma bcseq_correct :
  forall p1 p2 f, bcexec (p1 ; p2) f = bcexec p2 (bcexec p1 f).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma bccnot_correct :
  forall x y f,
    x <> y ->
    bcexec (bccnot x y) f = f[y |-> (f y ⊕ f x)].
Proof.
  intros. apply functional_extensionality; intro i. simpl. unfold update.
  bnauto.
Qed.

Lemma bcswap_correct :
  forall x y f,
    x <> y ->
    bcexec (bcswap x y) f = fun i => if i =? x then f y else if i =? y then f x else f i.
Proof.
  intros. apply functional_extensionality; intro i. simpl.
  unfold update. bnauto.
Qed.

Lemma bcccnot_correct :
  forall x y z f,
    x <> y ->
    y <> z ->
    x <> z ->
    bcexec (bcccnot x y z) f = f[z |-> (f z ⊕ (f y && f x))].
Proof.
  intros. apply functional_extensionality; intro i. simpl. unfold update. bnauto.
Qed.

(*Here we define the wellformedness of bc circuit. *)
Inductive bcfresh : nat -> bccom -> Prop :=
| bcfresh_skip : forall q, q <> 0 -> bcfresh q bcskip 
     (* q <> 0 fits the requirement in SQIR, which is unnecessary in principle *)
| bcfresh_x : forall q n, q <> n -> bcfresh q (bcx n)
| bcfresh_cont : forall q n p, q <> n -> bcfresh q p -> bcfresh q (bccont n p)
| bcfresh_seq  : forall q p1 p2, bcfresh q p1 -> bcfresh q p2 -> bcfresh q (p1; p2)
.

Inductive bc_well_formed : bccom -> Prop :=
| bcWF_skip : bc_well_formed bcskip
| bcWF_x : forall n, bc_well_formed (bcx n)
| bcWF_cont : forall n p,  bcfresh n p -> bc_well_formed p -> bc_well_formed (bccont n p)
| bcWF_seq : forall p1 p2, bc_well_formed p1 -> bc_well_formed p2 -> bc_well_formed (p1; p2)
.

Inductive bcWT (dim : nat) : bccom -> Prop :=
| bcWT_skip : dim > 0 -> bcWT dim bcskip
| bcWT_x : forall n, n < dim -> bcWT dim (bcx n)
| bcWT_cont : forall n p, n < dim -> bcfresh n p -> bcWT dim p -> bcWT dim (bccont n p)
| bcWT_seq : forall p1 p2, bcWT dim p1 -> bcWT dim p2 -> bcWT dim (p1; p2)
.

Lemma bcWT_bc_well_formed :
  forall dim p,
    bcWT dim p -> bc_well_formed p.
Proof.
  intros. induction p; inversion H; subst; constructor.
  - easy.
  - apply IHp. easy.
  - apply IHp1. easy.
  - apply IHp2. easy.
Qed.

Lemma bcWT_enlarge :
  forall p dim dim',
    dim < dim' ->
    bcWT dim p ->
    bcWT dim' p.
Proof.
  induction p; intros; inversion H0; subst; constructor; try easy; try lia.
  - apply IHp with (dim := dim); easy.
  - apply IHp1 with (dim := dim); easy.
  - apply IHp2 with (dim := dim); easy.
Qed.
    
(* compiling bc circuit to SQIR. *)
Fixpoint bc2ucom {dim} (p : bccom) : base_ucom dim :=
  match p with
  | bcskip => SKIP
  | bcx n => X n
  | bccont n p => control n (bc2ucom p)
  | bcseq p1 p2 => useq (bc2ucom p1) (bc2ucom p2)
  end.

Local Transparent ID. 
Lemma bcfresh_is_fresh :
  forall q p {dim},
    bcfresh q p -> @is_fresh _ dim q (bc2ucom p).
Proof.
  intros. induction p; simpl; inversion H.
  - apply fresh_app1. easy.
  - apply fresh_X. easy.
  - apply IHp in H4. apply fresh_control; easy.
  - apply IHp1 in H3. apply IHp2 in H4. apply fresh_seq; easy.
Qed.

Lemma bcWT_uc_well_typed :
  forall p {dim},
    bcWT dim p -> @uc_well_typed _ dim (bc2ucom p).
Proof.
  intros. induction p; simpl; inversion H.
  - constructor. easy.
  - apply uc_well_typed_X. easy.
  - apply IHp in H4. apply bcfresh_is_fresh with (dim := dim) in H3. apply uc_well_typed_control; easy.
  - apply IHp1 in H2. apply IHp2 in H3. apply WT_seq; easy.
Qed.
Local Opaque ID.

Lemma bcfresh_bcexec_irrelevant :
  forall p q f,
    bcfresh q p ->
    bcexec p f q = f q.
Proof.
  induction p; intros.
  - easy.
  - inversion H; subst. simpl. apply update_index_neq. lia.
  - inversion H; subst. apply IHp with (f := f) in H4. simpl. destruct (f n); easy.
  - inversion H; subst. apply IHp1 with (f := f) in H3. apply IHp2 with (f := bcexec p1 f) in H4. simpl.
    rewrite H4. rewrite H3. easy.
Qed.

Lemma bc2ucom_correct :
  forall dim p f,
    dim > 0 ->
    bcWT dim p ->
    (uc_eval (bc2ucom p)) × (f_to_vec dim f) = f_to_vec dim (bcexec p f).
Proof.
  intros dim p. induction p; intros; simpl.
  - rewrite denote_SKIP. Msimpl. easy. easy.
  - apply f_to_vec_X. inversion H0. easy.
  - inversion H0. assert (WT := H5). assert (FS := H4).
    apply bcfresh_is_fresh with (dim := dim) in H4. apply bcWT_uc_well_typed in H5.
    rewrite control_correct; try easy.
    destruct (f n) eqn:Efn.
    + rewrite Mmult_plus_distr_r.
      rewrite Mmult_assoc. rewrite IHp by easy.
      rewrite f_to_vec_proj_neq, f_to_vec_proj_eq; try easy.
      Msimpl. easy.
      rewrite bcfresh_bcexec_irrelevant; easy.
      rewrite Efn. easy.
    + rewrite Mmult_plus_distr_r.
      rewrite Mmult_assoc. rewrite IHp by easy.
      rewrite f_to_vec_proj_eq, f_to_vec_proj_neq; try easy.
      Msimpl. easy.
      rewrite bcfresh_bcexec_irrelevant by easy.
      rewrite Efn. easy.
  - inversion H0. specialize (IHp1 f H H3).
    rewrite Mmult_assoc. rewrite IHp1.
    specialize (IHp2 (bcexec p1 f) H H4).
    easy.
Qed.

(* Define bcinv op. For any bc_seq op, inv means to reverse the order. *)
Fixpoint bcinv p :=
  match p with
  | bcskip => bcskip
  | bcx n => bcx n
  | bccont n p => bccont n (bcinv p)
  | bcseq p1 p2 => bcinv p2; bcinv p1
  end.

Lemma bcinv_involutive :
  forall p,
    bcinv (bcinv p) = p.
Proof.
  induction p; simpl; try easy.
  - rewrite IHp. easy.
  - rewrite IHp1, IHp2. easy.
Qed.

Lemma bcfresh_bcinv :
  forall p q,
    bcfresh q p ->
    bcfresh q (bcinv p).
Proof.
  induction p; intros; inversion H; simpl; subst; try easy.
  - apply IHp in H4. constructor; easy.
  - apply IHp1 in H3. apply IHp2 in H4. constructor; easy.
Qed.

Lemma bc_well_formed_bcinv :
  forall p,
    bc_well_formed p ->
    bc_well_formed (bcinv p).
Proof.
  induction p; intros; inversion H; subst; simpl; constructor.
  - apply bcfresh_bcinv. easy.
  - apply IHp. easy.
  - apply IHp2. easy.
  - apply IHp1. easy.
Qed.

Lemma bcinv_correct :
  forall p f,
    bc_well_formed p ->
    bcexec (bcinv p; p) f = f.
Proof.
  induction p; intros; simpl.
  - easy.
  - apply functional_extensionality; intros. unfold update.
    bdestruct (x =? n). rewrite Nat.eqb_refl. subst. destruct (f n); easy.
    easy.
  - inversion H; subst. destruct (f n) eqn:Efn.
    assert (bcfresh n (bcinv p)) by (apply bcfresh_bcinv; easy).
    rewrite bcfresh_bcexec_irrelevant by easy. rewrite Efn.
    specialize (IHp f H3). simpl in IHp. easy.
    rewrite Efn. easy.
  - inversion H; subst. simpl in IHp1, IHp2.
    specialize (IHp1 (bcexec (bcinv p2) f) H2). rewrite IHp1.
    apply IHp2. easy.
Qed.

Lemma bcinv_correct_rev :
  forall p f,
    bc_well_formed p ->
    bcexec (p; bcinv p) f = f.
Proof.
  intros. apply bc_well_formed_bcinv in H.
  apply bcinv_correct with (f := f) in H.
  rewrite bcinv_involutive in H. easy.
Qed.

Definition MAJ a b c := bccnot c b ; bccnot c a ; bcccnot a b c.
Definition MAJ_neg a b c := bcinv (MAJ a b c).
Definition UMA a b c := bcccnot a b c ; bccnot c a ; bccnot a b.

Lemma MAJ_correct :
  forall a b c f,
    a <> b -> b <> c -> a <> c ->
    bcexec (MAJ c b a) f = ((f[a |-> 
    ((f a && f b) ⊕ (f a && f c) ⊕ (f b && f c))])[b |-> (f b ⊕ f a)])[c |-> (f c ⊕ f a)].
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

Fixpoint good_out' n f : nat -> bool :=
  match n with
  | 0 => f[1 |-> f 2 ⊕ f 1 ⊕ f 0]
  | S n' => (good_out' n' f)[2 * n + 1 |-> f (2 * n + 2) ⊕ f (2 * n + 1) ⊕ f (2 * n)]
  end.

Definition good_out n f : nat -> bool :=
     (good_out' n f)[2 * n + 3 |-> ((msb n f) (2 * n + 2)) ⊕ f (2 * n + 3)].

Lemma MAJ_UMA_correct :
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

Lemma uma_less_gt_same:
   forall n m f i b,
  m < 2 * n + 3 <= i ->
    bcexec (UMAseq n) (update f i b) m = bcexec (UMAseq n) f m.
Proof.
intro n.
induction n.
intros. 
destruct H.
simpl.
rewrite (update_index_neq f i 0).
rewrite (update_index_neq f i 1).
rewrite (update_index_neq f i 2).
destruct (f 0) eqn:eq1.
destruct (f 1) eqn:eq2.
rewrite (update_twice_neq f).
rewrite (update_index_neq (f [2 |-> ¬ (f 2)]) i 2).
destruct ((f [2 |-> ¬ (f 2)]) 2) eqn:eq3.
rewrite (update_index_neq (f [2 |-> ¬ (f 2)]) i 0).
rewrite (update_twice_neq (f [2 |-> ¬ (f 2)])).
rewrite (update_index_neq ((f [2 |-> ¬ (f 2)]) [0
          |-> ¬ ((f [2 |-> ¬ (f 2)]) 0)])).
rewrite (update_index_neq ((f [2 |-> ¬ (f 2)]) [0 |-> ¬ ((f [2 |-> ¬ (f 2)]) 0)])).
destruct (((f [2 |-> ¬ (f 2)]) [0 |-> ¬ ((f [2 |-> ¬ (f 2)]) 0)]) 0) eqn:eq4.
rewrite (update_twice_neq ((f [2 |-> ¬ (f 2)]) [0 |-> ¬ ((f [2 |-> ¬ (f 2)]) 0)])).
rewrite (update_index_neq (((f [2 |-> ¬ (f 2)]) [0 |-> ¬ ((f [2 |-> ¬ (f 2)]) 0)]) [1
  |-> ¬ (((f [2 |-> ¬ (f 2)]) [0
          |-> ¬ ((f [2 |-> ¬ (f 2)]) 0)]) 1)])).
reflexivity.
1 - 2 : lia.
rewrite (update_index_neq ((f [2 |-> ¬ (f 2)]) [0 |-> ¬ ((f [2 |-> ¬ (f 2)]) 0)])).
reflexivity.
1 - 5: lia.
rewrite (update_index_neq (f [2 |-> ¬ (f 2)])).
rewrite (update_index_neq (f [2 |-> ¬ (f 2)])).
destruct ((f [2 |-> ¬ (f 2)]) 0) eqn:eq4.
rewrite (update_twice_neq (f [2 |-> ¬ (f 2)])).
rewrite (update_index_neq ((f [2 |-> ¬ (f 2)]) [1 |-> ¬ ((f [2 |-> ¬ (f 2)]) 1)])).
reflexivity.
1 - 2 : lia.
rewrite (update_index_neq (f [2 |-> ¬ (f 2)])).
reflexivity.
1 - 5: lia.
rewrite (update_index_neq f).
rewrite (update_index_neq f).
destruct (f 2) eqn:eq3.
rewrite (update_twice_neq f).
rewrite (update_index_neq (f [0 |-> ¬ (f 0)])).
destruct ((f [0 |-> ¬ (f 0)]) 0) eqn:eq4.
rewrite (update_index_neq (f [0 |-> ¬ (f 0)])).
rewrite (update_twice_neq (f [0 |-> ¬ (f 0)])).
rewrite (update_index_neq ((f [0 |-> ¬ (f 0)]) [1 |-> ¬ ((f [0 |-> ¬ (f 0)]) 1)])).
reflexivity.
1-3:lia.
rewrite (update_index_neq (f [0 |-> ¬ (f 0)])).
reflexivity.
1-3:lia.
rewrite (update_index_neq f).
rewrite (update_twice_neq f).
destruct (f 0) eqn:eq4.
rewrite (update_index_neq f).
rewrite (update_index_neq (f [1 |-> ¬ (f 1)])).
reflexivity.
1 - 2: lia.
discriminate eq1.
1 - 4: lia.
rewrite (update_index_neq f).
rewrite (update_index_neq f).
destruct (f 2) eqn:eq2.
rewrite (update_twice_neq f).
rewrite (update_index_neq (f [0 |-> ¬ (f 0)])).
rewrite (update_index_neq (f [0 |-> ¬ (f 0)])).
destruct ((f [0 |-> ¬ (f 0)]) 0) eqn:eq3.
rewrite (update_twice_neq (f [0 |-> ¬ (f 0)])).
rewrite update_index_neq.
reflexivity.
1 - 2 : lia.
rewrite update_index_neq.
reflexivity.
1 - 4 : lia.
rewrite update_index_neq.
destruct (f 0) eqn:eq3.
discriminate eq1.
rewrite update_index_neq.
reflexivity.
1 - 7: lia.
intros.
destruct (m <? 2 * n + 3) eqn:eq.
apply Nat.ltb_lt in eq.
destruct H.
simpl.
rewrite (update_index_neq f).
rewrite (update_index_neq f).
rewrite (update_index_neq f).
destruct (f (S (n + S (n + 0)))) eqn:eq1.
destruct (f (S (n + S (n + 0) + 1))) eqn:eq2.
rewrite (update_twice_neq f).
rewrite update_index_neq.
destruct ((f [S (n + S (n + 0) + 2)
       |-> ¬ (f (S (n + S (n + 0) + 2)))])
        (S (n + S (n + 0) + 2))) eqn:eq3.
rewrite (update_index_neq (f [S (n + S (n + 0) + 2)
              |-> ¬ (f (S (n + S (n + 0) + 2)))])).
rewrite (update_twice_neq (f [S (n + S (n + 0) + 2)
       |-> ¬ (f (S (n + S (n + 0) + 2)))])).
rewrite update_index_neq.
destruct (((f [S (n + S (n + 0) + 2)
      |-> ¬ (f (S (n + S (n + 0) + 2)))]) [
     S (n + S (n + 0))
     |-> ¬ ((f [S (n + S (n + 0) + 2)
             |-> ¬ (f (S (n + S (n + 0) + 2)))])
              (S (n + S (n + 0))))]) (S (n + S (n + 0)))) eqn:eq4.
rewrite (update_index_neq ((f [S (n + S (n + 0) + 2)
             |-> ¬ (f (S (n + S (n + 0) + 2)))])
            [S (n + S (n + 0))
            |-> ¬ ((f [S (n + S (n + 0) + 2)
                    |-> ¬ (f (S (n + S (n + 0) + 2)))])
                     (S (n + S (n + 0))))])).
rewrite (update_twice_neq ((f [S (n + S (n + 0) + 2)
      |-> ¬ (f (S (n + S (n + 0) + 2)))]) [
     S (n + S (n + 0))
     |-> ¬ ((f [S (n + S (n + 0) + 2)
             |-> ¬ (f (S (n + S (n + 0) + 2)))])
              (S (n + S (n + 0))))])).
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
             (S (n + S (n + 0) + 1)))])).
reflexivity.
1 - 3 : lia.
rewrite (IHn m ((f [S (n + S (n + 0) + 2)
     |-> ¬ (f (S (n + S (n + 0) + 2)))]) [
    S (n + S (n + 0))
    |-> ¬ ((f [S (n + S (n + 0) + 2)
            |-> ¬ (f (S (n + S (n + 0) + 2)))])
             (S (n + S (n + 0))))])).
reflexivity.
1 - 4 : lia.
rewrite (update_index_neq (f [S (n + S (n + 0) + 2)
      |-> ¬ (f (S (n + S (n + 0) + 2)))])).
rewrite (update_index_neq (f [S (n + S (n + 0) + 2)
             |-> ¬ (f (S (n + S (n + 0) + 2)))])).
destruct ( (f [S (n + S (n + 0) + 2)
     |-> ¬ (f (S (n + S (n + 0) + 2)))]) 
      (S (n + S (n + 0)))) eqn:eq4.
rewrite (update_twice_neq (f [S (n + S (n + 0) + 2)
     |-> ¬ (f (S (n + S (n + 0) + 2)))])).
rewrite (IHn m ((f [S (n + S (n + 0) + 2)
     |-> ¬ (f (S (n + S (n + 0) + 2)))])
    [S (n + S (n + 0) + 1)
    |-> ¬ ((f [S (n + S (n + 0) + 2)
            |-> ¬ (f (S (n + S (n + 0) + 2)))])
             (S (n + S (n + 0) + 1)))])).
reflexivity.
1 - 2 : lia.
rewrite (IHn m (f [S (n + S (n + 0) + 2)
    |-> ¬ (f (S (n + S (n + 0) + 2)))])).
reflexivity.
1-5: lia.
rewrite update_index_neq.
destruct (f (S (n + S (n + 0) + 2))) eqn:eq3.
rewrite (update_index_neq f).
rewrite (update_twice_neq f).
rewrite (update_index_neq (f [S (n + S (n + 0)) |-> ¬ (f (S (n + S (n + 0))))])).
rewrite (update_index_neq (f [S (n + S (n + 0))
             |-> ¬ (f (S (n + S (n + 0))))])).
destruct ((f [S (n + S (n + 0)) |-> ¬ (f (S (n + S (n + 0))))])
      (S (n + S (n + 0)))) eqn:eq4.
rewrite (update_twice_neq (f [S (n + S (n + 0)) |-> ¬ (f (S (n + S (n + 0))))])).
rewrite (IHn m ((f [S (n + S (n + 0)) |-> ¬ (f (S (n + S (n + 0))))])
    [S (n + S (n + 0) + 1)
    |-> ¬ ((f [S (n + S (n + 0))
            |-> ¬ (f (S (n + S (n + 0))))])
             (S (n + S (n + 0) + 1)))])).
reflexivity.
1 - 2:lia.
rewrite (IHn m (f [S (n + S (n + 0)) |-> ¬ (f (S (n + S (n + 0))))])).
reflexivity.
1 - 5: lia.
rewrite (update_index_neq f).
rewrite (update_index_neq f).
destruct (f (S (n + S (n + 0)))) eqn:eq4.
rewrite (update_twice_neq f).
rewrite (IHn m (f [S (n + S (n + 0) + 1)
    |-> ¬ (f (S (n + S (n + 0) + 1)))])).
reflexivity.
1 - 2: lia.
discriminate eq1.
1 - 3: lia.
rewrite (update_index_neq f).
rewrite (update_index_neq f).
destruct (f (S (n + S (n + 0) + 2))) eqn:eq2.
rewrite (update_twice_neq f).
rewrite (update_index_neq (f [S (n + S (n + 0)) |-> ¬ (f (S (n + S (n + 0))))])).
destruct ((f [S (n + S (n + 0)) |-> ¬ (f (S (n + S (n + 0))))])
      (S (n + S (n + 0)))) eqn:eq3.
rewrite (update_index_neq (f [S (n + S (n + 0))
            |-> ¬ (f (S (n + S (n + 0))))])).
rewrite (update_twice_neq (f [S (n + S (n + 0)) |-> ¬ (f (S (n + S (n + 0))))])).
rewrite (IHn m ((f [S (n + S (n + 0)) |-> ¬ (f (S (n + S (n + 0))))])
    [S (n + S (n + 0) + 1)
    |-> ¬ ((f [S (n + S (n + 0))
            |-> ¬ (f (S (n + S (n + 0))))])
             (S (n + S (n + 0) + 1)))])).
reflexivity.
1 - 3 : lia.
rewrite (IHn m (f [S (n + S (n + 0)) |-> ¬ (f (S (n + S (n + 0))))])).
reflexivity.
1 - 3 : lia.
rewrite (update_index_neq f).
rewrite (update_index_neq f).
destruct (f (S (n + S (n + 0)))) eqn:eq3.
discriminate eq1.
rewrite (IHn m f).
reflexivity.
1 - 8 : lia.
specialize (Nat.ltb_lt m (2 * n + 3)) as eq1.
apply not_iff_compat in eq1.
apply not_true_iff_false in eq.
apply eq1 in eq.
assert (2 * n + 3 <= m) by lia.
simpl.
rewrite (update_index_neq f) by lia.
destruct (f (S (n + S (n + 0)))) eqn:eq2.
rewrite (update_index_neq f) by lia.
destruct (f (S (n + S (n + 0) + 1))) eqn:eq3.
rewrite (update_index_neq f) by lia.
rewrite (update_twice_neq f).
rewrite update_index_neq by lia.
destruct ((f [S (n + S (n + 0) + 2)
       |-> ¬ (f (S (n + S (n + 0) + 2)))])
        (S (n + S (n + 0) + 2))) eqn:eq4.
rewrite (update_index_neq (f [S (n + S (n + 0) + 2)
              |-> ¬ (f (S (n + S (n + 0) + 2)))])) by lia.
rewrite (update_twice_neq (f [S (n + S (n + 0) + 2)
       |-> ¬ (f (S (n + S (n + 0) + 2)))])).
rewrite update_index_neq by lia.
destruct ( ((f [S (n + S (n + 0) + 2)
      |-> ¬ (f (S (n + S (n + 0) + 2)))]) [
     S (n + S (n + 0))
     |-> ¬ ((f [S (n + S (n + 0) + 2)
             |-> ¬ (f (S (n + S (n + 0) + 2)))])
              (S (n + S (n + 0))))]) (S (n + S (n + 0)))) eqn:eq5.
rewrite (update_index_neq ((f [S (n + S (n + 0) + 2)
             |-> ¬ (f (S (n + S (n + 0) + 2)))])
            [S (n + S (n + 0))
            |-> ¬ ((f [S (n + S (n + 0) + 2)
                    |-> ¬ (f (S (n + S (n + 0) + 2)))])
                     (S (n + S (n + 0))))])) by lia.
rewrite (update_twice_neq ((f [S (n + S (n + 0) + 2)
      |-> ¬ (f (S (n + S (n + 0) + 2)))]) [
     S (n + S (n + 0))
     |-> ¬ ((f [S (n + S (n + 0) + 2)
             |-> ¬ (f (S (n + S (n + 0) + 2)))])
              (S (n + S (n + 0))))])).
rewrite uma_end_gt by lia.
rewrite uma_end_gt by lia.
rewrite update_index_neq by lia.
reflexivity.
lia.
rewrite uma_end_gt by lia.
rewrite uma_end_gt by lia.
rewrite update_index_neq by lia.
reflexivity.
lia.
rewrite update_index_neq by lia.
destruct ((f [S (n + S (n + 0) + 2)
     |-> ¬ (f (S (n + S (n + 0) + 2)))]) 
      (S (n + S (n + 0)))) eqn:eq5.
rewrite (update_index_neq (f [S (n + S (n + 0) + 2)
            |-> ¬ (f (S (n + S (n + 0) + 2)))])) by lia.
rewrite (update_twice_neq (f [S (n + S (n + 0) + 2)
     |-> ¬ (f (S (n + S (n + 0) + 2)))])).
rewrite uma_end_gt by lia.
rewrite uma_end_gt by lia.
rewrite update_index_neq by lia.
reflexivity.
lia.
rewrite uma_end_gt by lia.
rewrite uma_end_gt by lia.
rewrite update_index_neq by lia.
reflexivity.
lia.
rewrite update_index_neq by lia.
rewrite (update_index_neq f) by lia.
destruct (f (S (n + S (n + 0) + 2))) eqn:eq4.
rewrite (update_twice_neq f) by lia.
rewrite update_index_neq by lia.
destruct ((f [S (n + S (n + 0)) |-> ¬ (f (S (n + S (n + 0))))])
      (S (n + S (n + 0)))) eqn:eq5.
rewrite (update_index_neq (f [S (n + S (n + 0))
            |-> ¬ (f (S (n + S (n + 0))))])) by lia.
rewrite (update_twice_neq (f [S (n + S (n + 0)) |-> ¬ (f (S (n + S (n + 0))))])) by lia.
rewrite uma_end_gt by lia.
rewrite uma_end_gt by lia.
rewrite update_index_neq by lia.
reflexivity.
rewrite uma_end_gt by lia.
rewrite uma_end_gt by lia.
rewrite update_index_neq by lia.
reflexivity.
rewrite update_index_neq by lia.
destruct (f (S (n + S (n + 0)))) eqn:eq5.
rewrite (update_index_neq f) by lia.
rewrite (update_twice_neq f) by lia.
rewrite uma_end_gt by lia.
rewrite uma_end_gt by lia.
rewrite update_index_neq by lia.
reflexivity.
rewrite uma_end_gt by lia.
rewrite uma_end_gt by lia.
rewrite update_index_neq by lia.
reflexivity.
rewrite update_index_neq by lia.
destruct (f (S (n + S (n + 0) + 2))) eqn:eq3.
rewrite (update_index_neq f) by lia.
rewrite (update_twice_neq f) by lia.
rewrite update_index_neq by lia.
destruct ((f [S (n + S (n + 0)) |-> ¬ (f (S (n + S (n + 0))))])
      (S (n + S (n + 0)))) eqn:eq4.
rewrite (update_index_neq (f [S (n + S (n + 0))
            |-> ¬ (f (S (n + S (n + 0))))])) by lia.
rewrite (update_twice_neq (f [S (n + S (n + 0)) |-> ¬ (f (S (n + S (n + 0))))])) by lia.
rewrite uma_end_gt by lia.
rewrite uma_end_gt by lia.
rewrite update_index_neq by lia.
reflexivity.
rewrite uma_end_gt by lia.
rewrite uma_end_gt by lia.
rewrite update_index_neq by lia.
reflexivity.
rewrite update_index_neq by lia.
destruct (f (S (n + S (n + 0)))) eqn:eq4.
rewrite update_twice_neq by lia.
rewrite (update_index_neq f) by lia.
rewrite uma_end_gt by lia.
rewrite uma_end_gt by lia.
rewrite update_index_neq by lia.
reflexivity.
rewrite uma_end_gt by lia.
rewrite uma_end_gt by lia.
rewrite update_index_neq by lia.
reflexivity.
Qed.

Lemma uma_msb_hbit_eq :
   forall n m f, f 0 = false -> m < 2 * n + 3 ->
     bcexec (UMAseq n) ((msb n f) [2 * n + 2 |-> f (2 * n + 2)]) m =
              bcexec (UMAseq n) (msb n f) m.
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
Admitted.


Lemma adder_partial : 
   forall n m f, m < 2 * n + 3 ->
    (bcexec (UMAseq n) (msb n f)) m = (good_out' n f) m.
Proof.
  intro n.
  induction n.
  intros.
  unfold UMAseq.
  rewrite (UMA_correct_partial 2 1 0 f ((msb 0 f))).
  unfold msb, good_out'.
  rewrite update_twice_eq.
  rewrite (update_twice_neq ((f [0 |-> carry 0 f ⊕ f 2]) [1 |-> f 1 ⊕ f 2])).
  rewrite update_twice_eq.
  rewrite (update_twice_neq ((f [0 |-> carry 0 f ⊕ f 2]) [1 |-> (f 2 ⊕ f 1) ⊕ f 0])).
  rewrite (update_twice_neq (f [0 |-> carry 0 f ⊕ f 2])).
  rewrite update_twice_eq.
  rewrite (update_same f).
  rewrite (update_twice_neq f).
  rewrite (update_same f).
  1 - 2:reflexivity. 
  lia. reflexivity.
  1 - 6 : lia.
  unfold msb.
  rewrite (update_index_eq).
  unfold carry.
  simpl.
  rewrite (andb_comm). reflexivity.
  unfold msb.
  rewrite (update_twice_neq (f [0 |-> carry 0 f ⊕ f 2])).
  rewrite (update_index_eq).
  reflexivity.
  lia.
  unfold msb.
  rewrite (update_twice_neq f).
  rewrite (update_twice_neq (f [1 |-> f 1 ⊕ f 2])).
  rewrite (update_index_eq).
  unfold carry.
  reflexivity.
  1 - 2:lia.
  intros.
  Local Opaque UMA. Local Opaque msb. Local Opaque good_out'.
  simpl.
  Local Transparent UMA. Local Transparent msb. Local Transparent good_out'.
  rewrite (UMA_correct_partial (S (n + S (n + 0) + 2)) (S (n + S (n + 0) + 1))
         (S (n + S (n + 0))) f (msb (S n) f)).
  Local Opaque UMA.
  simpl.
  Local Transparent UMA.
  assert ((n + (n + 0) + 1) = 2 * n + 1) by lia.
  rewrite H0. clear H0.
  assert ((n + (n + 0) + 2) = 2 * n + 2) by lia.
  rewrite H0. clear H0.
  assert ((S (n + S (n + 0))) = 2 * n + 2) by lia.
  rewrite H0. clear H0.
  assert ((S (n + S (n + 0) + 1)) = 2 * n + 3) by lia.
  rewrite H0. clear H0.
  assert ((S (n + S (n + 0) + 2)) = 2 * n + 4) by lia.
  rewrite H0. clear H0.
  rewrite update_twice_eq.
  rewrite (update_twice_neq (((msb n f) [2 * n + 2
       |-> (((f (2 * n + 1) && f (2 * n + 2))
             ⊕ (f (2 * n + 2) && carry n f))
            ⊕ (f (2 * n + 1) && carry n f)) ⊕ 
           f (2 * n + 4)]) [2 * n + 3
      |-> f (2 * n + 3) ⊕ f (2 * n + 4)])).
  rewrite update_twice_eq.
  rewrite (update_twice_neq (msb n f)) by lia.
  rewrite (update_twice_neq ((msb n f) [2 * n + 3
      |-> (f (2 * n + 4) ⊕ f (2 * n + 3)) ⊕ f (2 * n + 2)])) by lia.
  rewrite update_twice_eq by lia.
  destruct (m <? 2 * n + 3) eqn:eq.
  apply Nat.ltb_lt in eq.
  rewrite (update_twice_neq ((msb n f) [2 * n + 3
     |-> (f (2 * n + 4) ⊕ f (2 * n + 3)) ⊕ f (2 * n + 2)])) by lia.
  rewrite uma_less_gt_same by lia.
  rewrite (update_twice_neq (msb n f)) by lia.
  rewrite uma_less_gt_same by lia.
  rewrite (update_index_neq (good_out' n f)) by lia.
  rewrite <- IHn by lia.
Admitted.

Definition adder n : bccom := MAJ_sign n; UMAseq n.

Lemma adder_correct :   
  forall n f,
    (bcexec (adder n) f) = (good_out n f).
Proof.
  induction n; intros.
  unfold adder.
  rewrite bcseq_correct.
  rewrite MAJ_sign_correct.
  unfold msbs,good_out.
  unfold UMAseq.
  rewrite (UMA_correct_partial 2 1 0 f 
        ((msb 0 f) [2 * 0 + 3 |-> msb 0 f (2 * 0 + 2) ⊕ f (2 * 0 + 3)])).
  unfold msb, good_out'.
  rewrite (update_twice_neq ((f [0 |-> carry 0 f ⊕ f 2]) [1 |-> f 1 ⊕ f 2])).
  rewrite update_twice_eq.
  rewrite (update_twice_neq (((f [0 |-> carry 0 f ⊕ f 2]) [1 |-> f 1 ⊕ f 2]) [2 * 0 + 3
   |-> (((f [0 |-> carry 0 f ⊕ f 2]) [1 |-> f 1 ⊕ f 2]) [2 |-> carry 1 f]) (2 * 0 + 2)
       ⊕ f (2 * 0 + 3)])).
  rewrite (update_twice_neq ((f [0 |-> carry 0 f ⊕ f 2]) [1 |-> f 1 ⊕ f 2])).
  rewrite update_twice_eq.
  rewrite (update_twice_neq ((f [0 |-> carry 0 f ⊕ f 2]) [1 |-> (f 2 ⊕ f 1) ⊕ f 0])).
  rewrite (update_twice_neq (f [0 |-> carry 0 f ⊕ f 2])).
  rewrite (update_twice_neq f).
  rewrite (update_same f).
  rewrite (update_twice_neq ((f [0 |-> carry 0 f ⊕ f 2]) [1 |-> (f 2 ⊕ f 1) ⊕ f 0])).
  rewrite (update_twice_neq (f [0 |-> carry 0 f ⊕ f 2])).
  rewrite update_twice_eq.
  rewrite (update_same f).
  reflexivity.
  reflexivity.
  1 - 2: lia.
  reflexivity.
  1 - 9: lia.
  unfold msb.
  rewrite (update_twice_neq ((f [0 |-> carry 0 f ⊕ f 2]) [1 |-> f 1 ⊕ f 2])).
  rewrite (update_index_eq).
  unfold carry.
  simpl.
  rewrite (andb_comm). reflexivity.
  lia.
  unfold msb.
  rewrite (update_twice_neq (f [0 |-> carry 0 f ⊕ f 2])).
  rewrite (update_twice_neq ((f [0 |-> carry 0 f ⊕ f 2]) [2 |-> carry 1 f])).
  rewrite (update_index_eq).
  reflexivity.
  1 - 2:lia.
  unfold msb.
  rewrite (update_twice_neq f).
  rewrite (update_twice_neq (f [1 |-> f 1 ⊕ f 2])).
  rewrite (update_twice_neq ((f [1 |-> f 1 ⊕ f 2]) [2 |-> carry 1 f])).
  rewrite (update_index_eq).
  unfold carry.
  reflexivity.
  1 - 3:lia.
  unfold adder,good_out.
  rewrite bcseq_correct.
  rewrite MAJ_sign_correct.
Admitted.




Fixpoint adder' dim n : bccom :=
  match n with
  | 0 => bccnot (2 * dim) (2 * dim + 1) 
  | S n' => (MAJ (dim - n) ((dim - n)+1) ((dim - n)+2);
     adder' dim n' ; UMA (dim - n) ((dim - n)+1) ((dim - n)+2))
  end.
Definition adder n := adder' n n.

Fixpoint good_out' (n:nat) (f : (nat -> bool)) : ((nat -> bool) * bool) := 
  match n with 
   | 0 => (f, f 0)
   | S m => (match good_out' m f with (f',c) => ((f'[(m+1) |-> (f (m+2) ⊕ f (m+1) ⊕ c)]),
                           (f (m+2) && f (m+1)) ⊕ (f (m+2) && c) ⊕ (f (m+1) && c)) end)
  end.
Definition good_out (n:nat) (f : (nat -> bool)) : (nat -> bool) :=
  match good_out' n f with (f',c) => f'[(2 * n + 1) |-> f (2 * n + 1) ⊕ c] end.

Lemma adder_correct :
  forall n f,
    bcexec (adder n) f = good_out n f.
Proof.
intros.
unfold good_out.
induction n.
unfold adder,adder',bcexec.
simpl.
destruct (f 0) eqn:eq1.
assert (f 1 ⊕ true = ¬ (f 1)) by easy.
rewrite H. reflexivity.
assert ((f 1) ⊕ false = (f 1)).
destruct (f 1). easy. easy.
rewrite H.
rewrite update_same. reflexivity. reflexivity.
Local Opaque MAJ UMA.
simpl.
Admitted.

(* Now, the C*x %M circuit. The input is a function where f 0 = 0, f 1, f 3 ,f 5, ... f (2 n + 1)
          are the bits representation of x, and we assume that 2 * x < 2 ^ n, 
           and f 2, f 4, f 6, f (2 * n + 2) are bits for M, and 2 * M < 2 ^ n, and also x < M, so 2*x - M < M
        and finally, 2 * n + 3 is a C_out bit for comparator.
   Now, we can see that if f (1,3,5,7...) are bits for x, then f (2n +1) must be zero, the most
        significant bit of the x representation must be zero.
   The same as the M representation, the most significant bit of M must also be zero. 
   The idea is that, the shifer is simply move the most significant bit in 2n+1 to the 1 position. 
   Then we compute 2x - M, and the result will also end up that the most significant bit is zero.
   Then, we can do the process again and again until we compute all bits in C. 
   For a summary, each step of the process is first to permutation the f 1 and f (2*n+1) bits, 
   The f(1,....2n+1) represents 2*x, then we compare 2* with M by using 2x-M, 
   The circuit will perform as in the x positions, it will be 2x-M, and in the M position, the circuit will keep M. 
   Then, we see the C_out bit, if it is 1, it means that 2x < M, in this case,
    we will add M to the 2x-M, so we need to implement an adder for (2x-M) + M.
    In addition, after the addition, we need to clean the C_out bit by using CCX. 
    The reason to use CCX is clear. The input for the C_out bit is z=1, and the output after the addition is z xor S_n = C_n = 
     (a_{n} && b_{n}) xor (a_{n} && c_{n}) xor (b_{n} && c_{n}). We have said that the most significant bit of x and M are zero
    so a_{n} and b_{n} are zero, so the above formula is zero, and 1 xor 0 = 1, so we just need to use bcx to clean up the bit to 0. 
   If 2x>=M, then we need 2x -M, and the comparator just gives the result, and we don't need anything else. *)

Fixpoint comparator' dim n : bccom :=
  match n with
  | 0 => bccnot (2 * dim) (2 * dim + 1) 
  | S n' => (bcx ((dim - n)+1) ; MAJ (dim - n) ((dim - n)+1) ((dim - n)+2)
               ; comparator' dim n' ; UMA (dim - n) ((dim - n)+1) ((dim - n)+2); bcx ((dim - n)+1))
  end.
Definition comparator n := comparator' n n.

Fixpoint good_out_com' (n:nat) (f : (nat -> bool)) : ((nat -> bool) * bool) := 
  match n with 
   | 0 => (f, f 0)
   | S m => (match good_out_com' m f with (f',c) => ((f'[(m+1) |-> ¬ (f (m+2) ⊕ (¬ (f (m+1))) ⊕ c)]),
                           (f (m+2) && ¬ (f (m+1))) ⊕ (f (m+2) && c) ⊕ (¬ (f (m+1)) && c)) end)
  end.
Definition good_out_com (n:nat) (f : (nat -> bool)) : (nat -> bool) :=
      match good_out' n f with (f',c) => f'[(2 * n + 1) |-> f (2 * n + 1) ⊕ c] end.

Lemma comparator_correct :
  forall n f,
    bcexec (comparator n) f = good_out_com n f.
Proof.
intros.
unfold good_out_com.
induction n.
unfold comparator,comparator',bcexec.
simpl.
destruct (f 0) eqn:eq1.
assert (f 1 ⊕ true = ¬ (f 1)) by easy.
rewrite H. reflexivity.
assert ((f 1) ⊕ false = (f 1)).
destruct (f 1). easy. easy.
rewrite H.
rewrite update_same. reflexivity. reflexivity.
Admitted.

(*
Definition bit_swap n (f: nat -> bool) : (nat -> bool) :=
    fun i => if i =? 1 then f (2*n+1) else if i =? (2 * n+1) then f 1 else f i.
*)

Definition one_step n := 
    bcswap 1 (2*n+1); (comparator (n+1)) ;  bccont (2 * n + 3) (adder (n+1)).

Lemma one_step_highbit_zero :
  forall n f f',  f 0 = false ->
       (f (2*n+1)) = false -> (f (2*n+2)) = false ->
    bcexec (one_step n) f = f' -> (f'(2*n+1)) = false.
Proof.
intros n f f'.
induction n.
intros.
unfold one_step,bcexec in H1.
Admitted.

Lemma one_step_same_a :
  forall n f f' i, i <= n ->
    bcexec (one_step n) f = f' -> (f'(2*i+2)) = f(2*i+2).
Proof.
intros n f f'.
induction n.
intros.
unfold one_step,bcexec in H0.
(* simpl in H0. why there is an infinite loop? *)
Admitted.

Definition bfun (f:nat -> bool) := 
   fun i => f(2*i+1).

Definition afun (f:nat -> bool) := 
   fun i => f(2*i+2).

Lemma one_step_correct_1 :
  forall n f f', f 0 = false -> (f (2*n+1)) = false
       -> (f (2*n+2)) = false -> f (2*n+3) = false ->
    bcexec (one_step n) f = f' ->
    let x := funbool_to_nat (n+1) (bfun f) in
     let M := funbool_to_nat (n+1) (afun f) in
       2 * x < M -> funbool_to_nat (n+1) (bfun f')= 2 * x.
Proof.
intros n f f'.
Admitted.

Lemma one_step_correct_2 :
  forall n f f', f 0 = false -> (f (2*n+1)) = false
       -> (f (2*n+2)) = false -> f (2*n+3) = false ->
    bcexec (one_step n) f = f' ->
    let x := funbool_to_nat (n+1) (bfun f) in
     let M := funbool_to_nat (n+1) (afun f) in
       2 * x >= M -> funbool_to_nat (n+1) (bfun f')= 2 * x - M.
Proof.
intros n f f'.
Admitted.

Fixpoint repeat_steps t n dim :=
   match n with 
    | 0 => (bcskip,t)
    | S m => match repeat_steps (t+1) m dim with
                (newc,t') => (bcswap (2*n+3) t ; (one_step dim);newc,t')
             end
   end.

(* is a function representing the value for C. The result of C*x %M is in the f(1,3,5...,2*n+1) *)

Fixpoint all_step' t dim n (c: nat -> bool) : bccom :=
   match n with 
    | 0 => bcskip
    | S m => if c (dim - n) then
      (match  (repeat_steps t (dim - m) dim) with
          (newc,t') => newc ;  all_step' t' dim m c
       end)
       else all_step' t dim m c
   end.
Definition all_step dim (c: nat -> bool) := all_step' (2 * dim + 4) dim dim c.


Lemma all_step_correct :
  forall n f f' cf, f 0 = false -> 
      (forall i, 2 * n < i -> f i = false) ->
    bcexec (one_step n) f = f' ->
    let x := funbool_to_nat (n+1) (bfun f) in
     let M := funbool_to_nat (n+1) (afun f) in
     let C := funbool_to_nat n cf in 
       funbool_to_nat (n+1) (bfun f')= (C * x) % M.
Proof.
intros n f f' cf.
Admitted.



















