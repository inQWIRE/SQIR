Require Import VectorStates UnitaryOps Coq.btauto.Btauto.

(* The following belows to the RCIR file, which contains only the boolean circuit. *)
(* Implementation Language *)
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
    
(* Implementation language to compile bc circuit to SQIR. *)
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
















