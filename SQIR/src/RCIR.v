Require Import VectorStates UnitaryOps.

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
Notation "i ':->' x '$' f" := (update f i x) (at level 45, right associativity).
Local Open Scope nat_scope.

Definition bccnot (x y : nat) := bccont x (bcx y).
Definition bcswap (x y : nat) := bccnot x y; bccnot y x; bccnot x y.
Definition bcccnot (x y z : nat) := bccont x (bccnot y z).

Fixpoint bcexec (p : bccom) (f : nat -> bool) :=
  match p with
  | bcskip => f
  | bcx n => n :-> (¬ (f n))$ f
  (*  | bccnot x y => update f y ((f y) ⊕ (f x)) *)
  | bccont n p => if f n then bcexec p f else f
  | bcseq p1 p2 => bcexec p2 (bcexec p1 f)
  end.

Lemma bccnot_correct :
  forall x y f,
    x <> y ->
    bcexec (bccnot x y) f = y :-> (f y ⊕ f x)$ f.
Proof.
  intros. apply functional_extensionality; intro i. simpl. unfold update.
  destruct (f x) eqn:Efx; simpl.
  bdestruct (i =? x); bdestruct (i =? y); subst; try contradiction; repeat rewrite Nat.eqb_refl; easy.
  bdestruct (i =? y); subst; try contradiction; repeat rewrite Nat.eqb_refl. symmetry. apply xorb_false_r. easy.
Qed.

Lemma bcswap_correct :
  forall x y f,
    x <> y ->
    bcexec (bcswap x y) f = fun i => if i =? x then f y else if i =? y then f x else f i.
Proof.
  intros. apply functional_extensionality; intro i. simpl.
  unfold update.
  destruct (f x) eqn:Ex; destruct (f y) eqn:Ey; simpl; repeat rewrite Nat.eqb_refl; bdestruct (x =? y); bdestruct (y =? x); subst; try contradiction.
  rewrite Ex.
  bdestruct (i =? x); bdestruct (i =? y); subst; try contradiction; repeat rewrite Nat.eqb_refl; easy.
  rewrite Ex. easy.
  rewrite Ex. simpl. 
  bdestruct (i =? x); bdestruct (i =? y); subst; try contradiction; repeat rewrite Nat.eqb_refl; try easy.
  rewrite Ey. easy.
  rewrite Ex.
  bdestruct (i =? x); bdestruct (i =? y); subst; try contradiction; repeat rewrite Nat.eqb_refl; easy.
Qed.

Lemma bcccnot_correct :
  forall x y z f,
    x <> y ->
    y <> z ->
    x <> z ->
    bcexec (bcccnot x y z) f = z :-> (f z ⊕ (f y && f x))$ f.
Proof.
  intros. apply functional_extensionality; intro i. simpl. unfold update.
  destruct (f x) eqn:Efx; destruct (f y) eqn:Efy; simpl;
    bdestruct (i =? z); subst; try contradiction; repeat rewrite Nat.eqb_refl; try easy;
      try (symmetry; apply xorb_false_r).
Qed.

Inductive bcfresh : nat -> bccom -> Prop :=
| bcfresh_skip : forall q, q <> 0 -> bcfresh q bcskip    (* q <> 0 fits the requirement in SQIR, which is unnecessary in principle *)
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
    bcexec (MAJ c b a) f = c :-> (f c ⊕ f a)$ b :-> (f b ⊕ f a)$ a :-> ((f a && f b) ⊕ (f a && f c) ⊕ (f b && f c))$ f.
Proof.
  intros ? ? ? ? Hab' Hbc' Hac'. apply functional_extensionality; intro i. simpl.
  assert (G: forall (x y : nat), x <> y -> y <> x) by (intros; lia).
  assert (Hba' := G a b Hab'). assert (Hcb' := G b c Hbc'). assert (Hca' := G a c Hac').
  assert (Hab := Hab'). assert (Hba := Hba'). assert (Hac := Hac'). assert (Hca := Hca'). assert (Hbc := Hbc'). assert (Hcb := Hcb').
  apply Nat.eqb_neq in Hab. apply Nat.eqb_neq in Hbc. apply Nat.eqb_neq in Hac.
  apply Nat.eqb_neq in Hba. apply Nat.eqb_neq in Hcb. apply Nat.eqb_neq in Hca.
  unfold update.
  destruct (f a) eqn:Ea; destruct (f b) eqn:Eb; destruct (f c) eqn:Ec; simpl; repeat rewrite Nat.eqb_refl;
    repeat rewrite Ea; repeat rewrite Eb; repeat rewrite Ec; repeat rewrite Hab; repeat rewrite Hbc; repeat rewrite Hac; repeat rewrite Hba; repeat rewrite Hcb; repeat rewrite Hca; repeat rewrite Nat.eqb_refl; simpl;
      bdestruct (i =? a); bdestruct (i =? b); bdestruct (i =? c); subst; try contradiction; repeat rewrite Nat.eqb_refl; repeat rewrite Ea; repeat rewrite Eb; repeat rewrite Ec; try easy.
Qed.
