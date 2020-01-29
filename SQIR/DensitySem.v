Require Export SQIR.
Require Export QWIRE.Quantum.
Require Export UnitarySem.
Require Import Setoid.

Local Open Scope com_scope.

(* TODO: Put in QWIRE's quantum file *)
Lemma compose_super_eq : forall {m n p} (A : Matrix m n) (B : Matrix n p), 
      compose_super (super A) (super B) = super (A × B).
Proof.
  intros.
  unfold compose_super, super.
  apply functional_extensionality. intros ρ.
  rewrite Mmult_adjoint.
  repeat rewrite Mmult_assoc.
  reflexivity.
Qed.

Fixpoint c_eval {dim} (c : base_com dim) : Superoperator (2^dim) (2^dim) :=
  match c with
  | skip           => fun ρ => ρ
  | c1 ; c2        => compose_super (c_eval c2) (c_eval c1)  
  | uc u           => super (uc_eval u)
  | meas n c1 c2   => Splus (compose_super (c_eval c1) (super (@pad 1 n dim (∣1⟩⟨1∣)))) 
                           (compose_super (c_eval c2) (super (@pad 1 n dim (∣0⟩⟨0∣)))) 
  end.

Lemma WF_c_eval : forall {dim} (c : base_com dim) ρ, 
  WF_Matrix ρ -> WF_Matrix (c_eval c ρ).
Proof.
  intros dim c.
  induction c; simpl; unfold Splus; auto with wf_db.
Qed.

Hint Resolve WF_c_eval : wf_db.

Lemma c_eval_ucom : forall dim (u : base_ucom dim) ρ,
  c_eval (uc u) ρ = (uc_eval u) × ρ × (uc_eval u)†.
Proof. intros. induction u; reflexivity. Qed.

(* Equivalence *)

Definition c_equiv {dim} (c1 c2 : base_com dim) := 
  (dim > 0)%nat -> forall ρ, WF_Matrix ρ -> c_eval c1 ρ = c_eval c2 ρ.
Infix "≡" := c_equiv : com_scope.

Lemma c_equiv_refl : forall {dim} (c1 : base_com dim), c1 ≡ c1. 
Proof. easy. Qed.

Lemma c_equiv_sym : forall {dim} (c1 c2 : base_com dim), c1 ≡ c2 -> c2 ≡ c1. 
Proof. unfold c_equiv. intros. rewrite H; try assumption. reflexivity. Qed.

Lemma c_equiv_trans : forall {dim} (c1 c2 c3 : base_com dim), 
  c1 ≡ c2 -> c2 ≡ c3 -> c1 ≡ c3. 
Proof. 
  unfold c_equiv.
  intros dim c1 c2 c3 H12 H23 Hdim ρ WFρ.
  rewrite H12; try assumption. 
  apply H23; assumption.
Qed.

Lemma seq_assoc : forall {dim} (c1 c2 c3 : base_com dim), 
  ((c1 ; c2) ; c3) ≡ (c1 ; (c2 ; c3)).
Proof.
  unfold c_equiv.
  intros dim c1 c2 c3 Hdim ρ WFρ. 
  simpl.
  unfold compose_super.
  reflexivity.
Qed.

Lemma seq_congruence : forall {dim} (c1 c1' c2 c2' : base_com dim),
    c1 ≡ c1' ->
    c2 ≡ c2' ->
    c1 ; c2 ≡ c1' ; c2'.
Proof.
  unfold c_equiv.
  intros dim c1 c1' c2 c2' Ec1 Ec2 Hdim ρ WFρ.
  simpl.
  unfold compose_super.
  rewrite Ec1, Ec2; auto with wf_db.
Qed.

Add Parametric Relation (dim : nat) : (base_com dim) (@c_equiv dim)
  reflexivity proved by c_equiv_refl
  symmetry proved by c_equiv_sym
  transitivity proved by c_equiv_trans
  as c_equiv_rel.

Add Parametric Morphism (dim : nat) : (@SQIR.seq base_Unitary dim) 
  with signature (@c_equiv dim) ==> (@c_equiv dim) ==> (@c_equiv dim) as seq_mor.
Proof. intros x y H x0 y0 H0. apply seq_congruence; easy. Qed.

(* SKIP is the reason we need the (dim > 0) and (WF_Matrix ρ) restrictions. *)
Lemma c_eval_SKIP : forall dim,
  uc SKIP ≡ (skip : base_com dim).
Proof.
  unfold c_equiv.
  intros dim Hdim ρ WFρ.
  simpl. unfold super.
  rewrite denote_SKIP; try assumption.
  Msimpl; reflexivity.
Qed.

Lemma c_eval_0 : forall dim (c : base_com dim),
  c_eval c Zero = Zero.
Proof.
  intros.
  induction c; simpl.
  - reflexivity.
  - unfold compose_super. rewrite IHc1, IHc2. reflexivity.
  - unfold super. Msimpl. reflexivity.
  - unfold Splus, compose_super, super. Msimpl. 
    rewrite IHc1, IHc2. Msimpl. reflexivity.
Qed.

(** Lemmas for derived commands **)

Lemma c_eval_measure : forall n dim ρ,
    c_eval (measure n) ρ = Splus (super (@pad 1 n dim (∣0⟩⟨0∣))) 
                                 (super (@pad 1 n dim (∣1⟩⟨1∣))) ρ.
Proof. 
  intros; simpl.
  unfold Splus.  
  rewrite Mplus_comm.
  reflexivity. 
Qed.

Lemma c_eval_reset : forall n dim ρ,
    c_eval (reset n) ρ = Splus (super (@pad 1 n dim (∣0⟩⟨0∣))) 
                               (super (@pad 1 n dim (∣0⟩⟨1∣))) ρ.
Proof.
  intros. simpl.
  repeat rewrite compose_super_eq.
  rewrite denote_X.
  unfold Splus, compose_super.
  repeat rewrite pad_mult.
  rewrite <- Mmult_assoc. 
  restore_dims.
  Qsimpl.
  rewrite Mplus_comm.
  reflexivity.  
Qed.

Definition c_eval_reset0 := c_eval_reset.

Lemma c_eval_reset1 : forall n dim ρ,
    c_eval (n <- 1) ρ = Splus (super (@pad 1 n dim (∣1⟩⟨0∣))) 
                             (super (@pad 1 n dim (∣1⟩⟨1∣))) ρ.
Proof.
  intros. simpl.
  repeat rewrite compose_super_eq.
  rewrite denote_X.
  unfold Splus, compose_super.
  repeat rewrite pad_mult.
  rewrite <- Mmult_assoc. 
  restore_dims.
  Qsimpl.
  rewrite Mplus_comm.
  reflexivity.  
Qed.
  
