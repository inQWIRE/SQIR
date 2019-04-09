Require Export SQIRE.
Require Export Quantum.
Require Export UnitarySem.
Require Import Setoid.

Local Open Scope com_scope.

Fixpoint c_eval (dim : nat) (c : com) : Superoperator (2^dim) (2^dim) :=
  match c with
  | skip      => super (I _) (*or: fun ρ => ρ  *)
  | seq c1 c2 => compose_super (c_eval dim c2) (c_eval dim c1)  
  | app u l   => super (ueval dim u l)
  | meas n    => Splus (super (@pad 1 n dim (∣0⟩⟨0∣))) (super (@pad 1 n dim (∣1⟩⟨1∣))) 
  | reset n   => Splus (super (@pad 1 n dim (∣0⟩⟨0∣))) (super (@pad 1 n dim (∣0⟩⟨1∣)))
  end.

Lemma c_eval_ucom : forall (c : ucom) (dim : nat),
    c_eval dim c = super (uc_eval dim c).
Proof.
  intros c dim.
  induction c; trivial.
  simpl. rewrite IHc1, IHc2.
  unfold compose_super, super; simpl.
  apply functional_extensionality. intros ρ.
  Msimpl; repeat rewrite Mmult_assoc.
  reflexivity.
Qed.

(* If skip is just id:
Lemma c_eval_ucom : forall (c : ucom) (dim : nat) (ρ : Density (2^dim)),
    WF_Matrix _ _ ρ ->
    c_eval dim c ρ = super (uc_eval dim c) ρ.
Proof.
  intros c dim.
  induction c; intros ρ H.
  - simpl. unfold super. Msimpl. easy.
  - simpl. unfold super, compose_super in *.
    rewrite IHc1, IHc2; auto with wf_db.
    Msimpl.
    repeat rewrite Mmult_assoc.
    easy.
  - simpl. reflexivity.
Qed.
*)

Definition c_equiv (c1 c2 : com) := forall dim, c_eval dim c1 = c_eval dim c2.

Infix "≡" := c_equiv : com_scope.

Lemma c_equiv_refl : forall c1, c1 ≡ c1. 
Proof. easy. Qed.

Lemma c_equiv_sym : forall c1 c2, c1 ≡ c2 -> c2 ≡ c1. 
Proof. easy. Qed.

Lemma c_equiv_trans : forall c1 c2 c3, c1 ≡ c2 -> c2 ≡ c3 -> c1 ≡ c3. 
Proof. intros c1 c2 c3 H12 H23 dim. rewrite H12. easy. Qed.

Lemma seq_assoc : forall c1 c2 c3, ((c1 ; c2) ; c3) ≡ (c1 ; (c2 ; c3)).
Proof.
  intros c1 c2 c3 dim. simpl.
  unfold compose_super.
  easy.
Qed.

Lemma seq_congruence : forall c1 c1' c2 c2',
    c1 ≡ c1' ->
    c2 ≡ c2' ->
    c1 ; c2 ≡ c1' ; c2'.
Proof.
  intros c1 c1' c2 c2' Ec1 Ec2 dim.
  simpl.
  rewrite Ec1, Ec2.
  reflexivity.
Qed.

(* "Parametric" isn't necessary, just displays better *)
Add Parametric Relation : com c_equiv 
  reflexivity proved by c_equiv_refl
  symmetry proved by c_equiv_sym
  transitivity proved by c_equiv_trans
  as uc_equiv_rel.

Add Parametric Morphism : seq 
  with signature c_equiv ==> c_equiv ==> c_equiv as useq_mor.
Proof. intros x y H x0 y0 H0. apply seq_congruence; easy. Qed.

