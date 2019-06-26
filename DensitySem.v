Require Export SQIRE.
Require Export QWIRE.Quantum.
Require Export UnitarySem.
Require Import Setoid.

Local Open Scope com_scope.

Fixpoint c_eval {dim} (c : com dim) : Superoperator (2^dim) (2^dim) :=
  match c with
  | skip         => fun ρ => ρ
  | c1 ; c2      => compose_super (c_eval c2) (c_eval c1)  
  | app1 u n     => super (ueval1 dim n u)
  | app2 _ m n   => super (ueval_cnot dim m n)
  | meas n c1 c2 => Splus (compose_super (c_eval c1) (super (@pad 1 n dim (∣0⟩⟨0∣)))) 
                         (compose_super (c_eval c2) (super (@pad 1 n dim (∣1⟩⟨1∣)))) 
  end.

Lemma c_eval_ucom : forall {dim} (c : ucom dim) (ρ : Density (2^dim)),
    WF_Matrix ρ ->
    c_eval c ρ = super (uc_eval c) ρ.
Proof.
  intros dim c.
  induction c; trivial; intros ρ H.
  - simpl. unfold super. Msimpl. reflexivity.
  - simpl. unfold super, compose_super in *.
    rewrite IHc1, IHc2; auto with wf_db.
    Msimpl.
    repeat rewrite Mmult_assoc.
    reflexivity.
Qed.

Definition c_equiv {dim} (c1 c2 : com dim) := c_eval c1 = c_eval c2.
Infix "≡" := c_equiv : com_scope.

Lemma c_equiv_refl : forall {dim} (c1 : com dim), c1 ≡ c1. 
Proof. easy. Qed.

Lemma c_equiv_sym : forall {dim} (c1 c2 : com dim), c1 ≡ c2 -> c2 ≡ c1. 
Proof. easy. Qed.

Lemma c_equiv_trans : forall {dim} (c1 c2 c3 : com dim), c1 ≡ c2 -> c2 ≡ c3 -> c1 ≡ c3. 
Proof. intros dim c1 c2 c3 H12 H23. unfold c_equiv. rewrite H12. easy. Qed.

Lemma seq_assoc : forall {dim} (c1 c2 c3 : com dim), ((c1 ; c2) ; c3) ≡ (c1 ; (c2 ; c3)).
Proof.
  intros dim c1 c2 c3. 
  unfold c_equiv; simpl.
  unfold compose_super.
  easy.
Qed.

Lemma seq_congruence : forall {dim} (c1 c1' c2 c2' : com dim),
    c1 ≡ c1' ->
    c2 ≡ c2' ->
    c1 ; c2 ≡ c1' ; c2'.
Proof.
  intros dim c1 c1' c2 c2' Ec1 Ec2.
  unfold c_equiv; simpl.
  rewrite Ec1, Ec2.
  reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (com dim) (@c_equiv dim)
  reflexivity proved by c_equiv_refl
  symmetry proved by c_equiv_sym
  transitivity proved by c_equiv_trans
  as c_equiv_rel.

Add Parametric Morphism (dim : nat) : (@seq dim) 
  with signature (@c_equiv dim) ==> (@c_equiv dim) ==> (@c_equiv dim) as seq_mor.
Proof. intros x y H x0 y0 H0. apply seq_congruence; easy. Qed.
