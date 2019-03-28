Require Export SQIMP.
Require Export Quantum.
Require Export UnitarySem.

Fixpoint c_eval (dim : nat) (c : com) : Superoperator (2^dim) (2^dim) :=
  match c with
  | skip      => fun ρ => ρ (* We could change to (super I _), making the next lemma trivial *)
  | seq c1 c2 => compose_super (c_eval dim c2) (c_eval dim c1)  
  | app u l   => super (ueval dim u l)
  | meas n    => Splus (super (@pad 2 n dim (∣0⟩⟨0∣))) (super (@pad 2 n dim (∣1⟩⟨1∣))) 
  | reset n   => Splus (super (@pad 2 n dim (∣0⟩⟨0∣))) (super (@pad 2 n dim (∣0⟩⟨1∣)))
  end.

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

(* Alternative lemma (requires change to skip):
Lemma c_eval_ucom' : forall (c : ucom) (dim : nat),
    c_eval dim c = super (uc_eval dim c).
*)
