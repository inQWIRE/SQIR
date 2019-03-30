Require Import Quantum.
Require Import List.
Require Import SQIMP.
Require Import UnitarySem.

(* Also move *)

Definition norm {n} (ψ : Vector n) :=
  sqrt (fst (ψ ∘ ψ†)).  

Open Scope com.

(* With scaling *)

Reserved Notation "c '/' ψ '⇩' ψ'"
                  (at level 40, ψ at level 39).

Inductive nd_eval {dim : nat} : com -> Vector (2^dim) -> Vector (2^dim) -> Prop :=
  | nd_skip : forall ψ, nd_eval skip ψ ψ
  | nd_app : forall n (u : Unitary n) (l : list nat) (ψ : Vector (2^dim)),
      app u l / ψ ⇩ ((ueval dim u l) × ψ)
  | nd_meas0 : forall n (ψ : Vector (2^dim)),
      let ψ' := @pad 2 n dim (∣0⟩⟨0∣) × ψ in 
      norm ψ' <> 0%R ->
      meas n / ψ ⇩ (scale (/(norm ψ')) ψ') 
  | nd_meas1 : forall n (ψ : Vector (2^dim)),
      let ψ' := @pad 2 n dim (∣1⟩⟨1∣) × ψ in
      norm ψ' <> 0%R ->
      meas n / ψ ⇩ (scale (/(norm ψ')) ψ') 
  | nd_reset0 : forall n (ψ : Vector (2^dim)),
      let ψ' := @pad 2 n dim (∣0⟩⟨0∣) × ψ in 
      meas n / ψ ⇩ (scale (/(norm ψ')) ψ') 
  | nd_reset1 : forall n (ψ : Vector (2^dim)),
      let ψ' := @pad 2 n dim (∣0⟩⟨1∣) × ψ in (* is this right? *)
      norm ψ' <> 0%R ->
      meas n / ψ ⇩ (scale (/(norm ψ')) ψ')
  | nd_seq : forall (c1 c2 : com) (ψ ψ' ψ'' : Vector (2^dim)),
      c1 / ψ ⇩ ψ' ->
      c2 / ψ' ⇩ ψ'' ->
      (c1 ; c2) / ψ ⇩ ψ''

where "c '/' ψ '⇩' ψ'" := (nd_eval c ψ ψ').              

Lemma nd_eval_ucom : forall (c : ucom) (dim : nat) (ψ ψ' : Vector (2^dim)),
    WF_Matrix _ _ ψ ->
    c / ψ ⇩ ψ' <-> (uc_eval dim c) × ψ = ψ'.
Proof.
  intros c dim ψ ψ' WF.
  split; intros H.
  - gen ψ' ψ.
    induction c; intros ψ' ψ WF E; dependent destruction E; subst.
    + simpl; Msimpl; easy.
    + simpl.
      rewrite Mmult_assoc.
      rewrite (IHc1 ψ'); trivial. 
      assert (WF_Matrix _ _ ψ') by (rewrite <- (IHc1 _ ψ) ; auto with wf_db).      
      rewrite (IHc2 ψ''); easy.
    + easy.
  - gen ψ' ψ.
    induction c; intros ψ' ψ WF E; subst.
    + simpl; Msimpl. constructor.
    + apply nd_seq with (uc_eval dim c1 × ψ).
      apply IHc1; trivial.
      apply IHc2; auto with wf_db.
      simpl; rewrite Mmult_assoc; easy.
    + simpl; constructor.
Qed.
