Require Import Quantum.
Require Import List.
Require Import SQIRE.
Require Import UnitarySem.
Require Import Setoid.

(* Also move *)

Definition norm {n} (ψ : Vector n) :=
  sqrt (fst (ψ ∘ ψ†)).  

Local Open Scope com.

Reserved Notation "c '/' ψ '⇩' ψ'"
                  (at level 40, ψ at level 39).

(* With scaling *)
(*
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
      norm ψ' <> 0%R ->
      reset n / ψ ⇩ (scale (/(norm ψ')) ψ') 
  | nd_reset1 : forall n (ψ : Vector (2^dim)),
      let ψ' := @pad 2 n dim (∣0⟩⟨1∣) × ψ in (* is this right? *)
      norm ψ' <> 0%R ->
      reset n / ψ ⇩ (scale (/(norm ψ')) ψ')
  | nd_seq : forall (c1 c2 : com) (ψ ψ' ψ'' : Vector (2^dim)),
      c1 / ψ ⇩ ψ' ->
      c2 / ψ' ⇩ ψ'' ->
      (c1 ; c2) / ψ ⇩ ψ''

where "c '/' ψ '⇩' ψ'" := (nd_eval c ψ ψ').              
*)

(* Without scaling *)
Inductive nd_eval {dim : nat} : com -> Vector (2^dim) -> Vector (2^dim) -> Prop :=
  | nd_skip : forall ψ, nd_eval skip ψ ψ
  | nd_app : forall n (u : Unitary n) (l : list nat) (ψ : Vector (2^dim)),
      app u l / ψ ⇩ ((ueval dim u l) × ψ)
  | nd_meas0 : forall n (ψ : Vector (2^dim)),
      let ψ' := @pad 1 n dim (∣0⟩⟨0∣) × ψ in 
      norm ψ' <> 0%R -> (* better way to say this in terms of partial trace? *)
      meas n / ψ ⇩ ψ' 
  | nd_meas1 : forall n (ψ : Vector (2^dim)),
      let ψ' := @pad 1 n dim (∣1⟩⟨1∣) × ψ in
      norm ψ' <> 0%R ->
      meas n / ψ ⇩ ψ' 
  | nd_reset0 : forall n (ψ : Vector (2^dim)),
      let ψ' := @pad 1 n dim (∣0⟩⟨0∣) × ψ in 
      norm ψ' <> 0%R ->
      reset n / ψ ⇩ ψ' 
  | nd_reset1 : forall n (ψ : Vector (2^dim)),
      let ψ' := @pad 1 n dim (∣0⟩⟨1∣) × ψ in (* is this right? *)
      norm ψ' <> 0%R ->
      reset n / ψ ⇩ ψ'
  | nd_seq : forall (c1 c2 : com) (ψ ψ' ψ'' : Vector (2^dim)),
      c1 / ψ ⇩ ψ' ->
      c2 / ψ' ⇩ ψ'' ->
      (c1 ; c2) / ψ ⇩ ψ''

where "c '/' ψ '⇩' ψ'" := (nd_eval c ψ ψ').              

Lemma nd_eval_ucom : forall (c : ucom) (dim : nat) (ψ ψ' : Vector (2^dim)),
    WF_Matrix ψ ->
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
      assert (WF_Matrix ψ') by (rewrite <- (IHc1 _ ψ) ; auto with wf_db).      
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

Definition nd_equiv (c1 c2 : com) := forall dim (ψ ψ' : Vector (2^dim)), 
  c1 / ψ ⇩ ψ' <-> c2 / ψ ⇩ ψ'.

(* Maybe a new scope is warranted? *)
Infix "≡" := nd_equiv : com_scope.

Lemma nd_seq_assoc : forall c1 c2 c3,
    ((c1 ; c2) ; c3) ≡ (c1 ; (c2 ; c3)).
Proof.
  intros c1 c2 c3 dim ψ ψ'.
  split; intros E.
  - dependent destruction E.
    dependent destruction E1.
    econstructor; eauto.
    econstructor; eauto.
  - dependent destruction E.
    dependent destruction E2.
    econstructor; eauto.
    econstructor; eauto.
Qed.

Lemma nd_equiv_refl : forall c1, c1 ≡ c1. 
Proof. easy. Qed.

Lemma nd_equiv_sym : forall c1 c2, c1 ≡ c2 -> c2 ≡ c1. 
Proof. easy. Qed.

Lemma nd_equiv_trans : forall c1 c2 c3, c1 ≡ c2 -> c2 ≡ c3 -> c1 ≡ c3. 
Proof. 
  intros c1 c2 c3 H12 H23 dim ψ ψ'. 
  specialize (H12 dim ψ ψ') as [L12 R12].
  specialize (H23 dim ψ ψ') as [L23 R23].
  split; auto.
Qed.

Add Parametric Relation : com nd_equiv 
  reflexivity proved by nd_equiv_refl
  symmetry proved by nd_equiv_sym
  transitivity proved by nd_equiv_trans
  as nd_equiv_rel.

Lemma nd_seq_congruence : forall c1 c1' c2 c2',
    c1 ≡ c1' ->
    c2 ≡ c2' ->
    c1 ; c2 ≡ c1' ; c2'.
Proof.
  intros c1 c1' c2 c2' Ec1 Ec2 dim ψ ψ'.
  split; intros H; dependent destruction H.
  - (* rewrite Ec1 in H. //Fails? *)
    apply Ec1 in H.
    apply Ec2 in H0.
    econstructor; eauto.
  - apply Ec1 in H.
    apply Ec2 in H0.
    econstructor; eauto.
Qed.

Add Parametric Morphism : seq 
  with signature nd_equiv ==> nd_equiv ==> nd_equiv as useq_mor.
Proof. intros x y H x0 y0 H0. apply nd_seq_congruence; easy. Qed.

Lemma meas_reset : forall q, meas q ; reset q ≡ reset q.
Proof.
  intros q dim ψ ψ'.
  split; intros H.
  - dependent destruction H;
    dependent destruction H;
    dependent destruction H0;
    subst ψ' ψ'0.
    + specialize (nd_reset0 q ψ H) as E. clear H H0.
      unfold pad in *.
      bdestruct (q + 1 <=? dim).
      * rewrite <- Mmult_assoc.
        restore_dims_strong.
        Msimpl.  
        replace (∣0⟩⟨0∣ × ∣0⟩⟨0∣) with (∣0⟩⟨0∣) by solve_matrix.
        revert E. restore_dims_strong. auto. 
      * rewrite <- Mmult_assoc. rewrite Mmult_0_r. auto. 
    + contradict H0.
      unfold norm. unfold pad.
      bdestruct (q + 1 <=? dim); simpl.
      rewrite <- Mmult_assoc.
      restore_dims_strong.
      Msimpl.  
      replace (∣0⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
      rewrite kron_0_r, kron_0_l, Mmult_0_l. (* Msimpl should handle *)
      unfold dot. (* need dot product lemmas *)
      rewrite Csum_0. 
      simpl. rewrite sqrt_0. reflexivity.
      intros; simpl; unfold adjoint, Zero. lca. 
      rewrite Mmult_0_l.
      unfold dot. (* need dot product lemmas *)
      rewrite Csum_0. 
      simpl. rewrite sqrt_0. reflexivity.
      intros; simpl; unfold adjoint, Zero. lca. 
    + contradict H0.
      unfold norm. unfold pad.
      bdestruct (q + 1 <=? dim); simpl.
      rewrite <- Mmult_assoc.
      restore_dims_strong.
      Msimpl.  
      replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix.
      rewrite kron_0_r, kron_0_l, Mmult_0_l. (* Msimpl should handle *)
      unfold dot. (* need dot product lemmas *)
      rewrite Csum_0. 
      simpl. rewrite sqrt_0. reflexivity.
      intros; simpl; unfold adjoint, Zero. lca. 
      rewrite Mmult_0_l.
      unfold dot. (* need dot product lemmas *)
      rewrite Csum_0. 
      simpl. rewrite sqrt_0. reflexivity.
      intros; simpl; unfold adjoint, Zero. lca. 
    + specialize (nd_reset1 q ψ) as E.
      unfold pad in *.
      bdestruct (q + 1 <=? dim).
      * revert E.
        revert H0.
        rewrite <- Mmult_assoc.
        restore_dims_strong.
        Msimpl.  
        replace (∣0⟩⟨1∣ × ∣1⟩⟨1∣) with (∣0⟩⟨1∣) by solve_matrix.
        restore_dims_strong. auto. 
      * rewrite <- Mmult_assoc. rewrite Mmult_0_r. auto. 
  - dependent destruction H; subst ψ'.
    + econstructor.
      apply nd_meas0; assumption.
      (* this could be its own lemma *)
      assert (L: @pad 1 q dim ∣0⟩⟨0∣ × ψ = @pad 1 q dim ∣0⟩⟨0∣ × (@pad 1 q dim ∣0⟩⟨0∣ × ψ)).
      clear. unfold pad. bdestruct (q + 1 <=? dim).
      rewrite <- Mmult_assoc. restore_dims_strong. Msimpl.
      replace (∣0⟩⟨0∣ × ∣0⟩⟨0∣) with (∣0⟩⟨0∣) by solve_matrix.
      reflexivity.
      repeat rewrite Mmult_0_l. reflexivity.
      rewrite L at 2.
      apply nd_reset0.
      rewrite <- L.
      assumption.
    + econstructor.
      apply nd_meas1.
      (* Well, that's annoying. We could use the same restriction for
         meas and reset, but I'd prefer a more succinct, computable
         restriction. *)
Abort.
