Require Import Matrix.
Require Import Setoid.

(* Important Cexp lemmas *)
Lemma Cexp_add: forall (x y : R), Cexp (x + y) = Cexp x * Cexp y.
Proof.
  intros.
  unfold Cexp.
  apply c_proj_eq; simpl.
  - apply cos_plus.
  - rewrite sin_plus. field.
Qed.

Definition proportional {m n : nat} (A B : Matrix m n) := 
  exists θ, A = Cexp θ .* B. 
Infix "∝" := proportional (at level 70).

Lemma proportional_refl : forall {m n} (A : Matrix m n), A ∝ A.
Proof.
  intros. exists 0.
  rewrite eulers0.
  rewrite Mscale_1_l.
  reflexivity.
Qed.

Lemma proportional_symm : forall {m n} (A B : Matrix m n), A ∝ B -> B ∝ A.
Proof.
  intros.
  destruct H as [θ H].
  rewrite H.
  exists (- θ)%R.
  rewrite Mscale_assoc.
  rewrite <- Cexp_add.
  rewrite Rplus_opp_l.
  rewrite eulers0.
  rewrite Mscale_1_l.
  reflexivity.
Qed.    

Lemma proportional_trans : forall {m n} (A B C : Matrix m n), 
  A ∝ B -> B ∝ C -> A ∝ C.
Proof.
  intros. 
  destruct H as [θab Hab].
  destruct H0 as [θbc Hbc].
  exists (θab + θbc)%R.
  rewrite Hab, Hbc.  
  rewrite Mscale_assoc.
  rewrite Cexp_add.
  reflexivity.
Qed.

Lemma Mmult_proportional_compat : forall {m n o} (A A' : Matrix m n) (B B' : Matrix n o),
  A ∝ A' -> B ∝ B' -> A × B ∝ A' × B'.
Proof.
  intros.
  destruct H as [θa Ha].
  destruct H0 as [θb Hb].
  subst.
  unfold proportional.
  rewrite Mscale_mult_dist_r.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_assoc.
  exists (θb + θa)%R.
  rewrite Cexp_add.
  reflexivity.
Qed.
  
Add Parametric Relation (m n : nat) : (Matrix m n) (@proportional m n)
  reflexivity proved by proportional_refl
  symmetry proved by proportional_symm
  transitivity proved by proportional_trans
  as uc_equiv_rel.

Add Parametric Morphism (m n o : nat) : (@Mmult m n o)
  with signature (@proportional m n) ==> (@proportional n o) ==> 
                                     (@proportional m o) as useq_mor.
Proof. intros x y H x0 y0 H0. apply Mmult_proportional_compat; easy. Qed.
