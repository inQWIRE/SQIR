Require Import Phase.
Require Import Setoid.

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
                                     (@proportional m o) as Mmult_mor.
Proof. intros x y H x0 y0 H0. apply Mmult_proportional_compat; easy. Qed.

(* Example: *)

Lemma phase_X : forall θ, phase_shift θ × σx ∝ σx × phase_shift (- θ).
Proof.
  intros. 
  exists θ.
  solve_matrix.
  rewrite Cexp_mul_neg_r.
  reflexivity.
Qed.

Require Import SQIRE.
Require Import UnitarySem.

Definition uc_cong {dim : nat} (c1 c2 : ucom dim) :=
  uc_eval c1 ∝ uc_eval c2.
Infix "≅" := uc_cong (at level 70).

Lemma uc_cong_refl : forall {dim : nat} (c1 : ucom dim), c1 ≅ c1.
Proof. intros. exists 0%R. rewrite Cexp_0. rewrite Mscale_1_l. reflexivity. Qed.

Lemma uc_cong_sym : forall {dim : nat} (c1 c2 : ucom dim), c1 ≅ c2 -> c2 ≅ c1.
Proof.
  intros. inversion H.
  exists (Ropp x). rewrite H0. rewrite Mscale_assoc. rewrite <- Cexp_add.
  rewrite Rplus_comm.
  rewrite Rplus_opp_r. rewrite Cexp_0. rewrite Mscale_1_l. reflexivity.
Qed.

Lemma uc_cong_trans : forall {dim : nat} (c1 c2 c3 : ucom dim), c1 ≅ c2 -> c2 ≅ c3 -> c1 ≅ c3.
Proof.
  intros. inversion H. inversion H0.
  exists (x + x0)%R. rewrite H1. rewrite H2.
  rewrite Mscale_assoc.
  rewrite Cexp_add. reflexivity.
Qed.

Lemma uc_equiv_cong : forall {dim : nat} (c c' : ucom dim), (c ≡ c')%ucom -> c ≅ c'.
Proof.
  intros.
  exists 0. rewrite Cexp_0, Mscale_1_l. 
  apply H.
Qed.

Require Import Representations.

Definition uc_cong_l {dim} (l1 l2 : gate_list dim) := 
  (list_to_ucom l1) ≅ (list_to_ucom l2).
Infix "≅l≅" := uc_cong_l (at level 20).

Open Scope ucom.

Lemma uc_seq_cong : forall {dim : nat} (c1 c1' c2 c2' : ucom dim),
    c1 ≅ c1' -> c2 ≅ c2' -> c1; c2 ≅ c1'; c2'.
Proof.
  intros dim c1 c1' c2 c2' Ec1 Ec2.
  inversion Ec1. inversion Ec2.
  exists (x + x0)%R. simpl.
  rewrite H. rewrite H0.
  rewrite Mscale_mult_dist_r.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_assoc.
  rewrite Cexp_add.
  reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (ucom dim) (@uc_cong dim)
  reflexivity proved by uc_cong_refl
  symmetry proved by uc_cong_sym
  transitivity proved by uc_cong_trans
  as uc_cong_rel.

Add Parametric Morphism (dim : nat) : (@useq dim) 
  with signature (@uc_cong dim) ==> (@uc_cong dim) ==> (@uc_cong dim) as useq_mor.
Proof. intros. apply uc_seq_cong; assumption. Qed.

Lemma uc_cong_l_refl : forall {dim : nat} (l1 : gate_list dim), l1 ≅l≅ l1.
Proof. intros. exists 0%R. rewrite Cexp_0. rewrite Mscale_1_l. reflexivity. Qed.

Lemma uc_cong_l_sym : forall {dim : nat} (l1 l2 : gate_list dim), l1 ≅l≅ l2 -> l2 ≅l≅ l1.
Proof. intros. unfold uc_cong_l in *. rewrite H. reflexivity. Qed.

Lemma uc_cong_l_trans : forall {dim : nat} (l1 l2 l3 : gate_list dim), l1 ≅l≅ l2 -> l2 ≅l≅ l3 -> l1 ≅l≅ l3.
Proof.
  intros.
  unfold uc_cong_l in *.
  eapply uc_cong_trans. apply H. apply H0.
Qed.  

Lemma uc_cong_l_cons_congruence : forall {dim : nat} (g : gate_app dim) (l l' : gate_list dim),
  l ≅l≅ l' -> (g :: l) ≅l≅ (g :: l').
Proof.
  intros. unfold uc_cong_l in *.
  simpl.
  inversion H.
  destruct g; exists x; simpl; rewrite <- Mscale_mult_dist_l; rewrite H0; reflexivity.
Qed.

Lemma uc_cong_l_app_congruence : forall {dim : nat} (l l' m m': gate_list dim),
  l ≅l≅ l' -> m ≅l≅ m' -> (m ++ l) ≅l≅ (m' ++ l').
Proof.
  intros.
  unfold uc_cong_l in *.
  inversion H. inversion H0.
  exists (x + x0)%R.
  repeat rewrite uc_eval_l_app.
  rewrite <- Mscale_mult_dist_l. rewrite H1. rewrite H2. 
  Search scale Mmult.
  rewrite Mscale_mult_dist_r.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_assoc.
  rewrite <- Cexp_add.
  rewrite Rplus_comm.
  rewrite Mscale_mult_dist_l.
  reflexivity.
Qed.
    
Add Parametric Relation (dim : nat) : (gate_list dim) (@uc_cong_l dim)
  reflexivity proved by uc_cong_l_refl
  symmetry proved by uc_cong_l_sym
  transitivity proved by uc_cong_l_trans
  as uc_cong_l_rel.

Add Parametric Morphism (dim : nat) : (@cons (gate_app dim))
  with signature eq ==> (@uc_cong_l dim) ==> (@uc_cong_l dim) as cons_mor.
Proof. intros. apply uc_cong_l_cons_congruence. easy. Qed.

Add Parametric Morphism (dim : nat) : (@app (gate_app dim))
  with signature (@uc_cong_l dim) ==> (@uc_cong_l dim) ==> (@uc_cong_l dim) as app_mor.
Proof. intros x y H x0 y0 H0. apply uc_cong_l_app_congruence; easy. Qed.

Lemma uc_equiv_cong_l : forall {dim : nat} (c c' : gate_list dim), c =l= c' -> c ≅l≅ c'.
Proof.
  intros.
  exists 0. rewrite Cexp_0, Mscale_1_l. 
  apply H.
Qed.
