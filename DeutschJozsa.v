Require Import Quantum.
Require Import List.
Require Import SQIMP.
Require Import UnitarySem.


Inductive boolean : nat -> ucom -> Set :=
  | boolean_I : forall u, u ≡ uskip -> boolean 1 u
  | boolean_X : forall u, u ≡ (X 0) -> boolean 1 u
  | boolean_U : forall u u1 u2 dim, boolean dim u1 -> boolean dim u2 ->
                uc_eval (S dim) u = (uc_eval dim u1 ⊗ ∣0⟩⟨0∣) .+ (uc_eval dim u2 ⊗ ∣1⟩⟨1∣) ->
                boolean (S dim) u.
  
Fixpoint count {dim : nat} {U : ucom} (P : boolean dim U)  : nat :=
  match P with
  | boolean_I _ _ => 0
  | boolean_X _ _ => 1
  | boolean_U u u1 u2 dim P1 P2 P => count P1 + count P2
  end.

Definition balanced (dim : nat) {U : ucom} (P : boolean dim U) : Prop :=
  count P = (2 ^ (dim - 1))%nat.

Definition constant (dim : nat) {U : ucom} (P : boolean dim U) : Prop :=
  count P = 0%nat \/ count P = (2 ^ dim)%nat.

Fixpoint cpar1 (n : nat) (u : nat -> ucom) : ucom :=
  match n with
  | 0 => uskip
  | S n' => cpar1 n' u ; u n'
  end.

Definition deutsch_jozsa (dim : nat) {U : ucom} (P : boolean dim U) : ucom := 
  cpar1 (S dim) H; U ; cpar1 (S dim) H.

Fixpoint nket (n : nat) (ψ : Matrix 2 1) : Matrix (2^n) 1 :=
  match n with
  | 0 => I 1
  | S n' => (nket n' ψ) ⊗ ψ
  end.

Type (nket 4 ∣0⟩) ⊗ ∣1⟩.

Lemma aux : forall a b : nat, (a + b = 0 <-> a = 0 /\ b = 0)%nat.
Proof.
  intros. lia.
Qed.

Require Import GHZ.

Lemma deutsch_jozsa_correct : forall (dim : nat) (U : ucom) (P : boolean dim U),
  (count P = 0)%nat -> 
  (@Mmult _ _ 1 (uc_eval (S dim) U) ((nket dim ∣0⟩) ⊗ ∣1⟩)) = ((nket dim ∣0⟩) ⊗ ∣1⟩).
Proof.
  induction P; intros H.
  - rewrite u0.
    simpl; Msimpl; reflexivity.
  - simpl in H. lia.
  - intros. inversion H. 
    apply aux in H1. inversion H1.
    apply IHP1 in H0.
    apply IHP2 in H2.
    Search uc_eval pad.
    replace (S (S dim))%nat with (S dim + 1)%nat by lia.
    rewrite <- pad_dims. (* need a proof that every boolean function is well-typed for it's dim *)
    rewrite e.
    simpl.

    (* /up to here - RNR *)

    
    rewrite u0; simpl.
    unfold ueval1, pad; simpl.
    simpl; Msimpl. 
    restore_dims.
    rewrite kron_mixed_product.
    autorewrite with ket_db; auto with wf_db.
    reflexivity.

    inversion H.

  intros. induction dim.
  - inversion P. simpl.
    + rewrite H0. simpl. rewrite Mmult_1_l. reflexivity. prove_wf.
    +  inversion H.
  - induction P.
    + rewrite u0 in *. simpl in *.


induction P.
  - rewrite u0. simpl. show_dimensions.
    rewrite Mmult_1_l.


  intros. induction P.
  - intros. rewrite u0. simpl. rewrite Mmult_1_l. reflexivity. prove_wf. 
  - intros. inversion H.
  - intros. inversion H. 
    apply aux in H1. inversion H1.
    apply IHP1 in H0.
    apply IHP2 in H2.
    




    generalize dependent dim0.
    induction e.
    induction dim.

    apply (IHP1 (S dim)) in H0. apply IHP2 in H2.
    remember (S dim) as k.



