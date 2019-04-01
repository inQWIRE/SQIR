Require Import SQIMP.
Require Import UnitarySem.

Module UTeleport.

Definition bell (c b : nat) : ucom := H c ; CNOT c b.
Definition alice (a c : nat) : ucom := CNOT a c ; H a.
Definition bob (a c b: nat) : ucom := CNOT c b; CZ a b.
Definition teleport (a c b : nat) : ucom := alice a c; bob a c b.


Open Scope R_scope.

Notation "∣+⟩" := (1/√2 .* ∣0⟩ .+ 1/√2 .* ∣1⟩)%C.

Definition epr00 : Vector 4 :=
  fun x y => match x, y with
             | 0, 0 => (1/√2)%C
             | 3, 0 => (1/√2)%C
             | _, _ => 0%C
             end.

Lemma epr_correct : 
  forall (ψ : Vector 2), WF_Matrix _ _ ψ -> (uc_eval 3 (bell 1 2)) × (ψ ⊗ ∣0⟩ ⊗ ∣0⟩) = ψ ⊗ epr00. 
Proof.
  intros.
  unfold bell. simpl. unfold ueval_cnot, ueval1. simpl. unfold pad. simpl.
  solve_matrix.
Qed.

Lemma teleport_correct : forall (ψ : Vector 2), 
    WF_Matrix _ _ ψ -> uc_eval 3 (teleport 0 1 2) × (ψ ⊗ epr00) = (∣+⟩ ⊗ ∣+⟩ ⊗ ψ).
Proof.
  intros.
  unfold teleport. simpl.
  unfold ueval1.
  unfold ueval_cnot, pad. simpl.
  solve_matrix;
  remember (ψ 0%nat 0%nat) as a; remember (ψ 1%nat 0%nat) as b.
  all : try rewrite (Cmult_comm a _); try rewrite (Cmult_comm b _).
  all : repeat rewrite Cmult_assoc.
  all : remember (/ √ 2 * / √ 2 * / √ 2 * b)%C as β.
  all : remember (/ √ 2 * / √ 2 * / √ 2 * a)%C as α.
  all : try rewrite (Copp_mult_distr_r (/√2)%C _).
  all : rewrite <- Cmult_plus_distr_l.
  all : repeat rewrite Cplus_assoc.
  all : try rewrite Copp_plus_distr; try rewrite Copp_involutive.
  all : try rewrite Cplus_assoc.
  all : try rewrite <- (Cplus_assoc α β α); try rewrite <- (Cplus_assoc α β (-α)). 
  all : rewrite (Cplus_comm β _); rewrite Cplus_assoc.
  all : autorewrite with C_db; try rewrite <- Cplus_assoc; autorewrite with C_db; rewrite Cdouble.
  all : try rewrite Heqα; try rewrite Heqβ.
  all : rewrite <- Cmult_plus_distr_l; repeat rewrite Cmult_assoc.
  all : autorewrite with C_db.
  all : rewrite <- (Cmult_assoc (/2) _ _); autorewrite with C_db.
  all : rewrite Cmult_assoc.
  all : rewrite <- (Cmult_assoc (/2) _ _); autorewrite with C_db; reflexivity.
Qed.

End UTeleport.

Section NDTeleport.

Definition q := 0. (* qubit for transmission *)
Definition a := 1. (* alice's qubit *)
Definition b := 2. (* bob's qubit *)

Require Import NDSem.

Definition bell : com := H a ; CNOT a b.
Definition alice : com := CNOT q a ; H a ; meas q ; meas a.
Definition bob : com := CNOT q b; CZ q a; reset q; reset a.
Definition teleport : com := bell; alice; bob.

Open Scope R_scope.

Definition epr00 : Vector 4 := / √ 2 .* ∣ 0, 0 ⟩ .+ / √ 2 .* ∣ 1, 1 ⟩.

Definition notc : Matrix 4 4 :=
  fun x y => match x, y with 
          | 1, 3 => 1%C
          | 3, 1 => 1%C
          | 0, 0 => 1%C
          | 2, 2 => 1%C
          | _, _ => 0%C
          end.          

Lemma cnot_decomposition : ∣1⟩⟨1∣ ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 2 = cnot.
Proof. solve_matrix. Qed.                                               

Lemma notc_decomposition : σx ⊗ ∣1⟩⟨1∣ .+ I 2 ⊗ ∣0⟩⟨0∣ = notc.
Proof. solve_matrix. Qed.                                               

Require Import Dirac.

Ltac kmp_rewrite A B C D :=
  rewrite (kron_mixed_product' _ _ _ _ _ _ _ _ _ _ _ A B C D); simpl; unify_pows_two; try omega.

Ltac destruct_seqs := 
  repeat match goal with
  | [H : ?a / _ ⇩ _ |- _] => unfold a in H
  | [H : (_ ; _) / _ ⇩ _ |- _] => dependent destruction H
  end.

Ltac destruct_apps := 
  repeat match goal with
  | [H : app _ _ / _ ⇩ _ |- _] => dependent destruction H
  end.

(* Thought I had this. *)
(* Generalizable? *)
Lemma ket_decomposition : forall (ψ : Vector 2), 
  WF_Matrix _ _ ψ ->
  ψ = (ψ 0%nat 0%nat) .* ∣ 0 ⟩ .+ (ψ 1%nat 0%nat) .* ∣ 1 ⟩.
Proof.
  intros.
  prep_matrix_equality.
  unfold scale, Mplus.
  destruct y as [|y']. 
  2:{ rewrite H; try omega. 
      unfold ket, qubit0, qubit1. simpl. 
      repeat (destruct x; try clra). 
  }
  destruct x as [| [| n]]; unfold ket, qubit0, qubit1; simpl; try clra.  
  rewrite H; try omega.
  clra.
Qed. 

Notation "∣+⟩" := (1/√2 .* ∣0⟩ .+ 1/√2 .* ∣1⟩)%C.
Notation "∣-⟩" := (1/√2 .* ∣0⟩ .+ (- 1/√2) .* ∣1⟩)%C.

Definition mult' := mult.
Definition pow' := Nat.pow.
Lemma mult_lock : mult = mult'. reflexivity. Qed.
Lemma pow_lock : Nat.pow = pow'. reflexivity. Qed.
Opaque mult'.
Opaque pow'.

(* Simplifies without simplifying Matrix dimensions. *)
Ltac simpl' := 
  repeat rewrite Nat.pow_1_r in *;
  repeat rewrite pow_lock;
  repeat rewrite mult_lock;
  simpl;
  repeat rewrite <- mult_lock;
  repeat rewrite <- pow_lock.

(* Normalize: Gives default dimensions to matrix expressions *)
Ltac restore_dims :=
  repeat match goal with
  | [ |- context[@Mmult ?m ?n ?o ?A ?B]] => let Matrix m' n' := type of A in 
                                          let Matrix n'' o' := type of B in 
                                          replace m with m' by easy
         end.



Lemma teleport_correct : forall (ψ : Vector (2^1)) (ψ' : Vector (2^3)),
  WF_Matrix _ _ ψ ->
  teleport / (ψ  ⊗ ∣ 0 , 0 ⟩) ⇩ ψ' -> ψ' = ∣ 0 , 0 ⟩ ⊗ ψ.   
Proof.
  intros ψ ψ' WF H.
  destruct_seqs; destruct_apps.
  evar (e : Vector (2^3)).  
  assert ((ueval 3 U_H [a] × (ueval 3 U_CNOT (q::[a]) × (ueval 3 U_CNOT (a::[b]) × (ueval 3 U_H [a] × (ψ ⊗ ∣ 0, 0 ⟩))))) = e).
  rewrite (ket_decomposition ψ); auto.
  unfold ueval, ueval_cnot, ueval1, pad; simpl'; Msimpl.
  setoid_rewrite cnot_decomposition.
  autorewrite with ket_db.
  rewrite <- kron_assoc.
  rewrite <- kron_assoc.
  Msimpl'.
setoid_rewrite kron_mixed_product'.
  Set Printing All.

  rewrite kron_mixed_product'.
  Msimpl.
  Msimpl'.
  autorewrite with ket_db.
  setoid_rewrite (kron_assoc _ _ _ _ _ _ ∣ 0 ⟩ ∣ 0 ⟩ ∣ 0 ⟩).
  setoid_rewrite (kron_assoc _ _ _ _ _ _ ∣ 0 ⟩ ∣ 1 ⟩ ∣ 0 ⟩).
  setoid_rewrite (kron_assoc _ _ _ _ _ _ ∣ 1 ⟩ ∣ 0 ⟩ ∣ 0 ⟩).
  setoid_rewrite (kron_assoc _ _ _ _ _ _ ∣ 1 ⟩ ∣ 1 ⟩ ∣ 0 ⟩).
  Msimpl'; try reflexivity.
  autorewrite with ket_db.
  setoid_rewrite CNOT00_spec.
  setoid_rewrite CNOT10_spec.
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ ∣ 0 ⟩ ∣ 0 ⟩ ∣ 0 ⟩).
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ ∣ 0 ⟩ ∣ 1 ⟩ ∣ 1 ⟩).
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ ∣ 1 ⟩ ∣ 0 ⟩ ∣ 0 ⟩).
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ ∣ 1 ⟩ ∣ 1 ⟩ ∣ 1 ⟩).
  Msimpl'. simpl. 
  kmp_rewrite cnot (I 2) ∣ 0 , 0 ⟩ ∣ 0 ⟩.
  kmp_rewrite cnot (I 2) ∣ 0 , 1 ⟩ ∣ 1 ⟩.
  kmp_rewrite cnot (I 2) ∣ 1 , 0 ⟩ ∣ 0 ⟩.
  kmp_rewrite cnot (I 2) ∣ 1 , 1 ⟩ ∣ 1 ⟩.
  autorewrite with ket_db; auto with wf_db.
  setoid_rewrite CNOT00_spec.
  setoid_rewrite CNOT01_spec.
  setoid_rewrite CNOT10_spec.
  setoid_rewrite CNOT11_spec.
  kmp_rewrite (I 2 ⊗ hadamard) (I 2) ∣ 0 , 0 ⟩ ∣ 0 ⟩.
  kmp_rewrite (I 2 ⊗ hadamard) (I 2) ∣ 0 , 1 ⟩ ∣ 1 ⟩.
  kmp_rewrite (I 2 ⊗ hadamard) (I 2) ∣ 1 , 1 ⟩ ∣ 0 ⟩.
  kmp_rewrite (I 2 ⊗ hadamard) (I 2) ∣ 1 , 0 ⟩ ∣ 1 ⟩.
  Msimpl'; trivial.
  autorewrite with ket_db C_db.  
  kmp_rewrite cnot (I 2) ∣ 0 , 1 ⟩ ∣ 1 ⟩.
  kmp_rewrite cnot (I 2) ∣ 1 , 0 ⟩ ∣ 0 ⟩.
  kmp_rewrite cnot (I 2) ∣ 1 , 1 ⟩ ∣ 1 ⟩.


Lemma teleport_correct : forall (ψ : Vector (2^1)) (ψ' : Vector (2^3)),
  WF_Matrix _ _ ψ ->
  teleport / (ψ  ⊗ ∣ 0 , 0 ⟩) ⇩ ψ' -> ψ' = ∣ 0 , 0 ⟩ ⊗ ψ.   
Proof.
  intros ψ ψ' WF H.
  destruct_seqs; destruct_apps.
  evar (e : Vector (2^3)).  
  assert ((ueval 3 U_H [a] × (ueval 3 U_CNOT (q::[a]) × (ueval 3 U_CNOT (a::[b]) × (ueval 3 U_H [a] × (ψ ⊗ ∣ 0, 0 ⟩))))) = e).
  rewrite (ket_decomposition ψ); auto.
  unfold ueval, ueval_cnot, ueval1, pad; simpl; Msimpl.
  setoid_rewrite cnot_decomposition.
  autorewrite with ket_db.
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ ∣ 0 ⟩ ∣ 0 ⟩ ∣ 0 ⟩).
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ ∣ 1 ⟩ ∣ 0 ⟩ ∣ 0 ⟩).
  Msimpl'; try reflexivity.
  autorewrite with ket_db.
  setoid_rewrite (kron_assoc _ _ _ _ _ _ ∣ 0 ⟩ ∣ 0 ⟩ ∣ 0 ⟩).
  setoid_rewrite (kron_assoc _ _ _ _ _ _ ∣ 0 ⟩ ∣ 1 ⟩ ∣ 0 ⟩).
  setoid_rewrite (kron_assoc _ _ _ _ _ _ ∣ 1 ⟩ ∣ 0 ⟩ ∣ 0 ⟩).
  setoid_rewrite (kron_assoc _ _ _ _ _ _ ∣ 1 ⟩ ∣ 1 ⟩ ∣ 0 ⟩).
  Msimpl'; try reflexivity.
  autorewrite with ket_db.
  setoid_rewrite CNOT00_spec.
  setoid_rewrite CNOT10_spec.
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ ∣ 0 ⟩ ∣ 0 ⟩ ∣ 0 ⟩).
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ ∣ 0 ⟩ ∣ 1 ⟩ ∣ 1 ⟩).
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ ∣ 1 ⟩ ∣ 0 ⟩ ∣ 0 ⟩).
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ ∣ 1 ⟩ ∣ 1 ⟩ ∣ 1 ⟩).
  Msimpl'. simpl. 
  kmp_rewrite cnot (I 2) ∣ 0 , 0 ⟩ ∣ 0 ⟩.
  kmp_rewrite cnot (I 2) ∣ 0 , 1 ⟩ ∣ 1 ⟩.
  kmp_rewrite cnot (I 2) ∣ 1 , 0 ⟩ ∣ 0 ⟩.
  kmp_rewrite cnot (I 2) ∣ 1 , 1 ⟩ ∣ 1 ⟩.
  autorewrite with ket_db; auto with wf_db.
  setoid_rewrite CNOT00_spec.
  setoid_rewrite CNOT01_spec.
  setoid_rewrite CNOT10_spec.
  setoid_rewrite CNOT11_spec.
  kmp_rewrite (I 2 ⊗ hadamard) (I 2) ∣ 0 , 0 ⟩ ∣ 0 ⟩.
  kmp_rewrite (I 2 ⊗ hadamard) (I 2) ∣ 0 , 1 ⟩ ∣ 1 ⟩.
  kmp_rewrite (I 2 ⊗ hadamard) (I 2) ∣ 1 , 1 ⟩ ∣ 0 ⟩.
  kmp_rewrite (I 2 ⊗ hadamard) (I 2) ∣ 1 , 0 ⟩ ∣ 1 ⟩.
  Msimpl'; trivial.
  autorewrite with ket_db C_db.  
  kmp_rewrite cnot (I 2) ∣ 0 , 1 ⟩ ∣ 1 ⟩.
  kmp_rewrite cnot (I 2) ∣ 1 , 0 ⟩ ∣ 0 ⟩.
  kmp_rewrite cnot (I 2) ∣ 1 , 1 ⟩ ∣ 1 ⟩.
  
  Msimpl'; try reflexivity.
  autorewrite with ket_db.
  

  intros ψ ψ' WF H.
  destruct_seqs; destruct_apps.
  evar (e : Vector (2^3)).
  assert ((ueval 3 U_H [a] × (ueval 3 U_CNOT (q::[a]) × (ueval 3 U_CNOT (a::[b]) × (ueval 3 U_H [a] × (ψ ⊗ ∣ 0, 0 ⟩))))) = e).
  unfold ueval, ueval_cnot, ueval1, pad; simpl; Msimpl.
  setoid_rewrite cnot_decomposition.
  setoid_rewrite kron_assoc.
  kmp_rewrite (I 2) (hadamard ⊗ I 2) ψ (∣ 0, 0 ⟩).
  simpl in *; autorewrite with ket_db; trivial. (* autorewrite should discharge WF conditions! *)
  idtac.                                                                                         
  kmp_rewrite hadamard (I 2) ∣ 0 ⟩ ∣ 0 ⟩.
  simpl in *; autorewrite with ket_db; auto with wf_db. (* autorewrite should discharge WF conditions! *)
  Msimpl'.
  simpl in *; autorewrite with ket_db; trivial. 
  setoid_rewrite CNOT00_spec.
  setoid_rewrite CNOT10_spec.
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ ψ ∣ 0 ⟩ ∣ 0 ⟩).
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ ψ ∣ 1 ⟩ ∣ 1 ⟩).
  simpl in *; autorewrite with ket_db; trivial. 
  kmp_rewrite cnot (I 2) (ψ ⊗ ∣ 0 ⟩) ∣ 0 ⟩.
  kmp_rewrite cnot (I 2) (ψ ⊗ ∣ 1 ⟩) ∣ 1 ⟩.
  Msimpl. 
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ (I 2) hadamard (I 2)).
  kmp_rewrite (I 2 ⊗ hadamard) (I 2) (cnot × (ψ ⊗ ∣ 0 ⟩)) ∣ 0 ⟩.  
  kmp_rewrite (I 2 ⊗ hadamard) (I 2) (cnot × (ψ ⊗ ∣ 1 ⟩)) ∣ 1 ⟩.  
  Msimpl.
  unfold e. reflexivity.
  dependent destruction H0_2.
  inversion H0_2; subst.
  
  
  
  inversion H0_2.
  unfold teleport in *.
  match goal with
  | [H : (_ ; _) / _ ⇩ _ |- _] => dependent destruction H
  end.
  
  dependent destruction H.
  dependent destruction H.
  (* Bell State *)
  assert ( ψ' = ψ ⊗ epr00).
  dependent destruction H.
  dependent destruction H.
  dependent destruction H0.
  
  
  replace (SQIMP.H a; CNOT a b) with (from_ucom (SQIMP.H a; CNOT a b))%ucom in H by reflexivity.
  apply nd_eval_ucom in H; auto with wf_db.
  simpl in H.
  

Lemma teleport_correct_manual : forall (ψ : Vector (2^1)) (ψ' : Vector (2^3)),
  WF_Matrix _ _ ψ ->
  teleport / (ψ  ⊗ ∣ 0 , 0 ⟩) ⇩ ψ' -> ψ' = ∣ 0 , 0 ⟩ ⊗ ψ.   
Proof.
  intros ψ ψ' WF H.
  dependent destruction H.
  dependent destruction H.
  (* Bell State *)
  assert ( ψ' = ψ ⊗ epr00).
  dependent destruction H.
  dependent destruction H.
  dependent destruction H0.
  simpl.
  unfold ueval_cnot, ueval1, pad; simpl; Msimpl.
  setoid_rewrite kron_assoc.
  simpl.
  kmp_rewrite (I 2) (hadamard ⊗ I 2) ψ (∣ 0, 0 ⟩).
  kmp_rewrite hadamard (I 2) ∣0⟩ ∣0⟩. 
  Msimpl.
  setoid_rewrite H0_spec.  
  kmp_rewrite (I 2) (∣1⟩⟨1∣ ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 2) ψ ((/ √ 2 .* ∣ 0 ⟩ .+ / √ 2 .* ∣ 1 ⟩) ⊗ ∣0⟩). 
  Msimpl.                                                                                              
  setoid_rewrite cnot_decomposition.
  rewrite kron_plus_distr_r.
  replace qubit0 with (ket 0) by reflexivity.
  repeat rewrite Mscale_kron_dist_l.
  rewrite Mmult_plus_distr_l.
  repeat rewrite Mscale_mult_dist_r.
  setoid_rewrite CNOT00_spec.
  setoid_rewrite CNOT10_spec.
  reflexivity.
  (* Teleport *)
  subst.
  dependent destruction H0.
  dependent destruction H0_.
  
  
  Search scale Mmult.
  Search cnot.
  Search Mmult Mplus.
  Search kron Mplus.
  
  rewrite Mmult_plus_dist_r.
  replace (∣1⟩⟨1∣ ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 2) with cnot by solve_matrix. (* should be a lemma *)
  kmp_rewrite hadamard (I 2) ∣0⟩ ∣0⟩. 
  rewrite (Mmult_1_l _ _ ∣0⟩); auto with wf_db.
                                    Msimpl.
kmp_rewrite hadamard (I 2) ∣0⟩ ∣0⟩. 
  Msimpl'.                                                                                                                                                                                     
  Msimpl.
  
  
  apply nd_seq_assoc in H.
  cbv [teleport] in H.
  repeat rewrite 
  unfold teleport in H, bell00 in H, alice, bob, teleport in *.
  
  
  dependent destruction H.
  dependent destruction H.
  dependent destruction H.
  inversion H; subst.
  dependent destruction H.
  dependent destruction H0.
  
  
  
