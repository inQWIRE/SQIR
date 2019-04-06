Require Import SQIMP.
Require Import UnitarySem.
Require Import Dirac.

Ltac restore_dims_rec A :=
   match A with
  | ?A × ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' =>
                  match type of B' with 
                  | Matrix ?n'' ?o' => constr:(@Mmult m' n' o' A' B')
                  end
                end 
  | ?A ⊗ ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' =>
                  match type of B' with 
                  | Matrix ?o' ?p' => constr:(@kron m' n' o' p' A' B')
                  end
                end
  | ?A †      => let A' := restore_dims_rec A in 
                match type of A' with
                | Matrix ?m' ?n' => constr:(@adjoint m' n' A')
                end
  | ?A .+ ?B => let A' := restore_dims_rec A in 
               let B' := restore_dims_rec B in 
               match type of A' with 
               | Matrix ?m' ?n' =>
                 match type of B' with 
                 | Matrix ?m'' ?n'' => constr:(@Mplus m' n' A' B')
                 end
               end
  | ?c .* ?A => let A' := restore_dims_rec A in 
               match type of A' with
               | Matrix ?m' ?n' => constr:(@scale m' n' c A')
               end
  | ?A       => A
   end.

Ltac restore_dims_fast := 
  match goal with
  | |- ?A = ?B => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                idtac A; idtac A';
                idtac B; idtac B';
                replace A with A' by reflexivity; 
                replace B with B' by reflexivity
  end.

Ltac has_term t exp  := 
  match exp with
    | context[t] => idtac 
  end.

Ltac group_radicals := 
  repeat match goal with
  | _ => rewrite square_rad2
  | |- context[(?x * ?y)%C] => tryif has_term (√2) x then fail else (has_term (√2) y; 
                             rewrite (Cmult_comm x y))
  | |- context[(?x * ?y * ?z)%C] => tryif has_term (√2) y then fail else (has_term (√2) x; has_term (√2) z; 
                                  rewrite <- (Cmult_assoc x y z))
  | |- context[(?x * (?y * ?z))%C] => has_term (√2) x; has_term (√2) y; 
                                    rewrite (Cmult_assoc x y z)
  end.  

Ltac cancel_terms t := 
  repeat rewrite Cmult_plus_distr_l;
  repeat rewrite Cmult_plus_distr_r; 
  repeat match goal with
  | _ => rewrite Cmult_1_l
  | _ => rewrite Cmult_1_r
  | _ => rewrite Cinv_r; try nonzero  
  | _ => rewrite Cinv_l; try nonzero
  | |- context[(?x * ?y)%C]        => tryif has_term (/ t)%C y then fail else has_term (/ t)%C x; has_term t y; 
                                    rewrite (Cmult_comm x y)
  | |- context[(?x * (?y * ?z))%C] => has_term t x; has_term (/ t)%C y; 
                                    rewrite (Cmult_assoc x y z)
  | |- context[(?x * (?y * ?z))%C] => tryif has_term t y then fail else has_term t x; has_term (/ t)%C z; 
                                    rewrite (Cmult_comm y z)
  | |- context[(?x * ?y * ?z)%C] => tryif has_term t x then fail else has_term t y; has_term (/ t)%C z; 
                                  rewrite <- (Cmult_assoc x y z)
  end.  

Module UTeleport.

Definition bell (c b : nat) : ucom := H c ; CNOT c b.
Definition alice (a c : nat) : ucom := CNOT a c ; H a.
Definition bob (a c b: nat) : ucom := CNOT c b; CZ a b.
Definition teleport (a c b : nat) : ucom := alice a c; bob a c b.

Open Scope R_scope.
Open Scope nat_scope.

Definition epr00 : Vector 4 :=
  fun x y => match x, y with
             | 0, 0 => (1/√2)%C
             | 3, 0 => (1/√2)%C
             | _, _ => 0%C
             end.

Lemma epr_correct : 
  forall (ψ : Vector 2), WF_Matrix ψ -> (uc_eval 3 (bell 1 2)) × (ψ ⊗ ∣0⟩ ⊗ ∣0⟩) = ψ ⊗ epr00. 
Proof.
  intros.
  unfold bell. simpl. unfold ueval_cnot, ueval1. simpl. unfold pad. simpl.
  solve_matrix.
Qed.

Lemma teleport_correct : forall (ψ : Vector 2), 
    WF_Matrix ψ -> uc_eval 3 (teleport 0 1 2) × (ψ ⊗ epr00) = (∣ + ⟩ ⊗ ∣ + ⟩ ⊗ ψ).
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

Section DensityTeleport.

Require Import DensitySem.

Local Open Scope com.

Definition q := 0. (* qubit for transmission *)
Definition a := 1. (* alice's qubit *)
Definition b := 2. (* bob's qubit *)

Definition bell : com := H a ; CNOT a b.
Definition alice : com := CNOT q a ; H q ; meas q ; meas a.
Definition bob : com := CNOT a b; CZ q b; reset q; reset a.
Definition teleport : com := bell; alice; bob.

Lemma teleport_correct : forall (ρ : Density 2),
  WF_Matrix ρ -> 
  c_eval 3 teleport (ρ ⊗ ∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣) = (∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣ ⊗ ρ).  
Proof.
  intros.
  simpl.
  unfold compose_super, Splus, super, pad; simpl.
  unfold ueval_cnot, ueval1, pad; simpl.
  restore_dims_fast.
  Msimpl.
  solve_matrix.
  all: repeat (try rewrite Cmult_plus_distr_l; 
               try rewrite Cmult_plus_distr_r;
               try rewrite <- Copp_mult_distr_r;
               try rewrite <- Copp_mult_distr_l).
  all: group_radicals.
  all: cancel_terms 2%R.
  all: lca.
Qed.

End DensityTeleport.

Module NDTeleport.

Require Import NDSem.

Definition q := 0. (* qubit for transmission *)
Definition a := 1. (* alice's qubit *)
Definition b := 2. (* bob's qubit *)

Definition bell : com := H a ; CNOT a b.
Definition alice : com := CNOT q a ; H q ; meas q ; meas a.
Definition bob : com := CNOT a b; CZ q b; reset q; reset a.
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

Ltac destruct_seqs := 
  repeat match goal with
  | [H : ?a / _ ⇩ _ |- _] => unfold a in H
  | [H : (_ ; _) / _ ⇩ _ |- _] => dependent destruction H
  end.

Ltac destruct_apps := 
  repeat match goal with
  | [H : app _ _ / _ ⇩ _ |- _] => dependent destruction H
  end.

(* Copied from above module *)
Ltac has_term t exp  := 
  match exp with
    | context[t] => idtac 
  end.

Ltac group_radicals := 
  repeat match goal with
  | _ => rewrite square_rad2
  | |- context[(?x * ?y)%C] => tryif has_term (√2) x then fail else (has_term (√2) y; 
                             rewrite (Cmult_comm x y))
  | |- context[(?x * ?y * ?z)%C] => tryif has_term (√2) y then fail else (has_term (√2) x; has_term (√2) z; 
                                  rewrite <- (Cmult_assoc x y z))
  | |- context[(?x * (?y * ?z))%C] => has_term (√2) x; has_term (√2) y; 
                                    rewrite (Cmult_assoc x y z)
  end.  


(* Via Matrix Multiplying *)
Lemma teleport_correct : forall (ψ : Vector (2^1)) (ψ' : Vector (2^3)),
  WF_Matrix ψ ->
  teleport / (ψ  ⊗ ∣ 0 , 0 ⟩) ⇩ ψ' -> ψ' = ∣ 0 , 0 ⟩ ⊗ ψ.   
Proof.
  intros ψ ψ' WF H.
  destruct_seqs; destruct_apps.
  evar (e : Vector (2^3)).  
  match goal with 
  | H : measure q / ?x ⇩ ?y |- _ => replace x with e in H
  end.
  2:{ unfold ueval, ueval_cnot, ueval1, pad; simpl; Msimpl.
      repeat reduce_matrices.
      unfold Cdiv.
      repeat rewrite <- Copp_mult_distr_l.
      group_radicals.
      autorewrite with C_db. 
      unfold e; reflexivity. }
  subst e.
  remember (measure q) as c.
  destruct H0_2; try discriminate. 
  1:{ 
inversion Heqc.
  
  dependent destruction H0_2.
  


  (* Can do first, but need a well-formedness lemma *)
  match goal with 
  | H : reset q / ?x ⇩ ?y |- _ => replace x with e in H
  end.
  2:{ unfold ueval, ueval_cnot, ueval1, pad; simpl; Msimpl.
      repeat reduce_matrices.
      unfold Cdiv.
      repeat rewrite <- Copp_mult_distr_l.
      group_radicals.
      autorewrite with C_db. 
      unfold e; reflexivity. }
  

  rewrite H in H0_2.
  crunch_matrix.
  reduce_matrices.
solve_matrix.                                                                                                                       all: try reflexivity.      
  2: reflexivity.

Require Import Dirac.


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
  2:{ rewrite H; try lia. 
      unfold ket, qubit0, qubit1. simpl. 
      repeat (destruct x; try lca). 
  }
  destruct x as [| [| n]]; unfold ket, qubit0, qubit1; simpl; try lca.  
  rewrite H; try lia.
  lca.
Qed. 

Notation "∣+⟩" := (1/√2 .* ∣0⟩ .+ 1/√2 .* ∣1⟩)%C.
Notation "∣-⟩" := (1/√2 .* ∣0⟩ .+ (- 1/√2) .* ∣1⟩)%C.


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

  restore_dims.
  autorewrite with ket_db.
  restore_dims.
  rewrite <- kron_assoc.
  rewrite <- kron_assoc.
  repeat rewrite kron_mixed_product.
  autorewrite with M_db.  
  repeat rewrite kron_assoc.
  autorewrite with M_db.  
  Msimpl
  
  Set Printing All.
  restore_dims.

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
  
  
  
