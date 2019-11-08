Require UnitarySem.
Require DensitySem.
Require NDSem.
Require Import QWIRE.Dirac.

(** Unitary Teleportation Circuit and Proof **)
Module UTeleport.

Import UnitarySem.

Open Scope ucom.

(* a = alice; b = bob; q = qubit to be teleported *)
Definition bell {n} (a b : nat) : base_ucom n := H a ; CNOT a b.
Definition alice {n} (q a : nat) : base_ucom n := CNOT q a ; H q.
Definition bob {n} (q a b: nat) : base_ucom n := CNOT a b; CZ q b.
Definition teleport {n} (q a b : nat) : base_ucom n := alice q a; bob q a b.

Definition epr00 : Vector 4 :=
  fun x y => match x, y with
             | 0, 0 => 1/√2
             | 3, 0 => 1/√2
             | _, _ => 0
             end.

Lemma epr_correct : 
  forall (ψ : Vector 2), WF_Matrix ψ -> (@uc_eval 3 (bell 1 2)) × (ψ ⊗ ∣0⟩ ⊗ ∣0⟩) = ψ ⊗ epr00. 
Proof.
  intros.
  unfold bell. 
  simpl; autorewrite with eval_db; simpl.
  solve_matrix.
Qed.

Lemma teleport_correct : forall (ψ : Vector 2), 
    WF_Matrix ψ -> @uc_eval 3 (teleport 0 1 2) × (ψ ⊗ epr00) = (∣ + ⟩ ⊗ ∣ + ⟩ ⊗ ψ).
Proof.
  intros.
  unfold teleport. simpl.
  autorewrite with eval_db. simpl.
  solve_matrix.
  all: repeat (try rewrite Cmult_plus_distr_l; 
               try rewrite Cmult_plus_distr_r;
               try rewrite <- Copp_mult_distr_r;
               try rewrite <- Copp_mult_distr_l).
  all: group_radicals.
  all: lca.
Qed.  

End UTeleport.

(** Non-unitary teleport, proof with density matrices **)
Module DensityTeleport.

Import DensitySem.

Local Open Scope com.

Definition q : nat := 0. (* qubit for transmission *)
Definition a : nat := 1. (* alice's qubit *)
Definition b : nat := 2. (* bob's qubit *)

Definition bell : base_com 3 := H a ; CNOT a b.
Definition alice : base_com 3 := CNOT q a ; H q; measure a; measure q.
Definition bob : base_com 3 := CNOT a b; CZ q b; reset a; reset q.
Definition teleport : base_com 3 := bell; alice; bob.

(* Short proof, but very very slow.

Lemma teleport_correct : forall (ρ : Density 2),
  WF_Matrix ρ -> 
  c_eval teleport (ρ ⊗ ∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣) = (∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣ ⊗ ρ).
Proof.
  intros.
  simpl.
  repeat rewrite compose_super_eq.
  unfold compose_super.
  autorewrite with eval_db; simpl.
  Msimpl_light.
  unfold Splus, super.
  Msimpl.
  solve_matrix. (* very slow! *)
  all: group_radicals; lca.
Qed. *)

Lemma combine_super : forall {n} (A B : Square n) ρ, 
  super A (super B ρ) = super (A × B) ρ.
Proof.
  intros.
  unfold super.
  rewrite Mmult_adjoint.
  repeat rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma super_add : forall {n} (A B C : Square n) ρ, 
  super A (super B ρ .+ super C ρ) = super (A × B) ρ .+ super (A × C) ρ.
Proof.
  intros.
  unfold super.
  repeat rewrite Mmult_adjoint.
  distribute_plus.
  repeat rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma teleport_correct : forall (ρ : Density 2),
  WF_Matrix ρ -> 
  c_eval teleport (ρ ⊗ ∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣) = (∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣ ⊗ ρ).
Proof.
  intros.
  simpl. 
  repeat rewrite compose_super_eq. 
  repeat rewrite compose_super_assoc.
  rewrite compose_super_eq. 
  unfold compose_super.
  autorewrite with eval_db; simpl.
  Msimpl_light.
  replace (I 4) with (I 2 ⊗ I 2).
  2: { rewrite id_kron. reflexivity. }
  repeat (distribute_plus;
          repeat rewrite <- kron_assoc;
          restore_dims).
  repeat rewrite kron_mixed_product.
  repeat rewrite <- (Mmult_assoc _ _ hadamard).
  Qsimpl.
  replace (hadamard × σx × hadamard) with σz by solve_matrix.  
  unfold Splus. 
  repeat rewrite combine_super.
  restore_dims.
  distribute_plus.
  repeat rewrite kron_mixed_product.
  repeat rewrite <- (Mmult_assoc _ _ hadamard).
  Qsimpl.
  repeat (try rewrite super_add; try rewrite combine_super).
  repeat (distribute_plus;
          repeat rewrite <- kron_assoc;
          restore_dims).
  repeat rewrite kron_mixed_product.
  repeat rewrite <- (Mmult_assoc _ _ hadamard).
  Qsimpl. 
  unfold super; Msimpl_light.
  (* Tired of manually simplifying; solve_matrix should be reasonable now. *)
  solve_matrix.
Qed.

End DensityTeleport.

(** Non-unitary teleport, proof with non-deterministic semantics **)
Module NDTeleport.

Import UnitarySem.
Import NDSem.
Import Proportional.

Local Open Scope com.

Definition q : nat := 0. (* qubit for transmission *)
Definition a : nat := 1. (* alice's qubit *)
Definition b : nat := 2. (* bob's qubit *)

Definition bell : base_com 3 := H a ; CNOT a b.
Definition alice : base_com 3 := CNOT q a ; H q; measure a; measure q.
Definition bob : base_com 3 := CNOT a b; CZ q b; reset a; reset q.
Definition teleport : base_com 3 := bell; alice; bob.

Local Open Scope R_scope.
Local Open Scope C_scope.

Definition epr00 : Vector 4 := / √ 2 .* ∣ 0, 0 ⟩ .+ / √ 2 .* ∣ 1, 1 ⟩.

Lemma ket_decomposition : forall (ψ : Vector 2), 
  WF_Matrix ψ ->
  ψ = (ψ 0%nat 0%nat) .* ∣ 0 ⟩ .+ (ψ 1%nat 0%nat) .* ∣ 1 ⟩.
Proof.
  intros.
  prep_matrix_equality.
  unfold scale, Mplus.
  destruct y as [|y']. 
  2:{ rewrite H; try lia. 
      unfold ket, qubit0, qubit1. simpl. 
      repeat (destruct x; try lca). }
  destruct x as [| [| n]]; unfold ket, qubit0, qubit1; simpl; try lca.  
  rewrite H; try lia.
  lca.
Qed. 

(* Alternative form of proportional for unscaled vectors. *)
Definition proportional {m n : nat} (A B : Matrix m n) := 
  exists s, A = s .* B. 
Infix "∝" := proportional (at level 70).

Lemma teleport_correct : forall (ψ : Vector (2^1)) (ψ' : Vector (2^3)),
  WF_Matrix ψ ->
  teleport / (ψ  ⊗ ∣ 0 , 0 ⟩) ⇩ ψ' -> ψ' ∝ ∣ 0 , 0 ⟩ ⊗ ψ.   
Proof.
  intros ψ ψ' WF S.
  dependent destruction S.
  dependent destruction S1.
  rename S1_1 into Bell.
  rename S1_2 into Alice.
  rename S2 into Bob.
  (* compute the result of the bell program *)
  assert (E00 : ψ' = ψ ⊗ epr00).
  { clear Alice Bob.
    repeat match goal with
    | H : _ / _ ⇩ _ |- _ => dependent destruction H
    end.
    autorewrite with eval_db; simpl.
    Msimpl.
    setoid_rewrite cnot_decomposition.
    restore_dims.
    rewrite kron_assoc. 
    restore_dims.
    rewrite kron_mixed_product.
    Msimpl.
    autorewrite with ket_db.
    unfold epr00. 
    autorewrite with ket_db.
    reflexivity.
  }
  subst. clear Bell.
  (* simplify the unitary part of the Alice program *)
  repeat match goal with
  | H : (_ ; _) / _ ⇩ _ |- _ => dependent destruction H
  end.
  dependent destruction Alice1_1_1.
  dependent destruction Alice1_1_2.
  dependent destruction Bob1_1_1.
  dependent destruction Bob1_1_2.
  evar (ψA : Vector (2^3)).
  assert (EA : uc_eval (H q) × (uc_eval (CNOT q a) × (ψ ⊗ epr00)) = ψA).
  { clear Alice1_2 Alice2 Bob1_2 Bob2. 
    autorewrite with eval_db; simpl. 
    Msimpl.
    unfold epr00.
    replace 4%nat with (2 * 2)%nat by reflexivity.
    rewrite <- id_kron.
    repeat rewrite <- kron_assoc.
    restore_dims.
    rewrite cnot_decomposition.
    autorewrite with Q_db ket_db. 
    repeat rewrite <- kron_assoc.
    restore_dims.
    repeat rewrite kron_mixed_product.
    Msimpl.
    rewrite (ket_decomposition ψ) by auto. 
    autorewrite with Q_db ket_db. 
    Qsimpl.
    autorewrite with Q_db ket_db. 
    rewrite <- Copp_mult_distr_r.
    group_radicals.
    subst ψA. 
    reflexivity.
  }    
  subst ψA. rewrite EA in Alice1_2. clear EA.
  (* now destruct measurements to get four cases: a ∈ {0,1}, q ∈ {0,1} *)
  dependent destruction Alice1_2.
  - (* measured a = 1 *)
    evar (ψ'pad : Vector (2^3)).
    assert(Epad : ψ' = ψ'pad).
    { subst ψ'.
      unfold pad; simpl.
      repeat rewrite Mmult_plus_distr_l.
      repeat rewrite Mscale_mult_dist_r. 
      restore_dims.
      repeat rewrite kron_mixed_product.
      replace (∣1⟩⟨1∣ × ∣ 1 ⟩) with (∣ 1 ⟩) by solve_matrix.
      replace (∣1⟩⟨1∣ × ∣ 0 ⟩) with (@Zero 2 1) by solve_matrix.
      Msimpl_light.
      subst ψ'pad.
      reflexivity.
    }
    subst ψ'pad. rewrite Epad in Alice1_2. clear H Epad ψ'.
    dependent destruction Alice1_2.
    dependent destruction Alice2.
    + (* measured q = 1 *)
      evar (ψ'pad : Vector (2^3)).
      assert(Epad : ψ' = ψ'pad).
      { subst ψ'.
        unfold pad; simpl.
        replace 4%nat with (2 * 2)%nat by reflexivity.
        rewrite <- id_kron.
        repeat rewrite <- kron_assoc.
        Msimpl_light.
        restore_dims.
        repeat rewrite Mmult_plus_distr_l.
        repeat rewrite Mscale_mult_dist_r. 
        restore_dims.
        repeat rewrite kron_mixed_product.
        replace (∣1⟩⟨1∣ × ∣ 1 ⟩) with (∣ 1 ⟩) by solve_matrix.
        replace (∣1⟩⟨1∣ × ∣ 0 ⟩) with (@Zero 2 1) by solve_matrix.
        Msimpl_light.
        subst ψ'pad.
        reflexivity.
      }
      subst ψ'pad. rewrite Epad in Alice2. clear H Epad ψ'.
      evar (ψBob : Vector (2^3)).
      assert(EBob : uc_eval (CZ 0 b) × (uc_eval (CNOT 1 b) × ψ'') = ψBob).
      { simpl; autorewrite with eval_db; simpl.
        replace 4%nat with (2 * 2)%nat by reflexivity.
        rewrite <- id_kron.
        Msimpl_light.
        restore_dims.
        distribute_plus.
        repeat rewrite <- kron_assoc.
        restore_dims.
        repeat rewrite kron_mixed_product; Msimpl_light.
        distribute_plus. 
        repeat rewrite <- Mmult_assoc.
        repeat rewrite kron_mixed_product; Qsimpl.
        replace (hadamard × σx × hadamard) with σz by solve_matrix.
        subst ψBob.
        reflexivity.
      }
      subst ψBob. rewrite EBob in Bob1_2. clear EBob.
      repeat match goal with
      | H : _ / _ ⇩ _ |- _ => dependent destruction H
      end.
      all: simpl; autorewrite with eval_db; simpl.
      all: replace 4%nat with (2 * 2)%nat by reflexivity;
           rewrite <- id_kron;
           repeat rewrite <- kron_assoc;
           Msimpl_light;
           restore_dims.
      all: repeat rewrite <- Mmult_assoc;
           repeat rewrite kron_mixed_product;
           Qsimpl.
      all: distribute_plus; distribute_scale.
      all: repeat rewrite kron_mixed_product.
      all: Qsimpl.
      all: replace (∣1⟩⟨1∣ × ∣ 1 ⟩) with (∣ 1 ⟩) by solve_matrix;
           replace (∣0⟩⟨0∣ × ∣ 1 ⟩) with (@Zero 2 1) by solve_matrix;
           Qsimpl.
      (* last 3 cases are Zero because values measured by Bob are pre-determined *)
      2,3,4: exists 0; solve_matrix. (* or show that the norm ≠ 0 condition is violated *)
      replace (∣0⟩⟨1∣ × ∣ 1 ⟩) with (∣ 0 ⟩) by solve_matrix.
      rewrite (ket_decomposition ψ WF).
      exists (/ 2).
      solve_matrix.
    + (* measured q = 0 *)
      evar (ψ'pad : Vector (2^3)).
      assert(Epad : ψ' = ψ'pad).
      { subst ψ'.
        unfold pad; simpl.
        replace 4%nat with (2 * 2)%nat by reflexivity.
        rewrite <- id_kron.
        repeat rewrite <- kron_assoc.
        Msimpl_light.
        restore_dims.
        repeat rewrite Mmult_plus_distr_l.
        repeat rewrite Mscale_mult_dist_r. 
        restore_dims.
        repeat rewrite kron_mixed_product.
        replace (∣0⟩⟨0∣ × ∣ 0 ⟩) with (∣ 0 ⟩) by solve_matrix.
        replace (∣0⟩⟨0∣ × ∣ 1 ⟩) with (@Zero 2 1) by solve_matrix.
        Msimpl_light.
        subst ψ'pad.
        reflexivity.
      }
      subst ψ'pad. rewrite Epad in Alice2. clear H Epad ψ'.
      evar (ψBob : Vector (2^3)).
      assert(EBob : uc_eval (CZ 0 b) × (uc_eval (CNOT 1 b) × ψ'') = ψBob).
      { simpl; autorewrite with eval_db; simpl.
        replace 4%nat with (2 * 2)%nat by reflexivity.
        rewrite <- id_kron.
        Msimpl_light.
        restore_dims.
        distribute_plus.
        repeat rewrite <- kron_assoc.
        restore_dims.
        repeat rewrite kron_mixed_product; Msimpl_light.
        distribute_plus. 
        repeat rewrite <- Mmult_assoc.
        repeat rewrite kron_mixed_product; Qsimpl.
        replace (hadamard × σx × hadamard) with σz by solve_matrix.
        subst ψBob.
        reflexivity.
      }
      subst ψBob. rewrite EBob in Bob1_2. clear EBob.
      repeat match goal with
      | H : _ / _ ⇩ _ |- _ => dependent destruction H
      end.
      all: simpl; autorewrite with eval_db; simpl.
      all: replace 4%nat with (2 * 2)%nat by reflexivity;
           rewrite <- id_kron;
           repeat rewrite <- kron_assoc;
           Msimpl_light;
           restore_dims.
      all: repeat rewrite <- Mmult_assoc;
           repeat rewrite kron_mixed_product;
           Qsimpl.
      all: distribute_plus; distribute_scale.
      all: repeat rewrite kron_mixed_product.
      all: Qsimpl.
      all: replace (∣1⟩⟨1∣ × ∣ 1 ⟩) with (∣ 1 ⟩) by solve_matrix;
           replace (∣0⟩⟨0∣ × ∣ 1 ⟩) with (@Zero 2 1) by solve_matrix;
           Qsimpl.
      all: replace (∣0⟩⟨0∣ × ∣ 0 ⟩) with (∣ 0 ⟩) by solve_matrix;
           replace (∣1⟩⟨1∣ × ∣ 0 ⟩) with (@Zero 2 1) by solve_matrix;
           Qsimpl.
      all: replace (∣0⟩⟨0∣ × ∣ 0 ⟩) with (∣ 0 ⟩) by solve_matrix;
           replace (∣0⟩⟨1∣ × ∣ 0 ⟩) with (@Zero 2 1) by solve_matrix;
           Qsimpl.
      1,2,4: exists 0; solve_matrix.      
      rewrite (ket_decomposition ψ WF).
      exists (/ 2).
      solve_matrix.
  - (* measured a = 0 *)
    evar (ψ'pad : Vector (2^3)).
    assert(Epad : ψ' = ψ'pad).
    { subst ψ'.
      unfold pad; simpl.
      repeat rewrite Mmult_plus_distr_l.
      repeat rewrite Mscale_mult_dist_r. 
      restore_dims.
      repeat rewrite kron_mixed_product.
      replace (∣0⟩⟨0∣ × ∣ 0 ⟩) with (∣ 0 ⟩) by solve_matrix.
      replace (∣0⟩⟨0∣ × ∣ 1 ⟩) with (@Zero 2 1) by solve_matrix.
      Msimpl_light.
      subst ψ'pad.
      reflexivity.
    }
    subst ψ'pad. rewrite Epad in Alice1_2. clear H Epad ψ'.
    dependent destruction Alice1_2.
    dependent destruction Alice2.
    + (* measured q = 1 *)
      evar (ψ'pad : Vector (2^3)).
      assert(Epad : ψ' = ψ'pad).
      { subst ψ'.
        unfold pad; simpl.
        replace 4%nat with (2 * 2)%nat by reflexivity.
        rewrite <- id_kron.
        repeat rewrite <- kron_assoc.
        Msimpl_light.
        restore_dims.
        repeat rewrite Mmult_plus_distr_l.
        repeat rewrite Mscale_mult_dist_r. 
        restore_dims.
        repeat rewrite kron_mixed_product.
        replace (∣1⟩⟨1∣ × ∣ 1 ⟩) with (∣ 1 ⟩) by solve_matrix.
        replace (∣1⟩⟨1∣ × ∣ 0 ⟩) with (@Zero 2 1) by solve_matrix.
        Msimpl_light.
        subst ψ'pad.
        reflexivity.
      }
      subst ψ'pad. rewrite Epad in Alice2. clear H Epad ψ'.
      evar (ψBob : Vector (2^3)).
      assert(EBob : uc_eval (CZ 0 b) × (uc_eval (CNOT 1 b) × ψ'') = ψBob).
      { simpl; autorewrite with eval_db; simpl.
        replace 4%nat with (2 * 2)%nat by reflexivity.
        rewrite <- id_kron.
        Msimpl_light.
        restore_dims.
        distribute_plus.
        repeat rewrite <- kron_assoc.
        restore_dims.
        repeat rewrite kron_mixed_product; Msimpl_light.
        distribute_plus. 
        repeat rewrite <- Mmult_assoc.
        repeat rewrite kron_mixed_product; Qsimpl.
        replace (hadamard × σx × hadamard) with σz by solve_matrix.
        subst ψBob.
        reflexivity.
      }
      subst ψBob. rewrite EBob in Bob1_2. clear EBob.
      repeat match goal with
      | H : _ / _ ⇩ _ |- _ => dependent destruction H
      end.
      all: simpl; autorewrite with eval_db; simpl.
      all: replace 4%nat with (2 * 2)%nat by reflexivity;
           rewrite <- id_kron;
           repeat rewrite <- kron_assoc;
           Msimpl_light;
           restore_dims.
      all: repeat rewrite <- Mmult_assoc;
           repeat rewrite kron_mixed_product;
           Qsimpl.
      all: distribute_plus; distribute_scale.
      all: repeat rewrite kron_mixed_product.
      all: Qsimpl.
      all: replace (∣0⟩⟨0∣ × ∣ 0 ⟩) with (∣ 0 ⟩) by solve_matrix;
           replace (∣1⟩⟨1∣ × ∣ 0 ⟩) with (@Zero 2 1) by solve_matrix;
           Qsimpl.
      all: replace (∣0⟩⟨0∣ × ∣ 0 ⟩) with (∣ 0 ⟩) by solve_matrix;
           replace (∣1⟩⟨1∣ × ∣ 1 ⟩) with (∣ 1 ⟩) by solve_matrix;
           replace (∣0⟩⟨1∣ × ∣ 0 ⟩) with (@Zero 2 1) by solve_matrix;
           replace (∣0⟩⟨0∣ × ∣ 1 ⟩) with (@Zero 2 1) by solve_matrix;
           Qsimpl.
      1,3,4: exists 0; solve_matrix.
      replace (∣0⟩⟨1∣ × ∣ 1 ⟩) with (∣ 0 ⟩) by solve_matrix.
      replace (σz × ∣ 0 ⟩) with (∣ 0 ⟩) by solve_matrix.
      replace (σz × ∣ 1 ⟩) with (- 1 .* ∣ 1 ⟩) by solve_matrix.
      rewrite (ket_decomposition ψ WF).
      exists (/ 2).
      solve_matrix.      
    + (* measured q = 0 *)
      evar (ψ'pad : Vector (2^3)).
      assert(Epad : ψ' = ψ'pad).
      { subst ψ'.
        unfold pad; simpl.
        replace 4%nat with (2 * 2)%nat by reflexivity.
        rewrite <- id_kron.
        repeat rewrite <- kron_assoc.
        Msimpl_light.
        restore_dims.
        repeat rewrite Mmult_plus_distr_l.
        repeat rewrite Mscale_mult_dist_r. 
        restore_dims.
        repeat rewrite kron_mixed_product.
        replace (∣0⟩⟨0∣ × ∣ 0 ⟩) with (∣ 0 ⟩) by solve_matrix.
        replace (∣0⟩⟨0∣ × ∣ 1 ⟩) with (@Zero 2 1) by solve_matrix.
        Msimpl_light.
        subst ψ'pad.
        reflexivity.
      }
      subst ψ'pad. rewrite Epad in Alice2. clear H Epad ψ'.
      evar (ψBob : Vector (2^3)).
      assert(EBob : uc_eval (CZ 0 b) × (uc_eval (CNOT 1 b) × ψ'') = ψBob).
      { simpl; autorewrite with eval_db; simpl.
        replace 4%nat with (2 * 2)%nat by reflexivity.
        rewrite <- id_kron.
        Msimpl_light.
        restore_dims.
        distribute_plus.
        repeat rewrite <- kron_assoc.
        restore_dims.
        repeat rewrite kron_mixed_product; Msimpl_light.
        distribute_plus. 
        repeat rewrite <- Mmult_assoc.
        repeat rewrite kron_mixed_product; Qsimpl.
        replace (hadamard × σx × hadamard) with σz by solve_matrix.
        subst ψBob.
        reflexivity.
      }
      subst ψBob. rewrite EBob in Bob1_2. clear EBob.
      repeat match goal with
      | H : _ / _ ⇩ _ |- _ => dependent destruction H
      end.
      all: simpl; autorewrite with eval_db; simpl.
      all: replace 4%nat with (2 * 2)%nat by reflexivity;
           rewrite <- id_kron;
           repeat rewrite <- kron_assoc;
           Msimpl_light;
           restore_dims.
      all: repeat rewrite <- Mmult_assoc;
           repeat rewrite kron_mixed_product;
           Qsimpl.
      all: distribute_plus; distribute_scale.
      all: repeat rewrite kron_mixed_product.
      all: Qsimpl.
      all: replace (∣0⟩⟨0∣ × ∣ 0 ⟩) with (∣ 0 ⟩) by solve_matrix;
           replace (∣1⟩⟨1∣ × ∣ 0 ⟩) with (@Zero 2 1) by solve_matrix;
           Qsimpl.
      all: replace (∣0⟩⟨0∣ × ∣ 0 ⟩) with (∣ 0 ⟩) by solve_matrix;
           replace (∣0⟩⟨1∣ × ∣ 0 ⟩) with (@Zero 2 1) by solve_matrix;
           Qsimpl.
      1,2,3: exists 0; solve_matrix.      
      rewrite (ket_decomposition ψ WF).
      exists (/ 2).
      solve_matrix.
Qed.

End NDTeleport.
