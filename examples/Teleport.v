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
Definition alice : base_com 3 := CNOT q a ; H q.
Definition bob : base_com 3 := mif a then (X b; X a) else skip; 
                               mif q then (Z b; X q) else skip.
Definition teleport : base_com 3 := bell; alice; bob.

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
  solve_matrix. (* slow! *)
Qed.

End DensityTeleport.

(** Non-unitary teleport, proof with non-deterinistic semantics **)
Module NDTeleport.

Import UnitarySem.
Import NDSem.
Import Proportional.

Local Open Scope com.

Definition q : nat := 0. (* qubit for transmission *)
Definition a : nat := 1. (* alice's qubit *)
Definition b : nat := 2. (* bob's qubit *)

Definition bell : base_com 3 := H a ; CNOT a b.
Definition alice : base_com 3 := CNOT q a ; H q.
Definition bob : base_com 3 := mif a then (X b; X a) else skip; 
                               mif q then (Z b; X q) else skip.
Definition teleport : base_com 3 := bell; alice; bob.

Local Open Scope R_scope.
Local Open Scope C_scope.

Definition epr00 : Vector 4 := / √ 2 .* ∣ 0, 0 ⟩ .+ / √ 2 .* ∣ 1, 1 ⟩.

(* Thought I had this. *)
(* Generalizable? *)
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
      repeat (destruct x; try lca). 
  }
  destruct x as [| [| n]]; unfold ket, qubit0, qubit1; simpl; try lca.  
  rewrite H; try lia.
  lca.
Qed. 

(* Alternative form of proportional for unscaled vectors. *)
Definition proportional {m n : nat} (A B : Matrix m n) := 
  exists s, A = s .* B. 
Infix "∝" := proportional (at level 70).

(* Long, mostly manual proof. Automated version below. *)
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
  assert (E00 : ψ' = ψ ⊗ epr00).
  { clear Alice Bob.
    dependent destruction Bell;
    dependent destruction Bell1;
    dependent destruction Bell2.
    simpl.
    autorewrite with eval_db; simpl.
    Msimpl.
    setoid_rewrite cnot_decomposition.
    restore_dims_fast.
    rewrite kron_assoc. 
    restore_dims_fast.
    rewrite kron_mixed_product.
    autorewrite with M_db ket_db; auto.
    unfold epr00. 
    autorewrite with ket_db.
    reflexivity.
  }
  subst. clear Bell.
  dependent destruction Alice.
  dependent destruction Alice1.  
  dependent destruction Alice2.  
  evar (ψA : Vector (2^3)).
  assert (EA : uc_eval (H q) × (uc_eval (CNOT q a) × (ψ ⊗ epr00)) = ψA).
  { clear Bob. 
    autorewrite with eval_db; simpl. 
    Msimpl.
    unfold epr00.
    replace 4%nat with (2 * 2)%nat by reflexivity.
    rewrite <- id_kron.
    repeat rewrite <- kron_assoc.
    replace (2 * 1)%nat with 2%nat by reflexivity.
    rewrite cnot_decomposition.
    restore_dims_fast.
    autorewrite with M_db ket_db. 
    repeat rewrite <- kron_assoc.
    restore_dims_fast.
    repeat rewrite kron_mixed_product.
    autorewrite with M_db ket_db. 
    rewrite (ket_decomposition ψ) by auto. 
    autorewrite with M_db ket_db. 
    try rewrite <- Copp_mult_distr_r.
    group_radicals.
    subst ψA. 
    reflexivity.
  }    
  subst ψA. rewrite EA in Bob. clear EA.
  dependent destruction Bob.
  dependent destruction Bob1.
  - (* Measured a = 1 *)
    evar (ψ'pad : Vector (2^3)).
    assert(Epad : ψ' = ψ'pad).
    { subst ψ'.
      unfold pad; simpl.
      repeat rewrite Mmult_plus_distr_l.
      repeat rewrite Mscale_mult_dist_r. 
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      replace (∣1⟩⟨1∣ × ∣ 0 ⟩) with (@Zero 2 1) by solve_matrix.
      replace (∣1⟩⟨1∣ × ∣ 1 ⟩) with (∣ 1 ⟩) by solve_matrix.
      Msimpl_light.
      subst ψ'pad; reflexivity.
    }
    subst ψ'pad. rewrite Epad in Bob1. clear H Epad ψ'.
    dependent destruction Bob1;
    dependent destruction Bob1_1;
    dependent destruction Bob1_2.
    evar (ψb : Vector (2^3)).
    assert(Eb : (uc_eval (X a)
          × (uc_eval (X b)
             × (/ 2 * ψ 1%nat 0%nat .* ∣ 0, 1, 0 ⟩
                .+ (- (/ 2 * ψ 1%nat 0%nat) .* ∣ 1, 1, 0 ⟩)
                .+ (/ 2 * ψ 0%nat 0%nat .* ∣ 0, 1, 1 ⟩
                    .+ / 2 * ψ 0%nat 0%nat .* ∣ 1, 1, 1 ⟩)))) = ψb).
    { clear Bob2.
      autorewrite with eval_db; simpl.
      replace 4%nat with (2 * 2)%nat by reflexivity.
      rewrite <- id_kron.
      rewrite kron_1_r. 
      repeat rewrite Mmult_plus_distr_l.
      repeat rewrite Mscale_mult_dist_r. 
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      autorewrite with ket_db; auto with wf_db.
      subst ψb; reflexivity.
    }
    subst ψb. rewrite Eb in Bob2. clear Eb.
    dependent destruction Bob2.
    + (* Measured q = 1 *)
      evar (ψ'pad : Vector (2^3)).
      assert(Epad : ψ' = ψ'pad).
      { subst ψ'.
        unfold pad; simpl.
        replace 4%nat with (2 * 2)%nat by reflexivity.
        rewrite <- id_kron.
        rewrite <- kron_assoc.
        rewrite kron_1_l; auto with wf_db.
        repeat rewrite Mmult_plus_distr_l.
        repeat rewrite Mscale_mult_dist_r. 
        restore_dims_fast.
        repeat rewrite kron_mixed_product.
        replace (∣1⟩⟨1∣ × ∣ 0 ⟩) with (@Zero 2 1) by solve_matrix.
        replace (∣1⟩⟨1∣ × ∣ 1 ⟩) with (∣ 1 ⟩) by solve_matrix.
        Msimpl_light.
        subst ψ'pad; reflexivity.
      }
      subst ψ'pad. rewrite Epad in Bob2. clear H Epad ψ'.
      dependent destruction Bob2;
      dependent destruction Bob2_1;
      dependent destruction Bob2_2.
      autorewrite with eval_db; simpl.
      replace 4%nat with (2 * 2)%nat by reflexivity.
      rewrite <- id_kron.
      rewrite <- kron_assoc.
      rewrite kron_1_r, kron_1_l; auto with wf_db.
      repeat rewrite Mmult_plus_distr_l.
      repeat rewrite Mscale_mult_dist_r. 
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      autorewrite with ket_db; auto with wf_db.
      replace (- (/ 2 * ψ 1%nat 0%nat) * -1) with (/ 2 * ψ 1%nat 0%nat) by lca.
      repeat rewrite <- Mscale_assoc.
      rewrite <- Mscale_plus_distr_r.
      repeat rewrite <- Mscale_kron_dist_r.
      rewrite <- kron_plus_distr_l.
      exists (/ 2).
      do 2 (apply f_equal2; try reflexivity).
      rewrite ket_decomposition by assumption.
      rewrite Mplus_comm.
      reflexivity.
    + (* Measured q = 0 *)
      dependent destruction Bob2.
      clear ψ' H.
      unfold pad; simpl.
      replace 4%nat with (2 * 2)%nat by reflexivity.
      rewrite <- id_kron.
      rewrite <- kron_assoc.
      rewrite kron_1_l; auto with wf_db.
      repeat rewrite Mmult_plus_distr_l.
      repeat rewrite Mscale_mult_dist_r. 
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      replace (∣0⟩⟨0∣ × ∣ 0 ⟩) with (∣ 0 ⟩) by solve_matrix.
      replace (∣0⟩⟨0∣ × ∣ 1 ⟩) with (@Zero 2 1) by solve_matrix.
      Msimpl_light.
      repeat rewrite <- Mscale_assoc.
      rewrite <- Mscale_plus_distr_r.
      repeat rewrite <- Mscale_kron_dist_r.
      rewrite <- kron_plus_distr_l.
      exists (/ 2).
      do 2 (apply f_equal2; try reflexivity).
      rewrite ket_decomposition by assumption.
      rewrite Mplus_comm.
      reflexivity.
  - (* Measured a = 0 *)
    evar (ψ'pad : Vector (2^3)).
    assert(Epad : ψ' = ψ'pad).
    { subst ψ'.
      unfold pad; simpl.
      repeat rewrite Mmult_plus_distr_l.
      repeat rewrite Mscale_mult_dist_r. 
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      replace (∣0⟩⟨0∣ × ∣ 0 ⟩) with (∣ 0 ⟩) by solve_matrix.
      replace (∣0⟩⟨0∣ × ∣ 1 ⟩) with (@Zero 2 1) by solve_matrix.
      Msimpl_light.
      subst ψ'pad; reflexivity.
    }
    subst ψ'pad. rewrite Epad in Bob1. clear H Epad ψ'.
    dependent destruction Bob1.
    dependent destruction Bob2.
    + (* Measured q = 1 *)
      evar (ψ'pad : Vector (2^3)).
      assert(Epad : ψ' = ψ'pad).
      { subst ψ'.
        unfold pad; simpl.
        replace 4%nat with (2 * 2)%nat by reflexivity.
        rewrite <- id_kron.
        rewrite <- kron_assoc.
        rewrite kron_1_l; auto with wf_db.
        repeat rewrite Mmult_plus_distr_l.
        repeat rewrite Mscale_mult_dist_r. 
        restore_dims_fast.
        repeat rewrite kron_mixed_product.
        replace (∣1⟩⟨1∣ × ∣ 0 ⟩) with (@Zero 2 1) by solve_matrix.
        replace (∣1⟩⟨1∣ × ∣ 1 ⟩) with (∣ 1 ⟩) by solve_matrix.
        Msimpl_light.
        subst ψ'pad; reflexivity.
      }
      subst ψ'pad. rewrite Epad in Bob2. clear H Epad ψ'.
      dependent destruction Bob2;
      dependent destruction Bob2_1;
      dependent destruction Bob2_2.
      autorewrite with eval_db; simpl.
      replace 4%nat with (2 * 2)%nat by reflexivity.
      rewrite <- id_kron.
      rewrite <- kron_assoc.
      rewrite kron_1_r, kron_1_l; auto with wf_db.
      repeat rewrite Mmult_plus_distr_l.
      repeat rewrite Mscale_mult_dist_r. 
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      autorewrite with ket_db; auto with wf_db.
      replace (- (/ 2 * ψ 1%nat 0%nat) * -1) with (/ 2 * ψ 1%nat 0%nat) by lca.
      repeat rewrite <- Mscale_assoc.
      rewrite <- Mscale_plus_distr_r.
      repeat rewrite <- Mscale_kron_dist_r.
      rewrite <- kron_plus_distr_l.
      exists (/ 2).
      do 2 (apply f_equal2; try reflexivity).
      rewrite ket_decomposition by assumption.
      reflexivity.
    + (* Measured q = 0 *)
      dependent destruction Bob2.
      clear ψ' H.
      unfold pad; simpl.
      replace 4%nat with (2 * 2)%nat by reflexivity.
      rewrite <- id_kron.
      rewrite <- kron_assoc.
      rewrite kron_1_l; auto with wf_db.
      repeat rewrite Mmult_plus_distr_l.
      repeat rewrite Mscale_mult_dist_r. 
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      replace (∣0⟩⟨0∣ × ∣ 0 ⟩) with (∣ 0 ⟩) by solve_matrix.
      replace (∣0⟩⟨0∣ × ∣ 1 ⟩) with (@Zero 2 1) by solve_matrix.
      Msimpl_light.
      repeat rewrite <- Mscale_assoc.
      rewrite <- Mscale_plus_distr_r.
      repeat rewrite <- Mscale_kron_dist_r.
      rewrite <- kron_plus_distr_l.
      exists (/ 2).
      do 2 (apply f_equal2; try reflexivity).
      rewrite ket_decomposition by assumption.
      reflexivity.
Qed.

(* More automated version *)
Lemma teleport_correct' : forall (ψ : Vector (2^1)) (ψ' : Vector (2^3)),
  WF_Matrix ψ ->
  teleport / (ψ  ⊗ ∣ 0 , 0 ⟩) ⇩ ψ' -> ψ' ∝ ∣ 0 , 0 ⟩ ⊗ ψ.   
Proof.
  intros ψ ψ' WF H.
  repeat match goal with
  | H : _ / _ ⇩ _ |- _ => dependent destruction H
  end.
  all: rewrite (ket_decomposition ψ);
       autorewrite with eval_db; simpl;
       auto with wf_db;
       replace 4%nat with (2 * 2)%nat by reflexivity;
       try rewrite <- id_kron;
       Msimpl_light;
       replace (2 * 1)%nat with 2%nat by reflexivity;
       rewrite cnot_decomposition.
  all: repeat rewrite kron_assoc;
       restore_dims_fast;
       autorewrite with ket_db;
       repeat rewrite kron_mixed_product;
       autorewrite with ket_db.
  all: auto with wf_db.
  all: repeat rewrite <- kron_assoc.
  all: restore_dims_fast;
       repeat rewrite kron_mixed_product;
       autorewrite with ket_db;
       auto 10 with wf_db.
  all: restore_dims_fast;
       repeat rewrite kron_mixed_product;
       autorewrite with ket_db;
       auto 10 with wf_db.
  all: replace ((∣ 0 ⟩) † × ∣ 1 ⟩) with (@Zero 1 1) by solve_matrix;
       replace ((∣ 1 ⟩) † × ∣ 0 ⟩) with (@Zero 1 1) by solve_matrix;
       replace ((∣ 0 ⟩) † × ∣ 0 ⟩) with (I 1) by solve_matrix;
       replace ((∣ 1 ⟩) † × ∣ 1 ⟩) with (I 1) by solve_matrix;
       Msimpl_light.
  all: autorewrite with ket_db.
  all: try rewrite <- Copp_mult_distr_r;
       group_radicals.
  all: replace (- (/ 2 * -1 * ψ 1%nat 0%nat)) with (/ 2 * ψ 1%nat 0%nat) by lca;
       repeat rewrite <- Mscale_assoc;
       rewrite <- Mscale_plus_distr_r;
       repeat rewrite <- Mscale_kron_dist_r;
       rewrite <- kron_plus_distr_l;
       exists (/ 2);
       reflexivity.
Qed.

End NDTeleport.
