Require Import UnitaryOps.

Local Open Scope ucom.

(** Quantum Phase Estimation (QPE) program definition **)

(* Controlled rotation cascade on n qubits. *)
Fixpoint controlled_rotations n : base_ucom n :=
  match n with
  | 0 | 1 => SKIP
  | 2     => control 1 (Rz (2 * PI / 2 ^ n) 0) (* makes 0,1 cases irrelevant *)
  | S n'  => cast (controlled_rotations n') n ;
            control n' (Rz (2 * PI / 2 ^ n) 0)
  end.

(* Quantum Fourier transform on n qubits. 
   We use the definition below (with cast and map_qubits) for proof convenience.
   For a more standard functional definition of QFT see Quipper:
   https://www.mathstat.dal.ca/~selinger/quipper/doc/src/Quipper/Libraries/QFT.html *)
Fixpoint QFT n : base_ucom n :=
  match n with
  | 0    => SKIP
  | 1    => H 0
  | S n' => H 0 ; controlled_rotations n ;
           cast (map_qubits S (QFT n')) n 
  end.

(* The QFT puts the qubits in the wrong order, so you typically want to reverse
   them at the end. *)
Fixpoint reverse_qubits' dim n : base_ucom dim :=
  match n with
  | 0    => SKIP
  | 1    => SWAP 0 (dim - 1) (* makes 0 case irrelevant *)
  | S n' => reverse_qubits' dim n' ; SWAP n' (dim - n' - 1)
  end.
Definition reverse_qubits n := reverse_qubits' n (n/2)%nat.
Definition QFT_w_reverse n := QFT n ; reverse_qubits n.

Fixpoint controlled_powers' {n} (c : base_ucom n) k kmax : base_ucom (kmax + n) :=
  match k with
  | 0    => SKIP
  | 1    => cast (control (kmax - 1) c) (kmax + n) (* makes 0 case irrelevant *)
  | S k' => controlled_powers' c k' kmax ;
           cast (niter (2 ^ k') (control (kmax - k' - 1) c)) (kmax + n)
  end.
Definition controlled_powers {n} (c : base_ucom n) k := controlled_powers' c k k.

(* k = number of digits in result
   n = number of qubits in input state *)
Definition QPE k n (c : base_ucom n) : base_ucom (k + n) :=
  cast (npar k U_H) (k + n) ;
  controlled_powers (map_qubits (fun q => k + q)%nat c) k; 
  cast (invert (QFT_w_reverse k)) (k + n).

(** Utility definitions for proof **)

(* 'shift' operation *)

Definition shift {A : Type} (f : nat -> A) k := fun i => f (i + k)%nat.

Lemma shift_0 : forall {A} (f : nat -> A),
  shift f 0 = f.
Proof.
  intros A f.
  unfold shift.
  apply functional_extensionality; intro i.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

Lemma f_to_vec_shift : forall n f k,
  f_to_vec 0 n (shift f k) = f_to_vec k n f.
Proof.
  intros n f k.
  unfold shift.
  induction n; simpl.
  reflexivity.
  rewrite IHn. 
  repeat rewrite (Nat.add_comm n k).
  reflexivity.
Qed.

Local Opaque Nat.mul.
Lemma funbool_to_nat_shift : forall n f k, (k < n)%nat ->
  funbool_to_nat n f  = (2 ^ (n - k) * funbool_to_nat k f + funbool_to_nat (n - k) (shift f k))%nat.
Proof.
  intros.
  unfold shift, funbool_to_nat.
  destruct n; try lia.
  induction n.
  destruct k; try lia.
  replace (1 - 0)%nat with (S O) by lia; simpl. reflexivity.
  remember (S n) as n'.
  replace (S n' - k)%nat with (S (n' - k))%nat by lia.
  simpl.
  replace (n' - k + k)%nat with n' by lia.
  bdestruct (n' =? k).
  subst.
  replace (S n - S n)%nat with O by lia; simpl.
  lia.
  rewrite IHn; lia.
Qed.
Local Transparent Nat.mul.

(* Indexed sum and kronecker product *)

Fixpoint vsum {d} n (f : nat -> Vector d) : Vector d :=
  match n with
  | 0 => Zero
  | S n' => vsum n' f .+  f n'
end.

Fixpoint vkron {d} n (f : nat -> Vector d) : Vector (d ^ n) :=
  match n with
  | 0    => I 1
  | S n' => vkron n' f ⊗ f n'
  end.

Lemma vsum_WF : forall d n (f : nat -> Vector d), 
  (forall i, (i < n)%nat -> WF_Matrix (f i)) -> 
  WF_Matrix (vsum n f).
Proof.
  intros. 
  induction n; simpl; auto with wf_db.
  apply WF_plus; auto.
Qed.

Lemma vkron_WF : forall d n (f : nat -> Vector d), 
  (forall i, (i < n)%nat -> WF_Matrix (f i)) -> 
  WF_Matrix (vkron n f).
Proof.
  intros. 
  induction n; simpl; auto with wf_db.
  apply WF_kron; auto. lia.
Qed.

Hint Resolve vsum_WF vkron_WF : wf_db.

Lemma vsum_rewrite : forall d n (f : nat -> Vector d),
  vsum (S n) f = (f O) .+ vsum n (shift f 1).
Proof.
  intros d n f.
  induction n.
  simpl. Msimpl. reflexivity.
  remember (S n) as n'.
  simpl.
  rewrite IHn; clear IHn.  
  subst; simpl.
  restore_dims; rewrite <- Mplus_assoc.
  unfold shift; simpl.
  replace (n + 1)%nat with (S n) by lia.
  reflexivity.
Qed.

Lemma vkron_rewrite : forall d n (f : nat -> Vector d),
  (forall i, WF_Matrix (f i)) ->
  vkron (S n) f = (f O) ⊗ vkron n (shift f 1).
Proof.
  intros d n f WF.
  induction n.
  simpl. Msimpl. reflexivity.
  remember (S n) as n'.
  simpl.
  rewrite IHn; clear IHn.  
  subst; simpl.
  restore_dims; rewrite <- kron_assoc.
  unfold shift; simpl.
  replace (n + 1)%nat with (S n) by lia.
  reflexivity.
Qed.

Lemma vkron_split : forall d n i (f : nat -> Vector d),
  (i < n)%nat ->
  vkron n f = (vkron i f) ⊗ f i ⊗ (vkron (n - 1 - i) (shift f (i + 1))).
Proof.
  intros.
  induction n; try lia.
  bdestruct (i =? n).
  subst.
  replace (S n - 1 - n)%nat with O by lia.
  simpl. Msimpl.
  reflexivity.
  assert (i < n)%nat by lia.
  specialize (IHn H1).
  replace (S n - 1 - i)%nat with (S (n - 1 - i))%nat by lia.
  simpl.
  rewrite IHn.
  unfold shift.
  replace (n - 1 - i + (i + 1))%nat with n by lia.
  restore_dims; repeat rewrite kron_assoc. 
  reflexivity.
Qed.

Lemma vsum_replace_f : forall {d} n (f f' : nat -> Vector d),
  (forall i, (i < n)%nat -> f i = f' i) -> vsum n f = vsum n f'.
Proof.
  intros d n f f' Heq.
  induction n; simpl.
  reflexivity.
  rewrite Heq by lia.
  rewrite IHn. reflexivity.
  intros. apply Heq. lia.
Qed.

Lemma vkron_replace_f : forall {d} n (f f' : nat -> Vector d),
  (forall i, (i < n)%nat -> f i = f' i) -> vkron n f = vkron n f'.
Proof.
  intros d n f f' Heq.
  induction n; simpl.
  reflexivity.
  rewrite Heq by lia.
  rewrite IHn. reflexivity.
  intros. apply Heq. lia.
Qed.

Lemma kron_vsum_distr_l : forall d1 d2 n (f : nat -> Vector d1) (ψ : Vector d2),
  ψ ⊗ vsum n f = vsum n (fun i => ψ ⊗ (f i)).
Proof.
  intros.
  induction n; simpl.
  Msimpl. reflexivity.
  rewrite kron_plus_distr_l.
  rewrite IHn. reflexivity.
Qed.

Lemma kron_vsum_distr_r : forall d1 d2 n (f : nat -> Vector d1) (ψ : Vector d2),
  vsum n f ⊗ ψ = vsum n (fun i => (f i) ⊗ ψ).
Proof.
  intros.
  induction n; simpl.
  Msimpl. reflexivity.
  rewrite kron_plus_distr_r.
  rewrite IHn. reflexivity.
Qed.

Lemma Mmult_vsum_distr_l : forall d n (f : nat -> Vector d) (U : Square d),
  U × vsum n f = vsum n (fun i => U × (f i)).
Proof.
  intros.
  induction n; simpl.
  Msimpl. reflexivity.
  rewrite Mmult_plus_distr_l.
  rewrite IHn. reflexivity.
Qed.

Local Opaque Nat.mul.
Lemma vsum_split : forall d n (f : nat -> Vector d),
  vsum (2 * n) f = vsum n f .+ vsum n (shift f n).
Proof.
  intros.
  induction n.
  simpl. Msimpl. reflexivity.
  replace (2 * S n)%nat with (S (S (2 * n)))%nat  by lia.
  simpl.
  rewrite IHn.
  unfold shift.
  replace (S (2 * n))%nat with (n + S n)%nat by lia.
  repeat rewrite Mplus_assoc. 
  apply f_equal2; try reflexivity.
  repeat rewrite <- Mplus_assoc. 
  apply f_equal2; try reflexivity.
  remember (shift f n) as f'.
  replace (f n) with (f' O).
  2: { subst. reflexivity. }
  replace (fun i : nat => f (i + S n)%nat) with (shift f' 1).
  2: { subst. unfold shift. 
       apply functional_extensionality; intro i.
       rewrite <- Nat.add_assoc. reflexivity. }  
  rewrite <- vsum_rewrite.
  subst. unfold shift. simpl.
  replace (n + n)%nat with (2 * n)%nat by lia.
  reflexivity.
Qed.
Local Transparent Nat.mul.

Lemma basis_vector_prepend_0 : forall n k,
  (n <> 0)%nat -> (k < n)%nat ->
  ∣0⟩ ⊗ basis_vector n k = basis_vector (2 * n) k.
Proof.
  intros.
  unfold basis_vector; solve_matrix. (* solve_matrix doesn't work? *)
  repeat rewrite andb_true_r.
  bdestruct (x / n =? 0).
  rewrite H1. apply Nat.div_small_iff in H1; auto.
  rewrite Nat.mod_small by auto.
  destruct (x =? k); lca.
  assert (H1' := H1).
  rewrite Nat.div_small_iff in H1'; auto.
  destruct (x / n)%nat; try lia.
  bdestructΩ (x =? k).
  destruct n0; lca.
  destruct (x / n)%nat; try lca.
  destruct n0; lca.
Qed.

Lemma basis_vector_prepend_1 : forall n k,
  (n <> 0)%nat -> (k < n)%nat ->
  ∣1⟩ ⊗ basis_vector n k = basis_vector (2 * n) (k + n).
Proof.
  intros.
  unfold basis_vector; solve_matrix.
  all: repeat rewrite andb_true_r.
  specialize (Nat.div_mod x n H) as DM.
  destruct (x / n)%nat.
  rewrite Nat.mul_0_r, Nat.add_0_l in DM.
  assert (x < n)%nat.
  rewrite DM. apply Nat.mod_upper_bound; auto.
  bdestructΩ (x =? k + n)%nat.
  lca.
  destruct n0.
  bdestruct (x mod n =? k).
  bdestructΩ (x =? k + n); lca.
  bdestructΩ (x =? k + n); lca.
  assert (x >= 2 * n)%nat.
  assert (n * S (S n0) >= 2 * n)%nat.
  clear. induction n0; lia.
  lia.
  bdestructΩ (x =? k + n); lca.
  destruct (x /  n)%nat; try lca.
  destruct n0; lca.
Qed.

Lemma vkron_to_vsum : forall n (c : R),
  (n > 0)%nat -> 
  vkron n (fun k => ∣0⟩ .+ Cexp (c * 2 ^ (n - k - 1)) .* ∣1⟩) = 
    vsum (2 ^ n) (fun k => Cexp (c * INR k) .* basis_vector (2 ^ n) k).
Proof.
  intros n c Hn.
  destruct n; try lia.
  induction n.
  simpl. Msimpl. 
  rewrite Rmult_0_r, Cexp_0, Mscale_1_l.
  replace (basis_vector 2 0) with ∣0⟩ by solve_matrix.
  replace (basis_vector 2 1) with ∣1⟩ by solve_matrix.
  reflexivity. 
  remember (S n) as n'.
  rewrite vkron_rewrite; auto with wf_db.
  replace (shift (fun k : nat => ∣0⟩ .+ Cexp (c * 2 ^ (S n' - k - 1)) .* ∣1⟩) 1) with (fun k : nat => ∣0⟩ .+ Cexp (c * 2 ^ (n' - k - 1)) .* ∣1⟩).
  2: { unfold shift. 
       apply functional_extensionality; intro k.
       replace (S n' - (k + 1) - 1)%nat with (n' - k - 1)%nat by lia.
       reflexivity. }
  rewrite IHn by lia.
  replace (S n' - 0 - 1)%nat with n' by lia.
  remember (2 ^ n')%nat as N.
  assert (HN: (N > 0)%nat).
  subst. apply pow_positive. lia.
  replace (2 ^ n')%R with (INR N).
  2: { subst. rewrite pow_INR. simpl INR. replace (1+1)%R with 2%R by lra.
       reflexivity. }
  replace (2 ^ S n')%nat with (2 * N)%nat.
  2: { subst. unify_pows_two. }
  clear - HN.
  rewrite kron_plus_distr_r.
  rewrite 2 kron_vsum_distr_l.
  rewrite vsum_split.
  rewrite (vsum_replace_f N (fun i : nat => ∣0⟩ ⊗ (Cexp (c * INR i) .* basis_vector N i)) (fun k : nat => Cexp (c * INR k) .* basis_vector (2 * N) k)).
  rewrite (vsum_replace_f N (fun i : nat => Cexp (c * INR N) .* ∣1⟩ ⊗ (Cexp (c * INR i) .* basis_vector N i)) (shift (fun k : nat => Cexp (c * INR k) .* basis_vector (2 * N) k) N)).
  reflexivity.
  intros i Hi.
  unfold shift.
  distribute_scale.
  rewrite <- Cexp_add, <- Rmult_plus_distr_l, <- plus_INR. 
  rewrite basis_vector_prepend_1; try lia.
  rewrite Nat.add_comm.
  reflexivity.
  intros i Hi.
  distribute_scale.
  rewrite basis_vector_prepend_0; try lia.
  reflexivity.
Qed.

(** Well-typedness of QFT (used in proof of QPE) **)

Local Opaque control.
Local Transparent Rz.
Lemma controlled_rotations_WT : forall n,
  (n > 1)%nat -> uc_well_typed (controlled_rotations n).
Proof.
  intros n Hn.
  destruct n; try lia.
  destruct n; try lia.
  induction n.
  simpl. 
  apply uc_well_typed_control; try lia.
  1,2: constructor; auto.
  replace (controlled_rotations (S (S (S n)))) with (cast (controlled_rotations (S (S n))) (S (S (S n))) ; control (S (S n)) (Rz (2 * PI / 2 ^ (S (S (S n)))) 0)) by reflexivity.
  constructor.
  apply typed_cast; try lia.
  apply IHn; try lia.
  apply uc_well_typed_control; try lia.
  1,2: constructor; lia.
Qed.
Local Opaque Rz.
Local Transparent control.

Lemma QFT_WT : forall n, (n > 0)%nat -> uc_well_typed (QFT n).
Proof.
  intros n Hn.
  destruct n; try lia.
  induction n.
  simpl. apply uc_well_typed_H; lia.
  replace (QFT (S (S n))) with (H 0 ; controlled_rotations (S (S n)) ; cast (map_qubits S (QFT (S n))) (S (S n))) by reflexivity.
  repeat constructor.
  apply uc_well_typed_H; lia.
  apply controlled_rotations_WT; lia.
  replace S with (fun i => 1 + i)%nat by reflexivity.
  apply uc_well_typed_map_qubits.
  simpl. apply IHn. lia.
Qed.

Lemma reverse_qubits_WT : forall n, (n > 0)%nat -> uc_well_typed (reverse_qubits n).
Proof.
  assert (H: forall n dim, (n > 0)%nat -> (2 * n <= dim)%nat -> uc_well_typed (reverse_qubits' dim n)).
  { intros n dim Hn Hdim.
    destruct n; try lia.
    induction n.
    apply uc_well_typed_SWAP; lia.
    replace (reverse_qubits' dim (S (S n))) with (reverse_qubits' dim (S n) ; SWAP (S n) (dim - (S n) - 1)) by reflexivity.
    constructor.
    apply IHn; lia.
    apply uc_well_typed_SWAP; lia. }
  intros n Hn.
  bdestruct (n =? 1); subst.
  unfold reverse_qubits; simpl.
  apply uc_well_typed_ID; lia. 
  apply H.
  apply Nat.div_str_pos. lia.
  apply Nat.mul_div_le. lia.
Qed.

Lemma QFT_w_reverse_WT : forall n, (n > 0)%nat -> uc_well_typed (QFT_w_reverse n).
Proof. intros. constructor. apply QFT_WT; auto. apply reverse_qubits_WT; auto. Qed.

(** Proof of QFT semantics **)

Definition b2R (b : bool) : R := if b then 1%R else 0%R.
Local Coercion b2R : bool >-> R.
Lemma f_to_vec_controlled_Rz : forall (n i j : nat) (θ : R) (f : nat -> bool),
  (i < n)%nat -> (j < n)%nat -> (i <> j)%nat ->
  uc_eval (control i (Rz θ j)) × (f_to_vec 0 n f) 
      = (Cexp (f i * f j * θ)) .* f_to_vec 0 n f.
Proof.
  intros. 
  rewrite control_correct; auto.
  rewrite Mmult_plus_distr_r.
  rewrite Mmult_assoc.
  rewrite f_to_vec_Rz by auto.
  rewrite Mscale_mult_dist_r.
  destruct (f i) eqn:fi.
  rewrite (f_to_vec_proj_1 _ _ _ true) by auto.
  rewrite (f_to_vec_proj_2 _ _ _ false); auto.
  2: rewrite fi; easy.
  Msimpl_light.
  rewrite Rmult_1_l.
  reflexivity.
  rewrite (f_to_vec_proj_1 _ _ _ false) by auto.
  rewrite (f_to_vec_proj_2 _ _ _ true); auto.
  2: rewrite fi; easy.
  simpl.
  autorewrite with R_db Cexp_db.
  Msimpl_light.
  reflexivity. 
  Local Transparent Rz.
  1,2: constructor; auto.
  Local Opaque Rz.
Qed.

Lemma controlled_rotations_action_on_basis : forall n f,
  (n > 1)%nat ->
  (uc_eval (controlled_rotations n)) × (f_to_vec 0 n f) = Cexp (2 * PI * (f O) * INR (funbool_to_nat (n-1) (shift f 1%nat)) / (2 ^ n)) .* (f_to_vec 0 n f).
Proof.
  intros n f Hn.
  destruct n; try lia.
  destruct n; try lia.
  induction n.
  - simpl uc_eval. 
    rewrite f_to_vec_controlled_Rz by lia.
    apply f_equal2; try reflexivity.
    unfold funbool_to_nat, shift; simpl.
    destruct (f (S O)); destruct (f O); simpl;
    autorewrite with R_db; reflexivity. 
  - (* easier way to do the following? "simpl" produces a gross expression;
       also, too much manual rewriting below *)
    replace (uc_eval (controlled_rotations (S (S (S n))))) with (uc_eval (control (S (S n)) (Rz (2 * PI / 2 ^ (S (S (S n)))) 0)) × uc_eval (cast (controlled_rotations (S (S n))) (S (S (S n))))) by reflexivity.
    replace (f_to_vec 0 (S (S (S n))) f) with (f_to_vec 0 (S (S n)) f ⊗ ∣ Nat.b2n (f (S (S n))) ⟩) by reflexivity.
    replace (S (S (S n))) with (S (S n) + 1)%nat by lia.
    rewrite <- pad_dims_r.
    simpl I.
    rewrite Mmult_assoc.
    replace (2 ^ ((S (S n)) + 1))%nat with (2 ^ (S (S n)) * (2 ^ 1))%nat by unify_pows_two.
    restore_dims. 
    rewrite kron_mixed_product.
    rewrite IHn by lia.
    Msimpl.
    rewrite Mscale_kron_dist_l.
    replace (f_to_vec 0 (S (S n)) f ⊗ ∣ Nat.b2n (f (S (S n))) ⟩) with (f_to_vec 0 (S (S (S n))) f) by reflexivity.
    replace (2 ^ ((S (S n)) + 1))%nat with (2 ^ (S (S n)) * (2 ^ 1))%nat by unify_pows_two.
    rewrite Mscale_mult_dist_r.
    replace (1 * 1)%nat with 1%nat by reflexivity.
    replace (2 ^ (S (S n)) * (2 ^ 1))%nat with (2 ^ ((S (S n)) + 1))%nat by unify_pows_two.
    replace (2 ^ (S (S n)) * 2)%nat with (2 ^ ((S (S n)) + 1))%nat by unify_pows_two.
    replace (S (S (S n))) with (S (S n) + 1)%nat by lia.
    rewrite f_to_vec_controlled_Rz by lia.
    rewrite Mscale_assoc.
    apply f_equal2; try reflexivity.
    rewrite <- Cexp_add.
    replace (f (S (S n)) * f 0%nat * (2 * PI / 2 ^ (S (S n) + 1)))%R with (2 * PI * f 0%nat * f (S (S n)) * / 2 ^ (S (S n) + 1))%R by lra.
    autorewrite with R_db.
    repeat rewrite Rmult_assoc.
    repeat rewrite <- Rmult_plus_distr_l.
    repeat rewrite <- Rmult_assoc.
    simpl.
    replace (INR (funbool_to_nat (S n) (shift f 1)) * / (2 * (2 * 2 ^ n)) + f (S (S n)) * / (2 * (2 * 2 ^ (n + 1))))%R with (INR (funbool_to_nat (S (n + 1)) (shift f 1)) * / (2 * (2 * 2 ^ (n + 1))))%R.
    repeat rewrite Rmult_assoc.
    reflexivity. 
    replace (n + 1)%nat with (S n) by lia.
    unfold funbool_to_nat. 
    simpl binlist_to_nat.
    repeat rewrite plus_INR.
    unfold shift; simpl.
    field_simplify_eq; try nonzero. 
    replace (S (n + 1)) with (S (S n)) by lia.
    destruct (f (S (S n))); simpl; lra.
    destruct (f (S (S n))); auto with wf_db.
    apply controlled_rotations_WT; lia.
Qed.

Lemma QFT_semantics : forall n f,
  (n > 0)%nat -> 
  uc_eval (QFT n) × (f_to_vec 0 n f) =
    / √(2 ^ n) .* vkron n (fun i => ∣0⟩ .+ Cexp (2 * PI * INR (funbool_to_nat (n - i) (shift f i)) / 2 ^ (n - i)) .* ∣1⟩).
Proof.
  intros n f Hn.
  generalize dependent f.
  destruct n; try lia.
  induction n; intro f.
  - simpl QFT.
    rewrite f_to_vec_H by lia.
    simpl; Msimpl.
    unfold funbool_to_nat, shift; simpl. 
    destruct (f O); simpl; autorewrite with R_db; try reflexivity.
    replace (2 * PI * / 2)%R with PI by lra.
    reflexivity.
  - replace (QFT (S (S n))) with (H 0 ; controlled_rotations (S (S n)) ; cast (map_qubits S (QFT (S n))) (S (S n))) by reflexivity. 
    Local Opaque QFT controlled_rotations Nat.pow funbool_to_nat.
    simpl uc_eval.
    repeat rewrite Mmult_assoc. 
    rewrite f_to_vec_H by lia. 
    distribute_scale. distribute_plus. distribute_scale.
    rewrite 2 controlled_rotations_action_on_basis by lia.
    rewrite 2 update_index_eq. 
    rewrite 2 Mscale_mult_dist_r.
    specialize (pad_dims_l (QFT (S n)) (S O)) as H.
    simpl in H. 
    replace (fun q : nat => S q) with S in H by reflexivity.
    rewrite <- H; clear H. 
    rewrite 2 (f_to_vec_split 0 (S (S n)) 0) by lia.
    remember (S n) as n'.
    simpl f_to_vec.
    replace (0 + 0)%nat with O by reflexivity.
    rewrite 2 update_index_eq.
    Msimpl_light.
    replace (n' - 0 - 0)%nat with n' by lia.
    repeat rewrite kron_mixed_product.
    Msimpl_light.
    rewrite 2 f_to_vec_update.
    2,3: left; lia.
    assert (H: (n' > 0)%nat) by lia.
    specialize (IHn H (shift f 1)).
    rewrite f_to_vec_shift in IHn.
    rewrite IHn; clear - Heqn'.
    distribute_scale.
    repeat rewrite <- Mscale_kron_dist_l.
    rewrite <- kron_plus_distr_r.
    simpl Cexp at 1 3; autorewrite with R_db C_db Cexp_db.
    rewrite Cmult_comm.
    rewrite <- Mscale_assoc.
    rewrite <- Mscale_plus_distr_r.
    rewrite <- Mscale_kron_dist_l.
    rewrite Mscale_assoc.
    rewrite Mscale_kron_dist_l.
    apply f_equal2. (* some missing automation from lca/lra here *)
    rewrite <- tech_pow_Rmult.
    rewrite sqrt_mult; try lra.
    rewrite RtoC_mult.
    rewrite Cinv_mult_distr; try nonzero. 
    intro contra. apply RtoC_inj in contra. 
    apply sqrt_neq_0_compat in contra. assumption.
    apply pow_lt. lra.
    apply pow_le. lra.
    replace (n' - 0)%nat with n' by lia.    
    rewrite <- Cexp_add.
    replace (shift (update f 0 true) 1) with (shift f 1).
    2: { unfold shift. apply functional_extensionality.
         intro x. rewrite update_index_neq; auto. lia. }
    replace (ClassicalStates.b2R (f 0%nat) * PI + 2 * PI * INR (funbool_to_nat n' (shift f 1)) * / (2 * 2 ^ n'))%R with (2 * PI * INR (funbool_to_nat (S n') f) * / (2 ^ S n'))%R.
    2: { Local Transparent funbool_to_nat.
         rewrite funbool_to_nat_shift with (k:=S O) by lia.
         unfold funbool_to_nat; simpl.
         field_simplify_eq; try nonzero. 
         replace (n' - 0)%nat with n' by lia. 
         repeat (try rewrite mult_INR; try rewrite plus_INR; try rewrite pow_INR). 
         simpl. replace (1 + 1)%R with 2%R by lra. 
         destruct (f O); simpl; lra. }
    remember (fun i => ∣0⟩ .+ Cexp (2 * PI * INR (funbool_to_nat (S n' - i) (shift f i)) / 2 ^ (S n' - i)) .* ∣1⟩) as f'.
    replace (fun i => ∣0⟩ .+ Cexp (2 * PI * INR (funbool_to_nat (n' - i) (shift (shift f 1) i)) / 2 ^ (n' - i)) .* ∣1⟩) with (shift f' 1).
    2: { rewrite Heqf'. unfold shift.
         apply functional_extensionality. intro x.
         replace (S n' - (x + 1))%nat with (n' - x)%nat by lia.
         replace (fun i => f (i + (x + 1))%nat) with (fun i => f (i + x + 1)%nat).
         reflexivity.
         apply functional_extensionality. intro x0.
         replace (x0 + x + 1)%nat with (x0 + (x + 1))%nat by lia.
         reflexivity. }
    simpl Nat.b2n.
    replace (∣ 0 ⟩ .+ Cexp (2 * PI * INR (funbool_to_nat (S n') f) * / 2 ^ S n') .* ∣ 1 ⟩) with (f' O).
    2: { subst; simpl. rewrite shift_0. reflexivity. }
    rewrite vkron_rewrite.
    reflexivity.
    intro i; subst; simpl; auto with wf_db.
Qed.
Local Transparent QFT controlled_rotations Nat.pow funbool_to_nat.

(* The property in the previous lemma can be stated without the shift operation *)
Lemma Cexp_shift : forall n i f, (i < n)%nat ->
  Cexp (2 * PI * INR (funbool_to_nat (n - i) (shift f i)) / 2 ^ (n - i)) =
    Cexp (2 * PI * INR (funbool_to_nat n f) / 2 ^ (n - i)).
Proof.
  intros n i f H.
  rewrite (funbool_to_nat_shift n f i) by auto.
  rewrite plus_INR, mult_INR, pow_INR.
  replace (INR 2) with 2%R by (simpl; lra).
  rewrite Rmult_plus_distr_l, Rdiv_plus_distr.
  rewrite Cexp_add.
  replace (2 * PI * (2 ^ (n - i) * INR (funbool_to_nat i f)) / 2 ^ (n - i))%R with (IZR (2 * Z_of_nat (funbool_to_nat i f)) * PI)%R.
  rewrite Cexp_2nPI.
  lca.
  rewrite mult_IZR, <- INR_IZR_INZ.
  field_simplify_eq; try nonzero.
Qed.

(* Should be added to a rewrite database *)
Lemma bra_ket_00 : ∣0⟩† × ∣ 0 ⟩ = I 1.
Proof. solve_matrix. Qed.
Lemma bra_ket_01 : ∣0⟩† × ∣ 1 ⟩ = Zero.
Proof. solve_matrix. Qed.
Lemma bra_ket_10 : ∣1⟩† × ∣ 0 ⟩ = Zero.
Proof. solve_matrix. Qed.
Lemma bra_ket_11 : ∣1⟩† × ∣ 1 ⟩ = I 1.
Proof. solve_matrix. Qed.

Lemma SWAP_action_on_product_state : 
  forall m n dim (A : Vector (2 ^ m)) (B : Vector (2 ^ (n - m - 1))) (C : Vector (2 ^ (dim - n - 1))) (ψ1 ψ2 : Vector 2),
  (m < n)%nat -> (n < dim)%nat ->
  WF_Matrix ψ1 -> WF_Matrix ψ2 -> WF_Matrix A -> WF_Matrix B -> WF_Matrix C ->
  @ Mmult _ _ (1 * 1 * 1 * 1 * 1) (@uc_eval dim (SWAP m n)) (A ⊗ ψ1 ⊗ B ⊗ ψ2 ⊗ C) = A ⊗ ψ2 ⊗ B ⊗ ψ1 ⊗ C.
Proof.
  intros m n dim A B C ψ1 ψ2 ? ? ? ? ? ? ?.
  autorewrite with eval_db. 
  gridify.
  replace ((m + (1 + x + 1) + d1 - (m + 1 + x) - 1))%nat with d1 by lia.
  repeat rewrite kron_mixed_product.
  Msimpl.
  rewrite (ket_decomposition ψ1) by auto.
  rewrite (ket_decomposition ψ2) by auto.
  repeat rewrite Mmult_assoc.
  repeat rewrite (Mmult_plus_distr_l _ _ _ (_†)).
  distribute_scale.
  repeat rewrite bra_ket_00, bra_ket_01, bra_ket_10, bra_ket_11.
  Msimpl.
  distribute_plus.
  distribute_scale.
  Msimpl.
  repeat rewrite (Cmult_comm (ψ1 _ _)).
  repeat rewrite Mplus_assoc.
  apply f_equal2; try reflexivity.
  repeat rewrite <- Mplus_assoc.
  apply f_equal2; try reflexivity.
  rewrite Mplus_comm. reflexivity.
  replace (m + (1 + x + 1) + d1 - (m + 1 + x) - 1)%nat with d1 by lia.
  assumption.
Qed.

Lemma SWAP_symmetric : forall m n dim, (@SWAP dim m n) ≡ SWAP n m.
Proof.
  intros.
  unfold uc_equiv.
  autorewrite with eval_db.
  gridify.
Qed.

Lemma SWAP_on_2_qubits : @uc_eval 2 (SWAP 0 1) = swap.
Proof. autorewrite with eval_db. solve_matrix. Qed.

Lemma SWAP_action_on_vkron : forall dim m n (f : nat -> Vector 2),
  (dim > 0)%nat -> (m < dim)%nat -> (n < dim)%nat -> (m <> n)%nat ->
  (forall i, (i < dim)%nat -> WF_Matrix (f i)) ->
  @Mmult _ _ (1 * 1) (uc_eval (SWAP m n)) (vkron dim f) = 
    vkron dim (fun k => if (k =? m) then f n else if (k =? n) then f m else f k).
Proof.
  intros dim m n f Hdim Hm Hn Hneq WF.
  destruct dim; try lia.
  destruct dim; try lia. 
  destruct dim.
  - destruct n; destruct m; try lia.
    destruct m; try lia. simpl. 
    rewrite SWAP_symmetric, SWAP_on_2_qubits.
    Qsimpl. reflexivity.
    destruct n; try lia. simpl. 
    rewrite SWAP_on_2_qubits.
    Qsimpl. reflexivity.
  - remember (S (S (S dim))) as dim'.
    remember (fun k : nat => if k =? m then f n else if k =? n then f m else f k) as f'.
    bdestruct (m <? n).
    + rewrite 2 (vkron_split _ dim' m); try lia.
      rewrite 2 (vkron_split _ (dim' - 1 - m) (n - m - 1)); try lia.
      replace (dim' - 1 - m - 1 - (n - m - 1))%nat with (dim' - n - 1)%nat by lia. (* slow *)
      restore_dims. repeat rewrite <- kron_assoc. restore_dims.
      rewrite SWAP_action_on_product_state; auto with wf_db.
      rewrite (vkron_replace_f _ f f').
      replace (shift f (m + 1) (n - m - 1)) with (f' m).
      rewrite (vkron_replace_f _ (shift f (m + 1)) (shift f' (m + 1))).
      replace (f m) with (shift f' (m + 1) (n - m - 1)).
      rewrite (vkron_replace_f _ (shift (shift f (m + 1)) (n - m - 1 + 1)) (shift (shift f' (m + 1)) (n - m - 1 + 1))).
      reflexivity.
      all: intros; subst f'; unfold shift.
      bdestructΩ (i + (n - m - 1 + 1) + (m + 1) =? m).
      bdestructΩ (i + (n - m - 1 + 1) + (m + 1) =? n).
      reflexivity.
      bdestructΩ (n - m - 1 + (m + 1) =? m).
      bdestructΩ (n - m - 1 + (m + 1) =? n).
      reflexivity.
      bdestructΩ (i + (m + 1) =? m).
      bdestructΩ (i + (m + 1) =? n).
      reflexivity.
      bdestructΩ (m =? m).
      replace (n - m - 1 + (m + 1))%nat with n by lia.
      reflexivity.
      bdestructΩ (i =? m). bdestructΩ (i =? n). reflexivity.
      all: try apply vkron_WF; intros; apply WF; lia.
    + rewrite 2 (vkron_split _ dim' n); try lia.
      rewrite 2 (vkron_split _ (dim' - 1 - n) (m - n - 1)); try lia.
      replace (dim' - 1 - n - 1 - (m - n - 1))%nat with (dim' - m - 1)%nat by lia. (* slow *)
      restore_dims. repeat rewrite <- kron_assoc. restore_dims.
      rewrite SWAP_symmetric.
      rewrite SWAP_action_on_product_state; auto with wf_db.
      rewrite (vkron_replace_f _ f f').
      replace (shift f (n + 1) (m - n - 1)) with (f' n).
      rewrite (vkron_replace_f _ (shift f (n + 1)) (shift f' (n + 1))).
      replace (f n) with (shift f' (n + 1) (m - n - 1)).
      rewrite (vkron_replace_f _ (shift (shift f (n + 1)) (m - n - 1 + 1)) (shift (shift f' (n + 1)) (m - n - 1 + 1))).
      reflexivity.
      all: intros; subst f'; unfold shift.
      bdestructΩ (i + (m - n - 1 + 1) + (n + 1) =? m).
      bdestructΩ (i + (m - n - 1 + 1) + (n + 1) =? n).
      reflexivity.
      bdestructΩ (m - n - 1 + (n + 1) =? m).
      bdestructΩ (m - n - 1 + (n + 1) =? n).
      reflexivity.
      bdestructΩ (i + (n + 1) =? m).
      bdestructΩ (i + (n + 1) =? n).
      reflexivity.
      bdestructΩ (n =? m). bdestructΩ (n =? n).
      replace (m - n - 1 + (n + 1))%nat with m by lia.
      reflexivity.
      bdestructΩ (i =? m). bdestructΩ (i =? n). reflexivity. lia.
      all: try apply vkron_WF; intros; apply WF; lia.
Qed.

Lemma reverse_qubits'_action_on_vkron : forall dim n (f : nat -> Vector 2),
  (n > 0)%nat -> (2 * n <= dim)%nat ->
  (forall i : nat, (i < dim)%nat -> WF_Matrix (f i)) ->
  @Mmult _ _ 1 (uc_eval (reverse_qubits' dim n)) (vkron dim f) = 
    vkron dim (fun k => if ((k <? n)%nat || (dim - n - 1 <? k)%nat) 
                     then f (dim - k - 1)%nat else f k).
Proof.
  intros dim n f Hn1 Hn2 WF.
  induction n; try lia.
  destruct n.
  - clear IHn. simpl.
    rewrite SWAP_action_on_vkron; try lia.
    apply vkron_replace_f.
    intros.
    bdestruct (i =? 0); bdestructΩ (i <? 1). 
    subst. replace (dim - 0 - 1)%nat with (dim - 1)%nat by lia. reflexivity.
    bdestruct (i =? dim - 1); bdestructΩ (dim - 1 - 1 <? i).
    subst. replace (dim - (dim - 1) - 1)%nat with O by lia. reflexivity.
    reflexivity.
    apply WF.
  - replace (uc_eval (reverse_qubits' dim (S (S n)))) with (uc_eval (SWAP (S n) (dim - (S n) - 1)) × uc_eval (reverse_qubits' dim (S n))) by reflexivity.
    rewrite Mmult_assoc.
    rewrite IHn by lia; clear IHn.
    rewrite SWAP_action_on_vkron; try lia.
    apply vkron_replace_f.
    intros.
    bdestruct (i =? S n); bdestructΩ (i <? S (S n)). 
    bdestructΩ (dim - S n - 1 <? S n); simpl.
    bdestructΩ (dim - S n - 1 <? dim - S n - 1). subst. reflexivity.
    bdestructΩ (i =? dim - S n - 1).
    bdestructΩ (i <? S n). reflexivity.
    bdestruct (i =? dim - S n - 1).
    bdestructΩ (S n <? S n). 
    bdestructΩ (dim - S n - 1 <? S n). 
    bdestructΩ (dim - S (S n) - 1 <? i). 
    subst. replace (dim - (dim - S n - 1) - 1)%nat with (S n) by lia. reflexivity.
    bdestructΩ (i <? S n).
    bdestruct (dim - S n - 1 <? i); bdestructΩ (dim - S (S n) - 1 <? i); reflexivity.
    intros i Hi.
    bdestruct (i <? S n); bdestruct (dim - S n - 1 <? i); simpl.
    all: apply WF; lia.
Qed.

Lemma reverse_qubits_action_on_vkron : forall n f,
  (n > 1)%nat -> (forall i : nat, (i < n)%nat -> WF_Matrix (f i)) ->
  uc_eval (reverse_qubits n) × (vkron n f) = vkron n (fun k => f (n - k - 1)%nat).
Proof. 
  intros n f Hn WF.
  unfold reverse_qubits.
  rewrite reverse_qubits'_action_on_vkron.
  apply vkron_replace_f.
  intros i Hi.
  bdestruct (i <? n / 2); bdestruct (n - n / 2 - 1 <? i); simpl; try reflexivity.
  destruct (Nat.even n) eqn:evn.
  apply Nat.even_spec in evn.
  destruct evn. subst.
  rewrite (Nat.mul_comm 2 x) in *.
  try rewrite Nat.div_mul in *; lia.
  apply negb_true_iff in evn.
  apply Nat.odd_spec in evn.
  destruct evn. subst.
  replace ((2 * x + 1) / 2)%nat with x in *.
  replace (2 * x + 1 - i - 1)%nat with i by lia. reflexivity.
  rewrite Nat.add_comm.
  replace (S O) with (Nat.b2n true) by reflexivity. 
  rewrite Nat.add_b2n_double_div2. reflexivity.
  apply Nat.div_str_pos. lia. 
  apply Nat.mul_div_le. lia.
  apply WF.
Qed.

(* QFT w/ reverse takes basis state ∣x⟩ to (1/√N) \sum_{k=0}^{N-1} e^{2πixk/N} ∣k⟩;
   this is a more useful form of QFT_semantics *)
Lemma QFT_w_reverse_semantics : forall n (f : nat -> bool),
  (n > 1)%nat ->
  uc_eval (QFT_w_reverse n) × (f_to_vec 0 n f) = / √(2 ^ n) .* vsum (2^n) (fun k => Cexp (2 * PI * INR (funbool_to_nat n f * k) / (2 ^ n)) .* basis_vector (2^n) k).
Proof.
  intros n f Hn.
  unfold QFT_w_reverse; simpl.
  rewrite Mmult_assoc.
  rewrite QFT_semantics by lia.
  distribute_scale.
  rewrite reverse_qubits_action_on_vkron; auto with wf_db.
  apply f_equal2; try reflexivity.
  remember (2 * PI * INR (funbool_to_nat n f) / 2 ^ n)%R as c.
  rewrite (vkron_replace_f _ (fun k : nat => ∣0⟩ .+ Cexp (2 * PI * INR (funbool_to_nat (n - (n - k - 1)) (shift f (n - k - 1))) / 2 ^ (n - (n - k - 1))) .* ∣1⟩) (fun k : nat => ∣0⟩ .+ Cexp (c * 2 ^ (n - k - 1)) .* ∣1⟩)).
  rewrite (vsum_replace_f _ (fun k : nat => Cexp (2 * PI * INR (funbool_to_nat n f * k) / 2 ^ n) .* basis_vector (2 ^ n) k) (fun k : nat => Cexp (c * INR k) .* basis_vector (2 ^ n) k)).
  apply vkron_to_vsum. lia.
  intros i Hi.
  subst. apply f_equal2; try reflexivity. apply f_equal. 
  rewrite mult_INR. lra.
  intros i Hi. 
  rewrite Cexp_shift by lia.
  subst. do 2 (apply f_equal2; try reflexivity). apply f_equal.
  field_simplify_eq; try nonzero.
  repeat rewrite Rmult_assoc.
  rewrite <- pow_add.
  replace (n - (n - i - 1) + (n - i - 1))%nat with n by lia.
  reflexivity.
Qed.

(* Simple description of QFT†; need the more general definition for general QPE *)
Lemma QFT_w_reverse_semantics_inverse : forall n (f : nat -> bool),
  (n > 1)%nat ->
  uc_eval (invert (QFT_w_reverse n)) × (/ √(2 ^ n) .* vsum (2^n) (fun k => Cexp (2 * PI * INR (funbool_to_nat n f * k) / (2 ^ n)) .* basis_vector (2^n) k)) = f_to_vec 0 n f.
Proof.
  intros n f Hn.
  rewrite <- invert_correct. 
  rewrite <- (Mmult_1_l _ _ (f_to_vec _ _ _)); auto with wf_db.
  assert (n > 0)%nat by lia.
  specialize (uc_eval_unitary n (QFT_w_reverse n) (QFT_w_reverse_WT n H)) as [_ WFU].
  rewrite <- WFU.
  rewrite Mmult_assoc.
  apply f_equal2; try reflexivity.
  symmetry. apply QFT_w_reverse_semantics.
  assumption.
Qed.

(** Proof of QPE semantics **)

Lemma f_to_vec_controlled_U : forall n k (c : base_ucom n) (ψ : Vector (2 ^ n)) (θ : R) i j (f : nat -> bool),
  (k > 0)%nat -> (n > 0)%nat -> (j < k)%nat -> (i > 0)%nat ->
  uc_well_typed c -> WF_Matrix ψ ->
  (uc_eval c) × ψ = Cexp θ .* ψ ->
  @Mmult _ _ (1 * 1) (uc_eval (cast (niter i (control j (map_qubits (fun q : nat => (k + q)%nat) c))) (k + n))) ((f_to_vec 0 k f) ⊗ ψ) = 
    Cexp (f j * INR i * θ) .* (f_to_vec 0 k f) ⊗ ψ.
Proof.
  intros n k c ψ θ i j f ? ? ? ? WT WF Heig. 
  rewrite cast_niter_commute. 
  rewrite niter_correct by lia.
  rewrite cast_control_commute.
  rewrite <- niter_correct by lia.
  rewrite niter_control_commute by lia.
  rewrite control_correct; try lia.
  rewrite Mmult_plus_distr_r.
  rewrite Mmult_assoc.
  rewrite niter_correct by lia.
  rewrite <- pad_dims_l.
  replace (2 ^ (k + n))%nat with (2 ^ k * 2 ^ n)%nat by unify_pows_two.
  rewrite Mmult_n_kron_distr_l. 
  rewrite kron_mixed_product. 
  rewrite Mmult_n_1_r.
  Msimpl.
  erewrite Mmult_n_eigenvector; auto.
  2: apply Heig.
  distribute_scale.
  replace (proj j (k + n) false) with (proj j k false ⊗ I (2 ^ n)).
  2: unfold proj; autorewrite with eval_db; gridify; trivial.
  replace (proj j (k + n) true) with (proj j k true ⊗ I (2 ^ n)).
  2: unfold proj; autorewrite with eval_db; gridify; trivial.
  restore_dims. 
  repeat rewrite kron_mixed_product.
  Msimpl.
  destruct (f j) eqn:fj.
  rewrite (f_to_vec_proj_1 _ _ _ true) by auto.
  rewrite (f_to_vec_proj_2 _ _ _ false); auto.
  2: rewrite fj; easy.
  Msimpl.
  rewrite Rmult_1_l. 
  rewrite Cexp_pow.
  rewrite Rmult_comm.
  reflexivity.
  rewrite (f_to_vec_proj_1 _ _ _ false) by auto.
  rewrite (f_to_vec_proj_2 _ _ _ true); auto.
  2: rewrite fj; easy.
  simpl. autorewrite with R_db Cexp_db.
  Msimpl.
  reflexivity. 
  apply is_fresh_niter; auto.
  apply map_qubits_fresh; auto.
  apply uc_well_typed_niter.
  apply uc_well_typed_map_qubits; auto.
Qed.

Lemma niter_1 : forall {d} (c : base_ucom d), niter 1 c = c.
Proof. reflexivity. Qed.

Lemma controlled_powers'_action_on_basis : 
  forall k kmax n (c : base_ucom n) (ψ : Vector (2^n)) f θ,
  (n > 0)%nat -> (k > 0)%nat -> (kmax >= k)%nat -> uc_well_typed c -> WF_Matrix ψ ->
  (uc_eval c) × ψ = Cexp (2 * PI * θ) .* ψ ->
  @Mmult _ _ (1 * 1) (uc_eval (controlled_powers' (map_qubits (fun q => kmax + q)%nat c) k kmax)) ((f_to_vec 0 kmax f) ⊗ ψ) =
    Cexp (2 * PI * θ * INR (funbool_to_nat k (shift f (kmax - k)))) .* ((f_to_vec 0 kmax f) ⊗ ψ).
Proof.
  intros k kmax n c ψ f θ Hn Hk Hkmax WT WF Heigen.
  destruct k; try lia.
  induction k.
  - simpl.
    rewrite <- (niter_1 (cast _ _)).
    rewrite <- cast_niter_commute.
    erewrite f_to_vec_controlled_U; try apply Heigen; auto.
    2: lia.
    rewrite Mscale_kron_dist_l.
    apply f_equal2; try reflexivity.
    unfold funbool_to_nat, shift; simpl.
    rewrite Nat.add_0_r.
    apply f_equal.
    destruct (f (kmax - 1)%nat); simpl; lra.
  - replace (controlled_powers' (map_qubits (fun q : nat => (kmax + q)%nat) c) (S (S k)) kmax) with (controlled_powers' (map_qubits (fun q : nat => (kmax + q)%nat) c) (S k) kmax ; cast (niter (2 ^ (S k)) (control (kmax - (S k) - 1) (map_qubits (fun q : nat => (kmax + q)%nat) c))) (kmax + n)) by reflexivity.
    Local Opaque controlled_powers' Nat.pow. 
    simpl uc_eval.
    rewrite Mmult_assoc. 
    rewrite IHk by lia; clear IHk.
    distribute_scale.
    erewrite f_to_vec_controlled_U; try apply Heigen; auto.
    2,3: lia.
    2: assert (2 ^ S k <> 0)%nat by (apply Nat.pow_nonzero; lia); lia.
    restore_dims. distribute_scale. 
    apply f_equal2; try reflexivity. 
    rewrite <- Cexp_add.
    apply f_equal.
    rewrite (funbool_to_nat_shift (S (S k)) _ (S O)) by lia.
    replace (S (S k) - 1)%nat with (S k) by lia.
    replace (shift (shift f (kmax - S (S k))) 1) with (shift f (kmax - S k)).
    2: { unfold shift. apply functional_extensionality; intro x. 
         replace (x + 1 + (kmax - S (S k)))%nat with (x + (kmax - S k))%nat by lia.
         reflexivity. }
    rewrite plus_INR, mult_INR. repeat rewrite pow_INR. 
    unfold shift; simpl. 
    replace (1 + 1)%R with 2%R by lra.
    replace (kmax - S (S k))%nat with (kmax - S k - 1)%nat by lia.
    unfold funbool_to_nat; simpl.
    field_simplify_eq. 
    destruct (f (kmax - S k - 1)%nat); simpl; lra.
Qed.

Lemma controlled_powers_action_on_basis : 
  forall k n (c : base_ucom n) (ψ : Vector (2^n)) f θ,
  (n > 0)%nat -> (k > 0)%nat -> uc_well_typed c -> WF_Matrix ψ ->
  (uc_eval c) × ψ = Cexp (2 * PI * θ) .* ψ ->
  @Mmult _ _ (1 * 1) (uc_eval (controlled_powers (map_qubits (fun q => k + q)%nat c) k)) ((f_to_vec 0 k f) ⊗ ψ) =
  Cexp (2 * PI * θ * INR (funbool_to_nat k f)) .* ((f_to_vec 0 k f) ⊗ ψ).
Proof.
  intros k n c ψ f θ Hn Hk WT WF Heigen.
  unfold controlled_powers.
  erewrite controlled_powers'_action_on_basis; try apply Heigen; auto.
  replace (k - k)%nat with O by lia.
  rewrite shift_0.
  reflexivity.
Qed.

Lemma kron_n_equals_vkron : forall {d} n (A : Vector d), n ⨂ A = vkron n (fun _ => A).
Proof.
  intros.
  induction n; simpl. reflexivity.
  rewrite IHn. reflexivity.
Qed.

(* n ⨂ hadamard produces a uniform superposition *)
Lemma H0_kron_n_spec_alt : forall n, (n > 0)%nat ->
  @Mmult _ _ 1 (n ⨂ hadamard) (n ⨂ ∣0⟩) = /√(2 ^ n) .* vsum (2 ^ n) (fun k => basis_vector (2 ^ n) k).
Proof. 
  intros n Hn. restore_dims.
  rewrite Dirac.H0_kron_n_spec.
  rewrite <- Mscale_plus_distr_r.
  rewrite Mscale_kron_n_distr_r.
  replace (n ⨂ (∣ 0 ⟩ .+ ∣ 1 ⟩)) with (vkron n (fun _ => ∣ 0 ⟩ .+ ∣ 1 ⟩)).
  2: symmetry; apply kron_n_equals_vkron.
  rewrite (vkron_replace_f _ (fun _ => ∣ 0 ⟩ .+ ∣ 1 ⟩) (fun i => ∣ 0 ⟩ .+ Cexp (0 * 2 ^ (n - i - 1)) .* ∣ 1 ⟩)).
  rewrite vkron_to_vsum by auto.  
  apply f_equal2. 
  repeat rewrite <- RtoC_inv; try nonzero.
  rewrite RtoC_pow. 
  rewrite <- Rinv_pow; try nonzero.
  (* blah *) admit. admit.
  apply vsum_replace_f.
  intros i Hi.
  autorewrite with R_db C_db Cexp_db. lma.
  intros i Hi.
  autorewrite with R_db C_db Cexp_db. lma.
Admitted.

(** Simplified QPE

  Preconditions:
   - z is the k-bit dyadic rational representation of θ
   - U × ∣ψ⟩ = Cexp (2πθ / 2^n) .* ∣ψ⟩

  Postcondition: the first k bits of the output state are z *)
Local Opaque QFT_w_reverse.
Lemma QPE_semantics : forall k n (c : base_ucom n) z (ψ : Vector (2 ^ n)),
  (n > 0)%nat -> (k > 1)%nat -> uc_well_typed c -> WF_Matrix ψ ->
  let θ := (INR (funbool_to_nat k z) / 2 ^ k)%R in
  (uc_eval c) × ψ = Cexp (2 * PI * θ) .* ψ ->
  @Mmult _ _ (1 * 1) (uc_eval (QPE k n c)) ((k ⨂ ∣0⟩) ⊗ ψ) = (f_to_vec 0 k z) ⊗ ψ.
Proof.
  intros k n c z ψ Hn Hk WT WF θ Heig.
  Local Opaque Nat.mul.
  unfold QPE; simpl.
  repeat rewrite Mmult_assoc.
  repeat rewrite <- pad_dims_r.
  rewrite npar_H by lia.
  replace (2 ^ (k + n))%nat with (2 ^ k * 2 ^ n)%nat by unify_pows_two. 
  rewrite Nat.pow_1_l.
  rewrite kron_mixed_product.
  Msimpl.
  rewrite H0_kron_n_spec_alt by lia.
  restore_dims. distribute_scale.
  rewrite kron_vsum_distr_r.
  replace (2 ^ (k + n))%nat with (2 ^ k * 2 ^ n)%nat by unify_pows_two. 
  rewrite Mmult_vsum_distr_l.
  rewrite (vsum_replace_f _ _ (fun i => (Cexp (2 * PI * INR (funbool_to_nat k z * i) / 2 ^ k) .* basis_vector (2 ^ k) i) ⊗ ψ)).
  2: { intros i Hi.
       rewrite basis_f_to_vec_alt by auto. restore_dims.
       erewrite controlled_powers_action_on_basis; try apply Heig; auto; try lia. 
       rewrite Mscale_kron_dist_l.
       apply f_equal2; try reflexivity.  
       subst θ. rewrite nat_to_funbool_inverse by auto. 
       rewrite mult_INR. apply f_equal. lra. }
  rewrite <- Mscale_mult_dist_r.
  rewrite <- kron_vsum_distr_r.
  rewrite <- Mscale_kron_dist_l.
  rewrite kron_mixed_product.
  Msimpl.
  rewrite QFT_w_reverse_semantics_inverse by auto.
  reflexivity.
  apply npar_WT.

(** TODO **)
(* In the general case, we will obtain the desired output state with probability
   at least 4/π^2. See the proof on Wikipedia: 
     https://en.wikipedia.org/wiki/Quantum_phase_estimation_algorithm#Measurement 

   Most everything should stay the same, but we will need changes to
   - the statement of correctess for QFT†
   - QPE_semantics lemma
*)
