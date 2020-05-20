Require Import Dirac.
Require Import UnitaryOps.

Local Open Scope ucom.

(****************************)
(**   Program Definition   **)
(****************************)

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

(****************************)
(**         Proofs         **)
(****************************)

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
  uc_eval (control i (Rz θ j)) × (f_to_vec n f) 
      = (Cexp (f i * f j * θ)) .* f_to_vec n f.
Proof.
  intros. 
  rewrite control_correct; auto.
  rewrite Mmult_plus_distr_r.
  rewrite Mmult_assoc.
  rewrite f_to_vec_Rz by auto.
  rewrite Mscale_mult_dist_r.
  destruct (f i) eqn:fi.
  rewrite (f_to_vec_proj_eq _ _ _ true) by auto.
  rewrite (f_to_vec_proj_neq _ _ _ false); auto.
  2: rewrite fi; easy.
  Msimpl_light.
  rewrite Rmult_1_l.
  reflexivity.
  rewrite (f_to_vec_proj_eq _ _ _ false) by auto.
  rewrite (f_to_vec_proj_neq _ _ _ true); auto.
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
  (uc_eval (controlled_rotations n)) × (f_to_vec n f) = 
    Cexp (2 * PI * (f O) * INR (funbool_to_nat (n-1) (shift f 1%nat)) / (2 ^ n)) .* 
      (f_to_vec n f).
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
    replace (f_to_vec (S (S (S n))) f) with (f_to_vec (S (S n)) f ⊗ ∣ Nat.b2n (f (S (S n))) ⟩) by reflexivity.
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
    replace (f_to_vec (S (S n)) f ⊗ ∣ Nat.b2n (f (S (S n))) ⟩) with (f_to_vec (S (S (S n))) f) by reflexivity.
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
    apply controlled_rotations_WT; lia.
Qed.

Lemma QFT_semantics : forall n f,
  (n > 0)%nat -> 
  uc_eval (QFT n) × (f_to_vec n f) =
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
    rewrite 2 f_to_vec_shift_update_oob by lia.
    assert (H: (n' > 0)%nat) by lia.
    specialize (IHn H (shift f 1)).
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
    rewrite Cinv_mult_distr; nonzero.
    apply pow_le; lra.
    replace (n' - 0)%nat with n' by lia.    
    rewrite <- Cexp_add.
    replace (shift (update f 0 true) 1) with (shift f 1).
    2: { unfold shift. apply functional_extensionality.
         intro x. rewrite update_index_neq; auto. lia. }
    replace (VectorStates.b2R (f 0%nat) * PI + 2 * PI * INR (funbool_to_nat n' (shift f 1)) * / (2 * 2 ^ n'))%R with (2 * PI * INR (funbool_to_nat (S n') f) * / (2 ^ S n'))%R.
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
    rewrite vkron_extend_l.
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
  rewrite (ket_decomposition ψ1) by auto.
  rewrite (ket_decomposition ψ2) by auto.
  autorewrite with ket_db.
  repeat rewrite (Cmult_comm (ψ1 _ _)).
  repeat rewrite Mplus_assoc.
  apply f_equal2; try reflexivity.
  repeat rewrite <- Mplus_assoc.
  apply f_equal2; try reflexivity.
  rewrite Mplus_comm. reflexivity.
Qed.

Lemma SWAP_symmetric : forall m n dim, (@SWAP dim m n) ≡ SWAP n m.
Proof.
  intros. unfold uc_equiv.
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
    + rewrite 2 (vkron_split dim' m) by lia.
      rewrite 2 (vkron_split (dim' - 1 - m) (n - m - 1)) by lia.
      replace (dim' - 1 - m - 1 - (n - m - 1))%nat with (dim' - n - 1)%nat by lia. (* slow *)
      restore_dims. repeat rewrite <- kron_assoc. restore_dims.
      repeat rewrite shift_simplify.
      rewrite SWAP_action_on_product_state; auto with wf_db.
      repeat rewrite shift_plus.
      replace (n - m - 1 + (m + 1))%nat with n by lia.
      replace (n - m - 1 + 1 + (m + 1))%nat with (n + 1)%nat by lia.
      rewrite (vkron_eq _ f f').
      replace (f n) with (f' m).
      rewrite (vkron_eq _ (shift f (m + 1)) (shift f' (m + 1))).
      replace (f m) with (f' n).
      rewrite (vkron_eq _ (shift f (n + 1)) (shift f' (n + 1))).
      reflexivity.
      all: intros; subst f'; unfold shift; bdestruct_all; trivial.
      all: try apply vkron_WF; intros; apply WF; lia.
    + rewrite 2 (vkron_split dim' n) by lia.
      rewrite 2 (vkron_split (dim' - 1 - n) (m - n - 1)) by lia.
      replace (dim' - 1 - n - 1 - (m - n - 1))%nat with (dim' - m - 1)%nat by lia. (* slow *)
      restore_dims. repeat rewrite <- kron_assoc. restore_dims.
      repeat rewrite shift_simplify.
      rewrite SWAP_symmetric.
      rewrite SWAP_action_on_product_state; auto with wf_db; try lia.
      repeat rewrite shift_plus.
      replace (m - n - 1 + (n + 1))%nat with m by lia.
      replace (m - n - 1 + 1 + (n + 1))%nat with (m + 1)%nat by lia.
      rewrite (vkron_eq _ f f').
      replace (f m) with (f' n).
      rewrite (vkron_eq _ (shift f (n + 1)) (shift f' (n + 1))).
      replace (f n) with (f' m).
      rewrite (vkron_eq _ (shift f (m + 1)) (shift f' (m + 1))).
      reflexivity.
      all: intros; subst f'; unfold shift; bdestruct_all; trivial.
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
    apply vkron_eq.
    intros.
    bdestruct_all; simpl.
    subst. replace (dim - 0 - 1)%nat with (dim - 1)%nat by lia. reflexivity.
    subst. replace (dim - (dim - 1) - 1)%nat with O by lia. reflexivity.
    reflexivity.
    apply WF.
  - replace (uc_eval (reverse_qubits' dim (S (S n)))) with (uc_eval (SWAP (S n) (dim - (S n) - 1)) × uc_eval (reverse_qubits' dim (S n))) by reflexivity.
    rewrite Mmult_assoc.
    rewrite IHn by lia; clear IHn.
    rewrite SWAP_action_on_vkron; try lia.
    apply vkron_eq.
    intros.
    bdestruct_all; simpl; subst; trivial.
    replace (dim - (dim - S n - 1) - 1)%nat with (S n) by lia.
    reflexivity.
    intros.
    bdestruct_all; simpl; apply WF; lia.
Qed.

Lemma reverse_qubits_action_on_vkron : forall n f,
  (n > 1)%nat -> (forall i : nat, (i < n)%nat -> WF_Matrix (f i)) ->
  uc_eval (reverse_qubits n) × (vkron n f) = vkron n (fun k => f (n - k - 1)%nat).
Proof. 
  intros n f Hn WF.
  unfold reverse_qubits.
  rewrite reverse_qubits'_action_on_vkron.
  apply vkron_eq.
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
  uc_eval (QFT_w_reverse n) × (f_to_vec n f) = 
    / √(2 ^ n) .* vsum (2^n) (fun k => Cexp (2 * PI * INR (funbool_to_nat n f * k) / (2 ^ n)) .* basis_vector (2^n) k).
Proof.
  intros n f Hn.
  unfold QFT_w_reverse; simpl.
  rewrite Mmult_assoc.
  rewrite QFT_semantics by lia.
  distribute_scale.
  rewrite reverse_qubits_action_on_vkron; auto with wf_db.
  apply f_equal2; try reflexivity.
  remember (2 * PI * INR (funbool_to_nat n f) / 2 ^ n)%R as c.
  rewrite (vkron_eq _ _ (fun k : nat => ∣0⟩ .+ Cexp (c * 2 ^ (n - k - 1)) .* ∣1⟩)).
  rewrite (vsum_eq _ _ (fun k : nat => Cexp (c * INR k) .* basis_vector (2 ^ n) k)).
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

Lemma Csum_geometric_series : forall (c : C) (n : nat),
  1 - c <> 0 -> Csum (fun i => c ^ i) n = (1 - c ^ n) / (1 - c).
Proof.
  intros c n Hc.
  induction n; simpl. lca.
  rewrite IHn. 
  field_simplify_eq; try lca. (* lca should complete proof here... *)
  apply Hc.
Qed.

Lemma Cexp_neq_1 : forall x,
  x <> 0 -> -2 * PI < x < 2 * PI -> Cexp x <> 1.
Proof.
  intros x Hnz [Hlt Hgt] contra.
  apply pair_equal_spec in contra as [H _].
  assert (cos x < 1).
  { destruct (Rlt_le_dec x 0).
    destruct (Rlt_le_dec x (- PI)).
    rewrite <- cos_2PI, <- cos_neg.
    apply cos_increasing_1; lra.
    rewrite <- cos_0, <- cos_neg.
    apply cos_decreasing_1; lra.
    destruct (Rlt_le_dec x PI).
    rewrite <- cos_0.
    apply cos_decreasing_1; lra.
    rewrite <- cos_2PI.
    apply cos_increasing_1; lra. }
  lra.  
Qed.

Lemma Csum_Cexp_nonzero : forall (z : BinInt.Z) (n : nat), 
  (IZR z <> 0) -> (- 2 ^ n < IZR z < 2 ^ n)%R ->
  Csum (fun i => Cexp (2 * PI * IZR z / 2 ^ n) ^ i) (2 ^ n) = 0.
Proof.
  intros z n Hnz [Hineq1 Hineq2].
  rewrite Csum_geometric_series.
  rewrite Cexp_pow.
  replace (2 * PI * IZR z / 2 ^ n * INR (2 ^ n))%R with (IZR (2 * z) * PI)%R.
  rewrite Cexp_2nPI. lca.
  rewrite mult_IZR, pow_INR. field_simplify_eq; try nonzero.
  assert (H : Cexp (2 * PI * IZR z / 2 ^ n) <> 1).
  apply Cexp_neq_1.
  (* is there a tactic that can prove inequalities over R? *)
  do 3 (apply Rmult_integral_contrapositive_currified; try nonzero).
  apply PI_neq0.
  split.
  assert (2 * PI * (- 2 ^ n) / 2 ^ n < 2 * PI * IZR z / 2 ^ n).
  replace (2 * PI * - 2 ^ n / 2 ^ n)%R with (- 2 ^ n * (2 * PI / 2 ^ n))%R.
  replace (2 * PI * IZR z / 2 ^ n)%R with (IZR z * (2 * PI / 2 ^ n))%R.
  apply Rmult_lt_compat_r. 
  apply Rmult_lt_0_compat.
  apply Rgt_2PI_0.
  apply Rinv_0_lt_compat. lra.
  assumption.
  1,2: field_simplify_eq; nonzero.
  replace (2 * PI * - 2 ^ n / 2 ^ n)%R with (-2 * PI)%R in H.
  2: field_simplify_eq; nonzero.
  assumption.
  replace (2 * PI * IZR z / 2 ^ n)%R with (IZR z * (2 * PI / 2 ^ n))%R.
  replace (2 * PI)%R with (2 ^ n * (2 * PI / 2 ^ n))%R at 2.    
  apply Rmult_lt_compat_r. 
  apply Rmult_lt_0_compat.
  apply Rgt_2PI_0.
  apply Rinv_0_lt_compat. lra.
  assumption.
  1,2: field_simplify_eq; nonzero. 
  apply Cminus_eq_contra.
  apply not_eq_sym.
  assumption.
Qed.  

Lemma QFT_w_reverse_semantics_inverse : forall n (f : nat -> bool),
  (n > 1)%nat ->
  uc_eval (invert (QFT_w_reverse n)) × f_to_vec n f = 
    (/ √(2 ^ n) .* vsum (2^n) (fun k => Cexp (- 2 * PI * INR (funbool_to_nat n f * k) / (2 ^ n)) .* basis_vector (2^n) k)).
Proof.
  intros n f Hn.
  rewrite <- invert_correct. 
  rewrite <- (Mmult_1_l _ _ (_ .* _)); auto with wf_db.
  assert (H : (n > 0)%nat) by lia.
  specialize (uc_eval_unitary n (QFT_w_reverse n) (QFT_w_reverse_WT n H)) as [_ WFU].
  rewrite <- WFU.
  rewrite Mmult_assoc.
  apply f_equal2; try reflexivity.
  distribute_scale. rewrite Mmult_vsum_distr_l.
  erewrite vsum_eq.
  2: { intros i Hi.
       distribute_scale.
       rewrite basis_f_to_vec_alt by auto.
       rewrite QFT_w_reverse_semantics by auto.
       rewrite Mscale_assoc.
       rewrite Mscale_vsum_distr_r.
       erewrite vsum_eq.
       2: { intros i0 Hi0.
            rewrite Mscale_assoc. 
            rewrite (Cmult_comm _ (/ _)).
            rewrite <- Cmult_assoc, <- Cexp_add.
            rewrite nat_to_funbool_inverse by auto.
            replace (-2 * PI * INR (funbool_to_nat n f * i) / 2 ^ n + 2 * PI * INR (i * i0) / 2 ^ n)%R with ((2 * PI * (INR i0 - INR (funbool_to_nat n f)) / 2 ^ n) * INR i)%R.
            reflexivity.
            repeat rewrite mult_INR; lra. }
       reflexivity. }
  rewrite vsum_swap_order.
  rewrite (vsum_eq _ _ (fun i => / √ (2 ^ n) .* (if i =? funbool_to_nat n f then (2 ^ n) .* basis_vector (2 ^ n) i else Zero))).
  2: { intros i Hi.
       rewrite Mscale_vsum_distr_l.
       rewrite <- Csum_mult_l.
       rewrite <- Mscale_assoc.
       apply f_equal2; try reflexivity.
       bdestruct (i =? funbool_to_nat n f).
       subst.
       rewrite Csum_1.
       rewrite pow_INR; simpl. replace (1 + 1)%R with 2%R by lra. 
       rewrite <- RtoC_pow. reflexivity.
       intro x.
       rewrite <- Cexp_0. apply f_equal. lra.
       replace (fun x : nat => Cexp (2 * PI * (INR i - INR (funbool_to_nat n f)) / 2 ^ n * INR x)) with (fun x => Cexp (2 * PI * (IZR (Z.of_nat i - Z.of_nat (funbool_to_nat n f))) / 2 ^ n) ^ x).
       rewrite Csum_Cexp_nonzero. Msimpl. reflexivity.
       rewrite minus_IZR. rewrite <- 2 INR_IZR_INZ. 
       apply Rminus_eq_contra. 
       apply not_INR. assumption.
       specialize (funbool_to_nat_bound n f) as Hf.
       clear - Hi Hf.
       apply inj_lt in Hi. apply inj_lt in Hf.
       replace (2 ^ n)%R with (IZR (Z.of_nat (2 ^ n))). 
       split. 
       rewrite <- opp_IZR. apply IZR_lt. lia.
       apply IZR_lt. lia. 
       rewrite <- INR_IZR_INZ, pow_INR; simpl.
       replace (1 + 1)%R with 2%R by lra. reflexivity.
       apply functional_extensionality; intro x. 
       rewrite Cexp_pow.
       rewrite minus_IZR. rewrite <- 2 INR_IZR_INZ.
       reflexivity. }
  rewrite <- Mscale_vsum_distr_r.
  rewrite Mscale_assoc.
  replace (vsum (2 ^ n) (fun i : nat => if i =? funbool_to_nat n f then (2 ^ n) .* basis_vector (2 ^ n) i else Zero)) with (2 ^ n .* basis_vector (2 ^ n) (funbool_to_nat n f)).
  rewrite basis_f_to_vec.
  rewrite Mscale_assoc.
  rewrite <- (Mscale_1_l _ _ (basis_vector _ _)) at 1.
  apply f_equal2; try reflexivity.
  field_simplify_eq; try nonzero.
  rewrite Csqrt_sqrt. rewrite RtoC_pow. reflexivity.
  rewrite pow_IZR. apply IZR_le. apply Z.pow_nonneg. lia.
  specialize (funbool_to_nat_bound n f) as ?.
  erewrite vsum_unique. 
  reflexivity.
  exists (funbool_to_nat n f).
  repeat split.
  assumption.
  rewrite Nat.eqb_refl. reflexivity.
  intros. bdestruct_all. reflexivity.
Qed.

(** Proof of QPE semantics **)

Lemma f_to_vec_controlled_U : forall n k (c : base_ucom n) (ψ : Vector (2 ^ n)) (θ : R) i j (f : nat -> bool),
  (k > 0)%nat -> (n > 0)%nat -> (j < k)%nat -> (i > 0)%nat ->
  uc_well_typed c -> WF_Matrix ψ ->
  (uc_eval c) × ψ = Cexp θ .* ψ ->
  @Mmult _ _ (1 * 1) (uc_eval (cast (niter i (control j (map_qubits (fun q : nat => (k + q)%nat) c))) (k + n))) ((f_to_vec k f) ⊗ ψ) = 
    Cexp (f j * INR i * θ) .* (f_to_vec k f) ⊗ ψ.
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
  rewrite (f_to_vec_proj_eq _ _ _ true) by auto.
  rewrite (f_to_vec_proj_neq _ _ _ false); auto.
  2: rewrite fj; easy.
  Msimpl.
  rewrite Rmult_1_l. 
  rewrite Cexp_pow.
  rewrite Rmult_comm.
  reflexivity.
  rewrite (f_to_vec_proj_eq _ _ _ false) by auto.
  rewrite (f_to_vec_proj_neq _ _ _ true); auto.
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
  @Mmult _ _ (1 * 1) (uc_eval (controlled_powers' (map_qubits (fun q => kmax + q)%nat c) k kmax)) ((f_to_vec kmax f) ⊗ ψ) =
    Cexp (2 * PI * θ * INR (funbool_to_nat k (shift f (kmax - k)))) .* ((f_to_vec kmax f) ⊗ ψ).
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
  @Mmult _ _ (1 * 1) (uc_eval (controlled_powers (map_qubits (fun q => k + q)%nat c) k)) ((f_to_vec k f) ⊗ ψ) =
  Cexp (2 * PI * θ * INR (funbool_to_nat k f)) .* ((f_to_vec k f) ⊗ ψ).
Proof.
  intros k n c ψ f θ Hn Hk WT WF Heigen.
  unfold controlled_powers.
  erewrite controlled_powers'_action_on_basis; try apply Heigen; auto.
  replace (k - k)%nat with O by lia.
  rewrite shift_0.
  reflexivity.
Qed.

Lemma kron_n_equals_vkron : forall n (A : Vector 2), n ⨂ A = vkron n (fun _ => A).
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
  rewrite (vkron_eq _ _ (fun i => ∣ 0 ⟩ .+ Cexp (0 * 2 ^ (n - i - 1)) .* ∣ 1 ⟩)).
  rewrite vkron_to_vsum by auto.  
  apply f_equal2. 
  repeat rewrite <- RtoC_inv; try nonzero.
  rewrite RtoC_pow. 
  rewrite <- Rinv_pow; try nonzero.
  rewrite sqrt_pow by lra. reflexivity.
  apply vsum_eq.
  intros i Hi.
  autorewrite with R_db C_db Cexp_db. lma.
  intros i Hi.
  autorewrite with R_db C_db Cexp_db. lma.
Qed.

(* Simplify the expression uc_eval (QPE k n c) × (k ⨂ ∣0⟩ ⊗ ψ) *)
Local Opaque QFT_w_reverse Nat.mul.
Lemma QPE_simplify : forall k n (c : base_ucom n) (ψ : Vector (2 ^ n)) θ,
  (n > 0)%nat -> (k > 1)%nat -> uc_well_typed c -> WF_Matrix ψ ->
  (uc_eval c) × ψ = Cexp (2 * PI * θ) .* ψ ->
  @Mmult _ _ (1 * 1) (uc_eval (QPE k n c)) (k ⨂ ∣0⟩ ⊗ ψ) = 
    (/ (2 ^ k) .* vsum (2 ^ k) (fun i : nat => (Csum (fun j => Cexp (2 * PI * (θ - INR i / 2 ^ k) * INR j)) (2 ^ k)) .* basis_vector (2 ^ k) i) ⊗ ψ).
Proof.
  intros k n c ψ θ Hn Hk WT WF Heig.
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
  erewrite vsum_eq.
  2: { intros i Hi.
       rewrite basis_f_to_vec_alt by auto. restore_dims.
       erewrite controlled_powers_action_on_basis; try apply Heig; auto; try lia. 
       rewrite nat_to_funbool_inverse by auto. reflexivity. }
  rewrite Mmult_vsum_distr_l.
  erewrite vsum_eq.
  2: { intros i Hi.
       rewrite Mscale_mult_dist_r.
       rewrite kron_mixed_product.
       Msimpl.
       rewrite QFT_w_reverse_semantics_inverse by auto.
       distribute_scale.
       rewrite (Cmult_comm _ (/ _)).
       rewrite <- Mscale_assoc.
       rewrite <- Mscale_kron_dist_l.
       rewrite Mscale_vsum_distr_r.       
       erewrite vsum_eq.
       2: { intros i0 Hi0.
            rewrite Mscale_assoc. 
            rewrite <- Cexp_add.
            rewrite nat_to_funbool_inverse by auto.
            replace (2 * PI * θ * INR i + -2 * PI * INR (i * i0) / 2 ^ k)%R with ((2 * PI * (θ - INR i0 / 2 ^ k)) * INR i)%R.
            reflexivity.
            repeat rewrite mult_INR; lra. }
       rewrite <- Mscale_kron_dist_l.
       reflexivity. }
  rewrite <- kron_vsum_distr_r.
  rewrite <- Mscale_vsum_distr_r. 
  distribute_scale.
  rewrite vsum_swap_order.
  erewrite vsum_eq.
  2: { intros i Hi.
       rewrite Mscale_vsum_distr_l.
       reflexivity. }
  replace (/ √ (2 ^ k) * / √ (2 ^ k)) with (/ 2 ^ k).
  reflexivity.
  rewrite <- Cinv_mult_distr; try nonzero.
  rewrite <- RtoC_mult, sqrt_def, <- RtoC_pow.
  reflexivity. 
  apply pow_le. lra. 
  apply npar_WT; try lia.
  apply uc_well_typed_invert.
  apply QFT_w_reverse_WT.
  lia.
Qed.
Local Transparent QFT_w_reverse Nat.mul.

(** Simplified QPE

  Preconditions:
   - z is the k-bit dyadic rational representation of θ
   - U × ∣ψ⟩ = Cexp (2πθ / 2^k) .* ∣ψ⟩

  Postcondition: the first k bits of the output state are z *)
Lemma QPE_semantics_simplified : forall k n (c : base_ucom n) z (ψ : Vector (2 ^ n)),
  (n > 0)%nat -> (k > 1)%nat -> uc_well_typed c -> WF_Matrix ψ ->
  let θ := (INR (funbool_to_nat k z) / 2 ^ k)%R in
  (uc_eval c) × ψ = Cexp (2 * PI * θ) .* ψ ->
  @Mmult _ _ (1 * 1) (uc_eval (QPE k n c)) (k ⨂ ∣0⟩ ⊗ ψ) = (f_to_vec k z) ⊗ ψ.
Proof.
  intros k n c z ψ Hn Hk WT WF θ Heig.
  rewrite QPE_simplify with (θ := θ) by assumption.
  rewrite (vsum_eq _ _ (fun i => if i =? funbool_to_nat k z then (2 ^ k) .* basis_vector (2 ^ k) i else Zero)).
  specialize (funbool_to_nat_bound k z) as Hz.
  rewrite vsum_unique with (v:=2 ^ k .* basis_vector (2 ^ k) (funbool_to_nat k z)). 
  distribute_scale. 
  replace (/ 2 ^ k * 2 ^ k) with C1.
  rewrite Mscale_1_l.
  rewrite basis_f_to_vec. reflexivity.
  rewrite Cinv_l; nonzero.
  exists (funbool_to_nat k z).
  repeat split.
  assumption.
  rewrite Nat.eqb_refl. reflexivity.
  intros. bdestruct_all. reflexivity.
  intros i Hi.
  bdestruct (i =? funbool_to_nat k z).
  rewrite Csum_1.
  rewrite RtoC_pow, pow_INR; simpl. reflexivity.
  intro x.
  subst i θ.
  rewrite <- Cexp_0.
  apply f_equal. lra.
  replace (fun j => Cexp (2 * PI * (θ - INR i / 2 ^ k) * INR j)) with (fun j => Cexp (2 * PI * IZR (Z.of_nat (funbool_to_nat k z) - Z.of_nat i) / 2 ^ k) ^ j).
  rewrite Csum_Cexp_nonzero.
  Msimpl. reflexivity.
  rewrite minus_IZR, <- 2 INR_IZR_INZ. 
  apply Rminus_eq_contra. 
  apply not_INR. apply not_eq_sym. assumption.
  specialize (funbool_to_nat_bound k z) as Hz.
  clear - Hi Hz.
  apply inj_lt in Hi. apply inj_lt in Hz.
  replace (2 ^ k)%R with (IZR (Z.of_nat (2 ^ k))). 
  split. 
  rewrite <- opp_IZR. apply IZR_lt. lia.
  apply IZR_lt. lia. 
  rewrite <- INR_IZR_INZ, pow_INR; simpl.
  replace (1 + 1)%R with 2%R by lra. reflexivity.
  apply functional_extensionality; intro x. 
  rewrite Cexp_pow.
  rewrite minus_IZR, <- 2 INR_IZR_INZ.
  subst θ. apply f_equal. lra.
Qed.

(** General QPE

  Preconditions:
   - z is the k-bit approximation of θ (i.e. θ = z/2^k + δ where δ < 1/2^k)
   - U × ∣ψ⟩ = Cexp (2πθ / 2^k) .* ∣ψ⟩

  Postcondition: the first k bits of the output state are z with probability
  at least 4/π^2. *)

(* Probability of outcome o given input state ψ - where should this be defined? *)
Definition probability_of_outcome {n} (ψ o : Vector n) : R := 
  (Cmod ((o† × ψ) 0%nat 0%nat)) ^ 2.

(* For now the proof relies on the following admitted lemmas, which describe
   bounds on sine. *)
Lemma upper_bound : forall x : R, Rabs (sin x) <= Rabs x.
Proof. Admitted.

Lemma lower_bound : forall x : R, Rabs x <= 1/2 -> Rabs (2 * x) <= Rabs (sin (PI * x)).
Proof. Admitted.

Local Opaque pow.
Lemma QPE_semantics_full : forall k n (c : base_ucom n) z (ψ : Vector (2 ^ n)) (δ : R),
  (n > 0)%nat -> (k > 1)%nat -> uc_well_typed c -> Pure_State_Vector ψ -> 
  (-1 / 2 ^ (k + 1) < δ < 1 / 2 ^ (k + 1))%R -> (δ <> 0)%R ->
  let θ := ((INR (funbool_to_nat k z) / 2 ^ k) + δ)%R in
  (uc_eval c) × ψ = Cexp (2 * PI * θ) .* ψ ->
  probability_of_outcome (@Mmult _ _ (1 * 1) (uc_eval (QPE k n c)) (k ⨂ ∣0⟩ ⊗ ψ)) ((f_to_vec k z) ⊗ ψ) >= 4 / (PI ^ 2).
Proof.
  intros k n c z ψ δ Hn Hk WT [WFM PS] [Hδlt Hδgt] Hδnz θ Heig.
  rewrite QPE_simplify with (θ := θ) by assumption.
  unfold probability_of_outcome.
  restore_dims. rewrite kron_adjoint.
  distribute_scale.
  rewrite kron_mixed_product.
  rewrite PS.
  Msimpl. 
  rewrite Mmult_vsum_distr_l. 
  specialize (funbool_to_nat_bound k z) as Hz.
  rewrite vsum_unique with (v:=(Csum (fun j => Cexp (2 * PI * δ) ^ j) (2 ^ k)) .* I 1).
  2: { exists (funbool_to_nat k z).
       repeat split.  
       assumption.
       distribute_scale.
       rewrite basis_f_to_vec.
       rewrite basis_vector_product_eq by assumption.
       apply f_equal2; try reflexivity.
       apply Csum_eq.
       apply functional_extensionality; intro x.
       rewrite Cexp_pow.
       apply f_equal. subst θ. lra.
       intros.
       distribute_scale.
       rewrite basis_f_to_vec.
       rewrite basis_vector_product_neq; try assumption. 
       lma.
       apply not_eq_sym. assumption. }
  unfold scale, I; simpl.
  clear - Hk Hδlt Hδgt Hδnz.
  assert (H : 1 - Cexp (2 * PI * δ) <> 0).
  apply Cminus_eq_contra.
  apply not_eq_sym.
  apply Cexp_neq_1.
  do 2 (apply Rmult_integral_contrapositive_currified; try nonzero).
  apply PI_neq0.
  split.
  replace (-2 * PI)%R with (2 * PI * -1)%R by lra.
  apply Rmult_lt_compat_l. 
  apply Rgt_2PI_0.
  assert (/ 2 ^ (k + 1) < 1)%R. 
  rewrite <- Rinv_1.
  apply Rinv_lt_contravar.
  rewrite Rmult_1_l. apply pow_lt. lra.
  apply Rlt_pow_R1; try lra; lia.
  lra.
  replace (2 * PI)%R with (2 * PI * 1)%R at 2 by lra.
  apply Rmult_lt_compat_l. 
  apply Rgt_2PI_0.
  assert (/ 2 ^ (k + 1) < 1)%R. 
  rewrite <- Rinv_1.
  apply Rinv_lt_contravar.
  rewrite Rmult_1_l. apply pow_lt. lra.
  apply Rlt_pow_R1; try lra; lia.
  lra.
  rewrite Csum_geometric_series by assumption. 
  rewrite Cmod_mult.
  rewrite RtoC_pow, <- RtoC_inv, Cmod_R; try nonzero.
  rewrite Cmult_1_r. 
  rewrite Cmod_div by assumption.
  clear H.
  rewrite Cexp_pow.
  repeat rewrite Rmult_assoc.
  rewrite 2 Cmod_Cexp.
  rewrite 2 Cmod_mult.
  repeat rewrite <- RtoC_mult. 
  repeat rewrite Cmod_R.
  rewrite (Rabs_right (/ 2 ^ k)).
  rewrite (Rabs_right 2) by lra.
  2: { rewrite Rinv_pow by lra. apply Rle_ge. apply pow_le. lra. }
  rewrite 2 Rdiv_unfold.
  apply Rle_ge.
  replace 4%R with (2 ^ 2)%R by lra.
  repeat rewrite Rinv_pow; try lra.
  2: apply PI_neq0.
  rewrite <- Rpow_mult_distr.
  apply pow_incr.
  split.
  apply Rle_mult_inv_pos; try lra. apply PI_RGT_0. 
  rewrite (Rmult_comm 2 (Rabs _)).
  autorewrite with R_db in *.
  assert (Hsin_nz: Rabs (sin (PI * δ)) <> 0).
  { apply Rabs_no_R0.
    intro contra. 
    apply sin_eq_0_0 in contra.
    destruct contra as [x contra].
    rewrite (Rmult_comm _ PI) in contra.
    apply Rmult_eq_reg_l in contra.
    subst.
    assert (H1: IZR x < 1). 
    eapply Rlt_trans. apply Hδgt.
    rewrite <- Rinv_1. apply Rinv_1_lt_contravar.
    apply Rle_refl. apply Rlt_pow_R1; try lia; lra.
    assert (H2: IZR x > -1). 
    eapply Rlt_trans. 2: apply Hδlt.
    replace (-1) with (Ropp 1) by reflexivity.
    rewrite <- Ropp_mult_distr_l.
    apply Ropp_lt_contravar. rewrite Rmult_1_l.
    rewrite <- Rinv_1. apply Rinv_1_lt_contravar.
    apply Rle_refl. apply Rlt_pow_R1; try lia; lra.
    apply lt_IZR in H1.
    apply lt_IZR in H2.
    contradict Hδnz.
    apply IZR_eq. lia.
    apply PI_neq0. }
  rewrite Rinv_mult_distr; try lra.
  rewrite Rmult_assoc.
  rewrite <- (Rmult_assoc 2).
  rewrite Rinv_r_simpl_r by lra.
  rewrite <- Rmult_assoc.
  remember (Rabs (sin (PI * (δ * INR (2 ^ k))))) as num.
  remember (Rabs (sin (PI * δ))) as denom.
  assert (Hnum: Rabs (2 * (δ * INR (2 ^ k))) <= num). 
  { subst. apply lower_bound. 
    apply Rabs_le. split.
    replace (- (1 / 2))%R with (-1 * / 2 ^ (k + 1) * INR (2 ^ k))%R.
    apply Rmult_le_compat_r. apply pos_INR.
    apply Rlt_le. apply Hδlt.
    rewrite pow_INR.
    simpl INR. replace (1 + 1)%R with 2%R by lra.
    field_simplify_eq; try nonzero.
    rewrite pow_add. lra.
    replace (1 / 2)%R with (/ 2 ^ (k + 1) * INR (2 ^ k))%R.
    apply Rmult_le_compat_r. apply pos_INR.
    apply Rlt_le. apply Hδgt.
    rewrite pow_INR.
    simpl INR. replace (1 + 1)%R with 2%R by lra.
    field_simplify_eq; try nonzero.
    rewrite pow_add. lra. }
  assert (Hdenom : denom <= Rabs (PI * δ)). 
  { subst. apply upper_bound. }
  replace (2 * / PI)%R with ((/ 2) ^ k * Rabs (2 * (δ * INR (2 ^ k))) * / Rabs (PI * δ))%R.
  repeat rewrite Rmult_assoc.
  apply Rmult_le_compat_l. 
  apply pow_le. lra.
  apply Rmult_le_compat.
  apply Rabs_pos.
  rewrite <- Rmult_1_l. 
  apply Rle_mult_inv_pos. lra. 
  apply Rabs_pos_lt.
  apply Rmult_integral_contrapositive_currified. 
  apply PI_neq0. assumption.
  apply Hnum.
  apply Rinv_le_contravar.
  assert (0 <= denom). subst. apply Rabs_pos. 
  lra.
  apply Hdenom.
  rewrite pow_INR.
  simpl INR. replace (1 + 1)%R with 2%R by lra.
  repeat rewrite Rabs_mult.
  rewrite <- RPow_abs.
  rewrite (Rabs_right 2) by lra.
  rewrite (Rabs_right PI).
  field_simplify_eq.
  rewrite Rmult_assoc. rewrite <- Rpow_mult_distr.
  rewrite Rinv_l; try lra. rewrite pow1. lra. 
  split. apply PI_neq0. 
  apply Rabs_no_R0. assumption.
  apply Rgt_ge. apply PI_RGT_0.
Qed.