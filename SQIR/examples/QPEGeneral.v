From Interval Require Import Tactic.
Require Import Reals Psatz.
Require Import QPE.

(* The proof of quantum phase estimation in QPE.v assumes the phase is a k-bit 
   dyadic fraction. In the general case, phase estimation does not recover 
   the phase exactly, but rather a k-bit approximation. The statement of
   correctness in this file says that QPE recovers the best k-bit approximation 
   of the phase with probability at least 4/PI^2.

   We've split this proof into its own file because it relies on two trig identities 
   (sin_sublinear and sin_PIx_ge_2x) that are most easily proved using the Interval 
   package, which is not a dependency of SQIR.

   Thanks to Laurent Thery for the pointer to Interval and providing proofs of 
   sin_sublinear and sin_PIx_ge_2x!

   To compile this file, you will need to install Interval <http://coq-interval.gforge.inria.fr/> 
*)

Open Scope R_scope.

Lemma Rabs_le_sym (f g : R -> R) a x :
  (forall x, 0 <= x <= a -> f (- x) = - f x /\  g (- x) = - g x /\ 
             0 <= f x <= g x) ->
  (Rabs x <= a) -> Rabs (f x) <= Rabs (g x).
Proof.
intros xB.
assert (xH := xB x); assert (mxH := xB (- x));
assert (f (-- x) = f x) by (apply f_equal; lra);
assert (g (-- x) = g x) by (apply f_equal; lra).
now split_Rabs; lra.
Qed.

Lemma sin_sublinear x : Rabs (sin x) <= Rabs x.
Proof.
assert (H : Rabs x >= 1 \/ Rabs x <= 1) by lra; destruct H as [x_gt1|x_le1].
  assert (Rabs (sin x) <= 1) by (assert (sH := SIN_bound x); split_Rabs; lra).
  now split_Rabs; lra.
apply Rabs_le_sym with (g := id) (2 := x_le1); intros y yP.
assert (sH1 := sin_neg y); assert (sH2 := sin_ge_0 y); assert (pH := PI2_1).
repeat split; unfold id; try lra.
assert (H : y = 0 \/ 0 < y) by lra; destruct H as [yZ|y_pos].
  now subst; rewrite sin_0; lra.
assert (H : y = 1 \/ y < 1) by lra; destruct H as [yE1|y_lt1].
  now subst; assert (sH := SIN_bound 1); lra.
assert (dH : forall z, 0 <= z <= y -> derivable_pt_lim sin z (cos z)).
  now intros z _; apply derivable_pt_lim_sin.
destruct (MVT_cor2 _ _ _ _ y_pos (fun z H => derivable_pt_lim_sin z)) as 
    [z [zH1 zH2]].
now assert (sH := sin_0); assert (bH := COS_bound z); nra.
Qed.

Lemma sin_PIx_ge_2x x : Rabs x <= 1 / 2 -> Rabs (2 * x) <= Rabs (sin (PI * x)).
Proof.
intros xP.
assert (dH : forall z, derivable_pt_lim (fun x => sin (PI * x) - 2 * x) z 
                                        (PI * cos (PI * z) - 2)).
  intro z; apply derivable_pt_lim_minus.
    rewrite Rmult_comm.
    apply derivable_pt_lim_comp; [idtac | apply derivable_pt_lim_sin].
    replace PI with (0 * z + PI * 1) at 2 by lra.
    apply derivable_pt_lim_mult; [apply derivable_pt_lim_const | idtac].
    now apply derivable_pt_lim_id.
  replace 2 with (0 * z + 2 * 1) at 2 by lra.
  apply derivable_pt_lim_mult; [apply derivable_pt_lim_const | idtac].
  now apply derivable_pt_lim_id.
apply Rabs_le_sym with (f := fun x => 2 * x) (g := fun x => sin (PI * x))
                       (2 := xP); intros y yP; repeat split; try lra.
  now rewrite <- sin_neg; apply f_equal; lra.   
assert (H : y = 0 \/ y > 0) by lra; destruct H as [yZ | y_pos].
  now subst; rewrite !Rmult_0_r, sin_0; lra.
assert (H : y = 1 / 2 \/ y < 1 / 2) by lra; destruct H as [y12 | y_lt12].
  now subst; replace (PI * (1 / 2)) with (PI / 2) by lra; rewrite sin_PI2; lra.
assert (H : (y < 1 / 10) \/ (1 / 10 <= y <= 1 / 2 - 1 / 10) \/ 
            (1 / 2 - 1 / 10 < y)) by lra; destruct H as [lH | [mH | rH]].
- destruct (MVT_cor2 _ _ _ _ y_pos (fun z _ => dH z)) as [z [zH1 zH2]].
  rewrite !Rmult_0_r, sin_0 in zH1.
  assert (0 <= PI * cos (PI * z) - 2); [idtac | nra].
  assert (0 <= z <= 1 / 10) by lra.
  now interval with (i_bisect z, i_taylor z).
- assert (0 <= sin (PI * y) - 2 * y) by interval with (i_bisect y, i_taylor y).
  now lra.
destruct (MVT_cor2 _ _ _ _ y_lt12 (fun z _ => dH z)) as [z [H1z H2z]].
replace (PI * (1 / 2)) with (PI / 2) in H1z by lra; rewrite sin_PI2 in H1z.
assert (PI * cos (PI * z) - 2 <= 0); [idtac | nra].
assert (1 / 2 - 1 / 10 <= z <= 1 / 2) by lra.
now interval with (i_bisect z, i_taylor z).
Qed.

Open Scope C_scope.

(** General QPE

  Preconditions:
   - z is the k-bit approximation of θ (i.e. θ = z/2^k + δ where δ < 1/2^k)
   - U × ∣ψ⟩ = Cexp (2πθ / 2^k) .* ∣ψ⟩

  Postcondition: the first k bits of the output state are z with probability
  at least 4/π^2. *)

(* Probability of outcome o given input state ψ *)
Definition probability_of_outcome {n} (ψ o : Vector n) : R := 
  (Cmod ((o† × ψ) 0%nat 0%nat)) ^ 2.

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
  { subst. apply sin_PIx_ge_2x. 
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
  { subst. apply sin_sublinear. }
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
