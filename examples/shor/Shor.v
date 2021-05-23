Require Import Reals Psatz ZArith Znumtheory Btauto.
Require Export QPEGeneral ModMult ShorAux.
Require Import Interval.Tactic.

Local Close Scope R_scope.
Local Coercion INR : nat >-> R.
Local Coercion Z.of_nat : nat >-> BinNums.Z.

(* Parameter assumptions of the Shor's algorithm *)
Definition BasicSetting (a r N m n : nat) :=
  0 < a < N /\
  Order a r N /\
  N^2 < 2^m <= 2 * N^2 /\
  N < 2^n <= 2 * N.

Definition basisPowerA (a r N n : nat) := basis_vector (2^n) (a^r mod N).

Definition ω_neg (r : nat) := Cexp (-2 * PI / r)%R.

(* The ψ states are the eigenstates of the modular multiplication circuit. Described in https://cs.uwaterloo.ca/~watrous/LectureNotes/CPSC519.Winter2006/10.pdf. *)
Definition ψ (a r N j n : nat) :=
  (1%R / (RtoC (√ r)%R)) .* vsum r (fun x => (ω_neg r)^(j * x) .* (basisPowerA a x N n)).

(* The description of the circuit implementing "multiply a modulo N". *)
Definition MultiplyCircuitProperty (a N n anc : nat) (c : base_ucom (n + anc)) : Prop :=
  forall x : nat,
    ((0 <= x < N)%nat ->
     @Mmult _ _ (1 * 1) (uc_eval c) ((basis_vector (2^n) x) ⊗ (basis_vector (2^anc) 0)) = basis_vector (2^n) (a * x mod N) ⊗ (basis_vector (2^anc) 0)).

Definition ModMulImpl (a N n anc : nat) (f : nat -> base_ucom (n + anc)) : Prop :=
  forall i x : nat,
    ((0 <= x < N)%nat ->
     @Mmult _ _ (1 * 1) (uc_eval (f i)) ((basis_vector (2^n) x) ⊗ (basis_vector (2^anc) 0)) = basis_vector (2^n) (a^(2^i) * x mod N) ⊗ (basis_vector (2^anc) 0)).

(* The Shor's algorithm applies QPE on the modular multiplication circuit c and state |1⟩. *)
Definition Shor_final_state m n anc (c : base_ucom (n + anc)) := @Mmult _ _ 1 (uc_eval (QPE m (n + anc) c)) ((basis_vector (2^m) 0) ⊗ (basis_vector (2^n) 1) ⊗ (basis_vector (2^anc) 0)).

Definition Shor_final_state_var m n anc (f : nat -> base_ucom (n + anc)) := @Mmult _ _ 1 (uc_eval (QPE_var m (n + anc) f)) ((basis_vector (2^m) 0) ⊗ (basis_vector (2^n) 1) ⊗ (basis_vector (2^anc) 0)).

(* The post-processing of Shor's algorithm is simply running continued fraction algorithm step by step. Each time a classical verifier examines whether the denominator is the order.
   OF_post outputs a candidate of the order r. It might still not be the order, but 0 or a multiple of the order. We proved with no less than 1/polylog(N) probability its output is r. *)
Definition OF_post_step (step o m : nat) := snd (ContinuedFraction step o (2^m)).

Definition modexp a x N := a ^ x mod N. (* for easier extraction -KH *)
Fixpoint OF_post' (step a N o m : nat) :=
  match step with
  | O => O
  | S step' => let pre := OF_post' step' a N o m in
              if (pre =? O) then
                (if (modexp a (OF_post_step step' o m) N =? 1) then OF_post_step step' o m
                 else O)
              else pre
  end.
Definition OF_post a N o m := OF_post' (2 * m + 2) a N o m.

Definition r_found o m r a N : R := if (OF_post a N o m =? r) then 1 else 0.

(* The final success probability of Shor's order finding algorithm. It sums over all the possible measurement results, and adds the probability of recovering r conditioned on measurement result x. *)
(* The main theorem states, given the basic settings, the probability of successully calculating order OF_post a N o m = ord a N is propotional to 1 / polylog N. *)
Definition probability_of_success (a r N m n anc : nat) (c : base_ucom (n + anc)) :=
  Rsum (2^m) (fun x => r_found x m r a N * prob_partial_meas (basis_vector (2^m) x) (Shor_final_state m n anc c))%R.

Definition probability_of_success_var (a r N m n anc : nat) (f : nat -> base_ucom (n + anc)) :=
  Rsum (2^m) (fun x => r_found x m r a N * prob_partial_meas (basis_vector (2^m) x) (Shor_final_state_var m n anc f))%R.

(* The post processing for factorization. Notice here `a` is set as input, while the real implementation needs a randomized `a` from 1<a<N such that gcd a N <> 1.
   The Shor's reduction proved in ShorAux.v ensures that with at least 1/2 probability, the randomly picked `a` will lead to a non-trivial factor if (OF_post a N o m = ord a N). The condition happens with probability at least 1/polylog(N) by the above main theorem.
*)
Definition Factor_post a N o m := if ((1 <? Nat.gcd (a ^ ((OF_post a N o m) / 2) - 1) N) && (Nat.gcd (a ^ ((OF_post a N o m) / 2) - 1) N <? N)) then Nat.gcd (a ^ ((OF_post a N o m) / 2) - 1) N else Nat.gcd (a ^ ((OF_post a N o m) / 2) + 1) N.





(* ======================= *)
(* =   ModMult Circuit   = *)
(* ======================= *)

Definition modmult_circuit a ainv N n := @bc2ucom (n + modmult_rev_anc n) (csplit (bcelim (modmult_rev N a ainv n))).

Lemma modmult_circuit_MCP :
  forall a ainv N n,
    0 < a < N -> ainv < N ->
    a * ainv mod N = 1 ->
    N < 2^n ->
    MultiplyCircuitProperty a N n (modmult_rev_anc n) (modmult_circuit a ainv N n).
Proof.
  intros. unfold MultiplyCircuitProperty. intros. unfold modmult_circuit.
  (*destruct H as [Ha [_ [_ [HN _]]]].*)
  replace (basis_vector (2 ^ n) x) with (basis_vector (2 ^ n) (x mod (2 ^ n))) by (rewrite Nat.mod_small by lia; easy).
  replace (basis_vector (2 ^ n) ((a * x) mod N)) with (basis_vector (2 ^ n) (((a * x) mod N) mod (2 ^ n))).
  2:{ remember ((a * x) mod N) as axN. rewrite Nat.mod_small. easy. subst.
      assert ((a * x) mod N < N) by (apply Nat.mod_upper_bound; lia).
      lia.
  }
  do 2 rewrite <- f_to_vec_num_with_anc.
  assert (0 < n) by (destruct n; simpl in *; lia).
  rewrite bc2ucom_csplit_bcelim.
  2: unfold modmult_rev_anc; lia.
  2: apply modmult_rev_eWT; easy.
  rewrite modmult_rev_correct; try easy. lia.
Qed.

Lemma modmult_circuit_uc_well_typed :
  forall a ainv N n,
    0 < a < N -> ainv < N ->
    a * ainv mod N = 1 ->
    N < 2^n ->
    uc_well_typed (modmult_circuit a ainv N n).
Proof.
  intros. apply eWT_uc_well_typed_csplit_bcelim. unfold modmult_rev_anc. lia. apply modmult_rev_eWT.
  destruct n; simpl in *; lia.
Qed.  

Definition f_modmult_circuit a ainv N n := fun (i : nat) => @bc2ucom (n + modmult_rev_anc n) (csplit (bcelim (modmult_rev N (a^(2^i) mod N) (ainv^(2^i) mod N) n))).

Lemma f_modmult_circuit_MMI :
  forall a r N m n ainv,
    BasicSetting a r N m n ->
    ainv < N ->
    a * ainv mod N = 1 ->
    ModMulImpl a N n (modmult_rev_anc n) (f_modmult_circuit a ainv N n).
Proof.
  intros. unfold ModMulImpl. intros.
  destruct H as [Ha [Horder [HNm HNn]]].
  assert (MultiplyCircuitProperty (a^(2^i) mod N) N n (modmult_rev_anc n) (modmult_circuit (a^(2^i) mod N) (ainv^(2^i) mod N) N n)).
  { apply modmult_circuit_MCP.
    split. apply Pow_pos with (r := r). easy. apply Nat.mod_upper_bound. lia.
    apply Nat.mod_upper_bound. lia. rewrite <- Nat.mul_mod by lia.
    apply inv_pow with (r := r); easy.
    lia.
  }
  unfold MultiplyCircuitProperty in H. specialize (H x H2). unfold f_modmult_circuit. unfold modmult_circuit in H. rewrite Nat.mul_mod_idemp_l in H by lia. apply H.
Qed.

Lemma f_modmult_circuit_uc_well_typed :
  forall a ainv N n i,
    0 < a < N -> ainv < N ->
    a * ainv mod N = 1 ->
    N < 2^n ->
    uc_well_typed (f_modmult_circuit a ainv N n i).
Proof.
  intros. apply eWT_uc_well_typed_csplit_bcelim. unfold modmult_rev_anc. lia. apply modmult_rev_eWT.
  destruct n; simpl in *; lia.
Qed.



(* ===================================================== *)
(* =   Properties of eigenpairs (ω_neg r ^ k, |ψ_k⟩)   = *)
(* ===================================================== *)

Local Open Scope R_scope.
Lemma ω_neg_sum_zero : forall r, Csum (fun i =>  (ω_neg r ^ (i * 0))%C) r = r.
Proof.
  intros.
  apply Csum_1.
  intros.
  unfold ω_neg.
  rewrite Cexp_pow.
  rewrite Nat.mul_0_r.
  autorewrite with R_db.
  apply Cexp_0.
Qed. 

Lemma ω_neg_sum_nonzero :
  forall (r k : nat),
    0 < k < r -> 
    Csum (fun i => (ω_neg r ^ (i * k))%C) r = 0.
Proof.
  intros.
  erewrite Csum_eq_bounded.
  2: { intros.
       unfold ω_neg.
       rewrite Cexp_pow.
       replace (-2 * PI / r * (x * k)%nat) with (2 * PI * (IZR (- k)) / r * x).
       rewrite <- Cexp_pow.
       reflexivity.
       rewrite Ropp_Ropp_IZR, <- INR_IZR_INZ.
       rewrite mult_INR.
       lra. }
  apply Csum_Cexp_nonzero. (* defined in QPE.v *)
  rewrite Ropp_Ropp_IZR, <- INR_IZR_INZ.
  lra.
  rewrite Ropp_Ropp_IZR, <- INR_IZR_INZ.
  lra.
Qed.

Lemma ω_neg_cancel :
  forall n i j,
    (i <= j)%nat ->
    (((ω_neg n) ^ i) ^* * ((ω_neg n) ^ j) = (ω_neg n) ^ (j - i))%C.
Proof.
  intros. 
  unfold ω_neg. 
  replace j with ((j - i) + i)%nat by lia.
  do 3 rewrite Cexp_pow.
  replace (-2 * PI / n * (j - i + i)%nat) 
    with (-2 * PI / n * i + -2 * PI / n * (j - i)%nat) 
    by (rewrite plus_INR; lra).
  rewrite Cexp_add. 
  rewrite Cmult_assoc. 
  rewrite <- Cmod_sqr. 
  rewrite Cmod_Cexp.
  replace (j - i + i - i)%nat with (j - i)%nat by lia. 
  lca.
Qed.

Lemma ω_neg_mod :
  forall n x,
    (n <> 0)%nat ->
    ((ω_neg n) ^ x = (ω_neg n) ^ (x mod n))%C.
Proof.
  intros. pattern x at 1. rewrite (Nat.div_mod x n) by easy. rewrite Cpow_add. rewrite Cpow_mult.
  unfold ω_neg. rewrite Cexp_pow.
  replace (-2 * PI / n * n) with (-2 * PI).
  2:{ field. apply not_0_INR. easy.
  }
  replace (-2 * PI) with (- (2 * PI)) by field. rewrite Cexp_neg. rewrite Cexp_2PI.
  replace (/ 1)%C with (C1).
  2:{ pattern C1 at 1. rewrite <- (Cinv_r C1). lca. apply RtoC_neq. lra.
  }
  rewrite RtoC_pow. rewrite pow1. lca.
Qed.

Lemma pure_state_vector_kron :
  forall {n m} (ϕ : Vector n) (ψ : Vector m),
    Pure_State_Vector ϕ ->
    Pure_State_Vector ψ ->
    Pure_State_Vector (ϕ ⊗ ψ).
Proof.
  unfold Pure_State_Vector.
  intros. destruct H as [Hwf1 Hi1]. destruct H0 as [Hwf2 Hi2].
  split. apply WF_kron; try easy; try lia.
  restore_dims. rewrite kron_adjoint. rewrite kron_mixed_product. rewrite Hi1, Hi2. Msimpl. easy.
Qed.

Lemma basis_vector_pure_state :
  forall n i,
    (i < n)%nat ->
    Pure_State_Vector (basis_vector n i).
Proof.
  intros. split. apply basis_vector_WF. easy.
  apply basis_vector_product_eq. easy.
Qed.

Lemma ψ_WF_matrix :
  forall a r N m n j : nat,
    BasicSetting a r N m n ->
    WF_Matrix (ψ a r N j n).
Proof.
  intros. unfold ψ. apply WF_scale. apply vsum_WF. intros. apply WF_scale. unfold basisPowerA. apply basis_vector_WF.
  assert (0 <= a^i mod N < N)%nat.
  { apply Nat.mod_bound_pos. lia.
    destruct H as [_ [HOrder _]]. apply Order_N_lb in HOrder. lia.
  }
  destruct H as [_ [_ [_ [Hn _]]]]. lia.
Qed.

Lemma Pow_mod_ub :
  forall a r N m n,
    BasicSetting a r N m n ->
    (forall x, a ^ x mod N < 2^n)%nat.
Proof.
  intros. destruct H as [HN [_ [_ [Hn _]]]].
  assert (N <> 0)%nat by lia. specialize (Nat.mod_upper_bound (a^x)%nat N H). lia.
Qed.

Lemma ψ_pure_state_vector :
  forall a r N m n j : nat,
    BasicSetting a r N m n ->
    Pure_State_Vector (ψ a r N j n).
Proof.
  intros. split.
  - apply ψ_WF_matrix with (m := m); easy.
  - unfold ψ. rewrite Mscale_adj. rewrite Mscale_mult_dist_l. rewrite Mscale_mult_dist_r.
    rewrite Mmult_vsum_distr_l.

    replace (fun i : nat => (vsum r (fun x : nat => ω_neg r ^ (j * x) .* basisPowerA a x N n)) † × (ω_neg r ^ (j * i) .* basisPowerA a i N n)) with (fun i : nat => (vsum r (fun x : nat => (ω_neg r ^ (j * x) .* basisPowerA a x N n) † × (ω_neg r ^ (j * i) .* basisPowerA a i N n)))).
    2:{ apply functional_extensionality. intro. symmetry. apply Mmult_adj_vsum_distr_l.
    }
    replace (fun i : nat => vsum r (fun x : nat => (ω_neg r ^ (j * x) .* basisPowerA a x N n) † × (ω_neg r ^ (j * i) .* basisPowerA a i N n))) with (fun i : nat => vsum r (fun x : nat => ((ω_neg r ^ (j * x))^* * ω_neg r ^ (j * i)) .* ((basisPowerA a x N n) † × basisPowerA a i N n))).
    2:{ apply functional_extensionality. intro. apply vsum_eq. intros.
        rewrite Mscale_adj. rewrite Mscale_mult_dist_r.
        rewrite Mscale_mult_dist_l. rewrite Mscale_assoc.
        replace ((ω_neg r ^ (j * i)) ^* * ω_neg r ^ (j * x))%C with (ω_neg r ^ (j * x) * (ω_neg r ^ (j * i)) ^* )%C by lca.
        easy.
    }
    assert (G := H). specialize (Pow_mod_ub a r N m n G) as Hpmub.
    rewrite vsum_diagonal.
    2:{ rename j into x. intros. unfold basisPowerA.
        rewrite basis_vector_product_neq. Msimpl. easy.
        apply Hpmub. apply Hpmub.
        apply Pow_diff_neq with (r:=r); try lia.
        destruct H as [_ [HOrder _]]. easy.
    }
    unfold basisPowerA.
    replace (fun i : nat => (ω_neg r ^ (j * i)) ^* * ω_neg r ^ (j * i) .* ((basis_vector (2 ^ n) (a ^ i mod N)) † × basis_vector (2 ^ n) (a ^ i mod N))) with (fun i : nat => I 1).
    2:{ apply functional_extensionality. intro.
        rewrite <- Cmod_sqr. unfold ω_neg. rewrite Cexp_pow. rewrite Cmod_Cexp. 
        rewrite basis_vector_product_eq by (apply Hpmub).
        simpl. do 2 rewrite Cmult_1_r. Msimpl. easy.
    } 
    rewrite vsum_constant.
    do 2 rewrite Mscale_assoc.
    assert (√ r <> 0).
    { destruct H as [_ [[Hr _] _]]. apply sqrt_neq_0_compat. apply lt_INR in Hr. simpl in Hr. easy.
    }
    rewrite <- RtoC_div by easy.
    rewrite Cconj_R. do 2 rewrite <- RtoC_mult.
    assert (forall x, x * r = x * (√r * √r)).
    { intro. apply Rmult_eq_compat_l. destruct H as [_ [[Hr _] _]]. apply lt_INR in Hr. simpl in Hr. apply Rlt_le in Hr. specialize (Rsqr_sqrt r Hr) as Hr2. unfold Rsqr in Hr2. lra.
    } 
    replace (1 / √ r * (1 / √ r) * r) with ((/ √ r * √ r) * ((/ √ r) * √ r)) by (rewrite H1; lra).
    rewrite Rinv_l by easy. rewrite Rmult_1_r. Msimpl. easy.
Qed.

Lemma ψ_basis_vector_pure_state :
  forall a r N m n j i s : nat,
    BasicSetting a r N m n ->
    (i < s)%nat ->
    Pure_State_Vector (ψ a r N j n ⊗ basis_vector s i).
Proof.
  intros. apply pure_state_vector_kron. apply ψ_pure_state_vector with (m := m). easy.
  apply basis_vector_pure_state. easy.
Qed.

Lemma sum_of_ψ_is_one :
  forall a r N m n : nat,
    BasicSetting a r N m n ->
    (1 / √r) .* vsum r (fun j => ψ a r N j n) = basis_vector (2^n) 1.
Proof.
  intros.
  destruct H as [? [[? _] _]]. (* we only need a few parts of H *)
  unfold ψ.
  rewrite <- Mscale_vsum_distr_r.
  rewrite Mscale_assoc.
  rewrite vsum_swap_order.
  erewrite vsum_eq.
  2: { intros. rewrite Mscale_vsum_distr_l. reflexivity. }
  erewrite vsum_unique.
  2: { exists O.
       split. assumption.
       split.
       rewrite ω_neg_sum_zero. reflexivity.
       intros.
       rewrite ω_neg_sum_nonzero.
       lma.
       split. apply not_eq_sym in H2. apply neq_0_lt in H2. apply lt_0_INR; assumption. apply lt_INR; assumption.
  }
  unfold basisPowerA.
  rewrite Nat.pow_0_r.
  rewrite Nat.mod_1_l by lia.
  rewrite Mscale_assoc.
  replace (1 / √ r * (1 / √ r) * r)%C with C1.
  lma.
  field_simplify_eq.
  rewrite <- RtoC_mult.
  rewrite sqrt_def. 
  reflexivity.
  apply pos_INR.
  apply RtoC_neq.
  apply sqrt_neq_0_compat.
  apply lt_0_INR. 
  assumption.
Qed.

Lemma MC_eigenvalue :
  forall (a r N j m n anc : nat) (c : base_ucom (n + anc)),
    BasicSetting a r N m n ->
    MultiplyCircuitProperty a N n anc c ->
    @Mmult _ _ (1 * 1) (uc_eval c) ((ψ a r N j n) ⊗ basis_vector (2^anc) 0) = Cexp (2 * PI * j / r) .* ((ψ a r N j n) ⊗ basis_vector (2^anc) 0).
Proof.
  intros. unfold ψ. 
  unfold BasicSetting in H. destruct H as [Ha [HOrder [HN1 HN2]]].
  distribute_scale. rewrite kron_vsum_distr_r.
  replace (2^(n+anc))%nat with (2^n * 2^anc)%nat by unify_pows_two.
  rewrite Mmult_vsum_distr_l.
  unfold MultiplyCircuitProperty in H0. remember (uc_eval c) as U.
  replace (2^n * 2^anc)%nat with (2^(n+anc))%nat by unify_pows_two.
  replace (vsum r (fun i : nat => U × (ω_neg r ^ (j * i) .* basisPowerA a i N n ⊗ basis_vector (2^anc) 0))) 
    with (vsum r (fun i : nat => (ω_neg r ^ (j * i) .* basisPowerA a (i+1) N n ⊗ basis_vector (2^anc) 0))).
  2:{
    replace (2^(n+anc))%nat with (2^n * 2^anc)%nat by unify_pows_two.
    apply vsum_eq. intros. distribute_scale. rewrite Mscale_mult_dist_r.
    unfold basisPowerA. restore_dims. rewrite H0. rewrite Nat.add_1_r. simpl. rewrite Nat.mul_mod_idemp_r. easy.
    (* N <> 0 *)
    destruct Ha. unfold not. intros. rewrite H3 in H2. easy.
    (* 0 <= a^i mod N < N *)
    apply Nat.mod_bound_pos. apply Nat.le_0_l. apply Nat.lt_trans with a. easy. easy. 
  }
  replace (vsum r (fun i : nat => ω_neg r ^ (j * i) .* basisPowerA a (i + 1) N n ⊗ basis_vector (2^anc) 0))
    with (vsum r (fun i : nat => Cexp (2 * PI * j / r) .* (ω_neg r ^ (j * i) .* basisPowerA a i N n ⊗ basis_vector (2^anc) 0))).
  rewrite <- Mscale_vsum_distr_r. restore_dims. rewrite Mscale_assoc. apply f_equal2. lca.
  replace (2^n * 2^anc)%nat with (2^(n+anc))%nat by unify_pows_two. easy.
  destruct r. easy. 
  rewrite vsum_extend_l. rewrite vsum_extend_r. rewrite Mplus_comm.
  unfold shift.
  assert (forall t (A B C D : Vector t), A = B -> C = D -> A .+ C = B .+ D).
  { intros. rewrite H. rewrite H1. easy. }
  apply H.   
  - apply vsum_eq. intros. distribute_scale. unfold ω_neg. rewrite Cexp_pow. rewrite Cexp_pow.
    rewrite <- Cexp_add. 
    replace (2 * PI * j / S r + -2 * PI / S r * (j * (i + 1))%nat) with (-2 * PI / S r * (j * i)%nat).
    easy. repeat rewrite mult_INR. rewrite plus_INR. simpl. lra.
  - unfold basisPowerA. remember (S r) as r'. unfold ω_neg. simpl. destruct HOrder as [Hr [HO1 HO2]].
    rewrite Nat.add_1_r. rewrite <- Heqr'. rewrite HO1. rewrite Nat.mod_small.
    distribute_scale. rewrite Mscale_assoc. repeat rewrite Cexp_pow. rewrite <- Cexp_add.
    rewrite <- (Cmult_1_l (Cexp (-2 * PI / r' * (j * r)%nat))). replace 1 with (1^j). rewrite <- RtoC_pow. 
    rewrite <- Cexp_2PI. rewrite Cexp_pow. rewrite <- Cexp_add. repeat rewrite mult_INR.  simpl.
    replace (2 * PI * j / r' + -2 * PI / r' * (j * 0)) with (2 * PI * j + -2 * PI / r' * (j * r)).
    easy. simpl. rewrite Heqr'. rewrite <- Nat.add_1_r. repeat rewrite plus_INR. repeat rewrite Rdiv_unfold. simpl.
    repeat rewrite Rmult_0_r. rewrite Rplus_0_r. replace (-2 * PI) with (2 * PI * -1) by lra. 
    repeat rewrite Rmult_assoc.
    repeat rewrite <- Rmult_plus_distr_l.
    replace (j + -1 * (/ (r + 1) * (j * r))) with (j * / (r + 1)). easy.
    rewrite <- (Rmult_1_r j) at 2. rewrite <- (Rinv_r (r+1)) at 2.
    rewrite Rmult_comm. lra. 
    + replace (r+1) with (r+1%nat). rewrite <- plus_INR. rewrite Nat.add_1_r. rewrite <- Heqr'.
      apply lt_0_INR in Hr. apply Rlt_dichotomy_converse. right. easy. easy.
    + apply pow1.
    + destruct N. easy. destruct N. easy. lia. 
Qed.

Lemma MMI_eigen :
  forall (a r N j m n anc k : nat) (f : nat -> base_ucom (n + anc)),
    BasicSetting a r N m n ->
    ModMulImpl a N n anc f ->
    @Mmult _ _ (1 * 1) (uc_eval (f k)) ((ψ a r N j n) ⊗ basis_vector (2^anc) 0) = Cexp (2 * PI * j / r * (2^k)%nat) .* ((ψ a r N j n) ⊗ basis_vector (2^anc) 0).
Proof.
  intros. unfold ψ. 
  unfold BasicSetting in H. destruct H as [Ha [HOrder [HN1 HN2]]].
  distribute_scale. rewrite kron_vsum_distr_r.
  replace (2^(n+anc))%nat with (2^n * 2^anc)%nat by unify_pows_two.
  rewrite Mmult_vsum_distr_l.
  unfold ModMulImpl in H0. specialize (H0 k). remember (uc_eval (f k)) as U.
  replace (2^n * 2^anc)%nat with (2^(n+anc))%nat by unify_pows_two.
  replace (vsum r (fun i : nat => U × (ω_neg r ^ (j * i) .* basisPowerA a i N n ⊗ basis_vector (2^anc) 0))) 
    with (vsum r (fun i : nat => (ω_neg r ^ (j * i) .* basisPowerA a (i+(2^k)) N n ⊗ basis_vector (2^anc) 0))).
  2:{
    replace (2^(n+anc))%nat with (2^n * 2^anc)%nat by unify_pows_two.
    apply vsum_eq. intros. distribute_scale. rewrite Mscale_mult_dist_r.
    unfold basisPowerA. restore_dims. rewrite H0. rewrite Nat.pow_add_r. rewrite Nat.mul_mod_idemp_r. rewrite Nat.mul_comm with (n := (a ^ i)%nat). easy.
    (* N <> 0 *)
    destruct Ha. unfold not. intros. lia.
    (* 0 <= a^i mod N < N *)
    apply Nat.mod_bound_pos. apply Nat.le_0_l. apply Nat.lt_trans with a. easy. easy. 
  }
  replace (vsum r (fun i : nat => ω_neg r ^ (j * i) .* basisPowerA a (i + 2^k) N n ⊗ basis_vector (2^anc) 0))
    with (vsum r (fun i : nat => Cexp (2 * PI * j / r * INR (2^k)) .* (ω_neg r ^ (j * i) .* basisPowerA a i N n ⊗ basis_vector (2^anc) 0))).
  rewrite <- Mscale_vsum_distr_r. restore_dims. rewrite Mscale_assoc. apply f_equal2. lca.
  replace (2^n * 2^anc)%nat with (2^(n+anc))%nat by unify_pows_two. easy.
  bdestruct (r =? 0). subst. easy.
  remember (fun i : nat => ((i + 2^k) mod r)%nat) as u.
  assert (finite_bijection r u).
  { rewrite Hequ. 
    exists (fun i : nat => ((r - (2^k) mod r + i) mod r)).
    intros x Hx.
    repeat split.
    apply Nat.mod_upper_bound. easy.
    apply Nat.mod_upper_bound. easy.
    rewrite Nat.add_mod with (a := x) by easy.
    rewrite Nat.add_mod_idemp_r by easy. rewrite Nat.add_comm.
    replace (x mod r + 2 ^ k mod r + (r - 2 ^ k mod r))%nat with (x mod r + (2 ^ k mod r + (r - 2 ^ k mod r)))%nat by lia.
    rewrite le_plus_minus_r. pattern r at 2. rewrite <- Nat.mul_1_l. rewrite Nat.mod_add by easy. rewrite Nat.mod_mod. apply Nat.mod_small. easy. easy.
    specialize (Nat.mod_upper_bound (2^k)%nat r H). lia.
    rewrite <- Nat.add_mod_idemp_r by easy. rewrite Nat.add_mod_idemp_l by easy.
    replace (r - 2 ^ k mod r + x + 2 ^ k mod r)%nat with (2 ^ k mod r + (r - 2 ^ k mod r) + x)%nat by lia.
    rewrite le_plus_minus_r. replace (r + x)%nat with (x + 1 * r)%nat by lia. rewrite Nat.mod_add by easy. apply Nat.mod_small. easy.
    specialize (Nat.mod_upper_bound (2^k)%nat r H). lia.
  }
  rewrite vsum_reorder with (f0 := u) by easy.
  rewrite Hequ. apply vsum_eq. intros. distribute_scale. apply f_equal2.
  replace (j * ((i + 2 ^ k) mod r))%nat with (((i + 2 ^ k) mod r) * j)%nat by lia.
  rewrite Cpow_mult. rewrite <- ω_neg_mod by easy. rewrite <- Cpow_mult.
  replace ((i + 2^k) * j)%nat with (j * 2^k + j * i)%nat by lia.
  rewrite Cpow_add. rewrite Cmult_assoc. unfold ω_neg. rewrite Cexp_pow. rewrite mult_INR.
  rewrite <- Cexp_add.
  replace (2 * PI * j / r * (2 ^ k)%nat + -2 * PI / r * (j * (2 ^ k)%nat)) with 0 by lra.
  rewrite Cexp_0. lca.
  unfold basisPowerA. pattern (i + 2 ^ k)%nat at 2. rewrite (Nat.div_mod (i + 2^k) r) by easy.
  rewrite Nat.pow_add_r. rewrite Nat.pow_mul_r. rewrite <- Nat.mul_mod_idemp_l by lia. rewrite pow_mod with (a := (a^r)%nat). destruct HOrder as [_ [Hr _]]. rewrite Hr. rewrite Nat.pow_1_l. rewrite Nat.mod_1_l by lia. do 2 rewrite Nat.mul_1_l. easy.
Qed.

Lemma ψ_perp :
  forall a r N m n i j : nat,
    BasicSetting a r N m n ->
    (i < j < r)%nat ->
    (ψ a r N i n) † × (ψ a r N j n) = Zero.
Proof.
  intros. unfold ψ. rewrite Mscale_adj. distribute_scale. rewrite <- Cmod_sqr.
  rewrite Mmult_adj_vsum_distr_l. erewrite vsum_eq.
  2:{ intros. apply Mmult_vsum_distr_l.
  }
  rewrite vsum_diagonal.
  2:{ intros. rewrite Mscale_adj. distribute_scale. unfold basisPowerA. rewrite basis_vector_product_neq. Msimpl. easy. apply Pow_mod_ub with (r:=r) (m:=m); easy. apply Pow_mod_ub with (r:=r) (m:=m); easy. apply Pow_diff_neq with (r:=r); try lia. destruct H as [_ [HOrder _]]. easy.
  }
  erewrite vsum_eq.
  2:{ intros. rewrite Mscale_adj. distribute_scale. unfold basisPowerA. rewrite basis_vector_product_eq by (apply Pow_mod_ub with (r:=r) (m:=m); easy).
      rewrite ω_neg_cancel by nia.
      replace (j * i0 - i * i0)%nat with (i0 * (j - i))%nat.
      reflexivity. 
      rewrite Nat.mul_comm.
      rewrite Nat.mul_sub_distr_r.
      reflexivity.
  }
  rewrite Mscale_vsum_distr_l. rewrite ω_neg_sum_nonzero. Msimpl. easy.
  assert (0 < j - i < r)%nat by lia. destruct H1 as [Hl Hr]. apply lt_INR in Hl. apply lt_INR in Hr. simpl in Hl. lra.
Qed.

Lemma ψ_perp_neq :
  forall a r N m n i j : nat,
    BasicSetting a r N m n ->
    (i < r)%nat ->
    (j < r)%nat ->
    (i <> j)%nat ->
    (ψ a r N i n) † × (ψ a r N j n) = Zero.
Proof.
  intros. bdestruct (i <? j).
  - apply ψ_perp with (m:=m). easy. lia.
  - assert (j < i)%nat by lia. rewrite <- adjoint_involutive with (A:=(ψ a r N i n) † × ψ a r N j n). rewrite Mmult_adjoint. rewrite adjoint_involutive. rewrite ψ_perp with (m:=m). Msimpl. easy. easy. lia.
Qed.

(* ===================================================== *)
(* =   Round function and commonly used inequalities   = *)
(* ===================================================== *)

(* Round operator. Round a real number to its nearest integer. round(0.5)=1. *)
Definition round (x : R) := up (x - /2).

Lemma round_inequality :
  forall x,
    x - /2 < IZR (round x) <= x + /2.
Proof.
  intros. unfold round.
  specialize (archimed (x - /2)) as H. destruct H as [H0 H1].
  lra.
Qed.

Lemma round_pos :
  forall x,
    0 <= x ->
    (0 <= round x)%Z.
Proof.
  intros. specialize (round_inequality x) as G. destruct G as [G0 G1].
  assert (-1 < IZR (round x)) by lra. apply lt_IZR in H0. lia.
Qed.

Lemma round_lt_Z :
  forall (x : R) (z : BinNums.Z),
    x <= IZR z ->
    (round x <= z)%Z.
Proof.
  intros. specialize (round_inequality x) as G. destruct G as [G0 G1].
  assert (IZR (round x) < IZR z + 1) by lra. replace (IZR z + 1) with (IZR (z + 1)) in H0 by (rewrite plus_IZR; easy). apply lt_IZR in H0. lia.
Qed.

Lemma IZR_IZN_INR :
  forall z,
    (0 <= z)%Z ->
    IZR z = Z.to_nat z.
Proof.
  intros. destruct z; try lia. easy.
  simpl. rewrite INR_IPR. easy.
Qed.

Lemma Inv__pow_2_m_and_N_square:
  forall a r N m n,
    BasicSetting a r N m n ->
    1 / (2 * 2^m) < 1 / (2 * N^2).
Proof.
  intros. destruct H as [Ha [HOrder [[Hm1 Hm2] HN2]]]. assert (HN := HOrder). apply Order_N_lb in HN. apply lt_INR in HN. simpl in HN.
  assert (0 < 2 ^ m) by nonzero.
  assert (0 < N^2) by nra.
  unfold Rdiv. do 2 rewrite Rinv_mult_distr by lra.
  do 2 rewrite Rmult_1_l.
  apply Rmult_lt_compat_l. nra.
  apply Rinv_lt_contravar. nra. 
  apply lt_INR in Hm1. do 2 rewrite pow_INR in Hm1. apply Hm1.
Qed.

Lemma round_k_r_2_m_nonneg :
  forall a r N m n k,
    BasicSetting a r N m n ->
    (0 <= k < r)%nat ->
    (0 <= round (k / r * 2 ^ m))%Z.
Proof.
  intros. apply round_pos. destruct H0 as [Hk Hr]. assert (0 < r)%nat by lia. apply le_INR in Hk. simpl in Hk. apply lt_INR in Hr. apply lt_INR in H0. simpl in H0. assert (0 <= k / r). unfold Rdiv. apply Rle_mult_inv_pos; easy. assert (0 < 2 ^ m) by nonzero. nra. 
Qed.

(* ======================================================== *)
(* =   Properties of the closest approximation to k / r   = *)
(* ======================================================== *)

(* The target basis we focus on. It is the closest integer near k/r when m precisions are considered *)
Definition s_closest (m k r : nat) :=
  Z.to_nat (round (k / r * 2^m)%R).

Lemma s_closest_is_closest :
  forall a r N m n k,
    BasicSetting a r N m n ->
    (0 <= k < r)%nat ->
    -1 / (2 * 2^m) < (s_closest m k r) / (2^m) - k / r <= 1 / (2 * 2^m).
Proof.
  intros. assert (HBS := H). destruct H as [Ha [HOrder [[Hm1 Hm2] HN2]]]. unfold s_closest. assert (HN := HOrder). apply Order_N_lb in HN. apply lt_INR in HN. simpl in HN.
  assert (PowM : 0 < 2 ^ m) by nonzero.
  specialize (round_k_r_2_m_nonneg _ _ _ _ _ _ HBS H0) as H.
  unfold Rdiv.
  replace (/ (2 * 2 ^ m)) with (/2 * /2^m) by (symmetry; apply Rinv_mult_distr; lra).  
  rewrite <- IZR_IZN_INR by easy.
  specialize (round_inequality (k / r * 2 ^ m)) as G. destruct G as [G0 G1].
  split.
  - apply Rmult_lt_compat_l with (r:=/2^m) in G0.
    2: nonzero.
    rewrite Rmult_minus_distr_l in G0.
    replace (/ 2 ^ m * (k / r * 2 ^ m)) with (/ 2^m * 2^m * (k / r)) in G0 by lra. rewrite Rinv_l in G0; lra.
  - apply Rmult_le_compat_r with (r:=/2^m) in G1.
    2: apply Rlt_le; nonzero.
    rewrite Rmult_plus_distr_r in G1.
    replace (k / r * 2 ^ m * / 2 ^ m) with (k / r * (2 ^ m * / 2 ^ m)) in G1 by lra. rewrite Rinv_r in G1; lra. 
Qed.

Corollary s_closest_Rabs :
  forall a r N m n k,
    BasicSetting a r N m n ->
    (0 <= k < r)%nat ->
    Rabs ((s_closest m k r) / (2^m) - k / r) <= 1 / (2 * 2^m).
Proof.
  intros. specialize (s_closest_is_closest a r N m n k H H0) as G.
  replace (-1 / (2 * 2 ^ m)) with (- (1 / (2 * 2 ^ m))) in G by lra.
  assert (T: forall x y z, x < y <= z -> x <= y <= z) by (intros; lra).
  apply T in G. apply Rabs_le in G. easy.
Qed.

Lemma s_closest_ub :
  forall a r N m n k,
    BasicSetting a r N m n ->
    (0 <= k < r)%nat ->
    (s_closest m k r < 2 ^ m)%nat.
Proof.
  intros a r N m n k H H1.
  apply INR_lt. rewrite pow_INR. specialize (s_closest_is_closest _ _ _ _ _ _ H H1) as G. destruct G as [_ G1].
  assert (k / r <= 1 - / r).
  { assert (0 < r). assert (0 < r)%nat by lia. apply lt_0_INR; easy.
    apply Rmult_le_reg_r with (r:=r). easy.
    rewrite Raux.Rmult_minus_distr_r. replace (k / r * r) with ((/r) * r * k) by lra. rewrite Rinv_l by lra.
    assert (H3 : (k + 1 <= r)%nat) by lia. apply le_INR in H3. rewrite plus_INR in H3. simpl in H3. lra.
  }
  assert (/N < /r).
  { apply Rinv_lt_contravar. destruct H as [HN [[Hr _] _]]. assert (0 < r * N)%nat by (apply Nat.mul_pos_pos; lia). apply lt_INR in H. rewrite mult_INR in H. easy.
    apply lt_INR. apply Order_r_lt_N with (a:=a). destruct H as [_ [H _]]. easy.
  }
  assert (/ (2 * 2^m) < /N).
  { apply Rinv_lt_contravar.
    destruct H as [HN [Horder _]]. apply Order_N_lb in Horder. assert (0 < N)%nat by lia. apply lt_INR in H. simpl in H.
    assert (0 < 2 ^ m) by nonzero.
    nra.
    destruct H as [_ [_ [[Hm _] _]]]. apply lt_INR in Hm. simpl in Hm. do 2 rewrite mult_INR in Hm. rewrite pow_INR in Hm. replace (INR 2%nat) with 2 in Hm by reflexivity. simpl in Hm.
    assert (N <= N * N)%nat by nia. apply le_INR in H. rewrite mult_INR in H.
    nra.
  }
  assert (s_closest m k r / 2^m < 1) by lra.
  replace (INR 2%nat) with 2 by reflexivity.
  assert (T : 0 < 2 ^ m) by nonzero.
  apply Rmult_lt_reg_r with (r:=/2^m). nonzero.
  rewrite Rinv_r by lra. lra.
Qed.

Lemma s_closest_injective :
  forall a r N m n i j : nat,
    BasicSetting a r N m n ->
    (i < r)%nat ->
    (j < r)%nat ->
    s_closest m i r = s_closest m j r -> i = j.
Proof.
  intros. assert (0 <= i < r)%nat by lia. assert (0 <= j < r)%nat by lia.
  specialize (s_closest_Rabs a r N m n i H H3) as Hi.
  specialize (s_closest_Rabs a r N m n j H H4) as Hj.
  rewrite <- H2 in Hj.
  specialize (Inv__pow_2_m_and_N_square a r N m n H) as Hm.
  specialize (Rle_lt_trans _ _ _ Hi Hm) as Hi'.
  specialize (Rle_lt_trans _ _ _ Hj Hm) as Hj'.
  replace (1 / (2 * N ^ 2)) with (/ (2 * N^2)) in Hi' by lra.
  replace (1 / (2 * N ^ 2)) with (/ (2 * N^2)) in Hj' by lra.
  assert (0 < r <= N)%nat.
  { destruct H as [_ [HOrder _] ]. specialize (Order_r_lt_N a r N HOrder) as G. destruct HOrder as [Hr _]. lia.
  }
  assert (i / r = j / r).
  { apply ClosestFracUnique with (α := s_closest m i r / 2 ^ m) (N := N); try easy.
    destruct H as [HN _]. lia.
  }
  unfold Rdiv in H6. apply INR_eq. apply Rmult_eq_reg_r with (r := /r). easy.
  destruct H5 as [Hr _]. apply lt_INR in Hr. simpl in Hr. apply Rinv_0_lt_compat in Hr. lra.
Qed.


(* ====================================== *)
(* =   Properties of Shor's algorithm   = *)
(* ====================================== *)

Lemma QPE_MC_partial_correct :
  forall (a r N k m n anc : nat) (c : base_ucom (n + anc)),
    BasicSetting a r N m n ->
    uc_well_typed c ->
    MultiplyCircuitProperty a N n anc c ->
    (0 <= k < r)%nat ->
    probability_of_outcome ((basis_vector (2^m) (s_closest m k r)) ⊗ (ψ a r N k n) ⊗ (basis_vector (2^anc) 0)) (@Mmult _ _ (1 * 1) (uc_eval (QPE m (n + anc) c)) ((basis_vector (2^m) 0) ⊗ (ψ a r N k n) ⊗ (basis_vector (2^anc) 0))) >= 4 / (PI ^ 2).
Proof.
  intros a r N k m n anc c H Hc H0 H1.
  repeat rewrite <- kron_n_0_is_0_vector.
  specialize (s_closest_ub a r N m n k H H1) as H2.
  rewrite kron_assoc; auto with wf_db. rewrite kron_assoc; auto with wf_db.
  2, 4, 6 : rewrite kron_n_0_is_0_vector; apply basis_vector_WF; apply pow_positive; easy.
  2, 3 : apply ψ_WF_matrix with (m := m); easy.
  rewrite basis_f_to_vec_alt by easy.
  replace (2^n * 2^anc)%nat with (2^(n+anc))%nat by unify_pows_two.
  replace ((2^m * 2^n) * (2^anc))%nat with (2^m * (2^(n+anc)))%nat by unify_pows_two.
  Local Opaque QPE. simpl.
  apply QPE_semantics_full with (δ:=k / r - s_closest m k r / 2^m).
  destruct H as [_ [Horder [_ [Hn _]]]]. apply Order_N_lb in Horder. destruct n. simpl in Hn. lia. lia.
  destruct H as [_ [Horder [[Hm _] _]]]. apply Order_N_lb in Horder. simpl in Hm. assert (4 <= 2^m)%nat by nia. destruct m. simpl in H. lia. destruct m. simpl in H. lia. lia.
  assumption.
  rewrite kron_n_0_is_0_vector.
  replace (2^(n+anc))%nat with (2^n * 2^anc)%nat by unify_pows_two.
  apply ψ_basis_vector_pure_state with (m := m). assumption. apply pow_positive. lia.
  specialize (s_closest_is_closest _ _ _ _ _ _ H H1). replace (2 ^ (m + 1)) with (2 * 2 ^ m). lra.
  rewrite pow_add. lra.
  rewrite nat_to_funbool_inverse by easy.
  replace (2 * PI * (s_closest m k r / 2 ^ m + (k / r - s_closest m k r / 2 ^ m))) with (2 * PI * k / r) by lra.
  rewrite kron_n_0_is_0_vector. apply MC_eigenvalue with (m:=m); easy.
Qed.

Lemma full_meas_swap :
  forall {d} (ψ : Vector d) (ϕ : Vector d),
    probability_of_outcome ψ ϕ = probability_of_outcome ϕ ψ.
Proof.
  intros d ψ ϕ. unfold probability_of_outcome.
  replace ((ϕ) † × ψ) with ((ϕ) † × ((ψ) †) †) by (rewrite adjoint_involutive; easy).
  rewrite <- Mmult_adjoint.
  replace (((ψ) † × ϕ) † 0%nat 0%nat) with ((((ψ) † × ϕ) 0%nat 0%nat)^* ) by easy.
  rewrite Cmod_Cconj. easy.
Qed.

Lemma vsum_by_cell :
  forall {d n} (f : nat -> Vector d) x y,
    vsum n f x y = Csum (fun i => f i x y) n.
Proof.
  intros d n f x y. induction n.
  - easy.
  - rewrite vsum_extend_r. unfold Mplus. rewrite IHn. easy.
Qed.

Lemma basis_vector_decomp :
  forall {d} (ψ : Vector d),
    WF_Matrix ψ ->
    ψ = vsum d (fun i => (ψ i 0%nat) .* basis_vector d i).
Proof.
  intros d ψ WF. do 2 (apply functional_extensionality; intros). rewrite vsum_by_cell.
  destruct (x <? d) eqn:Hx.
  - apply Nat.ltb_lt in Hx. 
    unfold scale. destruct x0.
    + rewrite Csum_unique with (k:=ψ x 0%nat). easy.
      exists x. split. easy.
      split. unfold basis_vector. rewrite Nat.eqb_refl. simpl. lca.
      intros. unfold basis_vector. apply eqb_neq in H. rewrite H. simpl. lca.
    + unfold WF_Matrix in WF. rewrite WF by lia.
      rewrite Csum_0. easy. intro.
      unfold basis_vector. assert (S x0 <> 0)%nat by lia. apply eqb_neq in H.
      rewrite H. rewrite andb_false_r. lca.
  - apply Nat.ltb_ge in Hx.
    unfold WF_Matrix in WF. rewrite WF by lia.
    rewrite Csum_0_bounded. easy. intros. unfold scale.
    unfold basis_vector. assert (x <> x1) by lia. apply eqb_neq in H0.
    rewrite H0. simpl. lca.
Qed.

Lemma full_meas_decomp :
  forall {n m} (ψ : Vector (2^(m+n))) (ϕ1 : Vector (2^m)) (ϕ2 : Vector (2^n)),
    Pure_State_Vector ϕ2 ->
    probability_of_outcome (ϕ1 ⊗ ϕ2) ψ = Cmod (Csum (fun i => ((ϕ2 i 0%nat) .* @Mmult _ _ (1 * 1) (ψ †) (ϕ1 ⊗ (basis_vector (2^n) i))) 0%nat 0%nat) (2^n)) ^ 2.
Proof.
  intros n m ψ ϕ1 ϕ2 [HWF Hnorm]. rewrite full_meas_swap. unfold probability_of_outcome.
  assert (T: forall x y, x = y -> Cmod x ^ 2 = Cmod y ^ 2).
  { intros. rewrite H. easy. }
  apply T. clear T.
  replace (ϕ1 ⊗ ϕ2) with (ϕ1 ⊗ vsum (2^n) (fun i => (ϕ2 i 0%nat) .* basis_vector (2^n) i)) by (rewrite <- basis_vector_decomp; easy).
  rewrite kron_vsum_distr_l.
  rewrite <- Nat.pow_add_r. rewrite Mmult_vsum_distr_l.
  rewrite vsum_by_cell. apply Csum_eq. apply functional_extensionality. intros.
  rewrite Mscale_kron_dist_r. rewrite <- Mscale_mult_dist_r. easy.
Qed.

Lemma full_meas_equiv :
  forall {d} (ψ : Vector d),
    fst (((ψ) † × ψ) 0%nat 0%nat) = Rsum d (fun i => Cmod (ψ i 0%nat) ^ 2).
Proof.
  intros d ψ. unfold Mmult.
  replace (fun y : nat => ((ψ) † 0%nat y * ψ y 0%nat)%C) with (fun y : nat => RtoC (Cmod (ψ y 0%nat) ^ 2)).
  apply RtoC_Rsum_Csum.
  apply functional_extensionality. intros.
  unfold adjoint. rewrite <- Cmod_sqr. symmetry. apply RtoC_pow.
Qed.

Lemma Cmod_adjoint :
  forall {n m} (A : Matrix n m),
    (A 0%nat 0%nat) ^* = (A †) 0%nat 0%nat.
Proof.
  intros. easy.
Qed.

(* May be easier to prove this by rewriting with prob_partial_meas_alt -KH *)
Lemma partial_meas_prob_ge_full_meas :
  forall {n m} (ψ : Vector (2^(m+n))) (ϕ1 : Vector (2^m)) (ϕ2 : Vector (2^n)),
    Pure_State_Vector ϕ2 ->
    prob_partial_meas ϕ1 ψ >= probability_of_outcome (ϕ1 ⊗ ϕ2) ψ.
Proof.
  intros n m ψ ϕ1 ϕ2 H. rewrite full_meas_decomp by easy. unfold prob_partial_meas.
  assert (T: forall q w e, q = w -> w >= e -> q >= e) by (intros; lra).
  eapply T.
  2:{ unfold scale.
      erewrite Csum_eq.
      2:{ apply functional_extensionality. intros. rewrite <- (Cconj_involutive (ϕ2 x 0%nat)). reflexivity.
      }
      apply Cplx_Cauchy.
  }
  simpl.
  replace (fun i : nat => Cmod ((ϕ2 i 0%nat) ^* ) * (Cmod ((ϕ2 i 0%nat) ^* ) * 1)) with (fun i : nat => Cmod (ϕ2 i 0%nat) ^ 2).
  2:{ apply functional_extensionality; intros. simpl.
      rewrite Cmod_Cconj. easy.
  } 
  rewrite <- full_meas_equiv.
  destruct H as [WF H]. rewrite H. simpl. rewrite Rmult_1_l.
  apply Rsum_eq. intros.
  unfold probability_of_outcome.
  rewrite <- Cmod_Cconj. rewrite Cmod_adjoint. rewrite Mmult_adjoint. rewrite adjoint_involutive.
  unfold pow.
  restore_dims.
  reflexivity.
Qed.

Lemma QPE_MC_correct :
  forall (a r N k m n anc : nat) (c : base_ucom (n + anc)),
    BasicSetting a r N m n ->
    MultiplyCircuitProperty a N n anc c ->
    uc_well_typed c ->
    (0 <= k < r)%nat ->
    prob_partial_meas (basis_vector (2^m) (s_closest m k r)) ((uc_eval (QPE m (n + anc) c)) × ((basis_vector (2^m) 0) ⊗ (basis_vector (2^n) 1) ⊗ (basis_vector (2^anc) 0))) >= 4 / (PI ^ 2 * r).
Proof.
  intros. rewrite <- kron_n_0_is_0_vector.
  rewrite <- (sum_of_ψ_is_one a r N m) by easy.
  rewrite Mscale_kron_dist_r. rewrite kron_vsum_distr_l. rewrite <- Nat.pow_add_r.
  simpl. distribute_scale. rewrite kron_vsum_distr_r.
  replace (2^(m+n)*2^anc)%nat with (2^(m + (n+anc)))%nat by unify_pows_two.
  rewrite Mmult_vsum_distr_l.
  eapply Rge_trans. apply partial_meas_prob_ge_full_meas.
  replace (2^(n+anc))%nat with (2^n * 2^anc)%nat by unify_pows_two.
  apply ψ_basis_vector_pure_state with (m := m) (j := k). apply H. apply pow_positive. lia.
  unfold probability_of_outcome.
  restore_dims. distribute_scale.
  rewrite kron_adjoint. do 2 rewrite Nat.pow_add_r. rewrite Mmult_vsum_distr_l.
  erewrite vsum_unique.
  2:{ exists k. split. lia. split. reflexivity. intros.
      assert (T: forall {o m n} (A : Matrix o m) (B C : Matrix m n), B = C -> A × B = A × C) by (intros o m0 n0 A B C HT; rewrite HT; easy).
      erewrite T.
      2:{ rewrite <- Nat.pow_add_r.
          restore_dims. rewrite kron_assoc.
          2: rewrite kron_n_0_is_0_vector; restore_dims; apply basis_vector_WF; apply pow_positive; easy.
          2: apply ψ_WF_matrix with (m := m); easy.
          2: apply basis_vector_WF; apply pow_positive; easy.
          replace (2^n * 2^anc)%nat with (2^(n+anc))%nat by unify_pows_two.
          apply QPE_simplify.
          destruct H as [HN [_ [_ Hn]]]. assert (2 <= 2 ^ n)%nat by lia. destruct n; simpl in H; lia.
          destruct H as [HN [_ [Hm _]]]. simpl in Hm. assert (4 <= 2 ^ m)%nat by nia. destruct m. simpl in H. lia. destruct m. simpl in H. lia. lia.
          easy.
          replace (2^(n+anc))%nat with (2^n * 2^anc)%nat by unify_pows_two.
          apply ψ_basis_vector_pure_state with (m := m). assumption. apply pow_positive. lia.
          rewrite MC_eigenvalue with (m:=m) by easy.
          replace (2 * PI * j / r) with (2 * PI * (j / r)) by lra. easy.
      }
      restore_dims. rewrite kron_mixed_product.
      rewrite kron_adjoint. rewrite kron_mixed_product.
      rewrite ψ_perp_neq with (m:=m); try easy; try lia. Msimpl. easy.
  }
  assert (INR r > 0).
  { destruct H as [_ [[Hr _] _]]. apply lt_INR in Hr. simpl in Hr. lra.
  }
  assert (0 < √ r) by (apply sqrt_lt_R0; lra).
  unfold scale. rewrite Cmod_mult. rewrite <- RtoC_div by lra. rewrite Cmod_R. rewrite Rpow_mult_distr. rewrite pow2_abs.
  replace (1 / √ r) with (/ √ r) by lra. rewrite <- sqrt_inv by lra. rewrite pow2_sqrt.
  2:{ apply Rlt_le. nonzero.
  }
  replace (4 / (PI * (PI * 1) * r)) with (/r * (4 / (PI ^ 2))).
  2:{ replace (/ r * (4 / PI ^ 2)) with (4 * ((/ PI ^2) * (/r))) by lra. rewrite <- Rinv_mult_distr. easy.
      apply pow_nonzero. apply PI_neq0. lra.
  }
  apply Rmult_ge_compat_l. apply Rinv_0_lt_compat in H3. lra.
  rewrite <- kron_adjoint. rewrite kron_n_0_is_0_vector. rewrite <- Nat.pow_add_r. 
  restore_dims.
  rewrite <- kron_assoc; restore_dims. apply QPE_MC_partial_correct; easy.
  apply basis_vector_WF; apply (s_closest_ub a _ N _ n _); easy.
  apply ψ_WF_matrix with (m := m); easy.
  apply basis_vector_WF; apply pow_positive; easy.
Qed.

Lemma QPE_MMI_correct :
  forall (a r N k m n anc : nat) (f : nat -> base_ucom (n + anc)),
    BasicSetting a r N m n ->
    ModMulImpl a N n anc f ->
    (forall i, (i < m)%nat -> uc_well_typed (f i)) ->
    (0 <= k < r)%nat ->
    prob_partial_meas (basis_vector (2^m) (s_closest m k r)) ((uc_eval (QPE_var m (n + anc) f)) × ((basis_vector (2^m) 0) ⊗ (basis_vector (2^n) 1) ⊗ (basis_vector (2^anc) 0))) >= 4 / (PI ^ 2 * r).
Proof.
  Local Opaque QPE_var pow.
  intros. remember (f O) as c.
  rewrite <- (sum_of_ψ_is_one a r N m) by easy.
  distribute_scale. rewrite kron_vsum_distr_l. rewrite <- Nat.pow_add_r.
  simpl. distribute_scale. rewrite kron_vsum_distr_r.
  replace (2^(m+n)*2^anc)%nat with (2^(m + (n+anc)))%nat by unify_pows_two.
  rewrite Mmult_vsum_distr_l.
  erewrite vsum_eq.
  2:{ intros j Hj. restore_dims.
      rewrite kron_assoc.
      2, 4 : apply basis_vector_WF; apply pow_positive; easy.
      2 : apply ψ_WF_matrix with (m := m); easy.
      rewrite <- kron_n_0_is_0_vector.
      specialize (QPE_var_equivalent m (n + anc) c f (ψ a r N j n ⊗ basis_vector (2 ^ anc) 0) (j / r)) as G.
      replace (2^n * 2^anc)%nat with (2^(n+anc))%nat by unify_pows_two.
      simpl. simpl in G. rewrite Nat.pow_1_l in G. rewrite <- G.
      reflexivity.
      destruct H as [HN [_ [_ [Hn _ ]]]]. assert (2 ^ n >= 2)%nat by lia. destruct n. simpl in H. lia. lia.
      assert (0 < 2^anc)%nat by (apply pow_positive; lia).
      specialize (ψ_basis_vector_pure_state a r N m n j O (2^anc)%nat H H3) as [G' _]. replace (2^n * 2^anc)%nat with (2^(n+anc))%nat in G' by unify_pows_two. easy.
      rewrite Heqc. apply H1. destruct H as [HN [_ [[Hm _] _]]]. destruct m. simpl in Hm. nia. lia.
      specialize (H0 O). subst. simpl in H0. rewrite Nat.mul_1_r in H0.
      replace (2 * PI * (j / r)) with (2 * PI * j / r) by lra. apply MC_eigenvalue with (m := m). easy. unfold MultiplyCircuitProperty. apply H0.
      apply H1.
      intros. replace (2 * PI * (j / r)) with (2 * PI * j / r) by lra. apply MMI_eigen with (m := m); easy.
  }
  specialize (H0 O) as Hc. rewrite <- Heqc in Hc. simpl in Hc. rewrite Nat.mul_1_r in Hc.
  assert (uc_well_typed c).
  { rewrite Heqc; apply H1.
    destruct H as [HN [_ [[Hm _] _]]]. destruct m. simpl in Hm. nia. lia.
  }
  specialize (QPE_MC_correct a r N k m n anc c H Hc H3 H2).
  rewrite <- (sum_of_ψ_is_one a r N m) by easy.
  distribute_scale. rewrite kron_vsum_distr_l. rewrite <- Nat.pow_add_r.
  simpl. distribute_scale. rewrite kron_vsum_distr_r.
  replace (2^(m+n)*2^anc)%nat with (2^(m + (n+anc)))%nat by unify_pows_two.
  rewrite Mmult_vsum_distr_l.
  rewrite kron_n_0_is_0_vector.
  erewrite vsum_eq.
  2:{ intros. restore_dims. rewrite kron_assoc.
      2, 4 : apply basis_vector_WF; apply pow_positive; easy.
      2 : apply ψ_WF_matrix with (m := m); easy.
      reflexivity.
  }
  replace (2^(n+anc))%nat with (2^n*2^anc)%nat by unify_pows_two.
  easy.
Qed.
  

(* ================================================ *)
(* =   The post-processings of Shor's algorithm   = *)
(* ================================================ *)


(* "Partial correct" of ContinuedFraction function. "Partial" because it is exactly correct only when k and r are coprime. Otherwise it will output (p, q) such that p/q=k/r. *)
Lemma Shor_partial_correct :
  forall a r N k m n : nat,
    BasicSetting a r N m n ->
    (0 <= k < r)%nat ->
    rel_prime k r ->
    exists step,
      (step < 2 * m + 2)%nat /\
      OF_post_step step (s_closest m k r) m = r.
Proof.
  intros. unfold OF_post_step.
  replace (2 * m + 2)%nat with (2 * (Nat.log2 (2^m) + 1))%nat by (rewrite Nat.log2_pow2; lia).
  apply Legendre_ContinuedFraction with (p := k).
  lia. apply s_closest_ub with (a := a) (N := N) (n := n); easy.
  replace (INR (2 ^ m)) with (2 ^ m) by (rewrite pow_INR; easy).
  specialize (s_closest_Rabs a r N m n k H H0) as G.
  eapply Rle_lt_trans. apply G. unfold Rdiv. do 2 rewrite Rmult_1_l.
  assert (0 < r)%nat by lia. apply lt_INR in H2. simpl in H2.
  apply Rinv_lt_contravar.
  nonzero.
  apply Rmult_lt_compat_l. lra. destruct H as [_ [HOrder [[Hm _] _]]]. specialize (Order_r_lt_N a r N HOrder) as Hr. apply lt_INR in Hm. apply lt_INR in Hr. do 2 rewrite pow_INR in Hm.
  assert (r ^ 2 < N ^ 2) by nra.
  replace (INR 2) with 2 in Hm by (simpl; lra).
  nra.
  easy.
Qed.

Lemma OF_post_step_inc :
  forall s1 s2 o m,
    (s1 <= s2)%nat ->
    (o < 2^m)%nat ->
    (OF_post_step s1 o m <= OF_post_step s2 o m)%nat.
Proof.
  intros. unfold OF_post_step, ContinuedFraction.
  specialize (CF_ite_CFpq s1 0 o (2 ^ m) H0) as G. unfold nthmodseq in G. simpl in G. rewrite G. clear G.
  specialize (CF_ite_CFpq s2 0 o (2 ^ m) H0) as G. unfold nthmodseq in G. simpl in G. rewrite G. clear G.
  simpl.
  specialize (CFq_inc (s2 - s1)%nat (s1 + 1)%nat o (2^m)%nat H0) as G.
  replace (s2 - s1 + (s1 + 1))%nat with (s2 + 1)%nat in G by lia.
  lia.
Qed.

Lemma OF_post'_nonzero_equal :
  forall x step a N o m,
    (OF_post' step a N o m <> 0)%nat ->
    OF_post' (x + step) a N o m = OF_post' step a N o m.
Proof.
  induction x; intros. easy.
  replace (S x + step)%nat with (S (x + step))%nat by lia.
  simpl. rewrite IHx by easy. apply Nat.eqb_neq in H. rewrite H. easy.
Qed.

Lemma OF_post'_nonzero_pre :
  forall step a N o m,
    (OF_post' step a N o m <> 0)%nat ->
    exists x, (x < step)%nat /\ OF_post_step x o m = OF_post' step a N o m.
Proof.
  induction step; intros. easy.
  simpl in *.
  bdestruct (OF_post' step a N o m =? 0).
  - exists step. split. lia.
    IfExpSimpl. 
  - apply IHstep in H. destruct H as [x [H1 H2]]. exists x.
    split. lia. easy.
Qed.

Lemma OF_post_step_r_aux :
  forall a r N m o step,
    Order a r N ->
    OF_post_step step o m = r ->
    (OF_post' (S step) a N o m <> 0)%nat.
Proof.
  intros. simpl.
  bdestruct (OF_post' step a N o m =? 0).
  - rewrite H0. destruct H as [? [? ?]]. 
    unfold modexp. rewrite H2, Nat.eqb_refl. lia.
  - easy.
Qed.

Lemma OF_post'_pow :
  forall a N o m step,
    (1 < N)%nat ->
    (a ^ (OF_post' step a N o m) mod N = 1)%nat.
Proof.
  intros. induction step. simpl. apply Nat.mod_small. easy.
  simpl. bdestruct (OF_post' step a N o m =? 0).
  unfold modexp.
  bdestruct (a ^ OF_post_step step o m mod N =? 1). easy.
  simpl. apply Nat.mod_small. easy.
  apply IHstep.
Qed.

Lemma OF_post_step_r :
  forall a r N m o step,
    Order a r N ->
    (o < 2 ^ m)%nat ->
    OF_post_step step o m = r ->
    OF_post' (S step) a N o m = r.
Proof.
  intros.
  assert (OF_post' (S step) a N o m <> 0)%nat by (apply OF_post_step_r_aux with (r := r); easy).
  assert (H3 := H2). apply OF_post'_nonzero_pre in H2. destruct H2 as [x [? ?]].
  assert (OF_post_step x o m <= r)%nat. {
    rewrite <- H1. apply OF_post_step_inc. lia. easy.
  }
  assert (1 < N)%nat by (apply Order_N_lb with (a := a) (r := r); easy).
  destruct H as [Hr [Hp Hq]].
  assert (OF_post' (S step) a N o m >= r)%nat. {
    apply Hq. split. lia.
    apply OF_post'_pow. easy.
  }
  lia.
Qed.

Lemma r_found_1 :
  forall a r N k m n : nat,
    BasicSetting a r N m n ->
    (0 <= k < r)%nat ->
    rel_prime k r ->
    r_found (s_closest m k r) m r a N = 1.
Proof.
  intros. unfold r_found, OF_post.
  destruct (Shor_partial_correct a r N k m n) as [x [? ?]]; auto.
  apply OF_post_step_r with (a := a) (N := N) in H3.
  assert (OF_post' (S x) a N (s_closest m k r) m = OF_post' ((2 * m + 2 - (S x)) + (S x)) a N (s_closest m k r) m). {
    symmetry. apply OF_post'_nonzero_equal. rewrite H3. lia.
  }
  replace (2 * m + 2 - S x + S x)%nat with (2 * m + 2)%nat in H4 by lia.
  rewrite <- H4, H3, Nat.eqb_refl. easy.
  destruct H as [_ [H _]]. easy.
  eapply s_closest_ub. apply H. easy.
Qed.

(* constant used in correctness stmt ~ 0.055 *)
Definition κ := 4 * exp(-2) / (PI ^ 2). 

(* The correctness specification. It succeed with prob proportional to 1/(log N)^4, which is asymptotically small, but big enough in practice (poly time).
   With better technique (calculate the LCM of multiple outputs), the number of rounds may be reduced to constant. But I don't know how to specify that, and the analysis in Shor's original paper refers the correctness to "personal communication" with Knill. *)
Lemma Shor_correct : forall (a r N m n anc : nat) (c : base_ucom (n + anc)),
  BasicSetting a r N m n ->
  MultiplyCircuitProperty a N n anc c ->
  uc_well_typed c ->
  probability_of_success a r N m n anc c >= κ / (Nat.log2 N)^4.
Proof.
  specialize (ϕ_n_over_n_lowerbound) as Heuler.
  assert (Hκ : exp(-2) > 0) by (subst; apply exp_pos).
  unfold probability_of_success. unfold Shor_final_state.
  intros. rename H1 into H2. assert (H1 : (r > 0)%nat) by (destruct H as [_ [[Hr _] _]]; lia).
  remember (fun x : nat =>
              r_found x m r a N *
              prob_partial_meas (basis_vector (2 ^ m) x)
                                (uc_eval (QPE m (n + anc) c) × (basis_vector (2 ^ m) 0 ⊗ basis_vector (2 ^ n) 1 ⊗ basis_vector (2 ^ anc) 0))) as f.
  cut (Rsum (2^m) f >= Rsum r (fun i => f (s_closest m i r))).
  intros. eapply Rge_trans. apply H3. destruct r. inversion H1. simpl.
  set (g := (fun i : nat => (if rel_prime_dec i (S r) then 1 else 0) * prob_partial_meas (basis_vector (2 ^ m) (s_closest m i (S r)))
                                                                                    (uc_eval (QPE m (n + anc) c) × (basis_vector (2 ^ m) 0 ⊗ basis_vector (2 ^ n) 1 ⊗ basis_vector (2 ^ anc) 0)))).
  cut (forall i : nat, (i <= r)%nat -> g i <= f (s_closest m i (S r))).
  intros. eapply Rge_trans. apply Rle_ge. apply sum_Rle. apply H4.
  cut (forall i : nat, (i <= r)%nat -> (fun i : nat => (if rel_prime_dec i (S r) then 1 else 0) * (4 / (PI ^ 2 * (S r)))) i <= g i).
  intros. eapply Rge_trans. apply Rle_ge. apply sum_Rle. apply H5.
  rewrite <- scal_sum. unfold ϕ in Heuler.
  remember (sum_f_R0 (fun i : nat => if rel_prime_dec i (S r) then 1 else 0) r) as t.
  assert (t / (S r) >= exp(-2) / (Nat.log2 N^4)).
  { subst. replace (sum_f_R0 (fun i : nat => if rel_prime_dec i (S r) then 1 else 0) r) with (Rsum (S r) (fun i : nat => if rel_prime_dec i (S r) then 1 else 0)).
    destruct r. simpl. replace (1 / 1) with (1 * 1) by lra.
    assert (1 <= Nat.log2 N)%nat.
    { destruct H as [HN _]. assert (2 <= N)%nat by lia.
      specialize (Nat.log2_le_mono _ _ H) as G. rewrite Nat.log2_2 in G. easy.
    }
    apply le_INR in H6. simpl in H6.
    assert (1 <= exp 2) by interval.
    unfold Rdiv. apply Rle_ge.
    apply Rmult_le_compat. lra.
    rewrite <- Rmult_1_l. apply Rle_mult_inv_pos. lra. interval.
    replace (-2) with (Ropp 2) by lra. rewrite exp_Ropp.
    replace 1 with (/ 1) by lra. apply Rle_Rinv; lra.
    replace 1 with (/ 1) by lra. apply Rle_Rinv; try interval. 
    interval with (i_prec 53). (* idk why we need i_prec 53 -KH *)
    rename r into r'. remember (S r') as r.
    eapply Rge_trans. apply Heuler. lia.
    assert ((Nat.log2 (S r) ^ 4) <= (Nat.log2 N ^ 4)).
    do 2 rewrite <- pow_INR. apply le_INR. apply Nat.pow_le_mono_l. apply Nat.log2_le_mono. destruct H. destruct H6. apply Nat.lt_le_incl. 
    apply Order_r_lt_N with a. auto.
    repeat rewrite Rdiv_unfold. apply Raux.Rinv_le in H6. apply Rmult_ge_compat_l. lra. lra. replace 0 with (INR 0%nat) by auto.
    rewrite <- pow_INR. apply lt_INR. cut (1 <= (Nat.log2 (S r)) ^ 4)%nat. lia. eapply Nat.le_trans.
    assert (1 <= (Nat.log2 2) ^ 4)%nat. unfold Nat.log2. simpl. lia. apply H7.
    apply Nat.pow_le_mono_l. apply Nat.log2_le_mono. lia.
    reflexivity.
  }
  unfold κ.
  repeat rewrite Rdiv_unfold. repeat rewrite Rinv_mult_distr. repeat rewrite Rdiv_unfold in H6.
  replace (4 * (/ PI ^ 2 * / S r) * t) with ((4 * / PI ^ 2) * (t * / S r)) by lra.
  replace ( 4 * exp(-2) * / PI ^ 2 * / (Nat.log2 N)^4) with ((4 * / PI ^ 2) * (exp(-2) * / (Nat.log2 N)^4)) by lra.
  apply Rmult_ge_compat_l. interval. easy. interval. replace 0 with (INR 0%nat) by auto. apply not_INR. lia. 
  - intros. destruct (rel_prime_dec i (S r)) eqn:He; unfold g; rewrite He. repeat rewrite Rmult_1_l.
    apply Rge_le. apply (QPE_MC_correct a _ N _ _ _); try lia; auto.
    repeat rewrite Rmult_0_l. lra.
  - intros. unfold g. rewrite Heqf. remember (prob_partial_meas (basis_vector (2 ^ m) (s_closest m i (S r)))
                                                                (uc_eval (QPE m (n + anc) c) × (basis_vector (2 ^ m) 0 ⊗ basis_vector (2 ^ n) 1 ⊗ basis_vector (2 ^ anc) 0))) as fi.
    destruct (rel_prime_dec i (S r)). rewrite r_found_1 with a _ N _ _ n; try lra; try lia; try easy.
    rewrite Rmult_0_l. apply Rmult_le_pos. unfold r_found. destruct (OF_post a N (s_closest m i (S r)) m =? S r); lra.
    subst. unfold prob_partial_meas. unfold Rsum. replace (2 ^ (n + anc))%nat with (S (pred (2 ^ (n + anc)))).
    apply cond_pos_sum. intros. unfold probability_of_outcome. interval.
    simpl. rewrite Nat.succ_pred_pos. easy. apply pow_positive. lia.
  - replace (2 ^ m)%nat with (S (pred (2 ^ m))).
    assert (forall i, 0 <= f i).
    { intros. subst. unfold r_found, prob_partial_meas, probability_of_outcome. apply Rmult_le_pos.
      destruct (OF_post a N i m =? r); lra.
      unfold Rsum. replace (2 ^ (n+anc))%nat with (S (pred (2 ^ (n+anc)))).
      apply cond_pos_sum. intros. interval. rewrite Nat.succ_pred_pos. easy. apply pow_positive. lia.
    }
    assert (r < N)%nat.
    apply Order_r_lt_N with a. destruct H. now destruct H4.
    assert (N <= N^2)%nat. rewrite <- Nat.pow_1_r at 1. apply Nat.pow_le_mono_r; try lia. 
    destruct r. 
    + (* r = 0 *)
      apply Rle_ge. apply cond_pos_sum. apply H3.
    + simpl. apply Rle_ge. apply rsum_subset.
      -- destruct H. apply lt_INR. lia. 
      -- auto.
      -- intros. assert (0 <= i < S r)%nat by lia. specialize (s_closest_ub a (S r) N m n i H H7) as G. lia. (*destruct H as (Ha & Hb & Hc & Hd). intros. lia.*)
      -- intros. apply s_closest_injective with a (S r) N m n; try lia; auto.
         rewrite Nat.succ_pred_pos. easy. apply pow_positive. lia.
Qed.

Lemma Shor_correct_var : forall (a r N m n anc : nat) (u : nat -> base_ucom (n + anc)),
      BasicSetting a r N m n ->
      ModMulImpl a N n anc u ->
      (forall i, (i < m)%nat -> uc_well_typed (u i)) ->
      probability_of_success_var a r N m n anc u >= κ / (Nat.log2 N)^4.
Proof.
  specialize (ϕ_n_over_n_lowerbound) as Heuler.
  assert (Hκ : exp(-2) > 0) by (subst; apply exp_pos).
  unfold probability_of_success_var. unfold Shor_final_state_var.
  intros. rename H1 into H2. assert (H1 : (r > 0)%nat) by (destruct H as [_ [[Hr _] _]]; lia).
  remember (fun x : nat =>
              r_found x m r a N *
              prob_partial_meas (basis_vector (2 ^ m) x)
                                (uc_eval (QPE_var m (n + anc) u) × (basis_vector (2 ^ m) 0 ⊗ basis_vector (2 ^ n) 1 ⊗ basis_vector (2 ^ anc) 0))) as f.
  cut (Rsum (2^m) f >= Rsum r (fun i => f (s_closest m i r))).
  intros. eapply Rge_trans. apply H3. destruct r. inversion H1. simpl.
  set (g := (fun i : nat => (if rel_prime_dec i (S r) then 1 else 0) * prob_partial_meas (basis_vector (2 ^ m) (s_closest m i (S r)))
                                                                                    (uc_eval (QPE_var m (n + anc) u) × (basis_vector (2 ^ m) 0 ⊗ basis_vector (2 ^ n) 1 ⊗ basis_vector (2 ^ anc) 0)))).
  cut (forall i : nat, (i <= r)%nat -> g i <= f (s_closest m i (S r))).
  intros. eapply Rge_trans. apply Rle_ge. apply sum_Rle. apply H4.
  cut (forall i : nat, (i <= r)%nat -> (fun i : nat => (if rel_prime_dec i (S r) then 1 else 0) * (4 / (PI ^ 2 * (S r)))) i <= g i).
  intros. eapply Rge_trans. apply Rle_ge. apply sum_Rle. apply H5.
  rewrite <- scal_sum. unfold ϕ in Heuler.
  remember (sum_f_R0 (fun i : nat => if rel_prime_dec i (S r) then 1 else 0) r) as t.
  assert (t / (S r) >= exp(-2) / (Nat.log2 N^4)).
  { subst. replace (sum_f_R0 (fun i : nat => if rel_prime_dec i (S r) then 1 else 0) r) with (Rsum (S r) (fun i : nat => if rel_prime_dec i (S r) then 1 else 0)).
    destruct r. simpl. replace (1 / 1) with (1 * 1) by lra.
    assert (1 <= Nat.log2 N)%nat.
    { destruct H as [HN _]. assert (2 <= N)%nat by lia.
      specialize (Nat.log2_le_mono _ _ H) as G. rewrite Nat.log2_2 in G. easy.
    }
    apply le_INR in H6. simpl in H6.
    assert (1 <= exp 2) by interval.
    unfold Rdiv. apply Rle_ge.
    apply Rmult_le_compat. lra.
    rewrite <- Rmult_1_l. apply Rle_mult_inv_pos. lra. interval.
    replace (-2) with (Ropp 2) by lra. rewrite exp_Ropp.
    replace 1 with (/ 1) by lra. apply Rle_Rinv; lra.
    replace 1 with (/ 1) by lra. apply Rle_Rinv; try interval.
    interval with (i_prec 53). (* idk why we need i_prec 53 -KH *)
    rename r into r'. remember (S r') as r.
    eapply Rge_trans. apply Heuler. lia.
    assert ((Nat.log2 (S r) ^ 4) <= (Nat.log2 N ^ 4)).
    do 2 rewrite <- pow_INR. apply le_INR. apply Nat.pow_le_mono_l. apply Nat.log2_le_mono. destruct H. destruct H6. apply Nat.lt_le_incl. 
    apply Order_r_lt_N with a. auto.
    repeat rewrite Rdiv_unfold. apply Raux.Rinv_le in H6. apply Rmult_ge_compat_l. lra. lra. replace 0 with (INR 0%nat) by auto.
    rewrite <- pow_INR. apply lt_INR. cut (1 <= (Nat.log2 (S r)) ^ 4)%nat. lia. eapply Nat.le_trans.
    assert (1 <= (Nat.log2 2) ^ 4)%nat. unfold Nat.log2. simpl. lia. apply H7.
    apply Nat.pow_le_mono_l. apply Nat.log2_le_mono. lia.
    reflexivity.
  }
  unfold κ.
  repeat rewrite Rdiv_unfold. repeat rewrite Rinv_mult_distr. repeat rewrite Rdiv_unfold in H6.
  replace (4 * (/ PI ^ 2 * / S r) * t) with ((4 * / PI ^ 2) * (t * / S r)) by lra.
  replace ( 4 * exp(-2) * / PI ^ 2 * / (Nat.log2 N)^4) with ((4 * / PI ^ 2) * (exp(-2) * / (Nat.log2 N)^4)) by lra.
  apply Rmult_ge_compat_l. interval. easy. interval. replace 0 with (INR 0%nat) by auto. apply not_INR. lia. 
  - intros. destruct (rel_prime_dec i (S r)) eqn:He; unfold g; rewrite He. repeat rewrite Rmult_1_l.
    apply Rge_le. apply (QPE_MMI_correct a _ N _ _ _); try lia; auto.
    repeat rewrite Rmult_0_l. lra.
  - intros. unfold g. rewrite Heqf. remember (prob_partial_meas (basis_vector (2 ^ m) (s_closest m i (S r)))
                                                                (uc_eval (QPE_var m (n + anc) u) × (basis_vector (2 ^ m) 0 ⊗ basis_vector (2 ^ n) 1 ⊗ basis_vector (2 ^ anc) 0))) as fi.
    destruct (rel_prime_dec i (S r)). rewrite r_found_1 with a _ N _ _ n; try lra; try lia; try easy.
    rewrite Rmult_0_l. apply Rmult_le_pos. unfold r_found. destruct (OF_post a N (s_closest m i (S r)) m =? S r); lra.
    subst. unfold prob_partial_meas. unfold Rsum. replace (2 ^ (n + anc))%nat with (S (pred (2 ^ (n + anc)))).
    apply cond_pos_sum. intros. unfold probability_of_outcome. interval.
    simpl. rewrite Nat.succ_pred_pos. easy. apply pow_positive. lia.
  - replace (2 ^ m)%nat with (S (pred (2 ^ m))).
    assert (forall i, 0 <= f i).
    { intros. subst. unfold r_found, prob_partial_meas, probability_of_outcome. apply Rmult_le_pos.
      destruct (OF_post a N i m =? r); lra.
      unfold Rsum. replace (2 ^ (n+anc))%nat with (S (pred (2 ^ (n+anc)))).
      apply cond_pos_sum. intros. interval. rewrite Nat.succ_pred_pos. easy. apply pow_positive. lia.
    }
    assert (r < N)%nat.
    apply Order_r_lt_N with a. destruct H. now destruct H4.
    assert (N <= N^2)%nat. rewrite <- Nat.pow_1_r at 1. apply Nat.pow_le_mono_r; try lia. 
    destruct r. 
    + (* r = 0 *)
      apply Rle_ge. apply cond_pos_sum. apply H3.
    + simpl. apply Rle_ge. apply rsum_subset.
      -- destruct H. apply lt_INR. lia. 
      -- auto.
      -- intros. assert (0 <= i < S r)%nat by lia. specialize (s_closest_ub a (S r) N m n i H H7) as G. lia. (*destruct H as (Ha & Hb & Hc & Hd). intros. lia.*)
      -- intros. apply s_closest_injective with a (S r) N m n; try lia; auto.
         rewrite Nat.succ_pred_pos. easy. apply pow_positive. lia.
Qed.

Lemma Shor_correct_full_implementation : forall (a N : nat),
      (0 < a < N)%nat ->
      (Nat.gcd a N = 1)%nat ->
      let m := Nat.log2 (2 * N^2)%nat in
      (*let n := Nat.log2_up N in*)
      let n := Nat.log2 (2 * N)%nat in
      probability_of_success_var a (ord a N) N m n (modmult_rev_anc n) (f_modmult_circuit a (modinv a N) N n) >= κ / (Nat.log2 N)^4.
Proof.
  specialize Shor_correct_var as H.
  intros.
  remember (ord a N) as r.
  assert (Order a r N). {
    subst. apply ord_Order; lia.
  }
  assert (BasicSetting a r N m n).
  { unfold BasicSetting. split. easy. split. easy. split.
    assert (m = S (Nat.log2 (N^2))) by (apply Nat.log2_double; simpl; nia).
    split. rewrite H3. apply Nat.log2_spec. simpl. nia.
    apply Nat.log2_spec. simpl. nia.
    assert (n = S (Nat.log2 N)) by (apply Nat.log2_double; simpl; nia).
    split. rewrite H3. apply Nat.log2_spec. simpl. nia.
    apply Nat.log2_spec. simpl. nia.
  }
  assert (modinv a N < N)%nat by (apply modinv_upper_bound; lia).
  assert (a * (modinv a N) mod N = 1)%nat by (apply Order_modinv_correct with (r := r); easy).
  apply H; try easy.
  apply f_modmult_circuit_MMI with (r := r) (m := m); easy.
  destruct H3 as [Ha [_ [_ HN]]].
  intros. apply f_modmult_circuit_uc_well_typed; try easy; try lia.
Qed.

(* Print Assumptions Shor_correct_full_implementation. *)
