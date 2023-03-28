Require Import SQIR.UnitaryOps.
Require Import QuantumLib.Matrix.
Require Import QuantumLib.Measurement.

Open Scope ucom.
Local Open Scope C_scope.
Local Open Scope R_scope.

Local Coercion Nat.b2n : bool >-> nat.

(* Utility function *)
Lemma times_n_C : forall (c : Complex.C) n, times_n c n = (INR n * c)%C.
Proof.
  intros c n. 
  induction n; simpl. 
  lca. 
  rewrite IHn.
  destruct n; lca.
Qed.

(* Bernstein Vazirani circuit *)
Definition bernstein_vazirani {n} (U : base_ucom n) : base_ucom n :=
    npar n U_H; U; npar n U_H.

(* Definition of the function the oracle will implement *)
(* This is f(s, x) = s . x mod 2 *)
Definition bitwise_xor n x y := 
  let n1f := nat_to_funbool n x in
  let n2f := nat_to_funbool n y in
  funbool_to_nat n (fun i => xorb (n1f i) (n2f i)).

Definition bitwise_product n x y :=
  Nat.b2n (product (nat_to_funbool n x) (nat_to_funbool n y) n).

(* Definition of phase oracle U : ∣ x ⟩ ↦ (-1) ^ (f(s, x)) ∣ x ⟩ *)
Definition phase_oracle {n} (U : base_ucom n) f :=
    forall (x : nat), (x < 2 ^ n)%nat ->
    @Mmult _ _ 1 (uc_eval U) (basis_vector (2 ^ n) x) = 
            (-1) ^ (f x) .* basis_vector (2 ^ n) x. 

(* Probability of measuring ∣ s ⟩ is 1 *)
Lemma bernstein_vazirani_is_correct :
    forall {n : nat} (U : base_ucom n) (s : nat),
    (n > 0)%nat -> (s < 2 ^ n)%nat -> phase_oracle U (bitwise_product n s) ->
    probability_of_outcome (basis_vector (2 ^ n) s) (uc_eval (bernstein_vazirani U) × (n ⨂ ∣0⟩)) = 1.
Proof.
    intros.
    unfold bernstein_vazirani.
    simpl uc_eval.
    rewrite npar_H by lia.
    repeat (rewrite Mmult_assoc; restore_dims).
    rewrite H0_kron_n_spec_alt by auto.
    restore_dims; distribute_scale.
    repeat rewrite Mmult_Msum_distr_l. 
    erewrite big_sum_eq_bounded.
    2: { intros.
        unfold phase_oracle in H1.
        rewrite (H1 x) by assumption.
        distribute_scale.
        reflexivity.
    }
    unfold probability_of_outcome, inner_product.
    distribute_scale.
    rewrite Mmult_Msum_distr_l.
    erewrite big_sum_eq_bounded.
    2: { intros.
        replace (basis_vector (2 ^ n) x) with (f_to_vec n (nat_to_funbool n x)).
        2: { rewrite basis_f_to_vec_alt by assumption; reflexivity. }
        rewrite H_kron_n_spec by assumption.
        distribute_scale.
        rewrite Cmult_comm.
        rewrite Mmult_Msum_distr_l.
        erewrite big_sum_unique.
        2: { exists s. 
            split; [lia | split].
            distribute_scale. 
            rewrite basis_vector_product_eq by lia.
            reflexivity.
            intros j ? ?.
            distribute_scale. 
            rewrite basis_vector_product_neq by lia.
            lma. }
        distribute_scale.
        unfold bitwise_product.
        reflexivity.
    }
    rewrite Mscale_Msum_distr_l.
    rewrite Mscale_assoc.
    erewrite big_sum_eq_bounded.
    2: { intros.
        rewrite product_comm.
        assert (forall a, (/ √ (2 ^ n) * (-1) ^ a * (-1) ^ a)%C = (/ √ (2 ^ n))%C).
        1: { intros.
            induction a.
            simpl; repeat rewrite Cmult_1_r; reflexivity.
            simpl.
            replace (/ √ (2 ^ n) * (-1 * (-1) ^ a) * (-1 * (-1) ^ a))%C with (/ √ (2 ^ n) * (-1) ^ a * (-1) ^ a)%C.
            rewrite IHa; reflexivity.
            repeat rewrite Cmult_assoc.
            rewrite (Cmult_comm (/ √ (2 ^ n) * -1 * (-1) ^ a )).
            repeat rewrite Cmult_assoc.
            rewrite (Cmult_comm (-1 * / √ (2 ^ n) )).
            repeat rewrite Cmult_assoc.
            replace (-1 * -1)%C with C1.
            rewrite Cmult_1_l; reflexivity.
            unfold C1, Cmult; simpl.
            repeat rewrite Rmult_0_l; rewrite Rmult_0_r, Rplus_0_l.
            unfold Rminus; rewrite Ropp_0, Rplus_0_r.
            field_simplify (-1 * -1)%R; reflexivity.
        }
        rewrite (H3 (product (nat_to_funbool n x) (nat_to_funbool n s) n)).
        reflexivity.
    }
    unfold I, scale.
    simpl.
    rewrite Cmult_1_r, Rmult_1_r.
    rewrite big_sum_constant.
    rewrite times_n_C.
    rewrite <- Cmod_mult.
    autorewrite with RtoC_db.
    replace (INR (2 ^ n)) with (2 ^ n)%R.
    2: { rewrite pow_INR; reflexivity. }
    assert (/ √ (2 ^ n) * / √ (2 ^ n) = / (2 ^ n)).
    rewrite <- sqrt_inv.
    rewrite sqrt_sqrt.
    reflexivity. 
    2: { repeat rewrite <- Rmult_assoc.
        rewrite Rmult_comm.
        repeat rewrite <- Rmult_assoc.
        rewrite H2.
        rewrite Rmult_comm.
        repeat rewrite <- Rmult_assoc.
        rewrite Rmult_comm.
        repeat rewrite <- Rmult_assoc.
        rewrite Rmult_comm.
        repeat rewrite <- Rmult_assoc.
        rewrite H2.
        field_simplify (/ 2 ^ n * 2 ^ n * / 2 ^ n * 2 ^ n)%R.
        rewrite Cmod_1; reflexivity.
        nonzero.
    }
    constructor.
    apply Rinv_0_lt_compat.
    nonzero.
Qed.
    