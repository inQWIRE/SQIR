Require Export UnitarySem.

Local Open Scope ucom_scope.
Local Close Scope C_scope.
Local Close Scope R_scope.

(** Example equivalences of unitary circuits. **)

Lemma uskip_id_l : forall {dim} (c : ucom dim),
   (uskip ; c) ≡ c.
Proof.
  intros dim c. 
  unfold uc_equiv.
  simpl; Msimpl; reflexivity.
Qed.

Lemma uskip_id_r : forall {dim} (c : ucom dim),
   (c ; uskip) ≡ c.
Proof.
  intros dim c.
  unfold uc_equiv.
  simpl; Msimpl; reflexivity.
Qed.

Lemma U_V_comm : forall {dim} (m n : nat) (U V : Unitary 1),
  m <> n ->
  @uc_equiv dim (uapp1 U m ; uapp1 V n) (uapp1 V n ; uapp1 U m). 
Proof.
  intros dim m n U V NE.
  unfold uc_equiv; simpl.
  simpl in *.
  unfold ueval1. 
  repeat match goal with
  | [|- context [pad m _ ?U ]] => remember U as U'
  | [|- context [pad n _ ?V ]] => remember V as V'
  end.
  assert (WFU : WF_Matrix U') by 
      (destruct U; subst; auto with wf_db).
  assert (WFV : WF_Matrix V') by 
      (destruct V; subst; auto with wf_db).
  clear HeqU' HeqV' U V.
  unfold pad.
  bdestruct (n + 1 <=? dim); bdestruct (m + 1 <=? dim);
    remove_zero_gates; trivial.
  bdestruct (m <? n).
  - remember (n - m - 1) as k.
    replace n with (m + 1 + k) by lia.
    replace (2 ^ (m+1+k)) with (2^m * 2 * 2^k) by unify_pows_two.
    remember (dim - 1 - (m + 1 + k)) as j.
    replace (dim - 1 - m) with (k + 1 + j) by lia.
    replace (2 ^ (k + 1 + j)) with (2^k * 2 * 2^ j) by unify_pows_two.
    simpl in *.
    repeat rewrite <- id_kron.
    restore_dims.
    repeat (rewrite kron_assoc; restore_dims).
    replace (2^dim) with (2 ^ m * 2 * 2 ^ k * 2 * 2 ^ j) by unify_pows_two.
    clear -WFU WFV.
    restore_dims_strong. 
    Msimpl.
    reflexivity.
  - rename m into n, n into m.
    remember (n - m - 1) as k.
    replace n with (m + 1 + k) by lia.
    replace (2 ^ (m+1+k)) with (2^m * 2 * 2^k) by unify_pows_two.
    remember (dim - 1 - (m + 1 + k)) as j.
    replace (dim - 1 - m) with (k + 1 + j) by lia.
    replace (2 ^ (k + 1 + j)) with (2^k * 2 * 2^ j) by unify_pows_two.
    repeat rewrite <- id_kron.
    simpl in *.
    repeat rewrite kron_assoc.
    repeat rewrite Nat.mul_assoc.
    restore_dims.
    repeat (rewrite kron_assoc; restore_dims).
    replace (2^dim) with (2 ^ m * 2 * 2 ^ k * 2 * 2 ^ j) by unify_pows_two.
    clear -WFU WFV.
    restore_dims_strong.
    Msimpl.
    reflexivity.
Qed.

(* This proof can still be cleaned up. Cases 4-6 are exactly the same as 1-3,
   except with n2 and n1 switched. *)
Lemma U_CNOT_comm : forall {dim} (q n1 n2 : nat) (U : Unitary 1),
  q <> n1 ->
  q <> n2 ->
  @uc_equiv dim (uapp1 U q ; CNOT n1 n2) (CNOT n1 n2 ; uapp1 U q). 
Proof.
  intros dim q n1 n2 U NE1 NE2.
  unfold uc_equiv.
  simpl; unfold ueval1, ueval_cnot. 
  match goal with
  | [|- context [pad q _ ?U ]] => remember U as U'
  end.
  assert (WFU : WF_Matrix U') by 
      (destruct U; subst; auto with wf_db).
  clear HeqU' U.
  bdestruct (n1 <? n2).
  - unfold pad.
    remember (n2 - n1 - 1) as i.
    replace (2 ^ (n2 - n1)) with (2 ^ i * 2) by unify_pows_two.
    repeat rewrite <- id_kron.
    rewrite <- (kron_assoc _ _ (I 2)).
    bdestruct (q + 1 <=? dim); bdestruct (n1 + (1 + i + 1) <=? dim); 
    remove_zero_gates; trivial.
    bdestruct (n2 <? q).
    (* Case 1/6: n1 < n2 < q *)
    + remember (q - (1 + i + 1) - n1) as j.
      remember (dim - 1 - q) as k.
      replace (2 ^ q) with (2 ^ n1 * (2 * 2 ^ i * 2) * 2 ^ j) by unify_pows_two.
      replace (2 ^ (dim - (1 + i + 1) - n1)) with (2 ^ j * 2 * 2 ^ k) by unify_pows_two.
      repeat rewrite <- id_kron.
      rewrite <- (kron_assoc _ _ (I (2 ^ k))).
      rewrite <- (kron_assoc _ _ (I 2)). 
      replace (2 ^ dim) with (2 ^ n1 * (2 * 2 ^ i * 2) * 2 ^ j * 2 * 2 ^ k) by unify_pows_two. 
      clear - WFU.
      restore_dims_strong.
      Msimpl.
      reflexivity.
    + apply le_lt_eq_dec in H2; destruct H2;
        try (contradict e; assumption).
      bdestruct (n1 <? q).
      (* Case 2/6: n1 < q < n2 *)
      * remember (q - n1 - 1) as j.
        remember (i - j - 1) as k.
        remember (dim - (1 + i + 1) - n1) as m.
        replace (2 ^ q) with (2 ^ n1 * 2 * 2 ^ j) by unify_pows_two.
        replace (2 ^ i) with (2 ^ j * 2 * 2 ^ k) by unify_pows_two.   
        replace (2 ^ (1 + i + 1)) with (2 * 2 ^ j * 2 * 2 ^ k * 2) by unify_pows_two.    
        replace (2 ^ (dim - 1 - q)) with (2 ^ k * 2 * 2 ^ m) by unify_pows_two.
        repeat rewrite <- id_kron.
        repeat rewrite <- kron_assoc.
        replace (2 ^ dim) with (2 ^ n1 * (2 * 2 ^ j * 2 * 2 ^ k * 2) * 2 ^ m) by unify_pows_two.
        clear - WFU.
        rewrite (kron_assoc (I (2 ^ n1)) _ (I (2 ^ j))).
        restore_dims_strong.
        rewrite (kron_assoc (I (2 ^ n1)) _ U').
        restore_dims_strong.
        rewrite (kron_assoc (I (2 ^ n1)) _ (I (2 ^ k))).
        restore_dims_strong.
        rewrite (kron_assoc (I (2 ^ n1)) _ (I 2)).
        replace (2 ^ 1) with 2 by easy.
        replace (2 * (2 ^ j * 2 * 2 ^ k) * 2) with (2 * 2 ^ j * 2 * 2 ^ k * 2) by unify_pows_two.
        replace (2 ^ n1 * (2 * 2 ^ j * 2 * 2 ^ k) * 2) with (2 ^ n1 * (2 * 2 ^ j * 2 * 2 ^ k * 2)) by unify_pows_two.
        Msimpl.
        rewrite Mmult_plus_distr_l.
        rewrite Mmult_plus_distr_r.
        Msimpl.
        reflexivity.
      (* Case 3/6: q < n1 < n2 *)
      * remember (n1 - q - 1) as j.
        remember (dim - (1 + i + 1) - n1) as k.
        replace (2 ^ n1) with (2 ^ q * 2 * 2 ^ j) by unify_pows_two.
        replace (2 ^ (dim - 1 - q)) with (2 ^ j * 2 ^ (1 + i + 1) * 2 ^ k) by unify_pows_two.
        repeat rewrite <- id_kron.
        replace (2 ^ dim) with (2 ^ q * 2 * 2 ^ j * 2 ^ (1 + i + 1) * 2 ^ k) by unify_pows_two.
        clear - WFU.
        repeat rewrite <- kron_assoc.
        replace (2 ^ 1) with 2 by easy.
        replace (2 ^ q * 2 * (2 ^ j * 2 ^ (1 + i + 1))) with (2 ^ q * 2 * 2 ^ j * 2 ^ (1 + i + 1)) by rewrite_assoc.
        Msimpl. 
        replace (2 ^ (1 + i + 1)) with (2 * 2 ^ i * 2) by unify_pows_two.
        rewrite Mmult_plus_distr_l.
        rewrite Mmult_plus_distr_r.
        Msimpl.
        reflexivity.
  - bdestruct (n2 <? n1); remove_zero_gates; trivial.
    unfold pad.
    remember (n1 - n2 - 1) as i.
    replace (2 ^ (n1 - n2)) with (2 * 2 ^ i) by unify_pows_two.
    repeat rewrite <- id_kron.
    bdestruct (q + 1 <=? dim); bdestruct (n2 + (1 + i + 1) <=? dim); 
      remove_zero_gates; trivial.
    bdestruct (n1 <? q).
    (* Case 4/6: n2 < n1 < q *)
    + remember (q - (1 + i + 1) - n2) as j.
      remember (dim - 1 - q) as k.
      replace (2 ^ q) with (2 ^ n2 * (2 * 2 ^ i * 2) * 2 ^ j) by unify_pows_two.
      replace (2 ^ (dim - (1 + i + 1) - n2)) with (2 ^ j * 2 * 2 ^ k) by unify_pows_two.
      repeat rewrite <- id_kron.
      rewrite <- (kron_assoc _ _ (I (2 ^ k))).
      rewrite <- (kron_assoc _ _ (I 2)). 
      replace (2 ^ dim) with (2 ^ n2 * (2 * 2 ^ i * 2) * 2 ^ j * 2 * 2 ^ k) by unify_pows_two. 
      clear - WFU. 
      restore_dims_strong.
      Msimpl.
      reflexivity.
    + apply le_lt_eq_dec in H3; destruct H3; 
        try (contradict e; assumption).
      bdestruct (n2 <? q).
      (* Case 5/6: n2 < q < n1 *)
      * remember (q - n2 - 1) as j.
        remember (i - j - 1) as k.
        remember (dim - (1 + i + 1) - n2) as m.
        replace (2 ^ q) with (2 ^ n2 * 2 * 2 ^ j) by unify_pows_two.
        replace (2 ^ i) with (2 ^ j * 2 * 2 ^ k) by unify_pows_two.   
        replace (2 ^ (1 + i + 1)) with (2 * 2 ^ j * 2 * 2 ^ k * 2) by unify_pows_two.    
        replace (2 ^ (dim - 1 - q)) with (2 ^ k * 2 * 2 ^ m) by unify_pows_two.
        repeat rewrite <- id_kron.
        repeat rewrite <- kron_assoc.
        replace (2 ^ dim) with (2 ^ n2 * (2 * 2 ^ j * 2 * 2 ^ k * 2) * 2 ^ m) by unify_pows_two.
        clear - WFU.
        rewrite (kron_assoc (I (2 ^ n2)) _ (I (2 ^ j))).
        restore_dims_strong.
        rewrite (kron_assoc (I (2 ^ n2)) _ U').
        restore_dims_strong.
        rewrite (kron_assoc (I (2 ^ n2)) _ (I (2 ^ k))).
        restore_dims_strong.
        rewrite (kron_assoc (I (2 ^ n2)) _ (I 2)).
        replace (2 ^ 1) with 2 by easy.
        replace (2 * (2 ^ j * 2 * 2 ^ k) * 2) with (2 * 2 ^ j * 2 * 2 ^ k * 2) by unify_pows_two.
        replace (2 ^ n2 * (2 * 2 ^ j * 2 * 2 ^ k) * 2) with (2 ^ n2 * (2 * 2 ^ j * 2 * 2 ^ k * 2)) by unify_pows_two.
        Msimpl.
        rewrite Mmult_plus_distr_l.
        rewrite Mmult_plus_distr_r.
        Msimpl.
        reflexivity.
      * apply le_lt_eq_dec in H3; destruct H3; 
          try (contradict e; assumption).
        (* Case 6/6: q < n2 < n1 *)
        remember (n2 - q - 1) as j.
        remember (dim - (1 + i + 1) - n2) as k.
        replace (2 ^ n2) with (2 ^ q * 2 * 2 ^ j) by unify_pows_two.
        replace (2 ^ (dim - 1 - q)) with (2 ^ j * 2 ^ (1 + i + 1) * 2 ^ k) by unify_pows_two.
        repeat rewrite <- id_kron.
        replace (2 ^ dim) with (2 ^ q * 2 * 2 ^ j * 2 ^ (1 + i + 1) * 2 ^ k) by unify_pows_two.
        clear - WFU.
        repeat rewrite <- kron_assoc.
        replace (2 ^ 1) with 2 by easy.
        replace (2 ^ q * 2 * (2 ^ j * 2 ^ (1 + i + 1))) with (2 ^ q * 2 * 2 ^ j * 2 ^ (1 + i + 1)) by rewrite_assoc.
        Msimpl. 
        replace (2 ^ (1 + i + 1)) with (2 * 2 ^ i * 2) by unify_pows_two.
        rewrite Mmult_plus_distr_l.
        rewrite Mmult_plus_distr_r.
        Msimpl.
        reflexivity.
Qed.

Lemma XX_id : forall {dim} q, 
  @uc_well_typed dim (X q) -> 
  @uc_equiv dim uskip (X q; X q).
Proof. 
  intros dim q WT. 
  unfold uc_equiv.
  simpl; unfold ueval1, pad. 
  inversion WT; subst. 
  bdestruct (q + 1 <=? dim); try lia.
  restore_dims_strong; Msimpl.
  replace (σx × σx) with (I 2) by solve_matrix.
  repeat rewrite id_kron.
  apply f_equal.
  unify_pows_two.
Qed.

Lemma X_CNOT_comm : forall {dim} c t, 
  @uc_equiv dim (X t; CNOT c t) (CNOT c t ; X t).
Proof.
  intros dim c t.
  unfold uc_equiv.
  simpl; unfold ueval1, pad. 
  bdestruct (t + 1 <=? dim); remove_zero_gates; trivial. 
  unfold ueval_cnot, pad. 
  bdestruct (c <? t).
  - bdestruct (c + (1 + (t - c - 1) + 1) <=? dim); remove_zero_gates; trivial. 
    (* c < t *)
    remember (t - c - 1) as i.
    replace (dim - (1 + i + 1) - c) with (dim - 1 - t) by lia.
    remember (dim - 1 - t) as j.
    replace (2 ^ t) with (2 ^ c * 2 * 2 ^ i) by unify_pows_two.
    replace (2 ^ (t - c)) with (2 ^ i * 2) by unify_pows_two.
    repeat rewrite <- id_kron.
    rewrite (kron_assoc (I (2 ^ c)) _ (I (2 ^ i))).
    replace dim with (c + (1 + i + 1) + j) by lia.
    clear.
    restore_dims_strong.
    rewrite (kron_assoc (I (2 ^ c)) _ σx).
    restore_dims_strong.
    repeat rewrite kron_mixed_product; remove_id_gates.
    rewrite <- (kron_assoc ∣0⟩⟨0∣ (I (2 ^ i)) (I 2)).
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r.
    repeat rewrite kron_mixed_product; remove_id_gates.
  - bdestruct (t <? c); remove_zero_gates; trivial.
    bdestruct (t + (1 + (c - t - 1) + 1) <=? dim); remove_zero_gates; trivial.
    (* t < c *)
    remember (c - t - 1) as i.
    replace (dim - (1 + i + 1) - t) with (dim - 1 - c) by lia.
    remember (dim - 1 - c) as j.
    replace (2 ^ (dim - 1 - t)) with (2 ^ i * 2 * 2 ^ j) by unify_pows_two.
    replace (2 ^ (c - t)) with (2 * 2 ^ i) by unify_pows_two.
    repeat rewrite <- id_kron.
    rewrite (kron_assoc (I (2 ^ t)) σx _).
    rewrite <- (kron_assoc σx _ (I (2 ^ j))).
    rewrite <- (kron_assoc σx (I (2 ^ i)) (I 2)).
    replace dim with (t + (1 + i + 1) + j) by lia.
    clear.
    restore_dims_strong.
    rewrite <- (kron_assoc (I (2 ^ t)) _ (I (2 ^ j))).
    restore_dims_strong.
    repeat rewrite kron_mixed_product; remove_id_gates.
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r.
    repeat rewrite kron_mixed_product; remove_id_gates.
Qed.
