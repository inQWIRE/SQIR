Require Export UnitarySem.
Require Import Tactics.

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
  unfold pad.
  repad.
  gridify; try lia.
  - replace d1 with d2 in * by lia.
    repeat rewrite mult_assoc.
    Msimpl.
    reflexivity.
  - replace d1 with d2 in * by lia.
    repeat rewrite mult_assoc.
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
  simpl.
  unfold ueval_cnot.
  unfold ueval1, pad.

  repad; gridify; try lia.
  - assert (d2 <= d) by lia. clear H0.
    replace d with (d2 + 1 + d3) in * by lia. clear.
    simpl; restore_dims_fast. 
    repeat rewrite Nat.pow_add_r;
    repeat rewrite <- id_kron;
    repeat rewrite kron_assoc;
    repeat rewrite <- mult_assoc.
    repeat (restore_dims_fast; distribute_plus). simpl.
    restore_dims_fast.
    repeat rewrite kron_assoc.
    restore_dims_fast.
    repeat rewrite kron_mixed_product.
    Msimpl.
    reflexivity.
  - 
    assert (d2 <= d) by lia. clear H0.
    replace d with (d2 + 1 + d3) in * by lia. clear.
    
    
    rewrite kron_plus_distr_l.
    rewrite 
    match goal with
    | |- (_ ⊗ _) × (_ ⊗ _) => idtac a
    end.
    rewrite kron_mixed_product.
    Msimpl.
    rewrite kron_mixed_
    
    
    
    
    replace d with d2 by lia.
    simpl.
    restore_dims_strong.
    repeat rewrite <- mult_assoc.
    repeat rewrite kron_assoc.
    rewrite kron_mixed_product.

    Msimpl.
    
    try rewrite H01 in; try lia.
  - 

    gridify.
  
  - assert (d2 <= d + d0) by lia. clear H1 NE1.
    assert (d1 = d + d0 - d2) by lia. clear R.
    

    restore_dims.
    repeat rewrite kron_assoc.
    repeat rewrite id_kron.
    rewrite kron_mixed_product.
    
    gridify.
    
    replace d0 with () by lia.
    replace d0 with (d + 1 + d1) by lia.
  
  cnot_tac; pad_tac.


  - 
  

  match goal with
  | H : ?a <? ?b = true |- context[?b - ?a - 1] => 
    let d := fresh "d" in
    let R := fresh "R" in
    remember (b - a - 1) as d eqn:R;
    rewrite (cnot_tac_lemma a b d H R) in * by assumption
  end.
    clear R H n2.
end.
  remember (n2 - n1 - 1) as d eqn:R.

  
  rewrite (cnot_tac_lemma  in *.

  cnot_tac; pad_tac.

  3: 
  - unfold ueval1, pad.
    pad_tac.
    + restore_dims_strong.
      Msimpl.
    

  match goal with
  | H : ?a < ?b |- context[?b - ?a - 1] => idtac a
  end.

  
  destruct (lt_eq_lt_dec n1 n2) as [[L1|E]|L2].

  

  remember 
  bdestruct
  




(* original proof *)
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

(* There are really only three different cases in the CNOT/CNOT commutativity 
   proof. Let n1 and n2 be the operands of the first CNOT  and let n1' and
   n2' be the operands of the second CNOT.

   - Case 1: n1 < n2 < n1' < n2'
   - Case 2: n1 < n1' < n2 < n2'
   - Case 3: n1 < n1' < n2' < n2

   The CNOT_CNOT_comm proof has 24 cases to account for swapping n1/n2, n1'/n2', 
   and n1/n1' + n2/n2'.

   Below are tactics to simplify each of these three cases... althought they're not
   really proper tactics because they're not useful for anything outside of this 
   proof.
*)

(* Case 1: n1 < n2 < n1' < n2'
         
   Strategy: break all terms into a grid with the following dimensions

     2 ^ n1 | 2 ^ (1 + i + 1) | 2 ^ j | 2 ^ (1 + i' + 1) | 2 ^ k 
     
   where i = n2 - n1 - 1
         i' = n2' - n1' - 1
         j = n1' - (n1 + (1 + i + 1))
         k = dim - (1 + i' + 1) - n1'
*)
Ltac CNOT_CNOT_comm_simpl_case1 dim n1 n1' n2 n2' :=
  remember (n2 - n1 - 1) as i;
  remember (n2' - n1' - 1) as i';
  remember (n1' - (n1 + (1 + i + 1))) as j;
  remember (dim - (1 + i' + 1) - n1') as k; 
  replace (2 ^ (dim - (1 + i + 1) - n1)) with (2 ^ j * 2 ^ (1 + i' + 1) * 2 ^ k) by unify_pows_two;
  replace (2 ^ n1') with (2 ^ n1 * 2 ^ (1 + i + 1) * 2 ^ j) by unify_pows_two;
  replace (2 ^ dim) with (2 ^ n1 * 2 ^ (1 + i + 1) * 2 ^ j * 2 ^ (1 + i' + 1) * 2 ^ k) by unify_pows_two;
  repeat rewrite <- id_kron;
  clear;
  repeat rewrite <- kron_assoc;
  replace (2 ^ (1 + i + 1)) with (2 * 2 ^ i * 2) by unify_pows_two;
  replace (2 ^ (1 + i' + 1)) with (2 * 2 ^ i' * 2) by unify_pows_two;
  restore_dims_strong;
  repeat rewrite kron_mixed_product;   
  Msimpl.

(* Case 2: n1 < n1' < n2 < n2'
  
   Strategy: break all terms into a grid with the following dimensions

     2 ^ n1 | 2 | 2 ^ j | 2 | 2 ^ k | 2 | 2 ^ l | 2 | 2 ^ m
     
   where i = n2 - n1 - 1
         i' = n2' - n1' - 1
         j = n1' - (n1 + 1)
         k = i - (j + 1)
         l = i' - (k + 1)
         m = dim - (1 + i' + 1) - n1'
 *)
Ltac CNOT_CNOT_comm_simpl_case2 dim n1 n1' n2 n2' :=
  remember (n2 - n1 - 1) as i;
  remember (n2' - n1' - 1) as i';
  remember (n1' - (n1 + 1)) as j;
  remember (i - (j + 1)) as k;
  remember (i' - (k + 1)) as l;
  remember (dim - (1 + i' + 1) - n1') as m;
  replace (2 ^ n1') with (2 ^ n1 * 2 * 2 ^ j) by unify_pows_two;
  replace (2 ^ (dim - (1 + i + 1) - n1)) with (2 ^ l * 2 * 2 ^ m) by unify_pows_two;
  replace (2 ^ (1 + i + 1)) with (2 * 2 ^ i * 2) by unify_pows_two;
  replace (2 ^ (1 + i' + 1)) with (2 * 2 ^ i' * 2) by unify_pows_two;
  replace (2 ^ i) with (2 ^ j * 2 * 2 ^ k) by unify_pows_two;
  replace (2 ^ i') with (2 ^ k * 2 * 2 ^ l) by unify_pows_two;
  replace (2 ^ dim) with (2 ^ n1 * 2 * 2 ^ j * 2 * 2 ^ k * 2 * 2 ^ l * 2 * 2 ^ m) by unify_pows_two;
  repeat rewrite <- id_kron;        
  clear;
  repeat rewrite <- kron_assoc;
  rewrite (kron_assoc (I (2 ^ n1)) (I 2) _);
  setoid_rewrite (kron_assoc (I (2 ^ n1)) (I 2 ⊗ I (2 ^ j)) _);
  rewrite (kron_assoc (I (2 ^ n1)) _ _);
  setoid_rewrite (kron_assoc (I (2 ^ n1)) _ (I 2));
  repeat rewrite mult_assoc;
  rewrite 2 kron_mixed_product;      
  replace (2 ^ n1 * 2 * 2 ^ j * 2 * 2 ^ k * 2 * 2 ^ l * 2) with (2 ^ n1 * (2 * 2 ^ j * 2 * 2 ^ k * 2 * 2 ^ l * 2)) by (repeat rewrite mult_assoc; reflexivity);
  rewrite 2 kron_mixed_product;
  rewrite Mmult_1_l; try auto with wf_db;
  rewrite Mmult_1_r; try auto with wf_db;
  rewrite 2 kron_plus_distr_r;
  rewrite kron_plus_distr_l;
  restore_dims_strong;
  rewrite 2 Mmult_plus_distr_r;
  repeat rewrite <- kron_assoc;
  repeat rewrite mult_assoc;  
  rewrite 4 Mmult_plus_distr_l;
  repeat rewrite kron_mixed_product;
  Msimpl.

(* Case 3: n1 < n1' < n2' < n2

   Strategy: break all terms into a grid with the following dimensions

     2 ^ n1 | 2 | 2 ^ j | 2 ^ (1 + i' + 1) | 2 ^ k | 2 | 2 ^ l
     
   where i = n2 - n1 - 1
         i' = n2' - n1' - 1
         j = n1' - (n1 + 1)
         k = i - (j + (1 + i' + 1))
         l = dim - (1 + i + 1) - n1
*)
Ltac CNOT_CNOT_comm_simpl_case3 dim n1 n1' n2 n2' :=
  remember (n2 - n1 - 1) as i;
  remember (n2' - n1' - 1) as i';
  remember (n1' - (n1 + 1)) as j;
  remember (i - (j + (1 + i' + 1))) as k;
  remember (dim - (1 + i + 1) - n1) as l;
  replace (2 ^ n1') with (2 ^ n1 * 2 * 2 ^ j) by unify_pows_two;
  replace (2 ^ (dim - (1 + i' + 1) - n1')) with (2 ^ k * 2 * 2 ^ l) by unify_pows_two;
  replace (2 ^ (1 + i + 1)) with (2 * 2 ^ i * 2) by unify_pows_two;
  replace (2 ^ i) with (2 ^ j * 2 ^ (1 + i' + 1) * 2 ^ k) by unify_pows_two;
  replace (2 ^ dim) with (2 ^ n1 * 2 * 2 ^ j * 2 ^ (1 + i' + 1) * 2 ^ k * 2 * 2 ^ l) by unify_pows_two;
  repeat rewrite <- id_kron; 
  clear;
  rewrite (kron_plus_distr_l _ _ _ _ (I (2 ^ n1)));
  repeat rewrite <- kron_assoc;
  repeat rewrite mult_assoc;
  rewrite kron_plus_distr_r;
  rewrite Mmult_plus_distr_l;
  rewrite Mmult_plus_distr_r;
  repeat rewrite kron_mixed_product;
  replace (2 ^ (1 + i' + 1)) with (2 * 2 ^ i' * 2) by unify_pows_two;
  Msimpl.

(* Warning: This proof takes forever to go through because of the calls to 
   unify_pows_two and restore_dims_strong. *)
Lemma CNOT_CNOT_comm : forall {dim} (n1 n2 n1' n2' : nat),
  n1' <> n1 ->
  n1' <> n2 ->
  n2' <> n1 ->
  n2' <> n2 ->
  @uc_equiv dim (CNOT n1 n2 ; CNOT n1' n2') (CNOT n1' n2' ; CNOT n1 n2). 
Proof.
  intros dim n1 n2 n1' n2' NE1 NE2 NE3 NE4.
  unfold uc_equiv.
  simpl; unfold ueval_cnot. 
  bdestruct (n1' <? n2'); bdestruct (n1 <? n2).
  + unfold pad.
    bdestruct (n1' + (1 + (n2' - n1' - 1) + 1) <=? dim); 
      bdestruct (n1 + (1 + (n2 - n1 - 1) + 1) <=? dim);
      remove_zero_gates; trivial.
    bdestruct (n1 <? n1').
    bdestruct (n2 <? n2').
    bdestruct (n1' <? n2).
    clear NE1 NE2 NE3 NE4 H H0.
    (* 1/24: n1 < n1' < n2 < n2' *)
    CNOT_CNOT_comm_simpl_case2 dim n1 n1' n2 n2'.
    rewrite (Mplus_assoc _ _ (∣1⟩⟨1∣ ⊗ I (2 ^ j) ⊗ ∣1⟩⟨1∣ ⊗ I (2 ^ k) ⊗ σx ⊗ I (2 ^ l) ⊗ σx)).
    rewrite <- (Mplus_assoc _ _ (∣0⟩⟨0∣ ⊗ I (2 ^ j) ⊗ ∣1⟩⟨1∣ ⊗ I (2 ^ k) ⊗ I 2 ⊗ I (2 ^ l) ⊗ σx)).
    rewrite (Mplus_comm _ _ (∣0⟩⟨0∣ ⊗ I (2 ^ j) ⊗ ∣1⟩⟨1∣ ⊗ I (2 ^ k) ⊗ I 2 ⊗ I (2 ^ l) ⊗ σx)).
    repeat rewrite <- Mplus_assoc.
    reflexivity.
    assert (n2 < n1') by lia.
    clear NE1 NE2 NE3 NE4 H3 H4 H5.
    (* 2/24: n1 < n2 < n1' < n2' *)
    CNOT_CNOT_comm_simpl_case1 dim n1 n1' n2 n2'.
    reflexivity. 
    assert (n2' < n2) by lia.
    clear NE1 NE2 NE3 NE4 H0 H4.
    (* 3/24: n1 < n1' < n2' < n2 *)
    CNOT_CNOT_comm_simpl_case3 dim n1 n1' n2 n2'.
    reflexivity.
    assert (n1' < n1) by lia.
    bdestruct (n2 <? n2').
    clear NE1 NE2 NE3 NE4 H H3.  
    (* 4/24: n1' < n1 < n2 < n2' *)
    CNOT_CNOT_comm_simpl_case3 dim n1' n1 n2' n2.
    reflexivity.
    assert (n2' < n2) by lia. 
    bdestruct (n1 <? n2'). 
    clear NE1 NE2 NE3 NE4 H H0 H3 H5.
    (* 5/24: n1' < n1 < n2' < n2 *)
    CNOT_CNOT_comm_simpl_case2 dim n1' n1 n2' n2.
    rewrite (Mplus_assoc _ _ (∣1⟩⟨1∣ ⊗ I (2 ^ j) ⊗ ∣1⟩⟨1∣ ⊗ I (2 ^ k) ⊗ σx ⊗ I (2 ^ l) ⊗ σx)).
    rewrite <- (Mplus_assoc _ _ (∣1⟩⟨1∣ ⊗ I (2 ^ j) ⊗ ∣0⟩⟨0∣ ⊗ I (2 ^ k) ⊗ σx ⊗ I (2 ^ l) ⊗ I 2)).
    rewrite (Mplus_comm _ _ (∣1⟩⟨1∣ ⊗ I (2 ^ j) ⊗ ∣0⟩⟨0∣ ⊗ I (2 ^ k) ⊗ σx ⊗ I (2 ^ l) ⊗ I 2)).
    repeat rewrite <- Mplus_assoc.
    reflexivity.
    assert (n2' < n1) by lia.
    clear NE1 NE2 NE3 NE4 H3 H4 H5 H6 H7.
    (* 6/24: n1' < n2' < n1 < n2 *)
    CNOT_CNOT_comm_simpl_case1 dim n1' n1 n2' n2.
    reflexivity.
  + bdestruct (n2 <? n1); remove_zero_gates; trivial.
    unfold pad.
    bdestruct (n1' + (1 + (n2' - n1' - 1) + 1) <=? dim); 
      bdestruct (n2 + (1 + (n1 - n2 - 1) + 1) <=? dim);
      remove_zero_gates; trivial.
    bdestruct (n2 <? n1').
    bdestruct (n1 <? n2').
    bdestruct (n1' <? n1).
    clear NE1 NE2 NE3 NE4 H H0 H1.
    (* 7/24: n2 < n1' < n1 < n2' *)
    CNOT_CNOT_comm_simpl_case2 dim n2 n1' n1 n2'.
    rewrite (Mplus_assoc _ _ (σx ⊗ I (2 ^ j) ⊗ ∣1⟩⟨1∣ ⊗ I (2 ^ k) ⊗ ∣1⟩⟨1∣ ⊗ I (2 ^ l) ⊗ σx)).
    rewrite <- (Mplus_assoc _ _ (I (2 * 2 ^ j) ⊗ ∣1⟩⟨1∣ ⊗ I (2 ^ k) ⊗ ∣0⟩⟨0∣ ⊗ I (2 ^ l) ⊗ σx)).
    rewrite (Mplus_comm _ _ (I (2 * 2 ^ j) ⊗ ∣1⟩⟨1∣ ⊗ I (2 ^ k) ⊗ ∣0⟩⟨0∣ ⊗ I (2 ^ l) ⊗ σx)).
    repeat rewrite <- Mplus_assoc.
    reflexivity.
    assert (n1 < n1') by lia.
    clear NE1 NE2 NE3 NE4 H0 H4 H5 H6.
    (* 8/24: n2 < n1 < n1' < n2' *)
    CNOT_CNOT_comm_simpl_case1 dim n2 n1' n1 n2'.
    reflexivity. 
    assert (n2' < n1) by lia.
    clear NE1 NE2 NE3 NE4 H0 H1 H5.
    (* 9/24: n2 < n1' < n2' < n1 *)
    CNOT_CNOT_comm_simpl_case3 dim n2 n1' n1 n2'.
    reflexivity.
    assert (n1' < n2) by lia.
    bdestruct (n1 <? n2').
    clear NE1 NE2 NE3 NE4 H H0 H4.  
    (* 10/24: n1' < n2 < n1 < n2' *)
    CNOT_CNOT_comm_simpl_case3 dim n1' n2 n2' n1.
    reflexivity.
    assert (n2' < n1) by lia. 
    bdestruct (n2 <? n2'). 
    clear NE1 NE2 NE3 NE4 H H0 H1 H4 H6.
    (* 11/24: n1' < n2 < n2' < n1 *)
    CNOT_CNOT_comm_simpl_case2 dim n1' n2 n2' n1.
    rewrite (Mplus_assoc _ _ (∣1⟩⟨1∣ ⊗ I (2 ^ j) ⊗ σx ⊗ I (2 ^ k) ⊗ σx ⊗ I (2 ^ l) ⊗ ∣1⟩⟨1∣)).
    rewrite <- (Mplus_assoc _ _ (∣1⟩⟨1∣ ⊗ I (2 ^ j) ⊗ I 2 ⊗ I (2 ^ k) ⊗ σx ⊗ I (2 ^ l) ⊗ ∣0⟩⟨0∣)).
    rewrite (Mplus_comm _ _ (∣1⟩⟨1∣ ⊗ I (2 ^ j) ⊗ I 2 ⊗ I (2 ^ k) ⊗ σx ⊗ I (2 ^ l) ⊗ ∣0⟩⟨0∣)).
    repeat rewrite <- Mplus_assoc.
    reflexivity.
    assert (n2' < n2) by lia.
    clear NE1 NE2 NE3 NE4 H0 H4 H5 H6 H7 H8.
    (* 12/24: n1' < n2' < n2 < n1 *)
    CNOT_CNOT_comm_simpl_case1 dim n1' n2 n2' n1.
    reflexivity.
  + bdestruct (n2' <? n1'); remove_zero_gates; trivial.
    unfold pad.
    bdestruct (n2' + (1 + (n1' - n2' - 1) + 1) <=? dim); 
      bdestruct (n1 + (1 + (n2 - n1 - 1) + 1) <=? dim);
      remove_zero_gates; trivial.
    bdestruct (n1 <? n2').
    bdestruct (n2 <? n1').
    bdestruct (n2' <? n2).
    clear NE1 NE2 NE3 NE4 H H0 H1.
    (* 13/24: n1 < n2' < n2 < n1' *)
    CNOT_CNOT_comm_simpl_case2 dim n1 n2' n2 n1'.
    rewrite (Mplus_assoc _ _ (∣1⟩⟨1∣ ⊗ I (2 ^ j) ⊗ σx ⊗ I (2 ^ k) ⊗ σx ⊗ I (2 ^ l) ⊗ ∣1⟩⟨1∣)).
    rewrite <- (Mplus_assoc _ _ (∣0⟩⟨0∣ ⊗ I (2 ^ j) ⊗ σx ⊗ I (2 ^ k) ⊗ I 2 ⊗ I (2 ^ l) ⊗ ∣1⟩⟨1∣)).
    rewrite (Mplus_comm _ _ (∣0⟩⟨0∣ ⊗ I (2 ^ j) ⊗ σx ⊗ I (2 ^ k) ⊗ I 2 ⊗ I (2 ^ l) ⊗ ∣1⟩⟨1∣)).
    repeat rewrite <- Mplus_assoc.
    reflexivity.
    assert (n2 < n2') by lia.
    clear NE1 NE2 NE3 NE4 H H4 H5 H6.
    (* 14/24: n1 < n2 < n2' < n1' *)
    CNOT_CNOT_comm_simpl_case1 dim n1 n2' n2 n1'.
    reflexivity. 
    assert (n1' < n2) by lia.
    clear NE1 NE2 NE3 NE4 H H0 H5.
    (* 15/24: n1 < n2' < n1' < n2 *)
    CNOT_CNOT_comm_simpl_case3 dim n1 n2' n2 n1'.
    reflexivity.
    assert (n2' < n1) by lia.
    bdestruct (n2 <? n1').
    clear NE1 NE2 NE3 NE4 H H1 H4.  
    (* 16/24: n2' < n1 < n2 < n1' *)
    CNOT_CNOT_comm_simpl_case3 dim n2' n1 n1' n2.
    reflexivity.
    assert (n1' < n2) by lia. 
    bdestruct (n1 <? n1'). 
    clear NE1 NE2 NE3 NE4 H H0 H1 H4 H6.
    (* 17/24: n2' < n1 < n1' < n2 *)
    CNOT_CNOT_comm_simpl_case2 dim n2' n1 n1' n2.
    rewrite (Mplus_assoc _ _ (σx ⊗ I (2 ^ j) ⊗ ∣1⟩⟨1∣ ⊗ I (2 ^ k) ⊗ ∣1⟩⟨1∣ ⊗ I (2 ^ l) ⊗ σx)).
    rewrite <- (Mplus_assoc _ _ (σx ⊗ I (2 ^ j) ⊗ ∣0⟩⟨0∣ ⊗ I (2 ^ k) ⊗ ∣1⟩⟨1∣ ⊗ I (2 ^ l) ⊗ I 2)).
    rewrite (Mplus_comm _ _ (σx ⊗ I (2 ^ j) ⊗ ∣0⟩⟨0∣ ⊗ I (2 ^ k) ⊗ ∣1⟩⟨1∣ ⊗ I (2 ^ l) ⊗ I 2)).
    repeat rewrite <- Mplus_assoc.
    reflexivity.
    assert (n1' < n1) by lia.
    clear NE1 NE2 NE3 NE4 H H4 H5 H6 H7 H8.
    (* 18/24: n2' < n1' < n1 < n2 *)
    CNOT_CNOT_comm_simpl_case1 dim n2' n1 n1' n2.
    reflexivity.
  + bdestruct (n2' <? n1'); bdestruct (n2 <? n1); remove_zero_gates; trivial.
    unfold pad.
    bdestruct (n2' + (1 + (n1' - n2' - 1) + 1) <=? dim); 
      bdestruct (n2 + (1 + (n1 - n2 - 1) + 1) <=? dim);
      remove_zero_gates; trivial.
    bdestruct (n2 <? n2').
    bdestruct (n1 <? n1').
    bdestruct (n2' <? n1).
    clear NE1 NE2 NE3 NE4 H H0 H1 H2.
    (* 19/24: n2 < n2' < n1 < n1' *)
    CNOT_CNOT_comm_simpl_case2 dim n2 n2' n1 n1'.
    rewrite (Mplus_assoc _ _ (σx ⊗ I (2 ^ j) ⊗ σx ⊗ I (2 ^ k) ⊗ ∣1⟩⟨1∣ ⊗ I (2 ^ l) ⊗ ∣1⟩⟨1∣)).
    rewrite <- (Mplus_assoc _ _ (I (2 * 2 ^ j) ⊗ σx ⊗ I (2 ^ k) ⊗ ∣0⟩⟨0∣ ⊗ I (2 ^ l) ⊗ ∣1⟩⟨1∣)).
    rewrite (Mplus_comm _ _ (I (2 * 2 ^ j) ⊗ σx ⊗ I (2 ^ k) ⊗ ∣0⟩⟨0∣ ⊗ I (2 ^ l) ⊗ ∣1⟩⟨1∣)).
    repeat rewrite <- Mplus_assoc.
    reflexivity.
    assert (n1 < n2') by lia.
    clear NE1 NE2 NE3 NE4 H H0 H5 H6 H7.
    (* 20/24: n2 < n1 < n2' < n1' *)
    CNOT_CNOT_comm_simpl_case1 dim n2 n2' n1 n1'.
    reflexivity. 
    assert (n1' < n1) by lia.
    clear NE1 NE2 NE3 NE4 H H0 H2 H6.
    (* 21/24: n2 < n2' < n1' < n1 *)
    CNOT_CNOT_comm_simpl_case3 dim n2 n2' n1 n1'.
    reflexivity.
    assert (n2' < n2) by lia.
    bdestruct (n1 <? n1').
    clear NE1 NE2 NE3 NE4 H H0 H1 H5.  
    (* 22/24: n2' < n2 < n1 < n1' *)
    CNOT_CNOT_comm_simpl_case3 dim n2' n2 n1' n1.
    reflexivity.
    assert (n1' < n1) by lia. 
    bdestruct (n2 <? n1'). 
    clear NE1 NE2 NE3 NE4 H H0 H1 H2 H5 H7.
    (* 23/24: n2' < n2 < n1' < n1 *)
    CNOT_CNOT_comm_simpl_case2 dim n2' n2 n1' n1.
    rewrite (Mplus_assoc _ _ (σx ⊗ I (2 ^ j) ⊗ σx ⊗ I (2 ^ k) ⊗ ∣1⟩⟨1∣ ⊗ I (2 ^ l) ⊗ ∣1⟩⟨1∣)).
    rewrite <- (Mplus_assoc _ _ (σx ⊗ I (2 ^ j) ⊗ I 2 ⊗ I (2 ^ k) ⊗ ∣1⟩⟨1∣ ⊗ I (2 ^ l) ⊗ ∣0⟩⟨0∣)).
    rewrite (Mplus_comm _ _ (σx ⊗ I (2 ^ j) ⊗ I 2 ⊗ I (2 ^ k) ⊗ ∣1⟩⟨1∣ ⊗ I (2 ^ l) ⊗ ∣0⟩⟨0∣)).
    repeat rewrite <- Mplus_assoc.
    reflexivity.
    assert (n1' < n2) by lia.
    clear NE1 NE2 NE3 NE4 H H0 H5 H6 H7 H8 H9.
    (* 24/24: n2' < n1' < n2 < n1 *)
    CNOT_CNOT_comm_simpl_case1 dim n2' n2 n1' n1.
    reflexivity.
Qed.

Lemma X_X_id : forall {dim} q, 
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
    repeat rewrite <- id_kron.
    rewrite (kron_assoc (I (2 ^ c)) _ (I (2 ^ i))).
    replace dim with (c + (1 + i + 1) + j) by lia.
    clear.
    restore_dims_strong.
    rewrite (kron_assoc (I (2 ^ c)) _ σx).
    restore_dims_strong.
    repeat rewrite kron_mixed_product; remove_id_gates.
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

Lemma H_H_id : forall {dim} q, 
  @uc_well_typed dim (H q) -> 
  @uc_equiv dim uskip (H q; H q).
Proof. 
  intros dim q WT. 
  unfold uc_equiv.
  simpl; unfold ueval1, pad. 
  inversion WT; subst. 
  bdestruct (q + 1 <=? dim); try lia.
  restore_dims_strong; Msimpl.
  replace (hadamard × hadamard) with (I 2) by solve_matrix.
  repeat rewrite id_kron.
  apply f_equal.
  unify_pows_two.
Qed.

Require Import Phase.

Definition Rz {dim} θ n : ucom dim := uapp1 (U_R θ) n.  

Lemma Rz_Rz_add : forall {dim} q θ θ', 
   @uc_equiv dim ((Rz θ) q; (Rz θ') q) ((Rz (θ + θ')) q).
Proof.
  intros.
  unfold uc_equiv.
  simpl; unfold ueval1, pad. 
  bdestruct (q + 1 <=? dim); remove_zero_gates; trivial.
  restore_dims_strong; Msimpl.
  rewrite phase_mul.
  rewrite Rplus_comm. 
  reflexivity.
Qed.

Lemma Rz_0_add : forall {dim} q, 
  @uc_well_typed dim ((Rz 0) q) -> 
  @uc_equiv dim ((Rz 0) q) uskip.
Proof.
  intros dim q WT. 
  unfold uc_equiv.
  simpl; unfold ueval1, pad. 
  inversion WT; subst. 
  bdestruct (q + 1 <=? dim); try lia.
  rewrite phase_0. 
  Msimpl.
  apply f_equal.
  unify_pows_two.
Qed.