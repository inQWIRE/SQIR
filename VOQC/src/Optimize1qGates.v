Require Import ChangeRotationBasis.
Require Export IBMGateSet.
Require Import List.
Open Scope ucom.

Local Open Scope ucom_scope.

(** Combine multiple U gates on a qubit to one U gate. **)

Fixpoint optimize_1q_gates' {dim} (l : IBM_ucom_l dim) (n: nat) acc : IBM_ucom_l dim :=
  match n with
  | O => rev_append acc l
  | S n' => 
    match l with
    | [] => rev_append acc []
    | (App1 u q) :: t => 
      match next_single_qubit_gate t q with
      | Some (l1, u', l2) => 
        let unew := 
          match u, u' with
          | UIBM_U1 a, UIBM_U1 a'           => UIBM_U1 (a' + a)
          | UIBM_U1 a, UIBM_U2 a' b         => UIBM_U2 a' (a + b)
          | UIBM_U1 a, UIBM_U3 a' b c       => UIBM_U3 a' b (a + c)
          | UIBM_U2 a b, UIBM_U1 a'         => UIBM_U2 (a + a') b
          | UIBM_U2 a b, UIBM_U2 a' b'      => UIBM_U3 (PI - (a + b')) (a' + PI/2) (b + PI/2)
          | UIBM_U2 a b, UIBM_U3 a' b' c    => compose_u3 (PI/2) a b a' b' c
          | UIBM_U3 a b c, UIBM_U1 a'       => UIBM_U3 a (b + a') c
          | UIBM_U3 a b c, UIBM_U2 a' b'    => compose_u3 a b c (PI/2) a' b'
          | UIBM_U3 a b c, UIBM_U3 a' b' c' => compose_u3 a b c a' b' c'
          end in
        optimize_1q_gates' (l1 ++ l2) n' (App1 unew q :: acc)
      | None => optimize_1q_gates' t n' (App1 u q :: acc)
      end
    | g :: t => optimize_1q_gates' t n' (g :: acc)
    end
  end.

Fixpoint simplify_1q_gates {dim} (l : IBM_ucom_l dim)  acc : IBM_ucom_l dim :=
  match l with
  | [] => rev_append acc []
  | (App1 (UIBM_U1 a) q) :: t => 
      if Reqb (cos a) 1 then simplify_1q_gates t acc
       else simplify_1q_gates t (U1 a q :: acc)
  | (App1 (UIBM_U3 a b c) q) :: t => 
      if Reqb (cos a) 1 
      then if Reqb (cos (b + c)) 1 
           then simplify_1q_gates t acc
           else simplify_1q_gates t (U1 (b + c) q :: acc)
      else if Reqb (sin a) 1 
           then simplify_1q_gates t (U2 b c q :: acc)
           else if Reqb (sin a) (-1)
                then simplify_1q_gates t (U2 (b + PI) (c - PI) q :: acc)
                else simplify_1q_gates t (U3 a b c q :: acc)
  | g :: t => simplify_1q_gates t (g :: acc)
  end.

Definition optimize_1q_gates {dim} (l : IBM_ucom_l dim) := 
  let l' := optimize_1q_gates' l (length l) [] in
  simplify_1q_gates l' [].

(** Proofs **)

Lemma U2_is_U3 : forall {dim} a b q,
  [@U2 dim a b q] =l= [U3 (PI/2) a b q].
Proof. reflexivity. Qed.

Lemma optimize_1q_gates'_sound : forall {dim} (l : IBM_ucom_l dim) n acc,
  uc_well_typed_l l ->
  optimize_1q_gates' l n acc ≅l≅ rev_append acc l.
Proof.
  intros dim l n acc WT.
  rewrite rev_append_rev.
  generalize dependent acc.
  generalize dependent l.
  induction n; intros l WT acc.
  simpl. rewrite rev_append_rev. reflexivity.
  destruct l.
  simpl. rewrite rev_append_rev. reflexivity.
  destruct g as [u | u | u]; simpl.
  - inversion WT; subst.
    destruct (next_single_qubit_gate l n0) eqn:nsqg.
    2: { rewrite IHn; auto. simpl. rewrite <- app_assoc. reflexivity. }
    repeat destruct p. 
    specialize (nsqg_WT _ _ _ _ _ nsqg H3) as [WTg0 WTg].
    apply nsqg_commutes in nsqg.
    apply uc_equiv_cong_l in nsqg.
    rewrite nsqg.
    rewrite IHn.
    2: { apply uc_well_typed_l_app; auto. }
    dependent destruction i; dependent destruction u. 
    all: (simpl;
          repeat rewrite (cons_to_app _ (_ ++ _));
          apply_app_congruence_cong;
          symmetry).
    + (* u1 ; u1 *)
      apply uc_equiv_cong_l.
      rewrite (Rplus_comm a0 a).
      apply combine_u1_u1; assumption.
    + (* u2 ; u1 *)
      apply uc_equiv_cong_l.
      apply combine_u2_u1; assumption.
    + (* u3 ; u1 *)
      apply uc_equiv_cong_l.
      rewrite (Rplus_comm b a0).
      apply combine_u3_u1; assumption.
    + (* u1 ; u2 *)
      apply uc_equiv_cong_l.
      apply combine_u1_u2; assumption.
    + (* u2 ; u2 *)
      apply combine_u2_u2; assumption.
    + (* u3 ; u2 *)
      erewrite uc_cong_l_app_congruence.
      2: { apply uc_equiv_cong_l. apply U2_is_U3. }
      2: reflexivity.
      apply combine_u3_u3; assumption.
    + (* u1 ; u3 *)
      apply uc_equiv_cong_l.
      apply combine_u1_u3; assumption.
    + (* u2 ; u3 *)
      erewrite uc_cong_l_app_congruence.
      2: reflexivity.
      2: { apply uc_equiv_cong_l. apply U2_is_U3. }      
      apply combine_u3_u3; assumption.
    + (* u3 ; u3 *)
      apply combine_u3_u3; assumption.
  - inversion WT; subst.
    rewrite IHn; auto. simpl. rewrite <- app_assoc. reflexivity.
  - inversion u.
Qed.

Lemma simplify_1q_gates_sound : forall {dim} (l : IBM_ucom_l dim) acc,
  uc_well_typed_l l ->
  simplify_1q_gates l acc ≅l≅ rev_append acc l.
Proof.
  intros dim l acc WT.
  rewrite rev_append_rev.
  generalize dependent acc.
  induction l; intros acc. 
  simpl. rewrite rev_append_rev. reflexivity.
  destruct a as [u | u | u]; simpl; 
    dependent destruction u; inversion WT; subst.
  - bdestruct (Reqb (cos a) 1); rewrite IHl by assumption.
    apply uc_equiv_cong_l.
    rewrite (cons_to_app _ l).
    setoid_rewrite u1_to_skip; auto.
    reflexivity.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
  - rewrite IHl by assumption.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
  - bdestruct (Reqb (cos a) 1).
    bdestruct (Reqb (cos (b + c)) 1); rewrite IHl by assumption.
    rewrite (cons_to_app _ l).
    setoid_rewrite u3_to_u1; auto.
    apply uc_equiv_cong_l.
    setoid_rewrite u1_to_skip; auto.
    reflexivity.
    rewrite (cons_to_app _ l).
    setoid_rewrite u3_to_u1; auto.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
    bdestruct (Reqb (sin a) 1).
    rewrite IHl by assumption.
    rewrite (cons_to_app _ l).
    setoid_rewrite u3_to_u2; auto.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
    bdestruct (Reqb (sin a) (-1)); rewrite IHl by assumption.
    rewrite (cons_to_app _ l).
    setoid_rewrite u3_to_u2_neg; auto.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
  - rewrite IHl by assumption.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma optimize_1q_gates_sound : forall {dim} (l : IBM_ucom_l dim),
  uc_well_typed_l l ->
  optimize_1q_gates l ≅l≅ l.
Proof.
  intros.
  unfold optimize_1q_gates.
  rewrite simplify_1q_gates_sound.
  rewrite rev_append_rev.
  simpl.
  rewrite optimize_1q_gates'_sound by assumption.
  rewrite rev_append_rev.
  reflexivity.
  eapply uc_cong_l_implies_WT. 
  symmetry.
  apply optimize_1q_gates'_sound.
  assumption.
  rewrite rev_append_rev.
  simpl.
  assumption.
Qed.
