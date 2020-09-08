Require Import UnitarySem.
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

Fixpoint simplify_1q_gates {dim} (l : IBM_ucom_l dim) (n: nat) acc : IBM_ucom_l dim :=
  match n with
  | O => rev_append acc l
  | S n' => 
    match l with
    | [] => rev_append acc []
    | (App1 (UIBM_U1 a) q) :: t => 
        if Reqb (cos a) 1 then simplify_1q_gates t n' acc
        else simplify_1q_gates t n' (U1 a q :: acc)
    | (App1 (UIBM_U3 a b c) q) :: t => 
        if Reqb (cos a) 1 
        then if Reqb (cos (b + c)) 1 
             then simplify_1q_gates t n' acc
             else simplify_1q_gates t n' (U1 (b + c) q :: acc)
        else if Reqb (sin a) 1 
             then simplify_1q_gates t n' (U2 b c q :: acc)
             else if Reqb (sin a) (-1)
                  then simplify_1q_gates t n' (U2 (b + PI) (c - PI) q :: acc)
                  else simplify_1q_gates t n' (U3 a b c q :: acc)
    | g :: t => simplify_1q_gates t n' (g :: acc)
    end
  end.

Definition optimize_1q_gates {dim} (l : IBM_ucom_l dim) := 
  let l' := optimize_1q_gates' l (length l) [] in
  simplify_1q_gates l' (length l') [].

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
    all: try (rewrite (cons_to_app _ (_ ++ _));
              rewrite (app_assoc (rev acc));
              rewrite (app_assoc (rev acc ++ _));
              rewrite <- (app_assoc (rev acc))).
    + (* u1 ; u1 *)
      apply uc_equiv_cong_l.
      setoid_rewrite combine_u1_u1; auto.
      rewrite (Rplus_comm a0 a).
      reflexivity.
    + (* u2 ; u1 *)
      apply uc_equiv_cong_l.
      setoid_rewrite combine_u2_u1; auto.
      reflexivity.
    + (* u3 ; u1 *)
      apply uc_equiv_cong_l.
      setoid_rewrite combine_u3_u1; auto.
      rewrite (Rplus_comm a0 b).
      reflexivity.
    + (* u1 ; u2 *)
      apply uc_equiv_cong_l.
      setoid_rewrite combine_u1_u2; auto.
      reflexivity.
    + (* u2 ; u2 *)
      setoid_rewrite combine_u2_u2; auto.
      reflexivity.
    + (* u3 ; u2 *)
      apply uc_equiv_cong_l.
      setoid_rewrite U2_is_U3.
      setoid_rewrite compose_u3_correct; auto.
      reflexivity.
    + (* u1 ; u3 *)
      apply uc_equiv_cong_l.
      setoid_rewrite combine_u1_u3; auto.
      reflexivity.
    + (* u2 ; u3 *)
      apply uc_equiv_cong_l.
      setoid_rewrite U2_is_U3.
      setoid_rewrite compose_u3_correct; auto.
      reflexivity.
    + (* u3 ; u3 *)
      apply uc_equiv_cong_l.
      setoid_rewrite compose_u3_correct; auto.
      reflexivity.
  - inversion WT; subst.
    rewrite IHn; auto. simpl. rewrite <- app_assoc. reflexivity.
  - inversion u.
Qed.
  
(* etc... *)
