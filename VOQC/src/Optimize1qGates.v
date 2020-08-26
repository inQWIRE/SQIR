Require Import UnitarySem.
Require Export QiSGateSet.
Require Import List.
Open Scope ucom.

Local Close Scope R_scope.
Local Open Scope matrix_scope.
Local Open Scope ucom_scope.

(**********************************************************************)
(** Optimization: simple combination w/ commutation **)
(**********************************************************************)

(* Combine several U gates on a qubit to one U gate. *)

(* equivalence rules for U1; U2 ; U3 *)

(* If both gates are U1, then sum them together. *)
Definition combine_U_equivalence1 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U1 a, l2) =>
       match next_single_qubit_gate l2 q with 
            | Some (l3, UQiS_U1 a', l4) => Some (l1 ++ [U1 (a + a')%R q] ++ l3 ++ l4)
            | _ => None end
    | _ => None end.

(* if u1 follows u2 then a + a, and b *)
Definition combine_U_equivalence2 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U1 a, l2) =>
       match next_single_qubit_gate l2 q with 
            | Some (l3, UQiS_U2 a' b, l4) => Some (l1 ++ [U2 a' (a+b) q] ++ l3 ++ l4)
            | _ => None end
    | _ => None end.

(* the oppose of equiv2 *)
Definition combine_U_equivalence3 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U2 a b, l2) =>
       match next_single_qubit_gate l2 q with 
            | Some (l3, UQiS_U1 a', l4) => Some (l1 ++ [U2 (a + a') b q] ++ l3 ++ l4)
            | _ => None end
    | _ => None end.


(* if u1 a follows U3 a b c then U3 a' (a + b) c *)
Definition combine_U_equivalence4 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U1 a, l2) =>
       match next_single_qubit_gate l2 q with 
            | Some (l3, UQiS_U3 a' b c, l4) => Some (l1 ++ [U3 a' b (a + c) q] ++ l3 ++ l4)
            | _ => None end
    | _ => None end.

(* the oppose of equiv4 *)
Definition combine_U_equivalence5 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U3 a b c, l2) =>
       match next_single_qubit_gate l2 q with 
            | Some (l3, UQiS_U1 a', l4) => Some (l1 ++ [U3 a (b + a') c q] ++ l3 ++ l4)
            | _ => None end
    | _ => None end.

(* if both are U2 (a b) (a' b'), then U3 (180 - b - a') (a + 90) (b' + 90)  *)
Definition combine_U_equivalence6 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U2 a b, l2) =>
       match next_single_qubit_gate l2 q with 
            | Some (l3, UQiS_U2 a' b', l4)
               => Some (l1 ++ [U3 (1 - (b' + a)) (a' + 1/2) (b + 1/2) q] ++ l3 ++ l4)
            | _ => None end
    | _ => None end.

(* if a U3 a b c, and if a is an interger then U1 0 0 ( b + c) *)
Definition combine_U_equivalence7 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U3 a b c, l2) =>
             if Reqb (cos (a * PI)) 1 then
                  Some (l1 ++ [U1 (b+c) q] ++ l2)
                else None
    | _ => None end.


(* if both are U3 a b c, if a mod 360 = 90 or 270 then U2 b/b+180 c/c-180. *)
Definition combine_U_equivalence8 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U3 a b c, l2) =>
             if (Reqb (sin (a * PI)) 1) then
                  Some (l1 ++ [U2 b c q] ++ l2)
                else if (Reqb (sin (a * PI)) (-1)) then
                  Some (l1 ++ [U2 (b+1) (c - 1) q] ++ l2)
                else None
    | _ => None end.

(* if both are U1 a, if a mod 360 = 0 then the gate can be canceled. *)
Definition combine_U_equivalence9 {dim} q (l : QiS_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
    | Some (l1, UQiS_U1 a, l2) =>
             if (Reqb (cos (a * PI)) 1) then
                  Some (l1 ++ l2)
                else None
    | _ => None end.

Definition combine_U_equivalence {dim} (l : QiS_ucom_l dim) (q:nat) : option (QiS_ucom_l dim)  := 
   try_rewrites l (combine_U_equivalence1 q :: combine_U_equivalence2 q :: combine_U_equivalence3 q
            :: combine_U_equivalence4 q :: combine_U_equivalence5 q :: combine_U_equivalence6 q ::
           combine_U_equivalence7 q :: combine_U_equivalence8 q :: combine_U_equivalence9 q :: []).

(*
Fixpoint combine_U_equivalences' {dim} (l : QiS_ucom_l dim) (n: nat) acc : QiS_ucom_l dim :=
  match n with
  | 0 => rev_append acc l
  | S n' => 
      match l with
      | [] => rev_append acc []
      | (App1 (UQiS_U1 a) q) :: t => 
          match combine_U_equivalence l q with
          | None => combine_U_equivalences' t n' (U1 a q :: acc)
          | Some l' => combine_U_equivalences' l' n' acc
          end
      | g :: t => combine_U_equivalences' t n' (g :: acc)
      end
  end.


Definition optimize1qgate {dim} (l : QiS_ucom_l dim) := 
  combine_U_equivalences' l (3 * (length l)) [].
*)

Lemma combine_U_equivalence1_sound : forall {dim} (l l' : QiS_ucom_l dim) q,
  combine_U_equivalence1 q l = Some l' ->
  l =l= l'. 
Proof.
  intros.
  unfold combine_U_equivalence1 in H.
  destruct_list_ops; simpl_dnr.
assert ((g0 ++ U1 (a + a0) q :: g2 ++ g1) = (g0 ++ [U1 (a + a0) q] ++ g2 ++ g1)).
rewrite (cons_to_app). reflexivity. rewrite H. clear H.
    rewrite (app_assoc _ _ g1).
    rewrite (app_assoc g0).
setoid_rewrite <- (does_not_reference_commutes_app1 g2); try assumption.
  apply_app_congruence.
  unfold uc_equiv_l; simpl.
  rewrite 2 SKIP_id_r.
  apply two_u1_to_one.
Qed.

(* proving equivalence of u1;u2 and u2;u1. *)
Lemma combine_U_equivalence2_sound : forall {dim} (l l' : QiS_ucom_l dim) q,
  combine_U_equivalence2 q l = Some l' ->
  l =l= l'. 
Proof.
  intros.
  unfold combine_U_equivalence2 in H.
  destruct_list_ops; simpl_dnr.
assert ((g0 ++ U2 a0 (a + b) q :: g2 ++ g1) = (g0 ++ [U2 a0 (a + b) q] ++ g2 ++ g1)).
rewrite (cons_to_app). reflexivity. rewrite H. clear H.
    rewrite (app_assoc _ _ g1).
    rewrite (app_assoc g0).
setoid_rewrite <- (does_not_reference_commutes_app1 g2); try assumption.
  apply_app_congruence.
  unfold uc_equiv_l; simpl.
  rewrite 2 SKIP_id_r.
  apply u1_u2_to_one.
Qed.

Lemma combine_U_equivalence3_sound : forall {dim} (l l' : QiS_ucom_l dim) q,
  combine_U_equivalence3 q l = Some l' ->
  l =l= l'. 
Proof.
  intros.
  unfold combine_U_equivalence3 in H.
  destruct_list_ops; simpl_dnr.
assert ((g0 ++ U2 (a + a0) b q :: g2 ++ g1) = (g0 ++ [U2 (a + a0) b q] ++ g2 ++ g1)).
rewrite (cons_to_app). reflexivity. rewrite H. clear H.
    rewrite (app_assoc _ _ g1).
    rewrite (app_assoc g0).
setoid_rewrite <- (does_not_reference_commutes_app1 g2); try assumption.
  apply_app_congruence.
  unfold uc_equiv_l; simpl.
  rewrite 2 SKIP_id_r.
  apply u2_u1_to_one.
Qed.

(* Proving equivalence of u1;u3 and u3;u1. *)
Lemma combine_U_equivalence4_sound : forall {dim} (l l' : QiS_ucom_l dim) q,
  combine_U_equivalence4 q l = Some l' ->
  l =l= l'. 
Proof.
  intros.
  unfold combine_U_equivalence4 in H.
  destruct_list_ops; simpl_dnr.
assert ((g0 ++ U3 a0 b (a + c) q :: g2 ++ g1) = (g0 ++ [U3 a0 b (a + c) q] ++ g2 ++ g1)).
rewrite (cons_to_app). reflexivity. rewrite H. clear H.
    rewrite (app_assoc _ _ g1).
    rewrite (app_assoc g0).
setoid_rewrite <- (does_not_reference_commutes_app1 g2); try assumption.
  apply_app_congruence.
  unfold uc_equiv_l; simpl.
  rewrite 2 SKIP_id_r.
  apply u1_u3_to_one.
Qed.

Lemma combine_U_equivalence5_sound : forall {dim} (l l' : QiS_ucom_l dim) q,
  combine_U_equivalence5 q l = Some l' ->
  l =l= l'. 
Proof.
  intros.
  unfold combine_U_equivalence5 in H.
  destruct_list_ops; simpl_dnr.
assert ((g0 ++ U3 a (b + a0) c q :: g2 ++ g1) = (g0 ++ [U3 a (b + a0) c q] ++ g2 ++ g1)).
rewrite (cons_to_app). reflexivity. rewrite H. clear H.
    rewrite (app_assoc _ _ g1).
    rewrite (app_assoc g0).
setoid_rewrite <- (does_not_reference_commutes_app1 g2); try assumption.
  apply_app_congruence.
  unfold uc_equiv_l; simpl.
  rewrite 2 SKIP_id_r.
  apply u3_u1_to_one.
Qed.


Lemma combine_U_equivalence6_sound : forall {dim} (l l' : QiS_ucom_l dim) q,
  combine_U_equivalence6 q l = Some l' ->
  l ≅l≅ l'. 
Proof.
  intros.
  unfold combine_U_equivalence6 in H.
  destruct_list_ops; simpl_dnr.
Locate cons_to_app.
assert ((g0 ++ U3 (1 - (b0 + a)) (a0 + 1 / 2) (b + 1 / 2) q :: g2 ++ g1)
              = (g0 ++ [U3 (1 - (b0 + a)) (a0 + 1 / 2) (b + 1 / 2) q] ++ g2 ++ g1)).
rewrite (cons_to_app). reflexivity. rewrite H. clear H.
    rewrite (app_assoc _ _ g1).
    rewrite (app_assoc g0).
assert (((g0 ++ [App1 (UQiS_U2 a b) q]) ++
 (g2 ++ [App1 (UQiS_U2 a0 b0) q]) ++ g1)
   =l= ((g0 ++ [App1 (UQiS_U2 a b) q]) ++
 ([App1 (UQiS_U2 a0 b0) q] ++ g2) ++ g1)).
setoid_rewrite <- (does_not_reference_commutes_app1 g2); try assumption.
reflexivity.
apply uc_equiv_cong_l in H.
rewrite H.
assert (@uc_cong_l dim ([App1 (UQiS_U2 a b) q] ++ [App1 (UQiS_U2 a0 b0) q]) [U3 (1 - (b0 + a)) (a0 + 1 / 2) (b + 1 / 2) q]).
  unfold uc_cong_l; simpl.
clear H.
rewrite 2 SKIP_id_r_cong.
  apply two_u2_to_one.
assert (((g0 ++ [App1 (UQiS_U2 a b) q]) ++ ([App1 (UQiS_U2 a0 b0) q] ++ g2) ++ g1)
  = (g0 ++ ([App1 (UQiS_U2 a b) q] ++ [App1 (UQiS_U2 a0 b0) q]) ++ (g2 ++ g1))).
apply_app_congruence. reflexivity.
rewrite H1.
rewrite H0.
reflexivity.
Qed.

(* if u3's theta is zero, then it is a u1 gate.*)
Lemma combine_U_equivalence7_sound : forall {dim} (l l' : QiS_ucom_l dim) q,
  combine_U_equivalence7 q l = Some l' ->
  l ≅l≅ l'. 
Proof.
  intros.
  unfold combine_U_equivalence7 in H.
  destruct_list_ops; simpl_dnr.
destruct (Reqb (cos (a * PI)) 1) eqn:eq1.
injection H as H1. rewrite <- H1. clear H1.
assert ((g0 ++ U1 (b + c) q :: g)
              = (g0 ++ [U1 (b + c) q] ++ g)).
rewrite (cons_to_app). reflexivity. rewrite H. clear H.
apply uc_cong_l_app_congruence.
apply uc_cong_l_app_congruence. reflexivity.
  unfold uc_cong_l; simpl.
  rewrite 2 SKIP_id_r_cong.
  apply u3_to_u1.
apply Reqb_eq in eq1. assumption.
reflexivity.
inversion H.
Qed.

(* if u3's theta is PI/2 or 3 * PI / 2, then it is a u2 gate.*)
Lemma combine_U_equivalence8_sound : forall {dim} (l l' : QiS_ucom_l dim) q,
  combine_U_equivalence8 q l = Some l' ->
  l ≅l≅ l'. 
Proof.
  intros.
  unfold combine_U_equivalence8 in H.
  destruct_list_ops; simpl_dnr.
destruct (Reqb (sin (a * PI)) 1) eqn:eq1.
injection H as H1. rewrite <- H1. clear H1.
assert ((g0 ++ U2 b c q :: g)
              = (g0 ++ [U2 b c q] ++ g)).
rewrite (cons_to_app). reflexivity. rewrite H. clear H.
apply uc_cong_l_app_congruence.
apply uc_cong_l_app_congruence. reflexivity.
  unfold uc_cong_l; simpl.
  rewrite 2 SKIP_id_r_cong.
  apply u3_to_u2.
apply Reqb_eq in eq1. assumption.
reflexivity.
destruct (Reqb (sin (a * PI)) (-1)) eqn:eq2.
injection H as H1. rewrite <- H1. clear H1.
assert ((g0 ++ U2 (b + 1) (c - 1) q :: g)
              = (g0 ++ [U2 (b + 1) (c - 1) q ] ++ g)).
rewrite (cons_to_app). reflexivity. rewrite H. clear H.
apply uc_cong_l_app_congruence.
apply uc_cong_l_app_congruence. reflexivity.
  unfold uc_cong_l; simpl.
  rewrite 2 SKIP_id_r_cong.
  apply u3_to_u2_neg.
apply Reqb_eq in eq2. assumption.
reflexivity.
inversion H.
Qed.

(* if lambda u1 is a n*2 * pi, then it is SKIP. *)
Lemma combine_U_equivalence9_sound : forall {dim} (l l' : QiS_ucom_l dim) q,
  (q < dim)%nat ->
  combine_U_equivalence9 q l = Some l' ->
  l =l= l'. 
Proof.
  intros.
  unfold combine_U_equivalence9 in H0.
  destruct_list_ops; simpl_dnr.
destruct (Reqb (cos (a * PI)) 1) eqn:eq1.
injection H0 as H1. rewrite <- H1. clear H1.
assert ((g0 ++ g) = (g0 ++ [] ++ g)).
rewrite  app_nil_l. reflexivity.
rewrite H0. clear H0.
  apply_app_congruence.
  unfold uc_equiv_l; simpl.
  rewrite SKIP_id_r.
  apply u1_to_skip. assumption.
  apply Reqb_eq in eq1. assumption.
  inversion H0.
Qed.


