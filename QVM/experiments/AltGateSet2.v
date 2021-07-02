Require Import UnitaryOps.

(** TODO: merge with utilities/AltGateSet.v
  
  Include all gates currently supported by VOQC
  - u1, u2, u3
  - id, x, y, z
  - h, s, t, sdg, tdg
  - rx, ry, rz
  - cx, cz, swap
  - ccx, ccz
 **)

Inductive ucom (U : nat -> Set) : Set :=
| useq :  ucom U -> ucom U -> ucom U
| uapp : forall n, U n -> list nat -> ucom U.
Arguments useq {U}.
Arguments uapp {U n}.
Notation "u1 >> u2" := (useq u1 u2) (at level 50). 
(* >> because ; is already used in the ucom scope *)

Inductive well_formed {U} : ucom U -> Prop :=
  | WF_useq : forall u1 u2, well_formed u1 -> well_formed u2 -> well_formed (u1 >> u2)
  | WF_uapp : forall n (g : U n) qs, length qs = n -> well_formed (uapp g qs).

(* RNR: Next three lemmas aren't needed but replace old 
   lemmas and could possibly be useful *)
Lemma uapp_WF_length : forall {U : nat -> Set} (n : nat) (g : U n) qs,
  well_formed (uapp g qs) -> length qs = n.
Proof.
  intros.
  inversion H; subst; easy.
Qed.

Lemma destruct_list_S : forall {A} (l : list A) (n : nat),
    length l = S n ->
    exists x l', length l' = n /\ l = x :: l'.
Proof.
  intros A l.
  induction l; intros.
  - discriminate.
  - eauto.
Qed.

Lemma destruct_list_0 : forall {A} (l : list A),
    length l = 0%nat ->
    l = nil.
Proof. destruct l; easy. Qed.

Ltac simpl_WF :=
  repeat match goal with
  | [H : well_formed _ |- _] => apply uapp_WF_length in H
  | [H : length ?l = ?n |- _] => destruct l; inversion H; clear H
  end.

Ltac simpl_WF_alt :=
  repeat match goal with
  | [H : well_formed _ |- _] => apply uapp_WF_length in H
  | [H : length ?l = S ?n |- _] => apply destruct_list_S in H as [? [? [? ?]]]; subst
  | [H : length ?l = O |- _] => apply destruct_list_0 in H; subst
  end.

(** More general gate set **)

Inductive U : nat -> Set :=
  | U_X : U 1
  | U_H : U 1
  | U_U1 : R -> U 1
  | U_U2 : R -> R -> U 1 
  | U_U3 : R -> R -> R -> U 1
  | U_CX : U 2
  | U_CCX : U 3.

Fixpoint to_base_ucom dim (u : ucom U) : base_ucom dim :=
  match u with
  | u1 >> u2 => (to_base_ucom dim u1 ; to_base_ucom dim u2)%ucom
  | uapp g qs => 
      match g, qs with
      | U_X, (q1 :: List.nil)%list => SQIR.X q1
      | U_H, (q1 :: List.nil) => H q1
      | U_U1 r1, (q1 :: List.nil) => U1 r1 q1
      | U_U2 r1 r2, (q1 :: List.nil) => U2 r1 r2 q1
      | U_U3 r1 r2 r3, (q1 :: List.nil) => U3 r1 r2 r3 q1
      | U_CX, (q1 :: q2 :: List.nil) => CNOT q1 q2
      | U_CCX, (q1 :: q2 :: q3 :: List.nil) => UnitaryOps.control q1 (CNOT q2 q3)
      (* dummy value - unreachable for well-formed progs *)
      | _, _ => SKIP
      end
  end.

Definition uc_eval dim (u : ucom U) := uc_eval (to_base_ucom dim u).

Lemma change_dim : forall u m n,
  uc_eval m u = UnitarySem.uc_eval (cast (to_base_ucom n u) m).
Proof.
  intros u m n.
  unfold uc_eval.
  induction u; simpl.
  rewrite IHu1, IHu2.
  reflexivity.
  destruct u; repeat (destruct l; try reflexivity).
Qed.

Ltac invert_WT :=
  repeat match goal with
  | H : uc_well_typed (UnitaryOps.control _ _)%ucom |- _ => idtac
  | H : uc_well_typed _ |- _ => inversion H; clear H; subst
  end.

Local Transparent SQIR.ID SQIR.X SQIR.H SQIR.Rz SQIR.CNOT SQIR.SWAP.
Local Opaque UnitaryOps.control.
Lemma change_dim_WT : forall (u : ucom U) (m n : nat),
  (m <= n)%nat -> 
  well_formed u ->
  uc_well_typed (to_base_ucom m u) ->
  uc_well_typed (to_base_ucom n u).
Proof.
  intros u m n Hmn WF WT.
  induction u.
  inversion WT; subst.
  inversion WF; subst.
  constructor; auto.
  destruct u; simpl in *; simpl_WF; invert_WT.
  all: repeat constructor; try lia.
  (* U_CCX *)
  apply uc_well_typed_control in WT as [? [? ?]].
  invert_WT; invert_is_fresh.
  apply uc_well_typed_control.
  repeat split; try constructor; lia.
Qed.
Local Transparent UnitaryOps.control.
Local Opaque SQIR.ID SQIR.X SQIR.H SQIR.Rz SQIR.U1 SQIR.U2 SQIR.U3 SQIR.CNOT SQIR.SWAP.

(* Defining constants separately for easier extraction. *)
Definition R2 : R := 2.
Definition R4 : R := 4.

Definition X q := uapp U_X [q].
Definition H q := uapp U_H [q].
Definition U1 r1 q := uapp (U_U1 r1) [q].
Definition U2 r1 r2 q := uapp (U_U2 r1 r2) [q].
Definition U3 r1 r2 r3 q := uapp (U_U3 r1 r2 r3) [q].
Definition T q := U1 (PI / R4) q.
Definition Tdg q := U1 (- (PI / R4)) q.
Definition SKIP := U1 R0 O. (* used as a dummy value *)
Definition CX q1 q2 := uapp U_CX (q1 :: q2 :: List.nil).
Definition CCX q1 q2 q3 := uapp U_CCX (q1 :: q2 :: q3 :: List.nil).

Definition decompose_CH (a b : nat) : ucom U := 
  U3 (PI/R4) R0 R0 b >> CX a b >> U3 (- (PI/R4)) R0 R0 b. 

Definition decompose_CU1 r1 (a b : nat) : ucom U := 
  U1 (r1/R2) a >> U1 (r1/R2) b >> CX a b >> U1 (- (r1/R2)) b >> CX a b.

Definition decompose_CU2 r1 r2 (a b : nat) : ucom U := 
  U1 ((r2+r1)/R2) a >> U1 ((r2-r1)/R2) b >> CX a b >>
  U3 (-(PI/R4)) R0 (-(r1+r2)/R2) b >> CX a b >> U3 (PI/R4) r1 R0 b.

Definition decompose_CU3 r1 r2 r3 (a b : nat) : ucom U := 
  U1 ((r3+r2)/R2) a >> U1 ((r3-r2)/R2) b >> CX a b >>
  U3 (-(r1/R2)) R0 (-(r2+r3)/R2) b >> CX a b >> U3 (r1/R2) r2 R0 b.

Definition decompose_CCX (a b c : nat) : ucom U := 
  H c >> CX b c >> Tdg c >> CX a c >> 
  T c >> CX b c >> Tdg c >> CX a c >> 
  CX a b >> Tdg b >> CX a b >>
  T a >> T b >> T c >> H c.

Fixpoint control' a (c : ucom U) (n : nat) : ucom U :=
  match n with 
  | O => SKIP (* unreachable with "fuel" below *)
  | S n' => 
      match c with
      | c1 >> c2 => control' a c1 n' >> control' a c2 n'
      | uapp U_X (b :: List.nil) => CX a b
      | uapp U_CX (b :: c :: List.nil) => CCX a b c
      | uapp U_CCX (b :: c :: d :: List.nil) => control' a (decompose_CCX b c d) n'
      | uapp (U_U1 r) (b :: List.nil) => decompose_CU1 r a b
      | uapp U_H (b :: List.nil) => decompose_CH a b
      | uapp (U_U2 r1 r2) (b :: List.nil) => decompose_CU2 r1 r2 a b
      | uapp (U_U3 r1 r2 r3) (b :: List.nil) => decompose_CU3 r1 r2 r3 a b
      | _ => SKIP (* unreachable *)
      end
  end.
(* Fuel for control'. This may return a larger number than necessary (meaning that
   control' will return before consuming all its fuel), but this will always
   provide enough fuel to complete the computation (see how "fuel" is used in 
   control'_correct. *)
Definition fuel_CCX : nat := 14.
Fixpoint fuel (c : ucom U) :=
  match c with
  | c1 >> c2 => S (max (fuel c1) (fuel c2))
  | uapp U_CCX _ => S fuel_CCX
  | _ => O
  end.
Definition control a (c : ucom U) :=
  control' a c (S (fuel c)).

Lemma fuel_CCX_eq : forall a b c, fuel (decompose_CCX a b c) = fuel_CCX.
Proof. intros. reflexivity. Qed.

Hint Rewrite <- RtoC_minus : RtoC_db.

Local Transparent SQIR.H SQIR.U3.
Lemma decompose_CH_is_control_H : forall dim a b,
  uc_eval dim (decompose_CH a b) = 
    UnitarySem.uc_eval (UnitaryOps.control a (SQIR.H b)).
Proof.
  assert (aux1 : rotation (- (PI / 4)) 0 0 × (σx × rotation (PI / 4) 0 0) =
                 Cexp (PI / 2) .* (rotation (PI / 2 / 2) 0 0 ×
                   (σx × (rotation (- (PI / 2) / 2) 0 (- PI / 2) × 
                     (σx × phase_shift (PI / 2)))))).
  { (* messy :) should make better automation -KH *)
    solve_matrix; repeat rewrite RIneq.Ropp_div; autorewrite with Cexp_db trig_db; 
      repeat rewrite RtoC_opp; field_simplify_eq; try nonzero.
    replace (((R1 + R1)%R, (R0 + R0)%R) * cos (PI / 4 / 2) * sin (PI / 4 / 2)) 
      with (2 * sin (PI / 4 / 2) * cos (PI / 4 / 2)) by lca.
    2: replace (((- (R1 + R1))%R, (- (R0 + R0))%R) * Ci * Ci * 
                  cos (PI / 2 / 2 / 2) * sin (PI / 2 / 2 / 2))
         with (2 * sin (PI / 2 / 2 / 2) * cos (PI / 2 / 2 / 2)) by lca.
    3: replace (- sin (PI / 4 / 2) * sin (PI / 4 / 2) + 
                  cos (PI / 4 / 2) * cos (PI / 4 / 2)) 
         with (cos (PI / 4 / 2) * cos (PI / 4 / 2) - 
                 sin (PI / 4 / 2) * sin (PI / 4 / 2)) by lca.
    3: replace ((R1 + R1)%R, (R0 + R0)%R) with (RtoC 2) by lca.
    4: replace (((- (R1 + R1))%R, (- (R0 + R0))%R) * sin (PI / 4 / 2) * 
                  cos (PI / 4 / 2)) 
         with (- (2 * sin (PI / 4 / 2) * cos (PI / 4 / 2))) by lca.
    4: replace (- Ci * Ci * sin (PI / 2 / 2 / 2) * sin (PI / 2 / 2 / 2) + 
                  Ci * Ci * cos (PI / 2 / 2 / 2) * cos (PI / 2 / 2 / 2))
         with (- (cos (PI / 2 / 2 / 2) * cos (PI / 2 / 2 / 2) - 
                 sin (PI / 2 / 2 / 2) * sin (PI / 2 / 2 / 2))) by lca.
    all: autorewrite with RtoC_db; rewrite <- sin_2a; rewrite <- cos_2a;
         replace (2 * (PI / 4 / 2))%R with (PI / 4)%R by lra;
         replace (2 * (PI / 2 / 2 / 2))%R with (PI / 4)%R by lra;
         autorewrite with trig_db; reflexivity. }
  assert (aux2 : rotation (- (PI / 4)) 0 0 × rotation (PI / 4) 0 0 =
                 rotation (PI / 2 / 2) 0 0 × 
                   (rotation (- (PI / 2) / 2) 0 (- PI / 2) × phase_shift (PI / 2))).
  { assert (aux: forall x, (x * x = x²)%R) by (unfold Rsqr; reflexivity).
    solve_matrix; repeat rewrite RIneq.Ropp_div; autorewrite with Cexp_db trig_db; 
      repeat rewrite RtoC_opp; field_simplify_eq; try nonzero; 
      autorewrite with RtoC_db; repeat rewrite aux.
    rewrite 2 (Rplus_comm ((cos _)²)).
    rewrite 2 sin2_cos2.
    reflexivity.
    rewrite 2 sin2_cos2.
    reflexivity. }
  intros dim a b.
  unfold SQIR.H, decompose_CH, uc_eval.
  simpl.
  autorewrite with eval_db.
  gridify; trivial; autorewrite with ket_db. (* slow! *)
  - rewrite Rminus_0_r, Rplus_0_l, Rplus_0_r.
    apply f_equal2.
    + rewrite <- Mscale_kron_dist_l.
      rewrite <- Mscale_kron_dist_r.
      do 2 (apply f_equal2; try reflexivity).
      apply aux1.
    + unfold R4. 
      replace R0 with 0 by reflexivity.
      rewrite aux2.
      reflexivity.
  - rewrite Rminus_0_r, Rplus_0_l, Rplus_0_r.
    apply f_equal2.
    + rewrite <- 3 Mscale_kron_dist_l.
      rewrite <- Mscale_kron_dist_r.
      do 4 (apply f_equal2; try reflexivity).
      apply aux1.
    + unfold R4.
      replace R0 with 0 by reflexivity.
      rewrite aux2.
      reflexivity.
Qed.
Local Opaque SQIR.H SQIR.U3.

Local Transparent SQIR.Rz SQIR.U1.
Lemma decompose_CU1_is_control_U1 : forall dim r a b,
  uc_eval dim (decompose_CU1 r a b) = 
    UnitarySem.uc_eval (UnitaryOps.control a (SQIR.U1 r b)).
Proof.
  intros dim r a b.
  unfold SQIR.U1, decompose_CU1, uc_eval.
  simpl.
  autorewrite with R_db.
  repeat rewrite phase_shift_rotation.
  rewrite phase_0.
  bdestruct (b <? dim).
  replace (pad b dim (I 2)) with (I (2 ^ dim)).
  Msimpl. reflexivity.
  unfold pad.
  gridify. reflexivity.
  autorewrite with eval_db.
  gridify.
Qed.
Local Opaque SQIR.Rz SQIR.U1.

Local Transparent SQIR.U2.
Lemma decompose_CU2_is_control_U2 : forall dim r1 r2 a b,
  uc_eval dim (decompose_CU2 r1 r2 a b) = 
    UnitarySem.uc_eval (UnitaryOps.control a (SQIR.U2 r1 r2 b)).
Proof.
  intros dim r1 r2 a b.
  unfold SQIR.U2, decompose_CU2, uc_eval.
  simpl.
  replace (PI / 2 / 2)%R with (PI / 4)%R by lra.
  replace (- (PI / 2) / 2)%R with (- (PI / 4))%R by lra.
  reflexivity.
Qed.
Local Opaque SQIR.U2.

Local Transparent SQIR.U3.
Lemma decompose_CU3_is_control_U3 : forall dim r1 r2 r3 a b,
  uc_eval dim (decompose_CU3 r1 r2 r3 a b) = 
    UnitarySem.uc_eval (UnitaryOps.control a (SQIR.U3 r1 r2 r3 b)).
Proof.
  intros dim r1 r2 r3 a b.
  unfold SQIR.U3, decompose_CU3, uc_eval.
  simpl.
  replace (- r1 / 2)%R with (- (r1 / 2))%R by lra.
  reflexivity.
Qed.
Local Opaque SQIR.U3.

Local Transparent SQIR.CNOT.
Lemma decompose_CCX_is_control_CX : forall dim a b c,
  uc_eval dim (decompose_CCX a b c) = 
    UnitarySem.uc_eval (UnitaryOps.control a (SQIR.CNOT b c)).
Proof.
  intros dim a b c.
  unfold decompose_CCX, uc_eval, SQIR.CNOT.
  simpl.
  reflexivity.
Qed.
Local Opaque SQIR.CNOT.

Lemma decompose_CU1_WF : forall r x y,
  well_formed (decompose_CU1 r x y).
Proof. intros. repeat constructor. Qed.

Lemma decompose_CCX_WF : forall x y z,
  well_formed (decompose_CCX x y z).
Proof. intros. repeat constructor. Qed.

Lemma control'_WF : forall a u n, well_formed u -> well_formed (control' a u n).
Proof.
  intros a u n.
  generalize dependent u.
  generalize dependent a.
  induction n; intros a u WF.
  constructor; reflexivity.
  destruct u; simpl.
  inversion WF; subst.
  constructor; apply IHn; assumption.
  destruct u; simpl_WF; repeat constructor.
  apply IHn. repeat constructor.
Qed.

Local Transparent SQIR.Rz SQIR.U1 SQIR.U2 SQIR.U3 SQIR.H SQIR.X SQIR.CNOT SQIR.SWAP UnitaryOps.CU.
Lemma decompose_CU1_fresh : forall dim a r b c,
  UnitaryOps.is_fresh a (to_base_ucom dim (decompose_CU1 r b c)) <->
  UnitaryOps.is_fresh a (UnitaryOps.control b (@SQIR.U1 dim r c)).
Proof.
  intros dim a r b c.
  split; intro H; simpl in *.
  invert_is_fresh.
  repeat constructor; auto.
  invert_is_fresh.
  repeat constructor; auto.
Qed.

Lemma decompose_CCX_fresh : forall dim a b c d,
  UnitaryOps.is_fresh a (to_base_ucom dim (decompose_CCX b c d)) <->
  UnitaryOps.is_fresh a (UnitaryOps.control b (@SQIR.CNOT dim c d)).
Proof.
  intros dim a b c d.
  split; intro H; simpl in *.
  invert_is_fresh.
  repeat constructor; auto.
  invert_is_fresh.
  repeat constructor; auto.
Qed.

Lemma fresh_control' : forall dim a b u n,
  (fuel u < n)%nat ->
  well_formed u ->
  (a <> b /\ UnitaryOps.is_fresh a (to_base_ucom dim u)) <-> 
  UnitaryOps.is_fresh a (to_base_ucom dim (control' b u n)).
Proof.
  intros dim a b u n Hfu WF.
  split.
  - intros [H1 H2].
    generalize dependent u.
    generalize dependent b.
    generalize dependent a.
    induction n; intros a b H1 u Hfu WF H2.
    lia.
    destruct u.
    inversion H2; subst.
    simpl in Hfu.
    inversion WF; subst.
    simpl.
    constructor; apply IHn; auto; lia.
    simpl.
    destruct u; simpl_WF.
    (* solve the cases that don't make a recursive call *)
    all: match goal with
         | |- context[control' _ _ _] => idtac
         | |- _ => invert_is_fresh; repeat constructor; auto
         end.
    (* C-CU1 *)
    apply IHn.
    assumption.
    simpl in Hfu. rewrite fuel_CCX_eq. lia.
    apply decompose_CCX_WF.
    invert_is_fresh; repeat constructor; auto.
  - generalize dependent u.
    generalize dependent b.
    generalize dependent a.
    induction n; intros a b u Hfu WF H.
    lia.
    destruct u.
    inversion H; subst.
    simpl in Hfu.
    inversion WF; subst.
    eapply IHn in H2 as [Hu1_1 Hu1_2].
    eapply IHn in H5 as [Hu2_1 Hu2_2].
    split. apply Hu1_1.
    constructor.
    apply Hu1_2.
    apply Hu2_2.
    lia.
    apply H4.
    lia.
    apply H3.
    destruct u; simpl_WF; simpl in *.
    1-6: invert_is_fresh; split; auto;repeat constructor; auto.
    apply IHn in H as [? ?].
    split; auto.
    rewrite fuel_CCX_eq. lia.
    apply decompose_CCX_WF.
Qed.

(*Lemma cont_decompose_CCX_fresh : forall dim a b c d e n,
  (fuel_CCX < n)%nat ->
  UnitaryOps.is_fresh a
    (to_base_ucom dim (control' b (decompose_CCX c d e) n)) <->
  UnitaryOps.is_fresh a
    (UnitaryOps.control b
      (UnitaryOps.control c (@CNOT dim d e))).
Proof.
  intros dim a b c d e n Hn.
  split; intro H.
  apply fresh_control' in H as [? ?].
  apply UnitaryOps.fresh_control.
  split; auto.
  specialize (fuel_CCX_bound1 c d e) as ?. lia.
  apply decompose_CCX_WF.
  apply UnitaryOps.fresh_control in H as [? ?].
  apply fresh_control'.
  specialize (fuel_CCX_bound1 c d e) as ?. lia.
  apply decompose_CCX_WF.
  split; auto.
Qed.

Lemma cont_cont_decompose_CCX_fresh : forall dim a b c d e f n,
  (fuel_CCX < n)%nat ->
  UnitaryOps.is_fresh a
    (to_base_ucom dim (control' b (control' c (decompose_CCX d e f) n) n)) <->
  UnitaryOps.is_fresh a
    (UnitaryOps.control b
       (UnitaryOps.control c (UnitaryOps.control d (@CNOT dim e f)))).
Proof.
  intros dim a b c d e f n Hn.
  split; intro H.
  apply fresh_control' in H as [? ?].
  apply fresh_control' in H1 as [? ?].
  do 2 (apply UnitaryOps.fresh_control; split; auto).
  specialize (fuel_CCX_bound1 d e f) as ?. lia.
  apply decompose_CCX_WF.
  specialize (fuel_CCX_bound2 d e f c n) as ?. lia.
  apply control'_WF.
  apply decompose_CCX_WF.
  apply UnitaryOps.fresh_control in H as [? ?].
  apply UnitaryOps.fresh_control in H1.
  apply fresh_control'.
  specialize (fuel_CCX_bound2 d e f c n) as ?. lia.
  apply control'_WF.
  apply decompose_CCX_WF.
  split; auto.
  apply fresh_control'.
  specialize (fuel_CCX_bound1 d e f) as ?. lia.
  apply decompose_CCX_WF.
  auto.
Qed.*)
Local Opaque SQIR.Rz SQIR.U1 SQIR.U2 SQIR.U3 SQIR.H SQIR.X SQIR.CNOT SQIR.SWAP UnitaryOps.CU.

Local Opaque decompose_CU1.
Lemma control'_correct : forall dim a u n,
  (fuel u < n)%nat ->
  well_formed u ->
  uc_eval dim (control' a u n) = 
    UnitarySem.uc_eval (UnitaryOps.control a (to_base_ucom dim u)).
Proof.
  intros dim a u n.
  generalize dependent u.
  generalize dependent a.
  induction n; intros a u Hfu WF.
  lia.
  destruct u; simpl.
  inversion WF; subst.
  unfold uc_eval in *.
  simpl in *.
  rewrite 2 IHn; try lia; auto.
  destruct u; simpl_WF.
  (* C-X *)
  unfold uc_eval.
  simpl.
  rewrite control_ucom_X.
  reflexivity.
  (* C-H *)
  rewrite <- decompose_CH_is_control_H.
  reflexivity.
  (* C-U1 *)
  rewrite <- decompose_CU1_is_control_U1.
  reflexivity.
  (* C-U2 *)
  rewrite <- decompose_CU2_is_control_U2.
  reflexivity.
  (* C-U3 *)
  rewrite <- decompose_CU3_is_control_U3.
  reflexivity.
  (* C-CX *)
  rewrite <- decompose_CCX_is_control_CX.
  reflexivity.
  (* C-CU1 *)
  unfold uc_eval in *.
  rewrite IHn.
  apply control_cong. 
  apply decompose_CCX_is_control_CX.
  apply decompose_CCX_fresh.
  simpl in Hfu. rewrite fuel_CCX_eq. lia.
  apply decompose_CCX_WF.
Qed.

Lemma control_correct : forall dim a u,
  well_formed u ->
  uc_eval dim (control a u) = 
    UnitarySem.uc_eval (UnitaryOps.control a (to_base_ucom dim u)).
Proof. intros. apply control'_correct; auto. Qed.

Fixpoint map_qubits (f : nat -> nat) (c : ucom U) : ucom U :=
  match c with
  | c1 >> c2 => map_qubits f c1 >> map_qubits f c2
  | uapp g qs => uapp g (List.map f qs)
  end.

Lemma map_qubits_WF : forall f (u : ucom U), 
  well_formed u -> well_formed (map_qubits f u).
Proof.
  intros f u WF.
  induction WF.
  simpl. constructor; auto.
  simpl. constructor.
  rewrite map_length. auto.
Qed.

Lemma map_qubits_same : forall dim f u,
  well_formed u ->
  to_base_ucom dim (map_qubits f u) = UnitaryOps.map_qubits f (to_base_ucom dim u).
Proof.
  intros dim f u WF.
  induction u.
  simpl.
  inversion WF; subst.
  rewrite <- IHu1, <- IHu2 by assumption.
  reflexivity.
  simpl.
  destruct u; simpl_WF; reflexivity.
Qed.

Lemma map_qubits_control' : forall f q u n,
  (fuel u < n)%nat ->
  well_formed u ->
  map_qubits f (control' q u n) = control' (f q) (map_qubits f u) n.
Proof.
  intros f q u n Hfu WF.
  generalize dependent u.
  generalize dependent q.
  induction n; intros q u Hfu WF.
  lia.
  destruct u.
  simpl.
  inversion WF; subst.
  simpl in Hfu.
  rewrite 2 IHn; auto; try lia.
  destruct u; simpl_WF; simpl in *; try reflexivity.
  (* C-CU1 *)
  rewrite IHn.
  reflexivity. 
  rewrite fuel_CCX_eq. lia.
  apply decompose_CCX_WF.
Qed.

Lemma map_qubits_fuel : forall f u, fuel (map_qubits f u) = fuel u.
Proof. intros f u. induction u; simpl; auto. Qed.

Lemma map_qubits_control : forall f q u,
  well_formed u -> map_qubits f (control q u) = control (f q) (map_qubits f u).
Proof. 
  intros. 
  unfold control. 
  rewrite map_qubits_fuel.
  apply map_qubits_control'; auto.
Qed.

Fixpoint npar n (u : U 1) : ucom U :=
  match n with
  | O => SKIP
  | S O => uapp u [O]
  | S n' => npar n' u >> uapp u [n']
  end.

Lemma npar_H_same : forall n,
  uc_eval n (npar n U_H) = UnitarySem.uc_eval (UnitaryOps.npar n SQIR.U_H).
Proof.
  intro dim.
  assert (H : forall n, (0 < dim)%nat -> (n <= dim)%nat -> 
            uc_eval dim (npar n U_H) = 
              UnitarySem.uc_eval (UnitaryOps.npar' dim n SQIR.U_H)).
  { intros n Hdim Hn.
    induction n; try reflexivity.
    destruct n.
    unfold uc_eval. simpl. autorewrite with eval_db. gridify.
    rewrite hadamard_rotation. reflexivity. lia.
    unfold uc_eval in *.
    simpl in *.
    rewrite IHn.
    reflexivity.
    lia. }
  destruct dim; try reflexivity.
  apply H; lia.
Qed.

Fixpoint invert (u : ucom U) : ucom U :=
  match u with
  | u1 >> u2 => invert u2 >> invert u1
  | uapp g qs => 
      match g, qs with
      | U_X, (q1 :: List.nil)%list => X q1
      | U_H, (q1 :: List.nil) => H q1
      | U_U1 r1, (q1 :: List.nil) => U1 (- r1) q1
      | U_U2 r1 r2, (q1 :: List.nil) => U2 (- r2 - PI) (- r1 + PI) q1
      | U_U3 r1 r2 r3, (q1 :: List.nil) => U3 (- r1) (- r3) (- r2) q1
      | U_CX, (q1 :: q2 :: List.nil) => CX q1 q2
      | U_CCX, (q1 :: q2 :: q3 :: List.nil) => CCX q1 q2 q3
      (* dummy value - unreachable for well-formed progs *)
      | _, _ => SKIP
      end
  end.

Lemma is_fresh_invert : forall {dim} q (u : base_ucom dim),
  is_fresh q u <-> is_fresh q (UnitaryOps.invert u).
Proof.
  intros dim q u.
  split; intro H.
  - induction u; try dependent destruction u.
    inversion H; subst.
    constructor; auto.
    invert_is_fresh; constructor; auto.
    invert_is_fresh; constructor; auto.
  - induction u; try dependent destruction u.
    inversion H; subst.
    constructor; auto.
    invert_is_fresh; constructor; auto.
    invert_is_fresh; constructor; auto.
Qed.

Local Transparent SQIR.U1 SQIR.U2 SQIR.U3 SQIR.SWAP SQIR.CNOT.
Lemma invert_same : forall dim u,
  well_formed u -> (* WF isn't necessary, but makes the proof easier *)
  uc_eval dim (invert u) = 
    UnitarySem.uc_eval (UnitaryOps.invert (to_base_ucom dim u)).
Proof.
  intros dim u WF.
  induction u.
  unfold uc_eval in *.
  simpl.
  inversion WF; subst.
  rewrite IHu1, IHu2; auto.
  destruct u; simpl_WF; simpl. 
  (* U_X *)
  rewrite invert_X.
  reflexivity.
  (* U_H *)
  rewrite invert_H.
  reflexivity.
  (* U_U1 *)
  unfold uc_eval. simpl.
  rewrite Ropp_0.
  apply f_equal.
  unfold rotation.
  solve_matrix; autorewrite with Cexp_db trig_db R_db; lca.
  (* U_U2 *)
  unfold uc_eval. simpl.
  apply f_equal.
  unfold rotation.
  solve_matrix; autorewrite with Cexp_db trig_db R_db; lca.
  (* U_U3 *)
  reflexivity.
  (* U_CX *)
  reflexivity.
  (* U_CCX *)
Admitted.
