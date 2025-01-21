Require Import GateDecompositions.

(** Definitions for the gate set and program representation used for extraction. *)

(* Experimenting with a version of ucom that uses a list argument and no 
   dependent dim type

   TODO: Consider replacing the defn in SQIR.v with this one *)
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
    length l = O ->
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
  | U_CU1 : R -> U 2
  | U_CH : U 2
  | U_SWAP : U 2
  | U_CCX : U 3
  | U_CCU1 : R -> U 3
  | U_CSWAP : U 3
  | U_C3X : U 4
  | U_C4X : U 5.

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
      | U_CU1 r, (q1 :: q2 :: List.nil) => UnitaryOps.control q1 (U1 r q2)
      | U_CH, (q1 :: q2 :: List.nil) => UnitaryOps.control q1 (H q2)
      | U_SWAP, (q1 :: q2 :: List.nil) => SWAP q1 q2
      | U_CCX, (q1 :: q2 :: q3 :: List.nil) => UnitaryOps.control q1 (CNOT q2 q3)
      | U_CCU1 r, (q1 :: q2 :: q3 :: List.nil) => 
          UnitaryOps.control q1 (UnitaryOps.control q2 (U1 r q3))
      | U_CSWAP, (q1 :: q2 :: q3 :: List.nil) => UnitaryOps.control q1 (SWAP q2 q3)
      | U_C3X, (q1 :: q2 :: q3 :: q4 :: List.nil) => 
          UnitaryOps.control q1 (UnitaryOps.control q2 (CNOT q3 q4))
      | U_C4X, (q1 :: q2 :: q3 :: q4 :: q5 :: List.nil) => 
          UnitaryOps.control q1 
            (UnitaryOps.control q2 (UnitaryOps.control q3 (CNOT q4 q5)))
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
  (* U_X, U_H, U_U1, U_U2, U_U3, U_CX, U_SWAP cases *) 
  all: repeat constructor; try lia.
  (* U_CU1 *)
  apply uc_well_typed_control in WT as [? [? ?]].
  invert_WT; invert_is_fresh.
  apply uc_well_typed_control.
  repeat split; try constructor; lia.
  (* U_CH *)
  apply uc_well_typed_control in WT as [? [? ?]].
  invert_WT; invert_is_fresh.
  apply uc_well_typed_control.
  repeat split; try constructor; lia.
  (* U_CCX *)
  apply uc_well_typed_control in WT as [? [? ?]].
  invert_WT; invert_is_fresh.
  apply uc_well_typed_control.
  repeat split; try constructor; lia.
  (* U_CCU1 *)
  apply uc_well_typed_control in WT as [? [? ?]].
  apply fresh_control in H0 as [? ?].
  apply uc_well_typed_control in H1 as [? [? ?]].
  invert_WT; invert_is_fresh.
  apply uc_well_typed_control.
  repeat split; try lia.
  apply fresh_control; split; try constructor; lia.
  apply uc_well_typed_control; repeat split; try constructor; lia.
  (* U_CSWAP *)
  apply uc_well_typed_control in WT as [? [? ?]].
  invert_WT; invert_is_fresh.
  apply uc_well_typed_control.
  repeat split; repeat constructor; lia.
  (* U_C3X *)
  apply uc_well_typed_control in WT as [? [? ?]].
  apply fresh_control in H0 as [? ?].
  apply uc_well_typed_control in H1 as [? [? ?]].
  invert_WT; invert_is_fresh.
  apply uc_well_typed_control.
  repeat split; try lia.
  apply fresh_control; split; try constructor; lia.
  apply uc_well_typed_control; repeat split; try constructor; lia.
  (* U_C4X *)
  apply uc_well_typed_control in WT as [? [? ?]].
  apply fresh_control in H0 as [? ?].
  apply fresh_control in H2 as [? ?].
  apply uc_well_typed_control in H1 as [? [? ?]].
  apply fresh_control in H4 as [? ?].
  apply uc_well_typed_control in H5 as [? [? ?]].
  invert_WT; invert_is_fresh.
  apply uc_well_typed_control.
  repeat split.
  lia.
  apply fresh_control; split. lia.
  apply fresh_control; split; try constructor; lia.
  apply uc_well_typed_control; repeat split. lia.
  apply fresh_control; split; try constructor; lia.
  apply uc_well_typed_control; repeat split; try constructor; lia.
Qed.
Local Transparent UnitaryOps.control.
Local Opaque SQIR.ID SQIR.X SQIR.H SQIR.Rz SQIR.U1 SQIR.U2 SQIR.U3 SQIR.CNOT SQIR.SWAP.

(* Defining constants separately for easier extraction. *)
Definition R2 : R := 2.
Definition R4 : R := 4.
Definition R8 : R := 8.

Definition X q := uapp U_X [q].
Definition H q := uapp U_H [q].
Definition U1 r1 q := uapp (U_U1 r1) [q].
Definition U2 r1 r2 q := uapp (U_U2 r1 r2) [q].
Definition U3 r1 r2 r3 q := uapp (U_U3 r1 r2 r3) [q].
Definition T q := U1 (PI / R4) q.
Definition Tdg q := U1 (- (PI / R4)) q.
Definition ID q := U1 R0 q.
Definition SKIP := ID O. (* used as a dummy value *)
Definition P8 q := U1 (PI / R8) q.
Definition P8dg q := U1 (- (PI / R8)) q.
Definition CX q1 q2 := uapp U_CX (q1 :: q2 :: List.nil).
Definition CU1 r q1 q2 := uapp (U_CU1 r) (q1 :: q2 :: List.nil).
Definition CH q1 q2 := uapp U_CH (q1 :: q2 :: List.nil).
Definition SWAP q1 q2 := uapp U_SWAP (q1 :: q2 :: List.nil).
Definition CCX q1 q2 q3 := uapp U_CCX (q1 :: q2 :: q3 :: List.nil).
Definition CCU1 r q1 q2 q3 := uapp (U_CCU1 r) (q1 :: q2 :: q3 :: List.nil).
Definition CSWAP q1 q2 q3 := uapp U_CSWAP (q1 :: q2 :: q3 :: List.nil).
Definition C3X q1 q2 q3 q4 := uapp U_C3X (q1 :: q2 :: q3 :: q4 :: List.nil).
Definition C4X q1 q2 q3 q4 q5 := uapp U_C4X (q1 :: q2 :: q3 :: q4 :: q5 :: List.nil).

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
      | U_CH, (q1 :: q2 :: List.nil) => CH q1 q2
      | U_CU1 r, (q1 :: q2 :: List.nil) => CU1 (- r) q1 q2
      | U_SWAP, (q1 :: q2 :: List.nil) => SWAP q1 q2
      | U_CCX, (q1 :: q2 :: q3 :: List.nil) => CCX q1 q2 q3
      | U_CCU1 r, (q1 :: q2 :: q3 :: List.nil) => CCU1 (- r) q1 q2 q3
      | U_CSWAP, (q1 :: q2 :: q3 :: List.nil) => CSWAP q1 q2 q3
      | U_C3X, (q1 :: q2 :: q3 :: q4 :: List.nil) => C3X q1 q2 q3 q4
      | U_C4X, (q1 :: q2 :: q3 :: q4 :: q5 :: List.nil) => C4X q1 q2 q3 q4 q5
      (* dummy value - unreachable for well-formed progs *)
      | _, _ => SKIP
      end
  end.

Lemma invert_WF : forall u, well_formed u -> well_formed (invert u).
Proof.
  intros u H. 
  induction u. 
  inversion H; subst.
  simpl. constructor; auto.
  destruct u; simpl_WF; constructor; reflexivity.
Qed.

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

Local Opaque UnitaryOps.control.
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
  destruct u; simpl_WF; simpl; try reflexivity.
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
  lma'; autorewrite with Cexp_db trig_db R_db; lca.
  (* U_U2 *)
  unfold uc_eval. simpl.
  apply f_equal.
  lma'; autorewrite with Cexp_db trig_db R_db; lca.
  (* U_CU1 *)
  rewrite invert_control.
  unfold uc_eval. simpl.
  apply control_cong.
  unfold uc_equiv. simpl.
  rewrite Ropp_0.
  apply f_equal.
  lma'; autorewrite with Cexp_db trig_db R_db; lca.
  split; intro; invert_is_fresh; repeat constructor; auto.
  (* U_CH *)
  rewrite invert_control.
  apply control_cong.
  rewrite invert_H.
  reflexivity.
  apply is_fresh_invert.
  (* U_SWAP *)
  unfold uc_eval. simpl. 
  rewrite Mmult_assoc. 
  reflexivity.
  (* U_CCX *)
  rewrite invert_control.
  reflexivity.
  (* U_CCU1 *)
  rewrite invert_control.
  unfold uc_eval. simpl.
  apply control_cong.
  rewrite invert_control.
  apply control_cong.
  unfold uc_equiv. simpl.
  rewrite Ropp_0.
  apply f_equal.
  lma'; autorewrite with Cexp_db trig_db R_db; lca.
  split; intro; invert_is_fresh; repeat constructor; auto.
  rewrite <- is_fresh_invert.
  rewrite <- 2 fresh_control.
  split; intros [? ?]; invert_is_fresh; repeat constructor; auto.
  (* U_CSWAP *)
  rewrite invert_control.
  unfold uc_eval. simpl.
  apply control_cong.
  unfold uc_equiv. simpl.
  rewrite Mmult_assoc. 
  reflexivity.
  split; intro; invert_is_fresh; repeat constructor; auto.
  (* U_C3X *)
  rewrite invert_control.
  apply control_cong.
  rewrite invert_control.
  reflexivity.
  apply is_fresh_invert.
  (* U_C4X *)
  rewrite invert_control.
  apply control_cong.
  rewrite invert_control.
  apply control_cong.
  rewrite invert_control.
  reflexivity.
  apply is_fresh_invert.
  apply is_fresh_invert.
Qed.
Local Opaque SQIR.U1 SQIR.U2 SQIR.U3 SQIR.SWAP SQIR.CNOT.

(** Optimized gate decompositions **)

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

Definition decompose_CCU1 r1 (a b c : nat) : ucom U := 
  CU1 (r1/R2) a b >> CX b c >> CU1 (-r1/R2) a c >> CX b c >> CU1 (r1/R2) a c.

Definition decompose_CSWAP (a b c : nat) : ucom U := 
  CX c b >> CCX a b c >> CX c b.

Definition decompose_CCX (a b c : nat) : ucom U := 
  H c >> CX b c >> Tdg c >> CX a c >> 
  T c >> CX b c >> Tdg c >> CX a c >> 
  CX a b >> Tdg b >> CX a b >>
  T a >> T b >> T c >> H c.

Definition decompose_C3X (a b c d : nat) : ucom U := 
  H d >> P8 a >> P8 b >> P8 c >> P8 d >>
  CX a b >> P8dg b >> CX a b >> CX b c >> P8dg c >> 
  CX a c >> P8 c >> CX b c >> P8dg c >> CX a c >> 
  CX c d >> P8dg d >> CX b d >> P8 d >> CX c d >> 
  P8dg d >> CX a d >> P8 d >> CX c d >> P8dg d >> 
  CX b d >> P8 d >> CX c d >> P8dg d >> CX a d >> H d.

Definition decompose_RC3X (a b c d : nat) : ucom U := 
  H d >> T d >> CX c d >> Tdg d >> H d >>
  CX a d >> T d >> CX b d >> Tdg d >> CX a d >>
  T d >> CX b d >> Tdg d >> H d >> T d >>
  CX c d >> Tdg d >> H d.

Definition CRTX (r : R) (a b : nat) : ucom U := 
  H b >> CU1 r a b >> H b.

Definition decompose_C3SQRTX (a b c d : nat) : ucom U := 
  CRTX (PI/R8) a d >> CX a b >>
  CRTX (-PI/R8) b d >> CX a b >>
  CRTX (PI/R8) b d >> CX b c >>
  CRTX (-PI/R8) c d >> CX a c >>
  CRTX (PI/R8) c d >> CX b c >>
  CRTX (-PI/R8) c d >> CX a c >>
  CRTX (PI/R8) c d.

Definition decompose_C4X (a b c d e : nat) : ucom U := 
  CRTX (PI/R2) d e >> 
  decompose_RC3X a b c d >>
  CRTX (-PI/R2) d e >> 
  invert (decompose_RC3X a b c d) >>
  decompose_C3SQRTX a b c e.

Fixpoint control' a (c : ucom U) (n : nat) : ucom U :=
  match n with 
  | O => SKIP (* unreachable with "fuel" below *)
  | S n' => 
      match c with
      | c1 >> c2 => control' a c1 n' >> control' a c2 n'
      | uapp U_X (b :: List.nil) => CX a b
      | uapp U_H (b :: List.nil) => CH a b
      | uapp (U_U1 r) (b :: List.nil) => CU1 r a b
      | uapp U_CX (b :: c :: List.nil) => CCX a b c
      | uapp (U_CU1 r) (b :: c :: List.nil) => CCU1 r a b c
      | uapp U_CCX (b :: c :: d :: List.nil) => C3X a b c d
      | uapp U_SWAP (b :: c :: List.nil) => CSWAP a b c
      | uapp U_C3X (b :: c :: d :: e :: List.nil) => C4X a b c d e
      (* We don't supprt CU2, CU3, CCH, C3U1, CCSWAP or C5X, so decompose *)
      | uapp (U_U2 r1 r2) (b :: List.nil) => decompose_CU2 r1 r2 a b
      | uapp (U_U3 r1 r2 r3) (b :: List.nil) => decompose_CU3 r1 r2 r3 a b
      | uapp U_CH (b :: c :: List.nil) => control' a (decompose_CH b c) n'
      | uapp (U_CCU1 r) (b :: c :: d :: List.nil) => 
          control' a (decompose_CCU1 r b c d) n'
      | uapp U_CSWAP (b :: c :: d :: List.nil) => 
          control' a (decompose_CSWAP b c d) n'
      | uapp U_C4X (b :: c :: d :: e :: f :: List.nil) => 
          control' a (decompose_C4X b c d e f) n'
      | _ =>  SKIP (* unreachable *)
      end
  end.

(* Fuel for control'. This may return a larger number than necessary (meaning that
   control' will return before consuming all its fuel), but this will always
   provide enough fuel to complete the computation (see how "fuel" is used in 
   control'_correct. *)
Definition fuel_CH : nat := 2.
Definition fuel_CCU1 : nat := 4.
Definition fuel_CSWAP : nat := 2.
Definition fuel_C4X : nat := 21.
Fixpoint fuel (c : ucom U) :=
  match c with
  | c1 >> c2 => S (max (fuel c1) (fuel c2))
  | uapp U_CH _ => S fuel_CH
  | uapp (U_CCU1 r) _ => S fuel_CCU1
  | uapp U_CSWAP _ => S fuel_CSWAP
  | uapp U_C4X _ => S fuel_C4X
  | _ => O
  end.
Definition control a (c : ucom U) :=
  control' a c (S (fuel c)).

Lemma fuel_CH_eq : forall a b, fuel (decompose_CH a b) = fuel_CH.
Proof. intros. reflexivity. Qed.
Lemma fuel_CCU1_eq : forall r a b c, fuel (decompose_CCU1 r a b c) = fuel_CCU1.
Proof. intros. reflexivity. Qed.
Lemma fuel_CSWAP_eq : forall a b c, fuel (decompose_CSWAP a b c) = fuel_CSWAP.
Proof. intros. reflexivity. Qed.
Lemma fuel_C4X_eq : forall a b c d e, fuel (decompose_C4X a b c d e) = fuel_C4X.
Proof. intros. reflexivity. Qed.

Lemma decompose_CH_WF : forall x y, well_formed (decompose_CH x y).
Proof. intros. repeat constructor. Qed.

Lemma decompose_CCU1_WF : forall r x y z, well_formed (decompose_CCU1 r x y z).
Proof. intros. repeat constructor. Qed.

Lemma decompose_CSWAP_WF : forall x y z, well_formed (decompose_CSWAP x y z).
Proof. intros. repeat constructor. Qed.

Lemma decompose_C4X_WF : forall w v x y z, well_formed (decompose_C4X w v x y z).
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
  all: apply IHn; repeat constructor.
Qed.

Local Transparent SQIR.ID SQIR.Rz SQIR.U1 SQIR.U2 SQIR.U3 SQIR.H SQIR.X SQIR.CNOT SQIR.SWAP UnitaryOps.CU.

Ltac invert_is_fresh :=
  repeat match goal with
  | H : is_fresh _ (UnitaryOps.control _ _) |- _ => apply fresh_control in H as [? ?]
  | H : is_fresh _ _ |- _ => inversion H; subst; clear H
  end; clear_dups.

Lemma decompose_CH_fresh : forall dim a b c,
  UnitaryOps.is_fresh a (to_base_ucom dim (decompose_CH b c)) <->
  UnitaryOps.is_fresh a (UnitaryOps.control b (@SQIR.H dim c)).
Proof.
  intros dim a b c.
  split; intro H; simpl in *.
  invert_is_fresh.
  apply fresh_control; repeat constructor; auto.
  invert_is_fresh.
  repeat constructor; auto.
Qed.

Lemma decompose_CCU1_fresh : forall dim a r b c d,
  is_fresh a (to_base_ucom dim (decompose_CCU1 r b c d)) <->
  is_fresh a (UnitaryOps.control b (UnitaryOps.control c (@SQIR.U1 dim r d))).
Proof.
  intros dim a r b c d.
  split; intro H; simpl in *.
  invert_is_fresh.
  apply fresh_control; split.
  invert_is_fresh; auto.
  apply fresh_control; repeat constructor; auto.
  invert_is_fresh.
  repeat constructor; auto.
  all: apply fresh_control; repeat constructor; auto.
Qed.

Lemma decompose_CSWAP_fresh : forall dim a b c d,
  is_fresh a (to_base_ucom dim (decompose_CSWAP b c d)) <->
  is_fresh a (UnitaryOps.control b (@SQIR.SWAP dim c d)).
Proof.
  intros dim a b c d.
  split; intro H; simpl in *.
  invert_is_fresh.
  apply fresh_control; repeat constructor; auto.
  invert_is_fresh.
  repeat constructor; auto.
  apply fresh_control; repeat constructor; auto.
Qed.

Lemma decompose_CCX_fresh : forall dim a b c d,
  is_fresh a (to_base_ucom dim (decompose_CCX b c d)) <->
  is_fresh a (UnitaryOps.control b (@SQIR.CNOT dim c d)).
Proof.
  intros dim a b c d.
  split; intro H; simpl in *.
  invert_is_fresh.
  apply fresh_control; repeat constructor; auto.
  invert_is_fresh.
  repeat constructor; auto.
Qed.

Lemma decompose_C3X_fresh : forall dim a b c d e,
  is_fresh a (to_base_ucom dim (decompose_C3X b c d e)) <->
  is_fresh a (UnitaryOps.control b (UnitaryOps.control c (@CNOT dim d e))).
Proof.
  intros dim a b c d e.
  split; intro H; simpl in *.
  invert_is_fresh.
  apply fresh_control; split; auto.
  apply fresh_control; repeat constructor; auto.
  invert_is_fresh.
  repeat constructor; auto.
Qed.

Lemma decompose_C4X_fresh : forall dim a b c d e f,
  is_fresh a (to_base_ucom dim (decompose_C4X b c d e f)) <->
  is_fresh a (UnitaryOps.control b (UnitaryOps.control c (UnitaryOps.control d (@CNOT dim e f)))).
Proof.
  intros dim a b c d e f.
  split; intro H; simpl in *.
  - invert_is_fresh.
    apply fresh_control; split; auto.
    apply fresh_control; split; auto.
    apply fresh_control; repeat constructor; auto.
  - invert_is_fresh.
    repeat constructor; auto.
    all: apply fresh_control; repeat constructor; auto.
Qed.

Lemma fresh_control' : forall dim a b u n,
  (fuel u < n)%nat ->
  well_formed u ->
  (a <> b /\ is_fresh a (to_base_ucom dim u)) <-> 
  is_fresh a (to_base_ucom dim (control' b u n)).
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
    1-7,9-10: invert_is_fresh; repeat (apply fresh_control; split); 
    repeat constructor; auto.
    (* C-CH *)
    apply IHn.
    assumption.
    simpl in Hfu. rewrite fuel_CH_eq. lia.
    apply decompose_CH_WF.
    apply decompose_CH_fresh.
    assumption.
    (* C-CCU1 *)
    apply IHn.
    assumption.
    simpl in Hfu. rewrite fuel_CCU1_eq. lia.
    apply decompose_CCU1_WF.
    apply decompose_CCU1_fresh.
    assumption.
    (* C-CSWAP *)
    apply IHn.
    assumption.
    simpl in Hfu. rewrite fuel_CSWAP_eq. lia.
    apply decompose_CSWAP_WF.
    apply decompose_CSWAP_fresh.
    assumption.
    (* C-C4X *)
    apply fresh_control; split; auto.
    apply IHn.
    assumption.
    simpl in Hfu. rewrite fuel_C4X_eq. lia.
    apply decompose_C4X_WF.
    apply decompose_C4X_fresh.
    assumption.
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
    destruct u; simpl_WF.
    (* solve the cases that don't make a recursive call *)
    1-7,9-10: simpl in *; invert_is_fresh; repeat (apply fresh_control; split); 
    split; auto; repeat constructor; auto.
    apply fresh_control; split; repeat constructor; auto.
    apply fresh_control; split; repeat constructor; auto.
    (* C-CH *)
    apply IHn in H as [? ?].
    split; auto.
    apply decompose_CH_fresh in H1.
    assumption.
    simpl in Hfu. rewrite fuel_CH_eq. lia.
    apply decompose_CH_WF.
    (* C-CCU1 *)
    apply IHn in H as [? ?].
    split; auto.
    apply decompose_CCU1_fresh in H1.
    assumption.
    simpl in Hfu. rewrite fuel_CCU1_eq. lia.
    apply decompose_CCU1_WF.
    (* C-CSWAP *)
    apply IHn in H as [? ?].
    split; auto.
    apply decompose_CSWAP_fresh in H1.
    assumption.
    simpl in Hfu. rewrite fuel_CSWAP_eq. lia.
    apply decompose_CSWAP_WF.
    (* C-C4X *)
    apply fresh_control in H. assumption.
    apply IHn in H as [? ?].
    split; auto.
    apply decompose_C4X_fresh in H1.
    assumption.
    simpl in Hfu. rewrite fuel_C4X_eq. lia.
    apply decompose_C4X_WF.
Qed.

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
  all: try reflexivity.
  (* C-X *)
  rewrite <- CNOT_is_control_X.
  reflexivity.
  (* C-U2 *)
  rewrite <- CU2_is_control_U2.
  reflexivity.
  (* C-U3 *)
  rewrite <- CU3_is_control_U3.
  reflexivity.
  (* C-H *)
  unfold uc_eval in *.
  rewrite IHn.
  apply control_cong. 
  rewrite <- CH_is_control_H.
  reflexivity.
  apply decompose_CH_fresh.
  simpl in Hfu. rewrite fuel_CH_eq. lia.
  apply decompose_CH_WF.
  (* C-CU1 *)
  unfold uc_eval in *.
  rewrite IHn.
  apply control_cong. 
  rewrite <- CCU1_is_control_CU1.
  simpl.
  repeat rewrite <- CU1_is_control_U1.
  reflexivity.
  apply decompose_CCU1_fresh.
  simpl in Hfu. rewrite fuel_CCU1_eq. lia.
  apply decompose_CCU1_WF.
  (* C-CSWAP *)
  unfold uc_eval in *.
  rewrite IHn.
  apply control_cong. 
  apply CSWAP_is_control_SWAP.
  apply decompose_CSWAP_fresh.
  simpl in Hfu. rewrite fuel_CSWAP_eq. lia.
  apply decompose_CSWAP_WF.
  (* C-C4X *)
  unfold uc_eval in *.
  rewrite IHn.
  apply control_cong.
  unfold uc_equiv.
  replace (UnitarySem.uc_eval (to_base_ucom dim (decompose_C4X n0 n1 n2 n3 n4)))
    with (UnitarySem.uc_eval (@GateDecompositions.C4X dim n0 n1 n2 n3 n4)).
  rewrite C4X_is_control_C3X.
  apply control_cong.
  rewrite C3X_is_control_CCX.
  reflexivity.
  apply decompose_C3X_fresh.
  simpl.
  repeat rewrite <- CU1_is_control_U1.
  repeat rewrite invert_H.
  repeat rewrite invert_CNOT.
  unfold SQIR.T, SQIR.TDAG.
  repeat rewrite invert_Rz.
  reflexivity.
  apply decompose_C4X_fresh.
  simpl in Hfu. rewrite fuel_C4X_eq. lia.
  apply decompose_C4X_WF.
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
  (* C-CH *)
  rewrite IHn.
  reflexivity. 
  rewrite fuel_CH_eq. lia.
  apply decompose_CH_WF.
  (* C-CCU1 *)
  rewrite IHn.
  reflexivity. 
  rewrite fuel_CCU1_eq. lia.
  apply decompose_CCU1_WF.
  (* C-CSWAP *)
  rewrite IHn.
  reflexivity. 
  rewrite fuel_CSWAP_eq. lia.
  apply decompose_CSWAP_WF.
  (* C-C4X *)
  rewrite IHn.
  reflexivity. 
  rewrite fuel_C4X_eq. lia.
  apply decompose_C4X_WF.
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
    rewrite I_rotation. Msimpl.
    rewrite hadamard_rotation. reflexivity.
    unfold uc_eval in *.
    simpl in *.
    rewrite IHn.
    reflexivity.
    lia. }
  destruct dim; try reflexivity.
  apply H; lia.
Qed.

(* VOQC currently doesn't support CH, CU1, CCU1, CSWAP, C3X, or C4X so it's useful 
   to decompose these gates before writing out to a file. *)
Fixpoint decompose_to_voqc_gates1 (u : ucom U) : ucom U :=
  match u with
  | u1 >> u2 => decompose_to_voqc_gates1 u1 >> decompose_to_voqc_gates1 u2
  | uapp (U_CCU1 r) (q1 :: q2 :: q3 :: List.nil) => decompose_CCU1 r q1 q2 q3
  | uapp U_C4X (q1 :: q2 :: q3 :: q4 :: q5 :: List.nil) => decompose_C4X q1 q2 q3 q4 q5
  | _ => u
  end.

Fixpoint decompose_to_voqc_gates2 (u : ucom U) : ucom U :=
  match u with
  | u1 >> u2 => decompose_to_voqc_gates2 u1 >> decompose_to_voqc_gates2 u2
  | uapp U_CH (q1 :: q2 :: List.nil) => decompose_CH q1 q2
  | uapp (U_CU1 r) (q1 :: q2 :: List.nil) => decompose_CU1 r q1 q2
  | uapp U_CSWAP (q1 :: q2 :: q3 :: List.nil) => decompose_CSWAP q1 q2 q3
  | uapp U_C3X (q1 :: q2 :: q3 :: q4 :: List.nil) => decompose_C3X q1 q2 q3 q4
  | _ => u
  end.

Definition decompose_to_voqc_gates u :=
  decompose_to_voqc_gates2 (decompose_to_voqc_gates1 u).

Lemma decompose_to_voqc_gates_preserves_semantics : forall dim u,
  uc_eval dim (decompose_to_voqc_gates u) = uc_eval dim u.
Proof.
  intro dim.
  assert (H1: forall u, uc_eval dim (decompose_to_voqc_gates1 u) = uc_eval dim u).
  { induction u.
    unfold uc_eval in *.
    simpl. 
    rewrite IHu1, IHu2.
    reflexivity.
    destruct u; simpl; try reflexivity.
    do 4 (destruct l; try reflexivity).
    unfold uc_eval; simpl. 
    rewrite <- CCU1_is_control_CU1.
    repeat rewrite <- CU1_is_control_U1.
    reflexivity.
    do 6 (destruct l; try reflexivity).
    unfold uc_eval. 
    replace (UnitarySem.uc_eval (to_base_ucom dim (decompose_C4X n n0 n1 n2 n3)))
      with (UnitarySem.uc_eval (@GateDecompositions.C4X dim n n0 n1 n2 n3)).
    rewrite C4X_is_control_C3X.
    apply control_cong.
    rewrite C3X_is_control_CCX.
    reflexivity.
    apply decompose_C3X_fresh.
    simpl.
    repeat rewrite <- CU1_is_control_U1.
    repeat rewrite invert_H.
    repeat rewrite invert_CNOT.
    unfold SQIR.T, SQIR.TDAG.
    repeat rewrite invert_Rz. 
    reflexivity. }
  assert (H2: forall u, uc_eval dim (decompose_to_voqc_gates2 u) = uc_eval dim u).
  { induction u.
    unfold uc_eval in *.
    simpl. 
    rewrite IHu1, IHu2.
    reflexivity.
    destruct u; simpl; try reflexivity.
    do 3 (destruct l; try reflexivity).
    apply CU1_is_control_U1.
    do 3 (destruct l; try reflexivity).
    apply CH_is_control_H.
    do 4 (destruct l; try reflexivity).
    apply CSWAP_is_control_SWAP.
    do 4 (destruct l; try reflexivity).
    destruct l; [| reflexivity].
    apply C3X_is_control_CCX. }
  unfold decompose_to_voqc_gates.
  intro u. rewrite H2, H1. reflexivity.
Qed.
