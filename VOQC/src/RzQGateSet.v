Require Export UnitaryListRepresentation.
Require Export NonUnitaryListRepresentation.
Require Export QArith.

Local Open Scope Z_scope.
Local Open Scope Q_scope.

(** RzQ Gate Set **)

Module RzQGateSet <: GateSet.

(* In our optimizer we use the gate set {H, X, RzQ, CNOT} where RzQ is
   rotation about the z-axis by i * PI / (2 ^ k) for integer i. We'll 
   call this the RzQ gate set. *)

Inductive RzQ_Unitary : nat -> Set := 
  | URzQ_H           : RzQ_Unitary 1 
  | URzQ_X           : RzQ_Unitary 1
  | URzQ_Rz (a : Q)  : RzQ_Unitary 1
  | URzQ_CNOT        : RzQ_Unitary 2.
Definition U := RzQ_Unitary.

Definition match_gate {n} (u u' : U n) : bool :=
  match u, u' with
  | URzQ_H, URzQ_H | URzQ_X, URzQ_X | URzQ_CNOT, URzQ_CNOT => true
  | URzQ_Rz q, URzQ_Rz q' => Qeq_bool q q'
  | _, _ => false
  end.

Definition to_base {n} (u : U n) :=
  match u with
  | URzQ_H     => U_R (PI/2) 0 PI
  | URzQ_X     => U_R PI 0 PI
  | URzQ_Rz a  => U_R 0 0 (Qreals.Q2R a * PI)%R
  | URzQ_CNOT  => U_CNOT
  end.

Lemma match_gate_implies_eq : forall n (u u' : U n), 
  match_gate u u' = true -> to_base u = to_base u'. 
Proof.
  intros n u u' H.
  dependent destruction u; dependent destruction u'; 
  auto; inversion H. simpl.
  apply Qeq_bool_iff in H1.
  apply f_equal. apply RMicromega.Q2R_m in H1. rewrite H1. reflexivity.
Qed.

End RzQGateSet.
Export RzQGateSet.

Module RzQProps := UListRepresentationProps RzQGateSet.
Export RzQProps.

(* Useful shorthands. *)

Definition URzQ_I := URzQ_Rz 0.
Definition URzQ_T := URzQ_Rz (1 / 4).
Definition URzQ_P := URzQ_Rz (1 / 2).
Definition URzQ_Z := URzQ_Rz 1.
Definition URzQ_PDAG := URzQ_Rz (3 / 2).
Definition URzQ_TDAG := URzQ_Rz (7 / 4).
Definition T {dim} q := @App1 _ dim URzQ_T q.
Definition TDAG {dim} q := @App1 _ dim URzQ_TDAG q.
Definition P {dim} q := @App1 _ dim URzQ_P q.
Definition PDAG {dim} q := @App1 _ dim URzQ_PDAG q.
Definition Z {dim} q := @App1 _ dim URzQ_Z q.
Definition Rz {dim} i q := @App1 _ dim (URzQ_Rz i) q.
Definition H {dim} q := @App1 _ dim URzQ_H q.
Definition X {dim} q := @App1 _ dim URzQ_X q.
Definition CNOT {dim} q1 q2 := @App2 _ dim URzQ_CNOT q1 q2.

Definition RzQ_ucom dim := ucom RzQ_Unitary dim.
Definition RzQ_ucom_l dim := gate_list RzQ_Unitary dim.
Definition RzQ_com dim := com RzQ_Unitary dim.
Definition RzQ_com_l dim := com_list RzQ_Unitary dim.

(* Used to convert benchmarks to RzQ set. *)
Definition CCX {dim} a b c : RzQ_ucom_l dim :=
  H c :: CNOT b c :: TDAG c :: CNOT a c :: 
  T c :: CNOT b c :: TDAG c :: CNOT a c :: 
  CNOT a b :: TDAG b :: CNOT a b :: 
  T a :: T b :: T c :: H c :: []. 
Definition CCZ {dim} a b c : RzQ_ucom_l dim :=
  CNOT b c :: TDAG c :: CNOT a c :: 
  T c :: CNOT b c :: TDAG c :: CNOT a c :: 
  CNOT a b :: TDAG b :: CNOT a b :: 
  T a :: T b :: T c :: []. 

(* re-define for with the match_gate arg. fixed *)
Definition remove_prefix {dim} (l pfx : RzQ_ucom_l dim) :=
  remove_prefix l pfx (fun n => @match_gate n).
Definition remove_suffix {dim} (l sfx : RzQ_ucom_l dim) :=
  remove_suffix l sfx (fun n => @match_gate n).
Definition replace_pattern {dim} (l pat rep : RzQ_ucom_l dim) :=
  replace_pattern l pat rep (fun n => @match_gate n).

(** Misc. Utilities **)

(* Check whether a (unitary) program is well typed. *)
Definition RzQ_ucom_l_well_typed_b dim (l : RzQ_ucom_l dim) := 
  uc_well_typed_l_b dim l.

(* Define some constants to make extraction easier. *)
Definition zero_Q := 0.
Definition two_Q := 2.

(* Put a rational into the range [0,2) by adding/subtracting multiples of 2 *)
Definition round_to_multiple_of_2 (a : Q) : BinInt.Z :=
  let num := Qnum a in
  let den := Qden a in
  (2 * (num / ((Zpos den) * 2)))%Z.
Definition bound (a : Q) :=
  if (Qle_bool zero_Q a) && negb (Qle_bool two_Q a) then a
  else if Qle_bool two_Q a 
       then a - inject_Z (round_to_multiple_of_2 a) (* a >= 2 *)
       else a + inject_Z (round_to_multiple_of_2 a) (* a < 0 *).

(* Combine Rz rotations; returns [] or [Rz (a + a') q] *)
Definition combine_rotations {dim} a a' q : RzQ_ucom_l dim :=
  let anew := bound (a + a') in
  if Qeq_bool anew zero_Q then [] else [Rz anew q].

Lemma bound_subs_multiples_of_2 : forall a,
  exists (b : BinInt.Z), a == (bound a) + (inject_Z b) * 2.
Proof. 
  intros a.
  assert (H: inject_Z (round_to_multiple_of_2 a / 2) * 2 == inject_Z (round_to_multiple_of_2 a)).
  { unfold round_to_multiple_of_2.
    destruct a.
    rewrite Zmult_comm, Z_div_mult, inject_Z_mult. 
    reflexivity. lia. }
  unfold bound, two_Q, zero_Q.
  destruct (Qle_bool 0 a) eqn:le0; destruct (Qle_bool 2 a) eqn:lt2; simpl.
  - exists ((round_to_multiple_of_2 a) / 2)%Z. rewrite H. lra.
  - exists 0%Z. unfold inject_Z. lra. 
  - apply not_true_iff_false in le0. rewrite Qle_bool_iff in le0.
    rewrite Qle_bool_iff in lt2. lra.
  - exists (- (round_to_multiple_of_2 a / 2))%Z. 
    rewrite inject_Z_opp, <- H. lra.
Qed.

Lemma combine_rotations_semantics : forall {dim} a a' q, 
  (q < dim)%nat ->
  @uc_equiv_l dim (combine_rotations a a' q) ([Rz a q] ++ [Rz a' q]).
Proof.
  intros dim a a' q Hq.
  unfold combine_rotations, zero_Q.
  specialize (bound_subs_multiples_of_2 (a + a')) as Hbound. 
  destruct Hbound as [k Hbound]. 
  destruct (Qeq_bool (bound (a + a')) 0) eqn:eq;
  unfold uc_equiv_l, uc_equiv; simpl; rewrite Mmult_assoc, pad_mult;
  repeat rewrite phase_shift_rotation; rewrite phase_mul;
  rewrite <- Rmult_plus_distr_r, Rplus_comm, <- Qreals.Q2R_plus.
  - apply Qeq_bool_eq in eq.
    rewrite eq in Hbound. rewrite Qplus_0_l in Hbound.
    apply Qreals.Qeq_eqR in Hbound. 
    rewrite Hbound. 
    Local Opaque Z.mul.
    autorewrite with eval_db; gridify.
    do 2 (apply f_equal2; try reflexivity). 
    unfold phase_shift; solve_matrix. 
    unfold Qreals.Q2R; simpl.
    replace (IZR (k * 2) * / 1 * PI)%R with (IZR (2 * k) * PI)%R.
    symmetry. apply Cexp_2nPI.
    rewrite Zmult_comm. lra.
  - apply Qreals.Qeq_eqR in Hbound. 
    rewrite Hbound. 
    rewrite Qreals.Q2R_plus, Rmult_plus_distr_r, <- phase_mul.
    autorewrite with eval_db; gridify.
    do 2 (apply f_equal2; try reflexivity). 
    rewrite <- (Mmult_1_r _ _ (phase_shift _)) at 1; auto with wf_db.
    apply f_equal2; try reflexivity.
    unfold phase_shift; solve_matrix. 
    unfold Qreals.Q2R; simpl.
    replace (IZR (k * 2) * / 1 * PI)%R with (IZR (2 * k) * PI)%R. 
    symmetry. apply Cexp_2nPI.
    rewrite Zmult_comm. lra.
Qed.

(* Invert a z-rotation. *)
Definition invert_rotation {dim} a q : gate_app RzQ_Unitary dim :=
  Rz (two_Q - a) q.

Local Open Scope ucom.
Local Transparent SQIR.Rz.
Lemma invert_rotation_semantics : forall {dim} a q,
  list_to_ucom [@invert_rotation dim a q] ≡ invert (SQIR.Rz (Qreals.Q2R a * PI)%R q).
Proof.
  intros dim a q.
  simpl. 
  rewrite SKIP_id_r.
  unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify.
  do 2 (apply f_equal2; try reflexivity).
  unfold rotation.
  solve_matrix.
  all: autorewrite with R_db C_db trig_db Cexp_db; trivial.
  rewrite Qreals.Q2R_minus.
  autorewrite with R_db.
  rewrite Rmult_plus_distr_r.
  rewrite Cexp_add, <- Cexp_neg.
  replace (Qreals.Q2R two_Q * PI)%R with (2 * PI)%R. 
  2: unfold Qreals.Q2R, two_Q; simpl; lra. 
  rewrite Cexp_2PI.
  autorewrite with C_db R_db; reflexivity.
Qed.