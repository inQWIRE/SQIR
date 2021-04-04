(* This file contains code for extracting the Shor's formalism to OCaml. We 
   currently extract Coq real numbers (used in U_R parameters) to OCaml floats.
   This is not ideal for two reasons: (1) floats are not a faithful 
   representation of real numbers, so we lose some guarantees from verification 
   and (2) once we extract to floats, gates get ugly, which could be a problem for
   compilers (e.g. the compiler may have a special rule for H, which we translate
   to U_R 3.14.. 0 1.57..).

   A potential solution to this is to switch the formalism and proofs to a
   different gate set like the following, which uses rationals instead of reals.

Inductive ext_Unitary : nat -> Set := 
  | U_R    : Q -> Q -> Q -> ext_Unitary 1
  | U_CNOT : ext_Unitary 2.

Definition H {dim} n : ext_ucom dim := uapp1 (U_R (1/2) 0 1) n.  
Definition X {dim} n : ext_ucom dim := uapp1 (U_R 1 0 1) n.
...

   That being said, the rest of the quantum software stack (e.g. OpenQASM
   format, simulator) use floating point numbers so we'll have to give up on
   perfect precision at some point.
*)

Require Coq.extraction.Extraction.
Require Import Shor.

(* Standard utilities for bools, options, etc. *)
Require Coq.extraction.ExtrOcamlBasic.

(* A few common functions not included in ExtrOcamlBasic. *)
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
Extract Inlined Constant negb => "not".
Extract Inlined Constant length => "List.length".
Extract Inlined Constant app => "List.append".
Extract Inlined Constant rev => "List.rev".
Extract Inlined Constant rev_append => "List.rev_append".
Extract Inlined Constant fold_right => "(fun f a l -> List.fold_right f l a)".
Extract Inlined Constant forallb => "List.for_all".

(* Standard extraction from nat -> OCaml int. *)
Require Coq.extraction.ExtrOcamlNatInt.

(* Custom extraction from R -> OCaml float. *)
Extract Constant R => "float".
Extract Constant R0 => "0.0".
Extract Constant R1 => "1.0".
Extract Constant Rplus => "( +. )".
Extract Constant Rmult => "( *. )".
Extract Constant Ropp => "((-.) 0.0)".
Extract Constant Rinv => "((/.) 1.0)".
Extract Constant Rdiv => "( /. )".
Extract Inlined Constant cos => "cos".
Extract Inlined Constant sin => "sin".
Extract Constant PI => "Float.pi".
Extract Inlined Constant Rle_dec => "( <= )".

(* Set "dim" to be implicit everywhere. *)
Extraction Implicit H [dim].
Extraction Implicit X [dim].
Extraction Implicit ID [dim].
Extraction Implicit SKIP [dim].
Extraction Implicit Rz [dim].
Extraction Implicit T [dim].
Extraction Implicit TDAG [dim].
Extraction Implicit CNOT [dim].
Extraction Implicit SWAP [dim].


(* special extraction for modular exponentiation so we don't run into 
   efficiency issues (this is a littele hacky -- it would be better to
   extract all operations to OCaml's Z type). *)
Definition modexp a x N := a ^ x mod N.
Extract Constant modexp => "fun a x n -> Z.to_int (Z.powm (Z.of_int a) (Z.of_int x) (Z.of_int n))".

(*
(* @Liyi: you can change the adder by commenting/uncommenting the following definitions *)
Require Import RCIRplus.

(* Old defn *)
Definition modmult_circuit a ainv N n i := 
  @bc2ucom (n + ModMult.modmult_rev_anc n) 
           (RCIR.csplit (RCIR.bcelim (ModMult.modmult_rev N (modexp a (2 ^ i) N) (modexp ainv (2 ^ i) N) n))).
Definition num_qubits n : nat := n + modmult_rev_anc n.

(* New defn #1 *)
Definition modmult_circuit a ainv N n i :=
  fst (modmult_sqir N (modexp a (2 ^ i) N) (modexp ainv (2 ^ i) N) n).
Definition num_qubits n : nat := get_dim (modmult_vars n).

(* New defn #2 *)
Definition modmult_circuit a ainv N n i := 
  fst (rz_mod_sqir N (modexp a (2 ^ i) N) (modexp ainv (2 ^ i) N) n).
Definition num_qubits n : nat := get_dim (rz_mod_vars n).
*)



(** Kesha's scratch-work. Will move elsewhere later. **)

(* version of bccom that includes swaps - worthwhile to include swap in normal bccom? *)
Inductive bcswap :=
  | Skip
  | X (a : nat)
  | Swap (a b : nat)
  | Ctrl (a : nat) (bc1 : bcswap)
  | Seq (bc1 bc2 : bcswap).

Fixpoint bccom_to_bcswap (bc : bccom) : bcswap :=
  match bc with
  | bcskip => Skip
  | bcx n => X n
  | bccont n p => Ctrl n (bccom_to_bcswap p)
  | (bccont a (bcx b) ; bccont c (bcx d) ; bccont e (bcx f))%bccom =>
      if (a =? d) && (d =? e) && (b =? c) && (c =? f)
      then Swap a b
      else Seq (Seq (Ctrl a (X b)) (Ctrl c (X d))) (Ctrl e (X f))
  | (p1; p2)%bccom => Seq (bccom_to_bcswap p1) (bccom_to_bcswap p2)
  end.

(* Gate set for Shor's *)
(* U2 and U3 aren't used for the inputs I tried, but I'm including them
   for full generality in the control' function. -KH *)
Inductive U : nat -> Set :=
  | U_X : U 1
  | U_H : U 1
  | U_U1 : R -> U 1
  | U_U2 : R -> R -> U 1 
  | U_U3 : R -> R -> R -> U 1
  | U_CX : U 2
  | U_CU1 : R -> U 2
  | U_SWAP : U 2
  | U_CCX : U 3
  | U_CSWAP : U 3
  | U_C3X : U 4
  | U_C4X : U 5.

(* Experimenting with a version of ucom that uses a list argument and no 
   dependent dim type... *)
Inductive ucom (U : nat -> Set) : Set :=
| useq :  ucom U -> ucom U -> ucom U
| uapp : forall n, U n -> list nat -> ucom U.
Arguments useq {U}.
Arguments uapp {U n}.
Notation "u1 >> u2" := (useq u1 u2) (at level 50).

Definition sqirU1 {dim} a n : base_ucom dim := uapp1 (U_R 0 0 a) n.
Definition sqirU2 {dim} a b n : base_ucom dim := uapp1 (U_R (PI / 2) a b) n.
Definition sqirU3 {dim} a b c n : base_ucom dim := uapp1 (U_R a b c) n.

Fixpoint to_base_ucom dim (u : ucom U) : base_ucom dim :=
  match u with
  | u1 >> u2 => (to_base_ucom dim u1 ; to_base_ucom dim u2)%ucom
  | uapp _ g qs => 
      match g, qs with
      | U_X, (q1 :: List.nil)%list => SQIR.X q1
      | U_H, (q1 :: List.nil) => H q1
      | U_U1 r1, (q1 :: List.nil) => sqirU1 r1 q1
      | U_U2 r1 r2, (q1 :: List.nil) => sqirU2 r1 r2 q1
      | U_U3 r1 r2 r3, (q1 :: List.nil) => sqirU3 r1 r2 r3 q1
      | U_CX, (q1 :: q2 :: List.nil) => CNOT q1 q2
      | U_CU1 r, (q1 :: q2 :: List.nil) => UnitaryOps.control q1 (sqirU1 r q2)
      | U_SWAP, (q1 :: q2 :: List.nil) => SWAP q1 q2
      | U_CCX, (q1 :: q2 :: q3 :: List.nil) => UnitaryOps.control q1 (CNOT q2 q3)
      | U_CSWAP, (q1 :: q2 :: q3 :: List.nil) => UnitaryOps.control q1 (SWAP q2 q3)
      | U_C3X, (q1 :: q2 :: q3 :: q4 :: List.nil) => 
          UnitaryOps.control q1 (UnitaryOps.control q2 (CNOT q3 q4))
      | U_C4X, (q1 :: q2 :: q3 :: q4 :: q5 :: List.nil) => 
          UnitaryOps.control q1 
            (UnitaryOps.control q2 (UnitaryOps.control q3 (CNOT q4 q5)))
      (* some dummy value -- unreachable for well-formed progs *)
      | _, _ => SKIP
      end
  end.

Definition uc_eval dim (u : ucom U) := uc_eval (to_base_ucom dim u).

Definition Xg q := uapp U_X [q].
Definition H q := uapp U_H [q].
Definition U1 r1 q := uapp (U_U1 r1) [q].
Definition U2 r1 r2 q := uapp (U_U2 r1 r2) [q].
Definition U3 r1 r2 r3 q := uapp (U_U3 r1 r2 r3) [q].
Definition T q := U1 (PI / 4) q.
Definition Tdg q := U1 (- (PI / 4)) q.
Definition SKIP := U1 0 O. (* used as a dummy value *)
Definition CX q1 q2 := uapp U_CX (q1 :: q2 :: List.nil).
Definition CU1 r q1 q2 := uapp (U_CU1 r) (q1 :: q2 :: List.nil).
Definition SWAP q1 q2 := uapp U_SWAP (q1 :: q2 :: List.nil).
Definition CCX q1 q2 q3 := uapp U_CCX (q1 :: q2 :: q3 :: List.nil).
Definition CSWAP q1 q2 q3 := uapp U_CSWAP (q1 :: q2 :: q3 :: List.nil).
Definition C3X q1 q2 q3 q4 := uapp U_C3X (q1 :: q2 :: q3 :: q4 :: List.nil).
Definition C4X q1 q2 q3 q4 q5 := uapp U_C4X (q1 :: q2 :: q3 :: q4 :: q5 :: List.nil).

Definition decompose_CH (a b : nat) : ucom U := 
  U3 (PI/4) 0 0 b >> CX a b >> U3 (- (PI/4)) 0 0 b. 

Definition decompose_CU1 r1 (a b : nat) : ucom U := 
  U1 (r1/2) a >> U1 (r1/2) b >> CX a b >> U1 (- (r1/2)) b >> CX a b.

Definition decompose_CU2 r1 r2 (a b : nat) : ucom U := 
  U1 ((r2+r1)/2) a >> U1 ((r2-r1)/2) b >> CX a b >>
  U3 (-(PI/4)) 0 (-(r1+r2)/2) b >> CX a b >> U3 (PI/4) r1 0 b.

Definition decompose_CU3 r1 r2 r3 (a b : nat) : ucom U := 
  U1 ((r3+r2)/2) a >> U1 ((r3-r2)/2) b >> CX a b >>
  U3 (-(r1/2)) 0 (-(r2+r3)/2) b >> CX a b >> U3 (r1/2) r2 0 b.

Definition decompose_CSWAP (a b c : nat) : ucom U := 
  CCX a b c >> CCX a c b >> CCX a b c.

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
      | uapp _ U_X (b :: List.nil) => CX a b
      | uapp _ U_CX (b :: c :: List.nil) => CCX a b c
      | uapp _ U_CCX (b :: c :: d :: List.nil) => C3X a b c d
      | uapp _ U_C3X (b :: c :: d :: e :: List.nil) => C4X a b c d e
      | uapp _ U_SWAP (b :: c :: List.nil) => CSWAP a b c
      | uapp _ (U_U1 r) (b :: List.nil) => CU1 r a b
      (* We don't supprt CH, CU2, CU3, CCU1, CCSWAP or C5X, so decompose *)
      | uapp _ U_H (b :: List.nil) => decompose_CH a b
      | uapp _ (U_U2 r1 r2) (b :: List.nil) => decompose_CU2 r1 r2 a b
      | uapp _ (U_U3 r1 r2 r3) (b :: List.nil) => decompose_CU3 r1 r2 r3 a b
      | uapp _ (U_CU1 r) (b :: c :: List.nil) => 
          control' a (decompose_CU1 r b c) n'
      | uapp _ U_CSWAP (b :: c :: d :: List.nil) => 
          control' a (decompose_CSWAP b c d) n'
      | uapp _ U_C4X (b :: c :: d :: e :: f :: List.nil) => 
          control' a 
            (control' b (control' c (decompose_CCX d e f) n') n') n'
      | _ => SKIP (* unreachable *)
      end
  end.
(* Fuel for control' *)
Definition fuel_CU1 : nat := 4.
Definition fuel_CSWAP : nat := 2.
Definition fuel_CCX : nat := 14.
Fixpoint fuel (c : ucom U) :=
  match c with
  | c1 >> c2 => S (max (fuel c1) (fuel c2))
  | uapp _ (U_CU1 r) _ => S fuel_CU1
  | uapp _ U_CSWAP _ => S fuel_CSWAP
  | uapp _ U_C4X _ => S (S (S fuel_CCX))
  | _ => O
  end.
Definition control a (c : ucom U) :=
  control' a c (S (fuel c)).

Lemma fuel_CU1_correct : forall r a b, fuel (decompose_CU1 r a b) = fuel_CU1.
Proof. intros. reflexivity. Qed.
Lemma fuel_CSWAP_correct : forall a b c, fuel (decompose_CSWAP a b c) = fuel_CSWAP.
Proof. intros. reflexivity. Qed.
Lemma fuel_CCX_correct : forall a b c, fuel (decompose_CCX a b c) = fuel_CCX.
Proof. intros. reflexivity. Qed.

Hint Rewrite <- RtoC_minus : RtoC_db.

Local Transparent SQIR.H.
Lemma decompose_CH_is_control_H : forall dim a b,
  uc_eval dim (decompose_CH a b) = 
    UnitarySem.uc_eval (UnitaryOps.control a (SQIR.H b)).
Proof.
  assert (aux1 : rotation (- (PI / 4)) 0 0 × (σx × rotation (PI / 4) 0 0) =
                 Cexp (PI / 2) .* (rotation (PI / 2 / 2) 0 0 ×
                   (σx × (rotation (- (PI / 2) / 2) 0 (- PI / 2) × 
                     (σx × phase_shift (PI / 2)))))).
  { (* messy :) should make better automation *)
    solve_matrix; repeat rewrite RIneq.Ropp_div; autorewrite with Cexp_db trig_db; 
      repeat rewrite RtoC_opp; field_simplify_eq; try nonzero.
    replace (((R1 + R1)%R, (R0 + R0)%R) * cos (PI / 4 / 2) * sin (PI / 4 / 2)) 
      with (2 * sin (PI / 4 / 2) * cos (PI / 4 / 2)) by lca.
    2: replace (((- (R1 + R1))%R, (- (R0 + R0))%R) * Ci * Ci * cos (PI / 2 / 2 / 2) * sin (PI / 2 / 2 / 2))
         with (2 * sin (PI / 2 / 2 / 2) * cos (PI / 2 / 2 / 2)) by lca.
    3: replace (- sin (PI / 4 / 2) * sin (PI / 4 / 2) + cos (PI / 4 / 2) * cos (PI / 4 / 2)) 
         with (cos (PI / 4 / 2) * cos (PI / 4 / 2) - sin (PI / 4 / 2) * sin (PI / 4 / 2)) by lca.
    3: replace ((R1 + R1)%R, (R0 + R0)%R) with (RtoC 2) by lca.
    4: replace (((- (R1 + R1))%R, (- (R0 + R0))%R) * sin (PI / 4 / 2) * cos (PI / 4 / 2)) 
         with (- (2 * sin (PI / 4 / 2) * cos (PI / 4 / 2))) by lca.
    4: replace (- Ci * Ci * sin (PI / 2 / 2 / 2) * sin (PI / 2 / 2 / 2) + Ci * Ci * cos (PI / 2 / 2 / 2) * cos (PI / 2 / 2 / 2))
         with (- (cos (PI / 2 / 2 / 2) * cos (PI / 2 / 2 / 2) - sin (PI / 2 / 2 / 2) * sin (PI / 2 / 2 / 2))) by lca.
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
    + rewrite aux2.
      reflexivity.
  - rewrite Rminus_0_r, Rplus_0_l, Rplus_0_r.
    apply f_equal2.
    + rewrite <- 3 Mscale_kron_dist_l.
      rewrite <- Mscale_kron_dist_r.
      do 4 (apply f_equal2; try reflexivity).
      apply aux1.
    + rewrite aux2.
      reflexivity.
Qed.
Local Opaque SQIR.H.

Local Transparent SQIR.Rz.
Lemma decompose_CU1_is_control_U1 : forall dim r a b,
  uc_eval dim (decompose_CU1 r a b) = 
    UnitarySem.uc_eval (UnitaryOps.control a (sqirU1 r b)).
Proof.
  intros dim r a b.
  unfold sqirU1, decompose_CU1, uc_eval.
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
Local Opaque SQIR.Rz.

Lemma decompose_CU2_is_control_U2 : forall dim r1 r2 a b,
  uc_eval dim (decompose_CU2 r1 r2 a b) = 
    UnitarySem.uc_eval (UnitaryOps.control a (sqirU2 r1 r2 b)).
Proof.
  intros dim r1 r2 a b.
  unfold sqirU2, decompose_CU2, uc_eval.
  simpl.
  replace (PI / 2 / 2)%R with (PI / 4)%R by lra.
  replace (- (PI / 2) / 2)%R with (- (PI / 4))%R by lra.
  reflexivity.
Qed.

Lemma decompose_CU3_is_control_U3 : forall dim r1 r2 r3 a b,
  uc_eval dim (decompose_CU3 r1 r2 r3 a b) = 
    UnitarySem.uc_eval (UnitaryOps.control a (sqirU3 r1 r2 r3 b)).
Proof.
  intros dim r1 r2 r3 a b.
  unfold sqirU3, decompose_CU3, uc_eval.
  simpl.
  replace (- r1 / 2)%R with (- (r1 / 2))%R by lra.
  reflexivity.
Qed.

Local Transparent SQIR.SWAP.
Lemma decompose_CSWAP_is_control_SWAP : forall dim a b c,
  uc_eval dim (decompose_CSWAP a b c) = 
    UnitarySem.uc_eval (UnitaryOps.control a (SQIR.SWAP b c)).
Proof.
  intros dim a b c.
  unfold decompose_CSWAP, uc_eval, SWAP.
  simpl.
  reflexivity.
Qed.
Local Opaque SQIR.SWAP.

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


Inductive gate_apps_well_formed {U} : nat -> ucom U -> Prop :=
  | WF_useq : forall dim u1 u2, 
      gate_apps_well_formed dim u1 -> 
      gate_apps_well_formed dim u2 -> 
      gate_apps_well_formed dim (u1 >> u2)
  | WF_uapp : forall dim n (g : U n) qs,
      length qs = n -> gate_apps_well_formed dim (uapp g qs).

Lemma uapp1_WF : forall {U : nat -> Set} dim (g : U 1%nat) qs,
  gate_apps_well_formed dim (uapp g qs) -> exists a, qs = a :: List.nil.
Proof.
  intros U dim g qs H.
  inversion H; subst.
  do 2 (destruct qs; try inversion H2).
  exists n.
  reflexivity.
Qed.

Lemma uapp2_WF : forall {U : nat -> Set} dim (g : U 2%nat) qs,
  gate_apps_well_formed dim (uapp g qs) -> exists a b, qs = a :: b :: List.nil.
Proof.
  intros U dim g qs H.
  inversion H; subst.
  do 3 (destruct qs; try inversion H2).
  exists n. exists n0.
  reflexivity.
Qed.

Lemma uapp3_WF : forall {U : nat -> Set} dim (g : U 3%nat) qs,
  gate_apps_well_formed dim (uapp g qs) -> exists a b c, qs = a :: b :: c :: List.nil.
Proof.
  intros U dim g qs H.
  inversion H; subst.
  do 4 (destruct qs; try inversion H2).
  exists n. exists n0. exists n1.
  reflexivity.
Qed.

Lemma uapp4_WF : forall {U : nat -> Set} dim (g : U 4%nat) qs,
  gate_apps_well_formed dim (uapp g qs) -> exists a b c d, qs = a :: b :: c :: d:: List.nil.
Proof.
  intros U dim g qs H.
  inversion H; subst.
  do 5 (destruct qs; try inversion H2).
  exists n. exists n0. exists n1. exists n2.
  reflexivity.
Qed.

Lemma uapp5_WF : forall {U : nat -> Set} dim (g : U 5%nat) qs,
  gate_apps_well_formed dim (uapp g qs) -> exists a b c d e, qs = a :: b :: c :: d :: e :: List.nil.
Proof.
  intros U dim g qs H.
  inversion H; subst.
  do 6 (destruct qs; try inversion H2).
  exists n. exists n0. exists n1. exists n2. exists n3.
  reflexivity.
Qed.

Local Opaque sqirU1 sqirU2 sqirU3 decompose_CU1.
Lemma control_correct : forall dim a u n,
  (fuel u < n)%nat ->
  gate_apps_well_formed dim u ->
  (* some precond. about a being fresh in u *)
  uc_eval dim (control' a u n) = 
    UnitarySem.uc_eval (UnitaryOps.control a (to_base_ucom dim u)).
Proof.
  intros dim a u n.
  generalize dependent u.
  induction n; intros u Hfu WT.
  lia.
  destruct u; simpl.
  inversion WT; subst.
  unfold uc_eval in *.
  simpl in *.
  rewrite 2 IHn; try lia; auto.
  destruct u; 
    try (apply uapp1_WF in WT; destruct WT as [x H]);
    try (apply uapp2_WF in WT; destruct WT as [x [y H]]);
    try (apply uapp3_WF in WT; destruct WT as [x [y [z H]]]);
    try (apply uapp4_WF in WT; destruct WT as [x [y [z [w H]]]]);
    try (apply uapp5_WF in WT; destruct WT as [x [y [z [w [q H]]]]]);
    subst.
  (* C-X *)
  unfold uc_eval.
  simpl.
  rewrite control_ucom_X.
  reflexivity.
  (* C-H *)
  rewrite <- decompose_CH_is_control_H.
  reflexivity.
  (* C-U1 *)
  reflexivity.
  (* C-U2 *)
  rewrite <- decompose_CU2_is_control_U2.
  reflexivity.
  (* C-U3 *)
  rewrite <- decompose_CU3_is_control_U3.
  reflexivity.
  (* C-CX *)
  reflexivity.
  (* C-CU1 *)
unfold uc_eval in *.
simpl.
rewrite IHn.
2: { simpl in Hfu. rewrite fuel_CU1_correct. lia. }
admit. admit.
  (* C-SWAP *)
  reflexivity.
  (* C-CCX *)
  reflexivity.
  (* C-CSWAP *)
  admit.
  (* C-C3X *)
  reflexivity.
  (* C-C4X *)
  admit.
Admitted.


Fixpoint bcswap2ucom (bc : bcswap) : ucom U :=
  match bc with
  | Skip => SKIP
  | X a => Xg a
  | Swap a b => SWAP a b
  | Ctrl a bc1 => control a (bcswap2ucom bc1)
  | Seq bc1 bc2 => (bcswap2ucom bc1) >> (bcswap2ucom bc2)
  end.

Lemma bcswap2ucom_correct : forall dim (bc : bccom),
  uc_eval dim (bcswap2ucom (bccom_to_bcswap bc)) = UnitarySem.uc_eval (bc2ucom bc).
Proof.
  intros dim bc.
  (* this proof will likely be annoying... *)
Admitted.

Definition modmult_circuit a ainv N n i := 
  bccom_to_bcswap (RCIR.bcelim (ModMult.modmult_rev N (modexp a (2 ^ i) N) (modexp ainv (2 ^ i) N) n)).
Definition num_qubits n : nat := n + modmult_rev_anc n. 

(* Redefining to use new gate set: *)
Fixpoint controlled_rotations n : ucom U :=
  match n with
  | 0 | 1 => SKIP
  | 2     => CU1 (2 * PI / 2 ^ n) 1 0
  | S n'  => controlled_rotations n' >> CU1 (2 * PI / 2 ^ n) n' 0
  end.

Fixpoint map_qubits (f : nat -> nat) (c : ucom U) : ucom U :=
  match c with
  | c1 >> c2 => map_qubits f c1 >> map_qubits f c2
  | uapp n g qs => uapp g (List.map f qs)
  end.

Fixpoint QFT n : ucom U :=
  match n with
  | 0    => SKIP
  | 1    => H 0
  | S n' => H 0 >> controlled_rotations n >> map_qubits S (QFT n')
  end.

Fixpoint reverse_qubits' dim n : ucom U :=
  match n with
  | 0    => SKIP
  | 1    => SWAP 0 (dim - 1)
  | S n' => reverse_qubits' dim n' >> SWAP n' (dim - n' - 1)
  end.
Definition reverse_qubits n := reverse_qubits' n (n/2)%nat.
Definition QFT_w_reverse n := QFT n >> reverse_qubits n.

Fixpoint controlled_powers_var' (f : nat -> bcswap) k kmax : bcswap :=
  match k with
  | O    => Skip
  | S O  => Ctrl (kmax - 1) (f O)
  | S k' => Seq (controlled_powers_var' f k' kmax)
               (Ctrl (kmax - k' - 1) (f k'))
  end.
Definition controlled_powers_var (f : nat -> bcswap) k : ucom U := 
  bcswap2ucom (controlled_powers_var' f k k).

Fixpoint npar n (u : U 1) : ucom U :=
  match n with
  | O => SKIP
  | S O =>  uapp u [O]
  | S n' => npar n' u >> uapp u [n']
  end.

Fixpoint map_bcswap (f : nat -> nat) (bc : bcswap) : bcswap :=
  match bc with
  | Skip => Skip
  | X a => X (f a)
  | Swap a b => Swap (f a) (f b)
  | Ctrl a bc1 => Ctrl (f a) (map_bcswap f bc1)
  | Seq bc1 bc2 => Seq (map_bcswap f bc1) (map_bcswap f bc2)
  end.

Fixpoint invert (u : ucom U) : ucom U :=
  match u with
  | u1 >> u2 => invert u2 >> invert u1
  | uapp _ g qs => 
      match g, qs with
      | U_X, (q1 :: List.nil)%list => Xg q1
      | U_H, (q1 :: List.nil) => H q1
      | U_U1 r1, (q1 :: List.nil) => U1 (- r1) q1
      | U_U2 r1 r2, (q1 :: List.nil) => U3 (- (PI/2)) (- r1) (- r2) q1
      | U_U3 r1 r2 r3, (q1 :: List.nil) => U3 (- r1) (- r2) (- r3) q1
      | U_CX, (q1 :: q2 :: List.nil) => CX q1 q2
      | U_CU1 r, (q1 :: q2 :: List.nil) => CU1 r q1 q2
      | U_SWAP, (q1 :: q2 :: List.nil) => SWAP q1 q2
      | U_CCX, (q1 :: q2 :: q3 :: List.nil) => CCX q1 q2 q3
      | U_CSWAP, (q1 :: q2 :: q3 :: List.nil) => CSWAP q1 q2 q3
      | U_C3X, (q1 :: q2 :: q3 :: q4 :: List.nil) => C3X q1 q2 q3 q4
      | U_C4X, (q1 :: q2 :: q3 :: q4 :: q5 :: List.nil) => C4X q1 q2 q3 q4 q5
      (* some dummy value -- unreachable for well-formed progs *)
      | _, _ => SKIP
      end
  end.

Definition QPE_var k (f : nat -> bcswap) : ucom U :=
  npar k U_H >>
  controlled_powers_var (fun x => map_bcswap (fun q => k + q)%nat (f x)) k >>
  invert (QFT_w_reverse k).

Lemma controlled_rotations_same : forall n,
  uc_eval n (controlled_rotations n) = 
    UnitarySem.uc_eval (QPE.controlled_rotations n).
Proof.
Admitted.

Lemma map_qubits_same : forall dim f u,
  gate_apps_well_formed dim u ->
  uc_eval dim (map_qubits f u) = 
    UnitarySem.uc_eval (UnitaryOps.map_qubits f (to_base_ucom dim u)).
Proof.
  intros dim f u WF.
  induction u.
  unfold uc_eval.
  simpl.
  inversion WF; subst.
  rewrite <- IHu1, <- IHu2 by assumption.
  reflexivity.
  simpl.
  destruct u; 
    try (apply uapp1_WF in WF; destruct WF as [x H]);
    try (apply uapp2_WF in WF; destruct WF as [x [y H]]);
    try (apply uapp3_WF in WF; destruct WF as [x [y [z H]]]);
    try (apply uapp4_WF in WF; destruct WF as [x [y [z [w H]]]]);
    try (apply uapp5_WF in WF; destruct WF as [x [y [z [w [q H]]]]]);
    subst.
  all: reflexivity.
Qed.

Lemma QFT_same : forall n,
  uc_eval n (QFT n) = UnitarySem.uc_eval (QPE.QFT n).
Proof.
  destruct n; try reflexivity.
  induction n; try reflexivity.
  replace (QFT (S (S n))) 
    with (H 0 >> controlled_rotations (S (S n)) >> map_qubits S (QFT (S n))) 
    by reflexivity.
  replace (QPE.QFT (S (S n))) 
    with (SQIR.H 0 ; QPE.controlled_rotations (S (S n)) ; 
          cast (UnitaryOps.map_qubits S (QPE.QFT (S n))) (S (S n)))%ucom 
    by reflexivity. 
  Local Opaque H controlled_rotations QFT QPE.controlled_rotations QPE.QFT.
  unfold uc_eval.
  simpl.  
  apply f_equal2; [ | apply f_equal2]; try reflexivity.
  admit. (* need a lemma about cast *)
  apply controlled_rotations_same.
Admitted.

Lemma reverse_qubits_same : forall n,
  uc_eval n (reverse_qubits n) = UnitarySem.uc_eval (QPE.reverse_qubits n).
Proof.
  assert (H : forall n dim, uc_eval dim (reverse_qubits' dim n) = 
                         UnitarySem.uc_eval (QPE.reverse_qubits' dim n)).
  { intros n dim.
    destruct n; try reflexivity.
    induction n; try reflexivity.
    unfold uc_eval in *.
    simpl in *.
    rewrite IHn.
    reflexivity. }
  intro n.
  unfold reverse_qubits.
  apply H.
Qed.

Lemma QFT_w_reverse_same : forall n,
  uc_eval n (QFT_w_reverse n) = UnitarySem.uc_eval (QPE.QFT_w_reverse n).
Proof.
  intro n.
  unfold uc_eval; simpl.
  rewrite <- QFT_same, <- reverse_qubits_same.
  reflexivity.
Qed.

Lemma controlled_powers_var_same : forall n (f : nat -> bcswap) k (f' : nat -> base_ucom n),
  (* some precondition relating f and f' *)
  uc_eval (k + n) (controlled_powers_var f k) = 
    UnitarySem.uc_eval (QPE.controlled_powers_var f' k).
Proof.
  assert (H : forall n f k kmax f',
    uc_eval (kmax + n) (bcswap2ucom (controlled_powers_var' f k kmax)) =
      UnitarySem.uc_eval (@QPE.controlled_powers_var' n f' k kmax)).
  { intros n f k kmax f'.
    destruct k; try reflexivity.
    induction k.
    unfold uc_eval; simpl.  
    admit. (* some fact about cast... *) 
    admit. }
  intros.
  apply H.
Admitted.

Lemma npar_same : forall n,
  uc_eval n (npar n U_H) = UnitarySem.uc_eval (UnitaryOps.npar n SQIR.U_H).
Proof.
Admitted.

(* ... and so on, ending with QPE_var_same *)

(** End of Kesha's scratch-work **)



(* requires 0 < a < N, gcd a N = 1 
   returns a circuit + the number of qubits used *)
Local Open Scope ucom_scope.
Definition shor_circuit a N := 
  let m := Nat.log2 (2 * N^2)%nat in
  let n := Nat.log2 (2 * N) in
  let ainv := modinv a N in
  let numq := num_qubits n in
  let f i := modmult_circuit a ainv N n i in
  (Xg (m + n - 1) >> QPE_var m f, (m + numq)%nat, m).

(* rewritten to use "modexp" *)
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

Definition post_process (a N o : nat) := 
  let m := Nat.log2 (2 * N^2)%nat in
  OF_post a N o m.

Separate Extraction shor_circuit post_process.

(* Shor's algorithm:

1. Run the circuit generated by (shor_circuit a N) on input  ∣0⟩_m ∣1⟩_n ∣0⟩_anc.
2. Measure the first m qubits, resulting in the m-bit number x.
3. Run (post_process a N x) to obtain Some(p,q) where p and q are nontrivial factors of N or None 
     (... or something like that)

The main correctness theorem in Shor.v (Shor_correct_full_implementation) 
guarantees that there exists a β > 0 s.t.for any 0 < a < N with gcd a N = 1,
the above algorithm returns Some(p,q) with probability >= β / (Nat.log2 N)^4. 
    (... or something like that)
    
TODO: Add proofs here of the claim above.
(The proofs will likely just call Shor_correct_full_implementation.)

(* The post-processing of Shor's algorithm is simply running continued fraction algorithm step by step. Each time a classical verifier examines whether the denominator is the order.
   OF_post outputs a candidate of the order r. It might still not be the order, but 0 or a multiple of the order. We proved with no less than 1/polylog(N) probability its output is r. *)
*)
 

