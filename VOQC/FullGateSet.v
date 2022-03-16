Require Export UnitaryListRepresentation.
Require Export QArith.

(* Other gate sets *)
Require Import IBMGateSet.
Require Import MappingGateSet.
Require Import RzQGateSet.
Require Import MappingConstraints.

Import Qreals. (* Coq version < 8.13.0 has Q2R defined in Qreals *) 

(** This gate set is intended to be the "full" gate set that contains every gate
   we could ever want. Optimizations are not defined directly over this set.
   Instead, we define optimizations over specialized sets (e.g. RzQ, IBM) and 
   provide translations from this set to those sets.

   The value of having a gate set that contains everything is that it removes
   some opportunities for error in the OpenQASM -> SQIR parser. For instance,
   the parser can directly translate "T" to the T gate in the full gate set
   rather than the Rz(PI/4) gate in the RzQ gate set. This is even more important
   for gates like CCX that have complicated translations to other gate sets.
  
   To extend this gate set with new gates, you will need to modify the definitions
   in this file and any optimizations defined over the full gate set (at
   present, these only include definitions in Main.v). **)

Local Open Scope R_scope.
Local Open Scope Q_scope.

Ltac invert_WT :=
  repeat match goal with
  | H: uc_well_typed _ |- _ => inversion H; subst; clear H
  end.

Ltac simpl_Reqb_and_Qeqb :=
  repeat match goal with
  | H : Reqb _ _ = true |- _ => apply Reqb_eq in H; rewrite H
  | H : _ && _ = true |- _ => apply andb_prop in H as [? ?]
  | H : Qeq_bool _ _ = true |- _ => apply Qeq_bool_iff in H; 
      apply RMicromega.Q2R_m in H; rewrite H
  end.

Module FullGateSet <: GateSet.

Inductive Full_Unitary : nat -> Set := 
  | U_I                           : Full_Unitary 1 
  | U_X                           : Full_Unitary 1
  | U_Y                           : Full_Unitary 1 
  | U_Z                           : Full_Unitary 1
  | U_H                           : Full_Unitary 1 
  | U_S                           : Full_Unitary 1
  | U_T                           : Full_Unitary 1 
  | U_Sdg                         : Full_Unitary 1
  | U_Tdg                         : Full_Unitary 1 
  | U_Rx (r : R)                  : Full_Unitary 1
  | U_Ry (r : R)                  : Full_Unitary 1 
  | U_Rz (r : R)                  : Full_Unitary 1
  | U_Rzq (q : Q)                 : Full_Unitary 1
  | U_U1 (r : R)                  : Full_Unitary 1
  | U_U2 (r : R) (r : R)          : Full_Unitary 1 
  | U_U3 (r : R) (r : R) (r : R)  : Full_Unitary 1
  | U_CX                          : Full_Unitary 2
  | U_CZ                          : Full_Unitary 2
  | U_SWAP                        : Full_Unitary 2
  | U_CCX                         : Full_Unitary 3
  | U_CCZ                         : Full_Unitary 3.
Definition U := Full_Unitary.

(* Used for proofs -- not extracted to OCaml, so efficiency isn't a concern *)
Definition to_base {n dim} (u : U n) (qs : list nat) (pf : List.length qs = n) :=
  match u with
  | U_I            => @SQIR.ID dim (List.nth O qs O)
  | U_X            => @SQIR.X dim (List.nth O qs O)
  | U_Y            => @SQIR.Y dim (List.nth O qs O)
  | U_Z            => @SQIR.Z dim (List.nth O qs O)
  | U_H            => @SQIR.H dim (List.nth O qs O)
  | U_S            => @SQIR.P dim (List.nth O qs O)
  | U_T            => @SQIR.T dim (List.nth O qs O)
  | U_Sdg          => @SQIR.PDAG dim (List.nth O qs O)
  | U_Tdg          => @SQIR.TDAG dim (List.nth O qs O)
  | U_Rx r         => @SQIR.Rx dim r (List.nth O qs O)
  | U_Ry r         => @SQIR.Ry dim r (List.nth O qs O)
  | U_Rz r         => @SQIR.Rz dim r (List.nth O qs O)
  | U_Rzq q        => @SQIR.Rz dim (Q2R q * PI)%R (List.nth O qs O)
  | U_U1 r         => @SQIR.U1 dim r (List.nth O qs O)
  | U_U2 r1 r2     => @SQIR.U2 dim r1 r2 (List.nth O qs O)
  | U_U3 r1 r2 r3  => @SQIR.U3 dim r1 r2 r3 (List.nth O qs O)
  | U_CX           => @SQIR.CNOT dim (List.nth O qs O) (List.nth (S O) qs O)
  | U_CZ           => @SQIR.CZ dim (List.nth O qs O) (List.nth (S O) qs O)
  | U_SWAP         => @SQIR.SWAP dim (List.nth O qs O) (List.nth (S O) qs O)
  | U_CCX          => @SQIR.CCX dim (List.nth O qs O) (List.nth (S O) qs O) (List.nth (S (S O)) qs O)
  | U_CCZ          => @SQIR.CCZ dim (List.nth O qs O) (List.nth (S O) qs O) (List.nth (S (S O)) qs O)
  end.

Local Transparent SQIR.ID SQIR.X SQIR.Y SQIR.Z SQIR.H SQIR.Rx 
                  SQIR.Ry SQIR.Rz SQIR.CNOT SQIR.SWAP.
Lemma to_base_only_uses_qs : forall {n} (dim : nat) (u : U n) (qs : list nat) (pf : List.length qs = n),
    @only_uses _ dim (to_base u qs pf) qs.
Proof.
  intros.
  destruct u; simpl;
  repeat constructor; apply nth_In; lia.
Qed.

Lemma to_base_WT : forall {n} (dim : nat) (u : U n) (qs : list nat) (pf : List.length qs = n),
  @uc_well_typed _ dim (to_base u qs pf) <-> (bounded_list qs dim /\ List.NoDup qs).
Proof.
  intros n dim u s pf.
  unfold bounded_list.
  split.
  - intro H.
    destruct u; invert_WT.
    all: repeat (destruct s; simpl in *; try lia). 
    all: split.
    all: repeat constructor; auto.
    all: try (intros x [Hx | Hx]; subst; easy). 
    all: try (intros x [Hx | [Hx | Hx]]; subst; easy). 
    all: try (intros x [Hx | [Hx | [Hx | Hx]]]; subst; easy). 
    all: try (intro contra; destruct_In; auto).
  - intros [H1 H2].
    assert (aux1: (length s >= 2)%nat -> nth 0 s O <> nth 1 s O).
    { intro H. clear pf.
      destruct s; [|destruct s; [|destruct s]]; simpl in H; try lia. 
      inversion H2; subst.
      simpl. 
      intro contra. 
      contradict H4. 
      subst; constructor; auto.
      inversion H2; subst.
      simpl. 
      intro contra. 
      contradict H4. 
      subst; constructor; auto. }
    assert (aux2: length s = 3%nat -> nth 0 s O <> nth 2 s O).
    { intro H. clear pf.
      destruct s; [|destruct s; [|destruct s; [|destruct s]]]; simpl in H; try lia. 
      inversion H2; subst.
      simpl. 
      intro contra. 
      contradict H4. 
      subst; right; constructor; auto. }
    assert (aux3: length s = 3%nat -> nth 1 s O <> nth 2 s O).
    { intro H. clear pf.
      destruct s; [|destruct s; [|destruct s; [|destruct s]]]; simpl in H; try lia. 
      inversion H2; subst.
      simpl. 
      inversion H5; subst.
      intro contra. 
      contradict H6. 
      subst; constructor; auto. }
    destruct u; repeat constructor.
    all: try apply H1.
    all: try (apply nth_In; lia).
    all: try (apply aux1; lia).
    all: try (apply aux2; assumption).
    all: try (apply aux3; assumption).
    apply Nat.neq_sym.
    apply aux1; lia.
Qed.

Lemma to_base_map_commutes : forall {n} (dim : nat) (u : U n) (qs : list nat) (pf : List.length qs = n) (f : nat -> nat) (pfm : List.length (map f qs) = n),
  @to_base _ dim u (map f qs) pfm = map_qubits f (to_base u qs pf).
Proof.
  intros n dim u qs pf f pfm.
  destruct u; simpl.
  all: repeat erewrite map_nth_In; try reflexivity; lia.
Qed.
Local Opaque SQIR.ID SQIR.X SQIR.Y SQIR.Z SQIR.H SQIR.Rx 
             SQIR.Ry SQIR.Rz SQIR.CNOT SQIR.SWAP.

Definition match_gate {n} (u u' : U n) : bool :=
  match u, u' with
  | U_I, U_I
  | U_X, U_X
  | U_Y, U_Y
  | U_Z, U_Z
  | U_H, U_H
  | U_S, U_S
  | U_T, U_T
  | U_Sdg, U_Sdg
  | U_Tdg, U_Tdg
  | U_CX, U_CX
  | U_CZ, U_CZ
  | U_SWAP, U_SWAP 
  | U_CCX, U_CCX 
  | U_CCZ, U_CCZ => true
  (* All rz gates are u1 gates, some u2 gates are H gates, etc.
     We will not bother to check for these cases. If desired, you could
     write an optimization pass that replaces gates with their equivalents. *)
  | U_Rx r, U_Rx r'
  | U_Ry r, U_Ry r'
  | U_Rz r, U_Rz r'
  | U_U1 r, U_U1 r' => Reqb r r'
  | U_Rzq q, U_Rzq q' => Qeq_bool q q'
  | U_U2 r1 r2, U_U2 r1' r2' => Reqb r1 r1' && Reqb r2 r2'
  | U_U3 r1 r2 r3, U_U3 r1' r2' r3' => Reqb r1 r1' && Reqb r2 r2' && Reqb r3 r3'
  | _, _ => false
  end.

Lemma match_gate_refl : forall {n} (u : U n), match_gate u u = true.
Proof. 
  intros. 
  dependent destruction u; simpl; auto.
  apply Reqb_eq; auto.
  apply Reqb_eq; auto.
  apply Reqb_eq; auto.
  apply Qeq_bool_iff; reflexivity.
  apply Reqb_eq; auto.
  apply andb_true_iff.
  split; apply Reqb_eq; auto.
  apply andb_true_iff.
  split; [apply andb_true_iff; split |]; apply Reqb_eq; auto.
Qed.

Lemma match_gate_implies_equiv : forall {n} dim (u u' : U n) (qs : list nat) (pf : List.length qs = n), 
  match_gate u u' = true -> uc_equiv (@to_base n dim u qs pf) (to_base u' qs pf).
Proof.
  intros.
  dependent destruction u; dependent destruction u'.
  all: inversion H; simpl; simpl_Reqb_and_Qeqb; reflexivity.
Qed.

End FullGateSet.
Export FullGateSet.

Module FullList := UListProofs FullGateSet.

Definition full_ucom dim := ucom Full_Unitary dim.
Definition full_ucom_l dim := gate_list Full_Unitary dim.

(** Some useful gate decompositions **)

Lemma Cexp_plus_PI2 : forall x, Cexp (x + PI/2) = (Ci * Cexp x)%C.
Proof. intros. autorewrite with Cexp_db. lca. Qed.

Lemma Cexp_minus_PI2 : forall x, Cexp (x - PI/2) = (- Ci * Cexp x)%C.
Proof. 
  intros. 
  unfold Cexp. 
  replace (x - PI / 2)%R with (- (PI / 2 - x))%R by lra.
  rewrite cos_neg, sin_neg.
  rewrite cos_shift, sin_shift.
  lca.
Qed.

(* All 4 cases in u3_to_rz can be solved by the same commands. *)
Ltac u3_to_rz_aux a :=
  try rewrite Cexp_add;
  try rewrite Cexp_plus_PI2; 
  try rewrite Cexp_minus_PI2;
  unfold Cexp;
  autorewrite with trig_db;
  replace (sin a) with (sin (2 * (a/2))) by (apply f_equal; lra);
  rewrite sin_2a;
  apply c_proj_eq; simpl; field_simplify_eq; try nonzero;
  change_to_sqr;
  try rewrite sin_half_squared;
  try rewrite cos_half_squared;
  rewrite Rsqr_sqrt by lra;
  lra.

Local Open Scope ucom_scope.
Local Close Scope Q_scope.
Local Open Scope R_scope.
Lemma u3_to_rz : forall dim a b c q,
  @SQIR.U3 dim a b c q ≅ SQIR.Rz (c - (PI/2)) q ; SQIR.H q ; SQIR.Rz a q ; SQIR.H q ; SQIR.Rz (b + (PI/2)) q.
Proof.
  intros. 
  unfold uc_cong; simpl.
  exists (- (a / 2)).
  autorewrite with eval_db.
  bdestruct_all.
  gridify.
  rewrite <- Mscale_kron_dist_l.
  rewrite <- Mscale_kron_dist_r.
  apply f_equal2; try reflexivity.
  apply f_equal2; try reflexivity.
  unfold phase_shift, rotation, hadamard.
  solve_matrix; u3_to_rz_aux a. (* all goals solved by ltac above *)
  (* final case is ill-typed *)
  Msimpl. 
  reflexivity.
Qed.

Lemma u2_to_rz : forall dim a b q,
  @SQIR.U2 dim a b q ≡ SQIR.Rz (b - PI) q ; SQIR.H q ; SQIR.Rz a q.
Proof.
  intros. 
  unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify.
  apply f_equal2; try reflexivity.
  apply f_equal2; try reflexivity.
  unfold phase_shift, rotation, hadamard.
  solve_matrix;
  try rewrite Cexp_add;
  try rewrite Cexp_minus_PI;
  replace (PI / 2 / 2) with (PI / 4) by lra;
  autorewrite with trig_db RtoC_db;
  lca.
Qed.

Lemma rx_to_rz : forall dim a q,
  @SQIR.Rx dim a q ≅ SQIR.H q ; SQIR.Rz a q ; SQIR.H q.
Proof.
  intros dim a q. 
  assert (H: @Rx dim a q ≅ U3 a (- (PI / 2)) (PI / 2) q).
  reflexivity.  
  rewrite H.
  rewrite u3_to_rz.
  replace (PI / 2 - PI / 2) with 0 by lra.
  replace (- (PI / 2) + PI / 2) with 0 by lra.
  apply uc_equiv_cong.
  rewrite Rz_0_id.
  bdestruct (q <? dim)%nat.
  rewrite ID_equiv_SKIP by assumption.
  rewrite SKIP_id_l, SKIP_id_r by assumption.
  reflexivity. 
  unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify.
Qed.

Lemma ry_to_rz : forall dim a q,
  @SQIR.Ry dim a q ≅ SQIR.PDAG q ; SQIR.H q ; SQIR.Rz a q ; SQIR.H q ; SQIR.P q.
Proof.
  intros dim a q. 
  assert (H: @Ry dim a q ≅ U3 a 0 0 q).
  reflexivity.  
  rewrite H.
  rewrite u3_to_rz.
  replace (0 - PI / 2) with (- (PI / 2)) by lra.
  replace (0 + PI / 2) with (PI / 2) by lra.
  reflexivity.
Qed.

(** * Function to convert between gate sets **)

Local Open Scope Z_scope.

(* Effectively List.map, but tail recursive *)
Fixpoint change_gate_set' {dim : nat} {U1 U2 : nat -> Set} 
      (f : gate_app U1 dim -> gate_list U2 dim) (l : gate_list U1 dim) 
      (acc : gate_list U2 dim) : gate_list U2 dim := 
  match l with
  | [] => List.rev acc
  (* technically ++ isn't tail recursive, but when the first argument (i.e. f g)
     is small it shouldn't matter *)
  | g :: t => change_gate_set' f t (List.rev (f g) ++ acc) 
  end.

Definition change_gate_set {dim : nat} {U1 U2 : nat -> Set} 
      (f : gate_app U1 dim -> gate_list U2 dim) (l : gate_list U1 dim) 
      : gate_list U2 dim := 
  change_gate_set' f l [].

Lemma change_gate_set_nil : forall {dim U1 U2} f,
  @change_gate_set dim U1 U2 f [] = [].
Proof. intros. reflexivity. Qed.

Lemma change_gate_set_cons : forall {dim U1 U2} f h t,
  @change_gate_set dim U1 U2 f (h :: t) = f h ++ change_gate_set f t.
Proof.
  intros.
  assert (forall l acc, change_gate_set' f l acc = rev acc ++ change_gate_set' f l []).
  { induction l; intro acc; simpl.
    rewrite app_nil_r.
    reflexivity.
    rewrite IHl.
    rewrite (IHl (_ ++ _)).
    repeat rewrite rev_app_distr.
    repeat rewrite rev_involutive.
    simpl.
    rewrite app_assoc.
    reflexivity. }
  unfold change_gate_set.
  simpl.
  rewrite H.  
  rewrite rev_app_distr.
  rewrite rev_involutive.
  simpl.
  reflexivity.
Qed.

Lemma change_gate_set_app : forall {dim U1 U2} f l1 l2,
  @change_gate_set dim U1 U2 f (l1 ++ l2) = change_gate_set f l1 ++ change_gate_set f l2.
Proof.
  intros.
  induction l1.
  reflexivity.
  rewrite <- app_comm_cons.
  rewrite 2 change_gate_set_cons.
  rewrite IHl1.
  rewrite app_assoc.
  reflexivity.
Qed.

(** * IBM gate set **)

Definition full_to_IBM_u {dim} (g : gate_app Full_Unitary dim) : IBM_ucom_l dim :=
  match g with
  | App1 U_I m              => [IBMGateSet.Rz 0 m]
  | App1 U_X m              => [IBMGateSet.X m]
  | App1 U_Y m              => [IBMGateSet.Y m]
  | App1 U_Z m              => [IBMGateSet.Z m]
  | App1 U_H m              => [IBMGateSet.H m]
  | App1 U_S m              => [IBMGateSet.P m]
  | App1 U_T m              => [IBMGateSet.T m]
  | App1 U_Sdg m            => [IBMGateSet.PDAG m]
  | App1 U_Tdg m            => [IBMGateSet.TDAG m]
  | App1 (U_Rx r) m         => [IBMGateSet.Rx r m]
  | App1 (U_Ry r) m         => [IBMGateSet.Ry r m]
  | App1 (U_Rz r) m         => [IBMGateSet.Rz r m]
  | App1 (U_Rzq q) m        => [IBMGateSet.Rz (Q2R q * PI) m]
  | App1 (U_U1 r) m         => [IBMGateSet.U1 r m]
  | App1 (U_U2 r1 r2) m     => [IBMGateSet.U2 r1 r2 m]
  | App1 (U_U3 r1 r2 r3) m  => [IBMGateSet.U3 r1 r2 r3 m]
  | App2 U_CX m n           => [IBMGateSet.CNOT m n]
  | App2 U_CZ m n           => IBMGateSet.CZ m n
  | App2 U_SWAP m n         => IBMGateSet.SWAP m n
  | App3 U_CCX m n p        => IBMGateSet.CCX m n p
  | App3 U_CCZ m n p        => IBMGateSet.CCZ m n p
  | _ => [] (* unreachable *)
  end.

Definition IBM_to_full_u {dim} (g : gate_app IBM_Unitary dim) : full_ucom_l dim :=
  match g with
  | App1 (UIBM_U1 a) m      => [App1 (U_U1 a) m]
  | App1 (UIBM_U2 a b) m    => [App1 (U_U2 a b) m]
  | App1 (UIBM_U3 a b c) m  => [App1 (U_U3 a b c) m]
  | App2 UIBM_CNOT m n      => [App2 U_CX m n]
  | _ => [] (* unreachable *)
  end.

Definition full_to_IBM {dim} (l : full_ucom_l dim) : IBM_ucom_l dim := 
  change_gate_set full_to_IBM_u l.

Definition IBM_to_full {dim} (l : IBM_ucom_l dim) : full_ucom_l dim := 
  change_gate_set IBM_to_full_u l.

Lemma IBM_to_base1 : forall {dim} (u : IBM_Unitary 1) n,
  IBMGateSet.to_base u [n] (one_elem_list n) ≡ 
    FullList.list_to_ucom (IBM_to_full_u (@App1 _ dim u n)).
Proof.
  intros dim u n.
  dependent destruction u; simpl; rewrite SKIP_id_r; reflexivity.
Qed.

Lemma IBM_to_base2 : forall {dim} (u : IBM_Unitary 2) m n,
  IBMGateSet.to_base u (m :: n :: []) (two_elem_list m n) ≡ 
    FullList.list_to_ucom (IBM_to_full_u (@App2 _ dim u m n)).
Proof.
  intros dim u m n.
  dependent destruction u; simpl; rewrite SKIP_id_r; reflexivity.
Qed.

Lemma IBM_list_to_ucom : forall {dim} (l : IBM_ucom_l dim),
  IBMList.list_to_ucom l ≡ FullList.list_to_ucom (IBM_to_full l).
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  unfold IBM_to_full. 
  rewrite change_gate_set_cons.
  rewrite FullList.list_to_ucom_append.
  destruct a.
  rewrite IBM_to_base1, IHl.
  reflexivity.
  rewrite IBM_to_base2, IHl.
  reflexivity.
  dependent destruction i.
Qed.

Lemma IBM_to_full_equiv : forall {dim} (l l' : IBM_ucom_l dim),
  IBMGateSet.IBMList.uc_equiv_l l l' ->
  FullList.uc_equiv_l (IBM_to_full l) (IBM_to_full l').
Proof.
  intros dim l l' H.
  unfold FullList.uc_equiv_l.
  unfold IBMGateSet.IBMList.uc_equiv_l in H.
  rewrite 2 IBM_list_to_ucom in H.
  assumption.
Qed.

Lemma IBM_to_full_cong : forall {dim} (l l' : IBM_ucom_l dim),
  IBMGateSet.IBMList.uc_cong_l l l' ->
  FullList.uc_cong_l (IBM_to_full l) (IBM_to_full l').
Proof.
  intros dim l l' H.
  unfold FullList.uc_equiv_l.
  unfold IBMGateSet.IBMList.uc_cong_l in H.
  unfold uc_cong in H.
  rewrite 2 IBM_list_to_ucom in H.
  assumption.
Qed.

Lemma IBM_to_full_inv : forall {dim} (l : full_ucom_l dim),
  FullList.uc_equiv_l (IBM_to_full (full_to_IBM l)) l.
Proof.
  intros dim l.
  induction l.
  reflexivity.
  unfold full_to_IBM, IBM_to_full.
  rewrite change_gate_set_cons.
  rewrite change_gate_set_app.
  rewrite IHl.
  rewrite cons_to_app.
  FullList.apply_app_congruence.
  destruct a; dependent destruction f; 
  unfold change_gate_set; simpl; try reflexivity.
  all: unfold FullList.uc_equiv_l; simpl;
       repeat rewrite <- useq_assoc; reflexivity.
Qed.

Lemma full_to_IBM_WT : forall {dim} (l : full_ucom_l dim),
  uc_well_typed_l l ->
  uc_well_typed_l (full_to_IBM l).
Proof.
  intros dim l WT.
  unfold full_to_IBM.
  induction WT.
  - constructor. assumption.
  - dependent destruction u; rewrite change_gate_set_cons; 
    simpl; try constructor; assumption.
  - dependent destruction u; rewrite change_gate_set_cons; 
    simpl; repeat constructor; try assumption. lia.
  - dependent destruction u; rewrite change_gate_set_cons; 
    simpl; repeat constructor; assumption.
Qed.

Lemma full_to_IBM_preserves_mapping : forall {dim} (l : full_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph U_CX l ->
  respects_constraints_directed is_in_graph UIBM_CNOT (full_to_IBM l).
Proof.
  intros dim l is_in_graph H.
  unfold full_to_IBM.
  induction l.
  constructor.
  rewrite change_gate_set_cons. 
  inversion H; subst.
  apply respects_constraints_directed_app; auto.
  dependent destruction u; repeat constructor.
  apply respects_constraints_directed_app; auto.
  repeat constructor.
  assumption.
Qed.

Lemma IBM_to_full_preserves_mapping : forall {dim} (l : IBM_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph UIBM_CNOT l ->
  respects_constraints_directed is_in_graph U_CX (IBM_to_full l).
Proof.
  intros dim l is_in_graph H.
  unfold IBM_to_full.
  induction l.
  constructor.
  rewrite change_gate_set_cons. 
  inversion H; subst.
  apply respects_constraints_directed_app; auto.
  dependent destruction u; repeat constructor.
  apply respects_constraints_directed_app; auto.
  repeat constructor.
  assumption.
Qed.

(** * RzQ gate set **)

(* A perfect real -> rational function DOES NOT exist because some real
   numbers are irrational. However, I am going to assert such a function
   as an axiom until we come up with a better solution. This is BAD and
   maybe be a source of troubles in the future. We extract this as a function
   that converts from floats to rationals (which is ok). -KH *)
Axiom R2Q : R -> Q.
Definition R2Q_PI x := R2Q (x / PI).
Axiom Q2R_R2Q_PI : forall r, (Q2R (R2Q_PI r) * PI)%R = r.
Definition Rx {dim} a q : RzQ_ucom_l dim := H q :: Rzq (R2Q_PI a) q :: H q :: [].
Definition Rz {dim} a q := @App1 _ dim (URzQ_Rz (R2Q_PI a)) q.
Definition Ry {dim} a q : RzQ_ucom_l dim := 
  PDAG q :: H q :: Rzq (R2Q_PI a) q :: H q :: P q :: [].
Definition U1 {dim} a q := @Rz dim a q.
Definition U2 {dim} a b q : RzQ_ucom_l dim := 
  Rzq (R2Q_PI (b - PI)) q :: H q :: Rzq (R2Q_PI a) q :: [].
Definition U3 {dim} a b c q : RzQ_ucom_l dim := 
  Rzq (R2Q_PI (c - (PI/2))) q :: H q :: Rzq (R2Q_PI a) q :: 
  H q :: Rzq (R2Q_PI (b + (PI/2))) q :: [].

Definition full_to_RzQ_u {dim} (g : gate_app Full_Unitary dim) : RzQ_ucom_l dim :=
  match g with
  | App1 U_I m              => [Rzq zero_Q m]
  | App1 U_X m              => [RzQGateSet.X m]
  | App1 U_Y m              => RzQGateSet.Y m
  | App1 U_Z m              => [RzQGateSet.Z m]
  | App1 U_H m              => [RzQGateSet.H m]
  | App1 U_S m              => [RzQGateSet.P m]
  | App1 U_T m              => [RzQGateSet.T m]
  | App1 U_Sdg m            => [RzQGateSet.PDAG m]
  | App1 U_Tdg m            => [RzQGateSet.TDAG m]
  | App1 (U_Rx r) m         => Rx r m
  | App1 (U_Ry r) m         => Ry r m
  | App1 (U_Rz r) m         => [Rz r m]
  | App1 (U_Rzq q) m        => [RzQGateSet.Rzq q m]
  | App1 (U_U1 r) m         => [U1 r m]
  | App1 (U_U2 r1 r2) m     => U2 r1 r2 m
  | App1 (U_U3 r1 r2 r3) m  => U3 r1 r2 r3 m
  | App2 U_CX m n           => [RzQGateSet.CNOT m n]
  | App2 U_CZ m n           => RzQGateSet.CZ m n
  | App2 U_SWAP m n         => RzQGateSet.SWAP m n
  | App3 U_CCX m n p        => RzQGateSet.CCX m n p
  | App3 U_CCZ m n p        => RzQGateSet.CCZ m n p
  | _ => [] (* unreachable *)
  end.

Definition RzQ_to_full_u {dim} (g : gate_app RzQ_Unitary dim) : full_ucom_l dim :=
  match g with
  | App1 URzQ_H m       => [App1 U_H m]
  | App1 URzQ_X m       => [App1 U_X m]
  | App1 (URzQ_Rz q) m  => [App1 (U_Rzq q) m]
  | App2 URzQ_CNOT m n  => [App2 U_CX m n]
  | _ => [] (* unreachable *)
  end.

Definition full_to_RzQ {dim} (l : full_ucom_l dim) : RzQ_ucom_l dim := 
  change_gate_set full_to_RzQ_u l.

Definition RzQ_to_full {dim} (l : RzQ_ucom_l dim) : full_ucom_l dim := 
  change_gate_set RzQ_to_full_u l.

Lemma RzQ_to_base1 : forall {dim} (u : RzQ_Unitary 1) n,
  RzQGateSet.to_base u [n] (one_elem_list n) ≡ 
    FullList.list_to_ucom (RzQ_to_full_u (@App1 _ dim u n)).
Proof.
  intros dim u n.
  dependent destruction u; simpl; rewrite SKIP_id_r; reflexivity.
Qed.

Lemma RzQ_to_base2 : forall {dim} (u : RzQ_Unitary 2) m n,
  RzQGateSet.to_base u (m :: n :: []) (two_elem_list m n) ≡ 
    FullList.list_to_ucom (RzQ_to_full_u (@App2 _ dim u m n)).
Proof.
  intros dim u m n.
  dependent destruction u; simpl; rewrite SKIP_id_r; reflexivity.
Qed.

Lemma RzQ_list_to_ucom : forall {dim} (l : RzQ_ucom_l dim),
  RzQList.list_to_ucom l ≡ FullList.list_to_ucom (RzQ_to_full l).
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  unfold RzQ_to_full. 
  rewrite change_gate_set_cons.
  rewrite FullList.list_to_ucom_append.
  destruct a.
  rewrite RzQ_to_base1, IHl.
  reflexivity.
  rewrite RzQ_to_base2, IHl.
  reflexivity.
  dependent destruction r.
Qed.

Lemma RzQ_to_full_equiv : forall {dim} (l l' : RzQ_ucom_l dim),
  RzQGateSet.RzQList.uc_equiv_l l l' ->
  FullList.uc_equiv_l (RzQ_to_full l) (RzQ_to_full l').
Proof.
  intros dim l l' H.
  unfold FullList.uc_equiv_l.
  unfold RzQGateSet.RzQList.uc_equiv_l in H.
  rewrite 2 RzQ_list_to_ucom in H.
  assumption.
Qed.

Lemma RzQ_to_full_cong : forall {dim} (l l' : RzQ_ucom_l dim),
  RzQGateSet.RzQList.uc_cong_l l l' ->
  FullList.uc_cong_l (RzQ_to_full l) (RzQ_to_full l').
Proof.
  intros dim l l' H.
  unfold FullList.uc_equiv_l.
  unfold RzQGateSet.RzQList.uc_cong_l in H.
  unfold uc_cong in H.
  rewrite 2 RzQ_list_to_ucom in H.
  assumption.
Qed.

Local Open Scope R.
Lemma Q2R_1_4_PI : forall {dim} q, 
  @SQIR.Rz dim (Q2R (1 / 4) * PI) q ≡ SQIR.Rz (PI / 4) q.
Proof.
  intros dim q.
  unfold Q2R; simpl.
  autorewrite with R_db.
  rewrite Rmult_comm.
  reflexivity.
Qed.

Lemma Q2R_7_4_PI : forall {dim} q, 
  @SQIR.Rz dim (Q2R (7 / 4) * PI) q ≡ SQIR.Rz (- (PI / 4)) q.
Proof.
  intros dim q.
  unfold Q2R; simpl.
  unfold uc_equiv; autorewrite with eval_db; try lia.
  gridify.
  replace (7 * / 4 * PI) with (2 * PI + - (PI / 4)) by lra.
  rewrite <- phase_mul.
  rewrite phase_2pi.
  Msimpl.
  reflexivity.
Qed.

Lemma Q2R_1_2_PI : forall {dim} q, 
  @SQIR.Rz dim (Q2R (1 / 2) * PI) q ≡ SQIR.Rz (PI / 2) q.
Proof.
  intros dim q.
  unfold Q2R; simpl.
  autorewrite with R_db.
  rewrite Rmult_comm.
  reflexivity.
Qed.

Lemma Q2R_3_2_PI : forall {dim} q,
  @SQIR.Rz dim (Q2R (3 / 2) * PI) q ≡ SQIR.Rz (- (PI / 2)) q.
Proof.
  intros dim q.
  unfold Q2R; simpl.
  unfold uc_equiv; autorewrite with eval_db; try lia.
  gridify.
  replace (3 * / 2 * PI) with (2 * PI + - (PI / 2)) by lra.
  rewrite <- phase_mul.
  rewrite phase_2pi.
  Msimpl.
  reflexivity.
Qed.

Lemma Q2R_1_PI : Q2R 1 * PI = PI.
Proof. unfold Q2R; simpl. lra. Qed.

Lemma RzQ_to_full_inv : forall {dim} (l : full_ucom_l dim),
  FullList.uc_cong_l (RzQ_to_full (full_to_RzQ l)) l.
Proof.
  intros dim l.
  induction l.
  reflexivity.
  unfold full_to_RzQ, RzQ_to_full.
  rewrite change_gate_set_cons.
  rewrite change_gate_set_app.
  rewrite IHl.
  rewrite cons_to_app.
  FullList.apply_app_congruence_cong.
  destruct a; dependent destruction f; 
  unfold change_gate_set; simpl; try reflexivity.
  all: unfold FullList.uc_cong_l; simpl; repeat rewrite <- uc_cong_assoc.
  all: unfold one_Q, half_Q, three_halves_Q, quarter_Q, seven_quarters_Q.
  all: try (apply uc_equiv_cong;
            repeat rewrite Q2R_1_2_PI; repeat rewrite Q2R_3_2_PI;
            repeat rewrite Q2R_1_4_PI; repeat rewrite Q2R_7_4_PI;
            try rewrite Q2R_1_PI; repeat rewrite Q2R_R2Q_PI; reflexivity).
  (* U_I *)
  unfold zero_Q.
  rewrite RMicromega.Q2R_0, Rmult_0_l.
  apply uc_equiv_cong.
  rewrite Rz_0_id.
  reflexivity. 
  (* U_Y *)
  apply uc_equiv_cong.
  rewrite Q2R_1_2_PI, Q2R_3_2_PI.
  rewrite 2 SKIP_id_r.
  unfold uc_equiv; simpl.
  autorewrite with eval_db; try lia.
  gridify.
  do 2 (apply f_equal2; try reflexivity).
  solve_matrix; autorewrite with Cexp_db; lca.
  (* U_Rx *)
  rewrite rx_to_rz. 
  apply uc_equiv_cong.
  rewrite Q2R_R2Q_PI.
  reflexivity.
  (* U_Ry *)
  rewrite ry_to_rz.
  apply uc_equiv_cong.
  rewrite Q2R_1_2_PI, Q2R_3_2_PI, Q2R_R2Q_PI.
  reflexivity.
  (* U_U2 *)
  apply uc_equiv_cong.
  rewrite 2 Q2R_R2Q_PI.
  rewrite u2_to_rz.
  reflexivity.
  (* U_U3 *)
  rewrite u3_to_rz.
  apply uc_equiv_cong.
  repeat rewrite Q2R_R2Q_PI.
  reflexivity.
Qed.

Lemma full_to_RzQ_WT : forall {dim} (l : full_ucom_l dim),
  uc_well_typed_l l ->
  uc_well_typed_l (full_to_RzQ l).
Proof.
  intros dim l WT.
  unfold full_to_RzQ.
  induction WT.
  - constructor. assumption.
  - dependent destruction u; rewrite change_gate_set_cons; 
    simpl; repeat constructor; assumption.
  - dependent destruction u; rewrite change_gate_set_cons; 
    simpl; repeat constructor; try assumption. lia.
  - dependent destruction u; rewrite change_gate_set_cons; 
    simpl; repeat constructor; assumption.
Qed.

Lemma full_to_RzQ_preserves_mapping : forall {dim} (l : full_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph U_CX l ->
  respects_constraints_directed is_in_graph URzQ_CNOT (full_to_RzQ l).
Proof.
  intros dim l is_in_graph H.
  unfold full_to_RzQ.
  induction l.
  constructor.
  rewrite change_gate_set_cons. 
  inversion H; subst.
  apply respects_constraints_directed_app; auto.
  dependent destruction u; repeat constructor.
  apply respects_constraints_directed_app; auto.
  repeat constructor.
  assumption.
Qed.

Lemma RzQ_to_full_preserves_mapping : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph U_CX (RzQ_to_full l).
Proof.
  intros dim l is_in_graph H.
  unfold RzQ_to_full.
  induction l.
  constructor.
  rewrite change_gate_set_cons. 
  inversion H; subst.
  apply respects_constraints_directed_app; auto.
  dependent destruction u; repeat constructor.
  apply respects_constraints_directed_app; auto.
  repeat constructor.
  assumption.
Qed.

(** * Mapping gate set **)

Definition decompose_to_cnot_and_swap_u {dim} (g : gate_app Full_Unitary dim) : full_ucom_l dim :=
  match g with
  | App2 U_CZ m n     => App1 U_H n :: App2 U_CX m n :: App1 U_H n :: []
  | App3 U_CCX m n p  => App1 U_H p :: App2 U_CX n p :: App1 U_Tdg p :: 
                        App2 U_CX m p :: App1 U_T p :: App2 U_CX n p :: 
                        App1 U_Tdg p :: App2 U_CX m p :: App2 U_CX m n :: 
                        App1 U_Tdg n :: App2 U_CX m n :: App1 U_T m :: 
                        App1 U_T n :: App1 U_T p :: App1 U_H p :: [] 
  | App3 U_CCZ m n p  => App2 U_CX n p :: App1 U_Tdg p :: 
                        App2 U_CX m p :: App1 U_T p :: App2 U_CX n p :: 
                        App1 U_Tdg p :: App2 U_CX m p :: App2 U_CX m n :: 
                        App1 U_Tdg n :: App2 U_CX m n :: App1 U_T m :: 
                        App1 U_T n :: App1 U_T p :: []
  | g => [g]
  end.

Definition full_to_map_u {dim} (g : gate_app Full_Unitary dim) : gate_app (Map_Unitary (Full_Unitary 1)) dim :=
  match g with
  | App1 u m         => App1 (UMap_U u) m
  | App2 U_CX m n    => App2 UMap_CNOT m n
  | App2 U_SWAP m n  => App2 UMap_SWAP m n
  | _ => App1 (UMap_U U_I) 0 (* unreachable *)
  end.

Definition full_to_map {dim} (l : full_ucom_l dim) : map_ucom_l (Full_Unitary 1) dim := 
  change_gate_set (fun g => map full_to_map_u (decompose_to_cnot_and_swap_u g)) l.

Definition map_to_full_u {dim} (g : gate_app (Map_Unitary (Full_Unitary 1)) dim) : full_ucom_l dim :=
  match g with
  | App1 (UMap_U u) m    => [App1 u m]
  | App2 UMap_CNOT m n   => [App2 U_CX m n]
  | App2 UMap_SWAP m n   => [App2 U_SWAP m n]
  | _ => [] (* unreachable *)
  end.

Definition map_to_full {dim} (l : map_ucom_l (Full_Unitary 1) dim) : full_ucom_l dim := 
  change_gate_set map_to_full_u l.

(* TODO (if needed):

Lemma map_to_full_equiv : forall {dim} (l l' : map_ucom_l (Std_Unitary 1) dim),
  MappingGateSet.MapList.uc_equiv_l l l' ->
  FullList.uc_equiv_l (map_to_full l) (map_to_full l').
*)

Lemma map_to_full_inv : forall {dim} (l : full_ucom_l dim),
  FullList.uc_cong_l (map_to_full (full_to_map l)) l.
Proof.
  intros dim l.
  induction l.
  reflexivity.
  unfold full_to_map, map_to_full.
  rewrite change_gate_set_cons.
  rewrite change_gate_set_app.
  rewrite IHl.
  rewrite cons_to_app.
  FullList.apply_app_congruence_cong.
  destruct a; dependent destruction f; 
  unfold change_gate_set; simpl; try reflexivity.
  all: unfold FullList.uc_cong_l; simpl; 
    repeat rewrite <- uc_cong_assoc; reflexivity.
Qed.

Lemma full_to_map_WT : forall {dim} (l : full_ucom_l dim),
  uc_well_typed_l l ->
  uc_well_typed_l (full_to_map l).
Proof.
  intros dim l WT.
  unfold full_to_map.
  induction WT.
  - constructor. assumption.
  - dependent destruction u; rewrite change_gate_set_cons; 
    simpl; repeat constructor; assumption.
  - dependent destruction u; rewrite change_gate_set_cons; 
    simpl; repeat constructor; assumption.
  - dependent destruction u; rewrite change_gate_set_cons; 
    simpl; repeat constructor; assumption.
Qed.

(** * Check that every gate in the program satisfies some predicate **)

Definition forall_gates {U : nat -> Set} {dim} (p : gate_app U dim -> Prop) (l : gate_list U dim) :=
  forall g, In g l -> p g.

Lemma forall_gates_drop : forall {U : nat -> Set} {dim} (p : gate_app U dim -> Prop) (g : gate_app U dim) (l : gate_list U dim),
  forall_gates p (g :: l) -> forall_gates p l.
Proof.
  intros U dim p g l H.
  unfold forall_gates in *.
  intros g0 Hg0.
  apply H.
  right.
  assumption.
Qed.

Lemma forall_gates_extend : forall {U : nat -> Set} {dim} (p : gate_app U dim -> Prop) (g : gate_app U dim) (l : gate_list U dim),
  p g -> forall_gates p l -> forall_gates p (g :: l).
Proof.
  intros U dim p g l Hg Hl.
  unfold forall_gates in *.
  intros g0 [Hg0 | Hg0].
  subst. 
  assumption.
  apply Hl.
  assumption.
Qed.

Lemma forall_gates_append : forall {U : nat -> Set} {dim} (p : gate_app U dim -> Prop) (l1 l2 : gate_list U dim),
  forall_gates p l1 -> forall_gates p l2 -> forall_gates p (l1 ++ l2).
Proof.
  intros U dim p l1 l2 Hl1 Hl2.
  unfold forall_gates in *.
  intros g Hg.
  apply in_app_or in Hg as [Hg | Hg]; auto.
Qed.

(** * Other gate set conversions **)

(* Transform program in the full gate set to only use CNOT + 1q gates *)
Definition decompose_to_cnot_u {dim} (g : gate_app Full_Unitary dim) : full_ucom_l dim :=
  match g with
  | App2 U_CZ m n     => App1 U_H n :: App2 U_CX m n :: App1 U_H n :: []
  | App2 U_SWAP m n   => App2 U_CX m n :: App2 U_CX n m :: App2 U_CX m n :: []
  | App3 U_CCX m n p  => App1 U_H p :: App2 U_CX n p :: App1 U_Tdg p :: 
                        App2 U_CX m p :: App1 U_T p :: App2 U_CX n p :: 
                        App1 U_Tdg p :: App2 U_CX m p :: App2 U_CX m n :: 
                        App1 U_Tdg n :: App2 U_CX m n :: App1 U_T m :: 
                        App1 U_T n :: App1 U_T p :: App1 U_H p :: [] 
  | App3 U_CCZ m n p  => App2 U_CX n p :: App1 U_Tdg p :: 
                        App2 U_CX m p :: App1 U_T p :: App2 U_CX n p :: 
                        App1 U_Tdg p :: App2 U_CX m p :: App2 U_CX m n :: 
                        App1 U_Tdg n :: App2 U_CX m n :: App1 U_T m :: 
                        App1 U_T n :: App1 U_T p :: []
  | g => [g]
  end.

Definition decompose_to_cnot {dim} (l : full_ucom_l dim) :=
  change_gate_set decompose_to_cnot_u l.

Definition only_cnots {dim} (g : gate_app Full_Unitary dim) :=
  match g with
  | App2 U_CZ _ _ | App2 U_SWAP _ _ | App3 U_CCX _ _ _ | App3 U_CCZ _ _ _ => False
  | _ => True
  end.

Lemma decompose_to_cnot_gates : forall {dim} (l : full_ucom_l dim),
  forall_gates only_cnots (decompose_to_cnot l).
Proof.
  intros dim l.
  unfold decompose_to_cnot.
  induction l.
  - rewrite change_gate_set_nil.
    intros g H.
    inversion H.
  - rewrite change_gate_set_cons.
    intros g H.
    apply in_app_or in H as [H | H].
    destruct a; dependent destruction f.
    all: simpl in H; repeat destruct H as [H | H]; try rewrite <- H; 
         simpl; auto; try contradiction. 
Qed.

Lemma decompose_to_cnot_sound : forall {dim} (l : full_ucom_l dim),
  FullList.uc_equiv_l (decompose_to_cnot l) l.
Proof.
  intros dim l.
  unfold decompose_to_cnot.
  induction l.
  - rewrite change_gate_set_nil.
    reflexivity.
  - rewrite change_gate_set_cons.
    unfold FullList.uc_equiv_l in *.
    simpl.
    rewrite FullList.list_to_ucom_append.
    destruct a; apply useq_congruence; try apply IHl;
      dependent destruction f; simpl; 
      repeat rewrite <- useq_assoc; rewrite SKIP_id_r; 
      reflexivity.
Qed.

Lemma decompose_to_cnot_WT : forall {dim} (l : full_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (decompose_to_cnot l).
Proof.
  intros dim l WT.
  eapply FullList.uc_equiv_l_implies_WT.
  symmetry.
  apply decompose_to_cnot_sound.
  assumption.
Qed.

Definition convert_to_ibm {dim} (l : full_ucom_l dim) : full_ucom_l dim := 
  IBM_to_full (full_to_IBM l).

Definition only_ibm {dim} (g : gate_app Full_Unitary dim) :=
  match g with
  | App1 (U_U1 _) _ | App1 (U_U2 _ _) _ | App1 (U_U3 _ _ _) _ | App2 U_CX _ _ => True
  | _ => False
  end.

Lemma convert_to_ibm_gates : forall {dim} (l : full_ucom_l dim),
  forall_gates only_ibm (convert_to_ibm l).
Proof.
  intro dim.
  assert (H : forall (l : IBM_ucom_l dim), forall_gates only_ibm (IBM_to_full l)).
  { unfold IBM_to_full.
    induction l.
    - rewrite change_gate_set_nil.
      intros g H.
      inversion H.
    - rewrite change_gate_set_cons.
      intros g H.
      apply in_app_or in H as [H | H].
      destruct a; dependent destruction i.
      all: simpl in H; repeat destruct H as [H | H]; try rewrite <- H.
      all: simpl; auto; contradiction. }
  intro l.
  apply H.  
Qed.

Lemma convert_to_ibm_sound : forall {dim} (l : full_ucom_l dim),
  FullList.uc_equiv_l (convert_to_ibm l) l.
Proof. intros. apply IBM_to_full_inv. Qed.

Lemma convert_to_ibm_preserves_mapping : forall {dim} (l : full_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph U_CX l ->
  respects_constraints_directed is_in_graph U_CX (convert_to_ibm l).
Proof.
  intros dim l is_in_graph H.
  unfold convert_to_ibm.
  apply IBM_to_full_preserves_mapping.
  apply full_to_IBM_preserves_mapping.
  assumption.
Qed.

Definition convert_to_rzq {dim} (l : full_ucom_l dim) : full_ucom_l dim := 
  RzQ_to_full (full_to_RzQ l).

Definition only_rzq {dim} (g : gate_app Full_Unitary dim) :=
  match g with
  | App1 U_H _ | App1 U_X _ | App1 (U_Rzq _) _ | App2 U_CX _ _ => True
  | _ => False
  end.

Lemma convert_to_rzq_gates : forall {dim} (l : full_ucom_l dim),
  forall_gates only_rzq (convert_to_rzq l).
Proof.
  intro dim.
  assert (H : forall (l : RzQ_ucom_l dim), forall_gates only_rzq (RzQ_to_full l)).
  { unfold RzQ_to_full.
    induction l.
    - rewrite change_gate_set_nil.
      intros g H.
      inversion H.
    - rewrite change_gate_set_cons.
      intros g H.
      apply in_app_or in H as [H | H].
      destruct a; dependent destruction r.
      all: simpl in H; repeat destruct H as [H | H]; try rewrite <- H.
      all: simpl; auto; contradiction. }
  intro l.
  apply H.  
Qed.

Lemma convert_to_rzq_sound : forall {dim} (l : full_ucom_l dim),
  FullList.uc_cong_l (convert_to_rzq l) l.
Proof. intros. apply RzQ_to_full_inv. Qed.

Lemma convert_to_rzq_preserves_mapping : forall {dim} (l : full_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph U_CX l ->
  respects_constraints_directed is_in_graph U_CX (convert_to_rzq l).
Proof.
  intros dim l is_in_graph H.
  unfold convert_to_rzq.
  apply RzQ_to_full_preserves_mapping.
  apply full_to_RzQ_preserves_mapping.
  assumption.
Qed.

(* Replace Rzq gates with I, Z, S, Sdg, T, Tdg, or Rz gates. *)
Definition replace_rzq_u {dim} (g : gate_app Full_Unitary dim) : full_ucom_l dim :=
  match g with
  | App1 (U_Rzq q) m => 
      if Qeq_bool q zero_Q then [App1 U_I m]
      else if Qeq_bool q one_Q then [App1 U_Z m]
      else if Qeq_bool q half_Q then [App1 U_S m]
      else if Qeq_bool q three_halves_Q then [App1 U_Sdg m]
      else if Qeq_bool q quarter_Q then [App1 U_T m]
      else if Qeq_bool q seven_quarters_Q then [App1 U_Tdg m]
      else [App1 (U_Rz (Q2R q * PI)) m]
  | g => [g]
  end.

Definition replace_rzq {dim} (l : full_ucom_l dim) :=
  change_gate_set replace_rzq_u l.

Definition no_rzq {dim} (g : gate_app Full_Unitary dim) :=
  match g with
  | App1 (U_Rzq _) _ => False
  | _ => True
  end.

Ltac destruct_Qeq_bool :=
  repeat match goal with
  | H : context[if Qeq_bool ?a ?b then _ else _] |- _ => 
      destruct (Qeq_bool a b) eqn:? 
  | |- context[if Qeq_bool ?a ?b then _ else _] => 
      destruct (Qeq_bool a b) eqn:? 
  | H : Qeq_bool _ _ = true |- _ => apply Qeq_bool_iff in H
  | H : Qeq_bool _ _ = false |- _ => clear H
  | H : (_ == _)%Q |- _ => apply Qeq_eqR in H; try rewrite H
  end.

Lemma replace_rzq_gates : forall {dim} (l : full_ucom_l dim),
  forall_gates no_rzq (replace_rzq l).
Proof.
  intros dim l.
  unfold replace_rzq.
  induction l.
  - rewrite change_gate_set_nil.
    intros g H.
    inversion H.
  - rewrite change_gate_set_cons.
    intros g H.
    apply in_app_or in H as [H | H].
    destruct a; dependent destruction f.
    all: simpl in H.
    all: destruct_Qeq_bool.
    all: repeat destruct H as [H | H]; try rewrite <- H.
    all: simpl; auto; try contradiction.
Qed.

Lemma replace_rzq_sound : forall {dim} (l : full_ucom_l dim),
  FullList.uc_equiv_l (replace_rzq l) l.
Proof.
  intros dim l.
  unfold replace_rzq.
  induction l.
  - rewrite change_gate_set_nil.
    reflexivity.
  - rewrite change_gate_set_cons.
    unfold FullList.uc_equiv_l in *.
    simpl.
    rewrite FullList.list_to_ucom_append.
    destruct a; apply useq_congruence; try apply IHl;
      dependent destruction f; simpl;
      repeat rewrite <- useq_assoc; try rewrite SKIP_id_r; try reflexivity.
    destruct_Qeq_bool; simpl; rewrite SKIP_id_r.
    unfold zero_Q.
    rewrite RMicromega.Q2R_0.
    rewrite Rmult_0_l.
    reflexivity.
    unfold one_Q.
    rewrite RMicromega.Q2R_1.
    rewrite Rmult_1_l.
    reflexivity.
    unfold half_Q.
    rewrite Q2R_1_2_PI.
    reflexivity.
    unfold three_halves_Q.
    bdestruct (n <? dim)%nat.
    rewrite Q2R_3_2_PI by assumption.
    reflexivity.
    unfold uc_equiv; simpl; unfold SQIR.PDAG; autorewrite with eval_db; gridify.
    unfold quarter_Q.
    rewrite Q2R_1_4_PI.
    reflexivity.
    unfold seven_quarters_Q.
    bdestruct (n <? dim)%nat.
    rewrite Q2R_7_4_PI by assumption.
    reflexivity.
    unfold uc_equiv; simpl; unfold SQIR.TDAG; autorewrite with eval_db; gridify.
    reflexivity.
Qed.

Lemma replace_rzq_preserves_mapping : forall {dim} (l : full_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph U_CX l ->
  respects_constraints_directed is_in_graph U_CX (replace_rzq l).
Proof.
  intros dim l is_in_graph H.
  unfold replace_rzq.
  induction l.
  constructor.
  rewrite change_gate_set_cons. 
  inversion H; subst.
  apply respects_constraints_directed_app; auto.
  dependent destruction u; repeat constructor.
  simpl.
  destruct_Qeq_bool; repeat constructor.
  apply respects_constraints_directed_app; auto.
  repeat constructor.
  assumption.
Qed.
