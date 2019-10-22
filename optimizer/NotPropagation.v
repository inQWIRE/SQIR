Require Import UnitarySem.
Require Import PI4GateSet.
Require Import Equivalences.
Require Import Proportional.
Require Import List.
Require Import Setoid.

Local Close Scope C_scope.
Local Close Scope R_scope.

(** Alternate gate set **)

(* Set of gates used in the benchmark programs. Same as the PI4 gate set, but
   with Toffoli (CCX) with +/- control. Irritatingly, some of our benchmarks 
   use CCZ instead of CCX, so we'll rely on the equivalence 
   'CCX a b c = H c; CCZ a b c; H c' *)
Inductive benchmark_Unitary : nat -> Set := 
  | UB_H                  : benchmark_Unitary 1 
  | UB_X                  : benchmark_Unitary 1
  | UB_Z                  : benchmark_Unitary 1
  | UB_T                  : benchmark_Unitary 1
  | UB_TDAG               : benchmark_Unitary 1
  | UB_P                  : benchmark_Unitary 1
  | UB_PDAG               : benchmark_Unitary 1
  | UB_CNOT               : benchmark_Unitary 2
  | UB_CCZ                : benchmark_Unitary 3
  | UB_CCX                : bool -> bool -> benchmark_Unitary 3.

Definition bench_ucom_l dim := gate_list benchmark_Unitary dim.

Definition CCX00 {dim} a b c : PI4_ucom_l dim :=
  H c :: CNOT b c :: T c :: CNOT a c :: 
  T c :: CNOT b c :: T c :: CNOT a c :: 
  CNOT a b :: TDAG b :: CNOT a b :: 
  TDAG a :: TDAG b :: T c :: H c :: []. 

Definition CCX01 {dim} a b c : PI4_ucom_l dim :=
  H c :: CNOT b c :: T c :: CNOT a c :: 
  T c :: CNOT b c :: TDAG c :: CNOT a c :: 
  CNOT a b :: TDAG b :: CNOT a b :: 
  T a :: TDAG b :: TDAG c :: H c :: []. 

Definition CCX10 {dim} a b c : PI4_ucom_l dim := CCX01 b a c.

Definition CCX11 {dim} a b c : PI4_ucom_l dim :=
  H c :: CNOT b c :: TDAG c :: CNOT a c :: 
  T c :: CNOT b c :: TDAG c :: CNOT a c :: 
  CNOT a b :: TDAG b :: CNOT a b :: 
  T a :: T b :: T c :: H c :: []. 

Definition CCZ {dim} a b c : PI4_ucom_l dim :=
  CNOT b c :: TDAG c :: CNOT a c :: 
  T c :: CNOT b c :: TDAG c :: CNOT a c :: 
  CNOT a b :: TDAG b :: CNOT a b :: 
  T a :: T b :: T c :: []. (* same as CCX11, but without first & last hadamards *)

Fixpoint to_PI4_list {dim} (l : bench_ucom_l dim) : PI4_ucom_l dim :=
  match l with
  | App1 UB_H a :: t      => H a :: (to_PI4_list t) 
  | App1 UB_X a :: t      => X a :: (to_PI4_list t) 
  | App1 UB_Z a :: t      => Z a :: (to_PI4_list t)
  | App1 UB_T a :: t      => T a :: (to_PI4_list t) 
  | App1 UB_TDAG a :: t   => TDAG a :: (to_PI4_list t) 
  | App1 UB_P a :: t      => P a :: (to_PI4_list t) 
  | App1 UB_PDAG a :: t   => PDAG a :: (to_PI4_list t) 
  | App2 UB_CNOT a b :: t => CNOT a b :: (to_PI4_list t) 
  | App3 UB_CCZ a b c :: t => (CCZ a b c)  ++ (to_PI4_list t)  
  | App3 (UB_CCX false false) a b c :: t => (CCX00 a b c)  ++ (to_PI4_list t)  
  | App3 (UB_CCX false true) a b c :: t  => (CCX01 a b c)  ++ (to_PI4_list t)  
  | App3 (UB_CCX true false) a b c :: t  => (CCX10 a b c)  ++ (to_PI4_list t)  
  | App3 (UB_CCX true true) a b c :: t   => (CCX11 a b c)  ++ (to_PI4_list t)  
  | _ => []
  end.

Lemma to_PI4_list_append : forall {dim} (l1 l2 : bench_ucom_l dim),
  to_PI4_list (l1 ++ l2) = to_PI4_list l1 ++ to_PI4_list l2.
Proof.
  intros dim l1 l2.
  induction l1; try reflexivity.
  Local Opaque CCX00 CCX01 CCX10 CCX11 CCZ.
  simpl.
  destruct a; dependent destruction b; simpl.
  10: destruct b; destruct b1.
  all: rewrite IHl1; reflexivity.
Qed.  

Lemma to_PI4_list_dnr : forall {dim} (l : bench_ucom_l dim) q,
  does_not_reference l q = true -> does_not_reference (to_PI4_list l) q = true.
Proof.
  intros dim l q H.
  induction l; try reflexivity.
  simpl in *.
  apply andb_true_iff in H as [H1 H2].
  specialize (IHl H2); clear H2.
  destruct a. 
  - simpl in H1. 
    dependent destruction b; simpl;
    apply andb_true_iff; split; assumption.
  - simpl in H1.
    dependent destruction b; simpl;
    apply andb_true_iff; split; assumption.
  - simpl in H1.
    dependent destruction b; simpl;
    try (destruct b; destruct b1).
    all: apply andb_true_iff; simpl.
    all: bdestruct (n =? q); bdestruct (n0 =? q); bdestruct (n1 =? q); 
         try discriminate; simpl.
    all: split; auto.
Qed.

Lemma to_PI4_list_WT : forall {dim} (l : bench_ucom_l dim),
  uc_well_typed_l l <-> uc_well_typed_l (to_PI4_list l).
Proof.
  split; intros H.
  - induction H.
    constructor; assumption. 
    all: simpl; dependent destruction u.
    10: destruct b; destruct b0. 
    all: try (apply uc_well_typed_l_app; split).
    all: try constructor; try assumption. 
    Local Transparent CCZ CCX00 CCX01 CCX10 CCX11.
    all: repeat constructor; try assumption; try lia.
  - induction l.
    inversion H.
    constructor; assumption. 
    destruct a. 
    dependent destruction b; inversion H; subst; constructor; try assumption.
    all: try (apply IHl; assumption).
    dependent destruction b. 
    inversion H; subst. 
    constructor; try assumption.
    apply IHl; assumption.
    dependent destruction b. 
    simpl in H. 
    repeat match goal with
    | H : uc_well_typed_l (_ :: _) |- _ => inversion H; subst; clear H
    end.
    constructor; try assumption. 
    apply IHl; assumption.
    simpl in H. 
    destruct b; destruct b1.
    all: repeat match goal with
    | H : uc_well_typed_l (_ :: _) |- _ => inversion H; subst; clear H
    end.
    all: constructor; try assumption; try lia. 
    all: apply IHl; assumption.
Qed.

Definition uc_equiv_l' {dim} (l1 l2 : bench_ucom_l dim) := 
  uc_equiv_l (to_PI4_list l1) (to_PI4_list l2).
Local Infix "=l=" := uc_equiv_l' (at level 70).

Lemma uc_equiv_l'_refl : forall {dim} (l1 : bench_ucom_l dim), l1 =l= l1.
Proof. easy. Qed.
 
Lemma uc_equiv_l'_sym : forall {dim} (l1 l2 : bench_ucom_l dim), l1 =l= l2 -> l2 =l= l1.
Proof. easy. Qed.
 
Lemma uc_equiv_l'_trans : forall {dim} (l1 l2 l3 : bench_ucom_l dim), 
  l1 =l= l2 -> l2 =l= l3 -> l1 =l= l3.
Proof. intros dim l1 l2 l3 H12 H23. unfold uc_equiv_l' in *. rewrite H12. easy. Qed.

Lemma uc_app_congruence' : forall {dim} (l1 l1' l2 l2' : bench_ucom_l dim),
  l1 =l= l1' ->
  l2 =l= l2' ->
  l1 ++ l2 =l= l1' ++ l2'.
Proof.
  intros dim l1 l1' l2 l2' Hl1 Hl2.
  unfold uc_equiv_l', uc_equiv_l, uc_equiv.
  repeat rewrite to_PI4_list_append, PI4_to_base_ucom_l_app, list_to_ucom_append. 
  simpl.
  rewrite Hl1, Hl2.
  reflexivity.
Qed.

Lemma uc_cons_congruence' : forall {dim} (g : gate_app benchmark_Unitary dim)  (l l' : bench_ucom_l dim),
  l =l= l' ->
  g :: l =l= g :: l'.
Proof.
  intros dim g l l' Hl.
  unfold uc_equiv_l', uc_equiv_l, uc_equiv.
  Local Opaque CCZ CCX00 CCX01 CCX10 CCX11.
  destruct g; dependent destruction b; simpl.
  all: try (rewrite Hl; reflexivity).
  2: destruct b; destruct b1.
  all: repeat rewrite PI4_to_base_ucom_l_app, list_to_ucom_append; simpl.
  all: rewrite Hl; reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (bench_ucom_l dim) (@uc_equiv_l' dim)
  reflexivity proved by uc_equiv_l'_refl
  symmetry proved by uc_equiv_l'_sym
  transitivity proved by uc_equiv_l'_trans
  as uc_equiv_l'_rel.

Add Parametric Morphism (dim : nat) : (@app (gate_app benchmark_Unitary dim))
  with signature (@uc_equiv_l' dim) ==> (@uc_equiv_l' dim) ==> (@uc_equiv_l' dim) as uc_app_mor'.
Proof. intros x y H x0 y0 H0. apply uc_app_congruence'; easy. Qed.

Add Parametric Morphism (dim : nat) : (@List.cons (gate_app benchmark_Unitary dim))
  with signature eq ==> (@uc_equiv_l' dim) ==> (@uc_equiv_l' dim) as uc_cons_mor'.
Proof. intros y x0 y0 H0. apply uc_cons_congruence'; easy. Qed.

(* Preprocessing - convert H ; CCZ ; H to CCX *)
Fixpoint CCZ_to_CCX' {dim} (l : bench_ucom_l dim) n :=
  match n with
  | O => l
  | S n' =>
    match l with
    | [] => []
    | (App1 UB_H q as h) :: t =>
        match next_gate t [q] with
        | Some (l1, App3 UB_CCZ a b c, l2) => 
            if q =? c 
            then match next_single_qubit_gate l2 q with
                 | Some (l2_1, UB_H, l2_2) => 
                     CCZ_to_CCX' (l1 ++ [App3 (UB_CCX true true) a b c] ++ l2_1 ++ l2_2) n'
                 | _ => h :: (CCZ_to_CCX' t n')
                 end
            else h :: (CCZ_to_CCX' t n')
        | _ => h :: (CCZ_to_CCX' t n')
        end
    | h :: t => h :: (CCZ_to_CCX' t n')
    end
  end.
Definition CCZ_to_CCX {dim} (l : bench_ucom_l dim) := CCZ_to_CCX' l (List.length l).

Lemma does_not_reference_commutes_app1 : forall {dim} (l : bench_ucom_l dim) u q,
  does_not_reference l q = true ->
  [App1 u q] ++ l =l= l ++ [App1 u q]. 
Proof.
  intros.
  unfold uc_equiv_l'.
  dependent destruction u.
  all: repeat rewrite to_PI4_list_append.
  all: apply does_not_reference_commutes_app1.
  all: apply to_PI4_list_dnr; assumption.
Qed.

Lemma CCZ_to_CCX_preserves_semantics : forall {dim} (l : bench_ucom_l dim),
  CCZ_to_CCX l =l= l.
Proof.
  intros dim l.
  assert (forall n, CCZ_to_CCX' l n =l= l).
  { intros n.
    generalize dependent l.
    induction n; try reflexivity.
    intros l.
    destruct l; try reflexivity.
    destruct g; dependent destruction b; simpl.
    all: try (rewrite IHn; reflexivity).
    destruct (next_gate l [n0]) eqn:ng.
    repeat destruct p.
    destruct g1.
    Local Opaque CCX00 CCX01 CCX10 CCX11 CCZ.
    all: try (rewrite IHn; reflexivity).
    dependent destruction b.
    bdestruct (n0 =? n3); subst.
    destruct (next_single_qubit_gate g n3) eqn:nsqg.
    repeat destruct p.
    dependent destruction b.
    all: try (rewrite IHn; reflexivity).
    assert (In n3 [n3]) by (constructor; reflexivity).
    specialize (next_gate_l1_does_not_reference _ _ _ _ _ ng n3 H) as dnrg0.
    apply next_gate_preserves_structure in ng.
    specialize (nsqg_l1_does_not_reference _ _ _ _ _ nsqg) as dnrg2.
    apply nsqg_preserves_structure in nsqg.
    subst.
    rewrite (cons_to_app (App3 (UB_CCX true true) n1 n2 n3)).
    rewrite (cons_to_app (App1 UB_H n3)).
    apply does_not_reference_commutes_app1 with (u:=UB_H) in dnrg0.
    apply does_not_reference_commutes_app1 with (u:=UB_H) in dnrg2.
    repeat rewrite app_assoc.   
    rewrite dnrg0. 
    rewrite <- 2 (app_assoc _ g2).
    rewrite <- dnrg2.
    rewrite IHn.
    rewrite (app_assoc _ g2).
    apply uc_app_congruence'; try reflexivity.
    repeat rewrite app_assoc.
    apply uc_app_congruence'; try reflexivity.
    repeat rewrite <- app_assoc.
    apply uc_app_congruence'; reflexivity. }
  apply H.
Qed.

Lemma CCZ_to_CCX_well_typed : forall {dim} (l : bench_ucom_l dim),
  uc_well_typed_l l ->
  uc_well_typed_l (CCZ_to_CCX l).
Proof.
  intros dim l WT.
  specialize (CCZ_to_CCX_preserves_semantics l) as H.
  symmetry in H.
  apply uc_equiv_l_implies_WT in H.
  apply to_PI4_list_WT; assumption.
  apply to_PI4_list_WT; assumption.
Qed.

(***********************************)
(** Optimization: not propagation **)
(***********************************)

(* Propagate an X gate on qubit q as far right as possible, cancelling the
   gate if possible. The propagation rules used are the following:
     - X b ; CNOT a b ≡ CNOT a b ; X b
     - X a ; CCX [b1 b2] a b c ≡ CCX [(¬ b1) b2] a b c ; X a
     - X b ; CCX [b1 b2] a b c ≡ CCX [b1 (¬ b2)] a b c ; X b
     - X c ; CCX [b1 b2] a b c ≡ CCX [b1 b2] a b c ; X c
   
   This function returns None if no cancellation is possible or (Some l') 
   where l' is the result of removing the appropriate X gate from l. *)
Fixpoint propagate_X {dim} (l : bench_ucom_l dim) q n : option (bench_ucom_l dim) :=
  match n with 
  | O => None
  | S n' =>
    match next_gate l [q] with
    (* Cancel with X *)
    | Some (l1, App1 UB_X a, l2) => Some (l1 ++ l2)
    (* Propagate through CNOT *)
    | Some (l1, App2 UB_CNOT a b, l2) => 
        if q =? a then None
        else match propagate_X l2 q n' with
             | Some l2' => Some (l1 ++ [App2 UB_CNOT a b] ++ l2')
             | _ => None
             end
    (* Propagate through Toffoli *)
    | Some (l1, App3 (UB_CCX b1 b2) a b c, l2) =>
        let b1' := if q =? a then negb b1 else b1 in
        let b2' := if q =? b then negb b2 else b2 in
        match propagate_X l2 q n' with
        | Some l2' => Some (l1 ++ [App3 (UB_CCX b1' b2') a b c] ++ l2')
        | _ => None
        end
    | _ => None
    end
  end.

(* Call propagate_X on all X gates in the circuit. 
   
   The extra n argument is to help Coq recognize termination. We start
   with n = (length l), which is the maximum number of times that propagate_nots 
   needs to be called. *)
Fixpoint not_propagation' {dim} (l : bench_ucom_l dim) n :=
  match n with
  | O => l
  | S n' => 
      match l with
      | [] => [] 
      | App1 UB_X a :: t =>
          match (propagate_X t a n') with
          | Some l' => not_propagation' l' n'
          | None => App1 UB_X a :: (not_propagation' t n')
          end
      | h  :: t => h :: (not_propagation' t n')
      end
  end.

Definition not_propagation {dim} (l : bench_ucom_l dim) := 
  not_propagation' (CCZ_to_CCX l) (List.length l).

(* Small test cases. *)
Definition test1 : bench_ucom_l 3 := App1 UB_X 0 :: App1 UB_H 1 :: App1 UB_X 0 :: App1 UB_X 1 :: App2 UB_CNOT 2 1 :: App1 UB_X 1 :: [].
Compute (not_propagation test1).
Definition test2 : bench_ucom_l 3 := App1 UB_X 0 :: App1 UB_X 1 :: App1 UB_H 0 :: App3 UB_CCZ 1 2 0 :: App1 UB_H 0 :: App1 UB_X 0 :: [].
Compute (not_propagation test2).
Definition test3 : bench_ucom_l 3 := App1 UB_X 0 :: App2 UB_CNOT 1 0 :: App1 UB_H 2 :: App3 UB_CCZ 1 0 2 :: App1 UB_H 2 :: App1 UB_X 0 :: [].
Compute (not_propagation test3).
Definition test4 : bench_ucom_l 9 := App1 UB_X 1 :: App1 UB_X 7 :: App1 UB_H 3 :: App1 UB_H 6 :: App3 UB_CCZ 1 8 6 :: App3 UB_CCZ 1 7 3 :: App1 UB_H 6 :: App1 UB_H 3 :: App1 UB_X 1 :: App2 UB_CNOT 6 4 :: App2 UB_CNOT 5 8 :: App1 UB_H 5 :: App1 UB_H 8 :: App3 UB_CCZ 1 7 5 :: App3 UB_CCZ 0 2 8 :: App1 UB_H 8 :: App1 UB_H 5 :: App1 UB_X 0 :: App1 UB_X 7 :: []. 
Compute (not_propagation test4).

Lemma X_X_cancel : forall {dim} q,
  q < dim -> [@App1 _ dim UB_X q] ++ [App1 UB_X q] =l= [].
Proof.
  intros dim q Hq.
  unfold uc_equiv_l', uc_equiv_l, uc_equiv.
  simpl.
  rewrite pauli_x_rotation.
  autorewrite with eval_db; try lia.
  gridify; Qsimpl.
  reflexivity.
Qed.

Lemma X_CNOT_commute : forall {dim} q1 q2,
  [@App1 _ dim UB_X q2] ++ [App2 UB_CNOT q1 q2] =l= [App2 UB_CNOT q1 q2] ++ [App1 UB_X q2].
Proof.
  intros dim q1 q2.
  unfold uc_equiv_l', uc_equiv_l; simpl.
  replace (uapp1 (U_R PI 0 PI) q2) with (@SQIR.X dim q2) by reflexivity.
  replace (uapp2 U_CNOT q1 q2) with (@SQIR.CNOT dim q1 q2) by reflexivity.
  rewrite 2 SKIP_id_r.
  apply X_CNOT_comm.
Qed.

(* probably want separate proofs for CCX00, CCX01, and CCX11. *)
Lemma X_TOFF_commute : forall {dim} q q1 q2 q3 b1 b2,
  [@App1 _ dim UB_X q] ++ [App3 (UB_CCX b1 b2) q1 q2 q3] =l= [App3 (UB_CCX (if q =? q1 then ¬ b1 else b1) (if q =? q2 then ¬ b2 else b2)) q1 q2 q3] ++ [App1 UB_X q].
Proof.
Admitted.

Lemma propagate_X_preserves_semantics : forall {dim} (l l' : bench_ucom_l dim) q n,
  q < dim ->
  propagate_X l q n = Some l' ->
  l' =l= (App1 UB_X q) :: l.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction n; intros l l' res; try discriminate.
  simpl in res.
  destruct (next_gate l [q]) eqn:ng; try discriminate.
  repeat destruct p.
  destruct g1.
  - dependent destruction b; try discriminate.
    inversion res; subst.
    assert (aux: List.In q [q]) by (constructor; reflexivity).
    specialize (next_gate_l1_does_not_reference _ _ _ _ _ ng _ aux) as dnr.
    specialize (next_gate_app1_returns_q _ _ _ _ _ _ ng) as Hq.
    inversion Hq; try easy.
    apply next_gate_preserves_structure in ng.
    subst.
    rewrite cons_to_app.
    rewrite (app_assoc g0).
    apply does_not_reference_commutes_app1 with (u:=UB_X) in dnr.
    rewrite <- dnr.
    repeat rewrite app_assoc.
    rewrite X_X_cancel; try assumption.
    reflexivity.
  - dependent destruction b.
    bdestruct (q =? n0); try discriminate.
    destruct (propagate_X g q n) eqn:prop; try discriminate.
    inversion res; subst.
    assert (aux: List.In q [q]) by (constructor; reflexivity).
    specialize (next_gate_l1_does_not_reference _ _ _ _ _ ng _ aux) as dnr.
    specialize (next_gate_app2_returns_q _ _ _ _ _ _ _ ng) as [Hq | Hq].
    inversion Hq; try easy.
    inversion Hq; try easy.
    apply next_gate_preserves_structure in ng.
    subst.
    apply IHn in prop.
    rewrite prop.
    rewrite cons_to_app.
    rewrite (cons_to_app (App1 UB_X n1)).
    rewrite app_comm_cons.
    rewrite (cons_to_app (App1 UB_X n1) g0).
    apply does_not_reference_commutes_app1 with (u:=UB_X) in dnr.
    rewrite dnr.
    rewrite <- app_assoc.
    rewrite (app_assoc [App1 UB_X n1]).
    rewrite X_CNOT_commute.
    reflexivity.
  - dependent destruction b; try discriminate.
    destruct (propagate_X g q n) eqn:prop; try discriminate.
    inversion res; subst.
    assert (aux: List.In q [q]) by (constructor; reflexivity).
    specialize (next_gate_l1_does_not_reference _ _ _ _ _ ng _ aux) as dnr.
    apply next_gate_preserves_structure in ng.
    subst.
    apply IHn in prop.
    rewrite prop.
    rewrite cons_to_app.
    rewrite (cons_to_app (App1 UB_X q)).
    rewrite app_comm_cons.
    rewrite (cons_to_app (App1 UB_X q) g0).
    apply does_not_reference_commutes_app1 with (u:=UB_X) in dnr.
    rewrite dnr.
    rewrite <- app_assoc.
    rewrite (app_assoc [App1 UB_X q]).
    rewrite X_TOFF_commute.
    reflexivity.
Qed.

Lemma propagate_X_well_typed : forall {dim} (l l' : bench_ucom_l dim) q n,
  q < dim ->
  uc_well_typed_l l ->
  propagate_X l q n = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros dim l l' q n Hq WT H.
  apply propagate_X_preserves_semantics in H; try assumption.
  assert (uc_well_typed_l (App1 UB_X q :: l)).
  constructor; assumption.
  symmetry in H.  
  apply uc_equiv_l_implies_WT in H.
  apply to_PI4_list_WT; assumption.
  apply to_PI4_list_WT; assumption.
Qed.

(* propagate_nots is semantics-preserving. *)
Lemma not_propagation_sound : forall {dim} (l : bench_ucom_l dim), 
  uc_well_typed_l l -> not_propagation l =l= l.
Proof.
  intros dim l WT.
  assert (forall n (l : bench_ucom_l dim), 
          uc_well_typed_l l -> not_propagation' l n =l= l). 
  { clear l WT. 
    intro n.
    induction n; intros l WT; try reflexivity.
    destruct l; try reflexivity.
    destruct g; inversion WT; subst; simpl.
    dependent destruction b.
    2: destruct (propagate_X l n0 n) eqn:prop.
    all: try (rewrite IHn; easy).
    rewrite IHn.
    eapply propagate_X_preserves_semantics; try apply prop; assumption.
    eapply propagate_X_well_typed; try apply prop; assumption. }
  unfold not_propagation.
  rewrite H.
  apply CCZ_to_CCX_preserves_semantics.
  apply CCZ_to_CCX_well_typed. assumption.
Qed.