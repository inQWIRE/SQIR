Require Import UnitarySem.
Require Import PI4GateSet.
Require Import Equivalences.
Require Import Proportional.
Require Import List.

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

Definition uc_equiv_l' {dim} (l1 l2 : bench_ucom_l dim) := 
  uc_equiv_l (to_PI4_list l1) (to_PI4_list l2).
Local Infix "=l=" := uc_equiv_l' (at level 70).

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

Lemma CCZ_to_CCX_sound : forall {dim} (l : bench_ucom_l dim),
  CCZ_to_CCX l =l= l.
Proof.
  intros dim l.
  assert (forall n, CCZ_to_CCX' l n =l= l).
  { intros n.
    generalize dependent l.
    induction n; try reflexivity.
    intros l.
    simpl.
    destruct l; try reflexivity.
    destruct g.
    all: dependent destruction b.
    destruct (next_gate l [n0]) eqn:ng.
    repeat destruct p.
    destruct g1.
    Local Opaque CCX00 CCX01 CCX10 CCX11 CCZ.
    all: unfold uc_equiv_l' in *; simpl. 
    13: destruct b; destruct b1.
    all: try (rewrite IHn; reflexivity).
    dependent destruction b.
    bdestruct (n0 =? n3); subst.
    destruct (next_single_qubit_gate g n3) eqn:nsqg.
    repeat destruct p.
    dependent destruction b.
    all: try (simpl; rewrite IHn; reflexivity).
    assert (In n3 [n3]) by (constructor; reflexivity).
    specialize (next_gate_l1_does_not_reference _ _ _ _ _ ng n3 H) as dnrg0.
    apply next_gate_preserves_structure in ng.
    specialize (nsqg_l1_does_not_reference _ _ _ _ _ nsqg) as dnrg2.
    apply nsqg_preserves_structure in nsqg.
    subst.
    rewrite (cons_to_app (App3 (UB_CCX true true) n1 n2 n3)).
    rewrite (cons_to_app (PI4GateSet.H n3)).
    repeat rewrite to_PI4_list_append.
    apply to_PI4_list_dnr in dnrg0.
    apply to_PI4_list_dnr in dnrg2.
    apply does_not_reference_commutes_app1 with (u:=UPI4_H) in dnrg0.
    apply does_not_reference_commutes_app1 with (u:=UPI4_H) in dnrg2.
    repeat rewrite app_assoc.   
    rewrite dnrg0. 
    rewrite <- (app_assoc _ (to_PI4_list g2)).
    rewrite <- dnrg2.
    rewrite IHn.
    repeat rewrite to_PI4_list_append.
    apply uc_app_congruence; try reflexivity.
    repeat rewrite app_assoc.
    apply uc_app_congruence; try reflexivity.
    repeat rewrite <- app_assoc.
    apply uc_app_congruence; reflexivity. }
  apply H.
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
Fixpoint propagate_not {dim} (l : bench_ucom_l dim) q n : option (bench_ucom_l dim) :=
  match n with 
  | O => None
  | S n' =>
    match next_gate l [q] with
    (* Cancel with X *)
    | Some (l1, App1 UB_X a, l2) => Some (l1 ++ l2)
    (* Propagate through CNOT *)
    | Some (l1, App2 UB_CNOT a b, l2) => 
        if q =? a then None
        else match propagate_not l2 q n' with
             | Some l2' => Some (l1 ++ [App2 UB_CNOT a b] ++ l2')
             | _ => None
             end
    (* Propagate through Toffoli *)
    | Some (l1, App3 (UB_CCX b1 b2) a b c, l2) =>
        let b1' := if q =? a then negb b1 else b1 in
        let b2' := if q =? b then negb b2 else b2 in
        match propagate_not l2 q n' with
        | Some l2' => Some (l1 ++ [App3 (UB_CCX b1' b2') a b c] ++ l2')
        | _ => None
        end
    | _ => None
    end
  end.

(* Call propagate_not on all X gates in the circuit. 
   
   The extra n argument is to help Coq recognize termination. We start
   with n = (length l), which is the maximum number of times that propagate_nots 
   needs to be called. *)
Fixpoint propagate_nots {dim} (l : bench_ucom_l dim) n :=
  match n with
  | O => l
  | S n' => 
      match l with
      | [] => [] 
      | App1 UB_X a :: t =>
          match (propagate_not t a n') with
          | Some l' => propagate_nots l' n'
          | None => App1 UB_X a :: (propagate_nots t n')
          end
      | h  :: t => h :: (propagate_nots t n')
      end
  end.

Definition rm_nots {dim} (l : bench_ucom_l dim) := 
  propagate_nots (CCZ_to_CCX l) (List.length l).

(* Small test cases. *)
Definition test1 : bench_ucom_l 3 := App1 UB_X 0 :: App1 UB_H 1 :: App1 UB_X 0 :: App1 UB_X 1 :: App2 UB_CNOT 2 1 :: App1 UB_X 1 :: [].
Compute (rm_nots test1).
Definition test2 : bench_ucom_l 3 := App1 UB_X 0 :: App1 UB_X 1 :: App1 UB_H 0 :: App3 UB_CCZ 1 2 0 :: App1 UB_H 0 :: App1 UB_X 0 :: [].
Compute (rm_nots test2).
Definition test3 : bench_ucom_l 3 := App1 UB_X 0 :: App2 UB_CNOT 1 0 :: App1 UB_H 2 :: App3 UB_CCZ 1 0 2 :: App1 UB_H 2 :: App1 UB_X 0 :: [].
Compute (rm_nots test3).
Definition test4 : bench_ucom_l 9 := App1 UB_X 1 :: App1 UB_X 7 :: App1 UB_H 3 :: App1 UB_H 6 :: App3 UB_CCZ 1 8 6 :: App3 UB_CCZ 1 7 3 :: App1 UB_H 6 :: App1 UB_H 3 :: App1 UB_X 1 :: App2 UB_CNOT 6 4 :: App2 UB_CNOT 5 8 :: App1 UB_H 5 :: App1 UB_H 8 :: App3 UB_CCZ 1 7 5 :: App3 UB_CCZ 0 2 8 :: App1 UB_H 8 :: App1 UB_H 5 :: App1 UB_X 0 :: App1 UB_X 7 :: []. 
Compute (rm_nots test4).
(*
(* propagate_not preserves well-typedness. *)
Lemma propagate_not_WT : forall {dim} (l l' : bench_ucom_l dim) q n,
  uc_well_typed_l l ->
  propagate_not l q n = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction n; intros l WT l' res; try discriminate.
  simpl in res.
  destruct (next_gate l [q]) eqn:ng; try discriminate.
  repeat destruct p.
  destruct g1.
  - dependent destruction b; try discriminate.
    (* next gate is H - try Toffoli propagation *)
    admit.
    (* next gate is X - cancel *)
    inversion res; subst.
    apply uc_well_typed_l_app.
    admit.
  - dependent destruction b.
    (* next gate is CNOT - try CNOT propagation *)
    bdestruct (q =? n0); try discriminate.
    destruct (propagate_not g q n) eqn:rec; try discriminate.
    inversion res; subst.
    admit.
  - dependent destruction b.
    (* next gate is CCZ - try Toffoli propagation *)
    admit.
Admitted.

(* propagate_not is semantics-preserving. *)
Lemma propagate_not_sound : forall {dim} (l l' : bench_ucom_l dim) q n,
  q < dim ->
  propagate_not l q n = Some l' ->
  l' =l= (App1 UB_X q) :: l.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction n; intros l l' res; try discriminate.
  simpl in res.
  destruct (next_gate l [q]) eqn:ng1; try discriminate.
  repeat destruct p.
  destruct g1.
  - dependent destruction b; try discriminate.
    (* next gate is H - try Toffoli propagation *)
    destruct (next_gate g [q]) eqn:ng2; try discriminate.
    repeat destruct p.
    destruct g3; try discriminate.
    dependent destruction b.
    bdestruct (q =? n3); subst; try discriminate.
    destruct (next_single_qubit_gate g1 n3) eqn:nsqg; try discriminate.
    repeat destruct p.
    dependent destruction b0; try discriminate.
    destruct (propagate_not g3 n3 n) eqn:rec; try discriminate.
    inversion res; subst; clear res.
    apply next_gate_preserves_structure in ng1.
    apply next_gate_preserves_structure in ng2.
    apply nsqg_preserves_structure in nsqg.
    subst.
    apply IHn in rec.
Admitted.*)
(*
    admit.
    (* next gate is X - cancel *)
    inversion res; subst.
    apply uc_well_typed_l_app.
    admit.
  - dependent destruction b.
    (* next gate is CNOT - try CNOT propagation *)
    bdestruct (q =? n0); try discriminate.
    destruct (propagate_not g q n) eqn:rec; try discriminate.
    inversion res; subst.
    admit.
  - dependent destruction b.
    (* next gate is CCZ - try Toffoli propagation *)
    admit.
Admitted.



  induction l; try easy.
  simpl; intros.   
  destruct a.
  dependent destruction p;
  (* u = H, Z, T, TDAG, P, PDAG *)
  try (bdestruct (q =? n); try discriminate;
       destruct (propagate_not l q); try discriminate;
       inversion H0; subst;
       rewrite IHl with (l':=p); trivial;
       unfold uc_equiv_l; simpl;
       repeat rewrite <- useq_assoc;
       rewrite U_V_comm; try reflexivity;
       apply not_eq_sym; assumption).
  - (* u = X *)
    bdestruct (q =? n).
    + inversion H0; subst.
      unfold uc_equiv_l; simpl.
      rewrite <- useq_assoc.
      specialize (@X_X_id dim n) as XX.
      unfold uc_equiv in *; simpl in *.
      rewrite denote_X, denote_ID in XX.
      rewrite pauli_x_rotation.
      rewrite XX.
      unfold pad.
      bdestructΩ (n + 1 <=? dim).
      repeat rewrite id_kron.
      Msimpl_light; reflexivity.
    + destruct (propagate_not l q); inversion H0; subst.
      rewrite IHl with (l':=p); trivial.
      unfold uc_equiv_l; simpl.
      repeat rewrite <- useq_assoc.
      rewrite U_V_comm; try reflexivity.
      apply not_eq_sym; assumption.
  - (* u = CNOT *)
    dependent destruction p.
    bdestruct (q =? n); try discriminate.
    destruct (propagate_not l q); inversion H0; subst.
    rewrite IHl with (l':=p); trivial.
    bdestruct (q =? n0).
    + subst. 
      unfold uc_equiv_l; simpl.
      repeat rewrite <- useq_assoc.
      specialize (@X_CNOT_comm dim n n0) as X_CNOT.
      unfold uc_equiv in *; simpl in *.
      rewrite denote_X, denote_cnot in X_CNOT.
      rewrite pauli_x_rotation.
      rewrite X_CNOT.
      reflexivity.
    + unfold uc_equiv_l; simpl.
      repeat rewrite <- useq_assoc.
      rewrite (U_CNOT_comm q n n0); try assumption.
      reflexivity.
  - inversion p.
Qed.   

(* propagate_nots is semantics-preserving. *)
Lemma propagate_nots_sound : forall {dim} (l : PI4_ucom_l dim) n, 
  uc_well_typed_l l -> l =l= propagate_nots l n.
Proof.
  intros.
  generalize dependent l.
  induction n; try easy.
  intros l WT.
  destruct l; try easy.
  destruct g.
  inversion WT; subst.
  simpl.
  dependent destruction p;
  (* u = H, Z, T, TDAG, P, PDAG *)
  try (apply (uc_cons_congruence _ l (propagate_nots l n));
       apply IHn; assumption).
  (* u = X *)
  - specialize (@propagate_not_sound dim) as H4.
    destruct (propagate_not l n0) eqn:prop.
    + specialize (H4 l p n0 H1 prop).
      rewrite <- H4.
      apply IHn.
      apply (propagate_not_WT l p n0); assumption.
    + apply (uc_cons_congruence _ l (propagate_nots l n));
      apply IHn; assumption.
  (* u = CNOT *)
  - inversion WT; subst. 
    apply (uc_cons_congruence _ l (propagate_nots l n)).
    apply IHn; assumption.
  - inversion p.
Qed.

(* rm_nots is semantics-preserving. 
   
   The well-typedness constraint is required because rm_nots can actually
   return a well-typed circuit given a circuit that is not well-typed.
     ==> Consider the program X 4; X 4 where dim = 3
   The output of the denotation function may change in this case. 
*)
Lemma rm_nots_sound : forall {dim} (l : PI4_ucom_l dim), 
  uc_well_typed_l l -> l =l= rm_nots l.
Proof.
  intros dim l WT.
  unfold rm_nots.
  rewrite <- propagate_nots_sound.
  reflexivity.
  assumption.
Qed.
*)