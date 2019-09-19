Require Import core.UnitarySem.
Require Import Equivalences.
Require Export ListRepresentation.
Require Import Setoid.

(** PI4 Gate Set **)

(* In our optimizations, we often use the gate set {H, X, PI4, CNOT} where
   PI4 is rotation about the z-axis by k * PI / 4 for integer k. We'll 
   call this the PI4 gate set. *)

Inductive PI4_Unitary : nat -> Set := 
  | UPI4_H                  : PI4_Unitary 1 
  | UPI4_X                  : PI4_Unitary 1
  | UPI4_PI4 (k : BinInt.Z) : PI4_Unitary 1
  | UPI4_CNOT               : PI4_Unitary 2.

(* We may want to consider adding Toffoli gates to the set. The semantics
   of the Toffoli gate is shown below. 

Definition TOFF (a b c : nat) :=
  H c :: CNOT b c :: TDAG c :: CNOT a c :: 
  T c :: CNOT b c :: TDAG c :: CNOT a c :: 
  CNOT a b :: TDAG b :: CNOT a b :: 
  T a :: T b :: T c :: H c :: []. 
*)

(* Useful shorthands. *)
Local Open Scope Z_scope.
Definition UPI4_ID := UPI4_PI4 0.
Definition UPI4_T := UPI4_PI4 1.
Definition UPI4_P := UPI4_PI4 2.
Definition UPI4_Z := UPI4_PI4 4.
Definition UPI4_PDAG := UPI4_PI4 6.
Definition UPI4_TDAG := UPI4_PI4 7.
Definition T {dim} q : gate_app PI4_Unitary dim := App1 UPI4_T q.
Definition TDAG {dim} q : gate_app PI4_Unitary dim := App1 UPI4_TDAG q.
Definition P {dim} q : gate_app PI4_Unitary dim := App1 UPI4_P q.
Definition PDAG {dim} q : gate_app PI4_Unitary dim := App1 UPI4_PDAG q.
Definition Z {dim} q : gate_app PI4_Unitary dim := App1 UPI4_Z q.
Definition H {dim} q : gate_app PI4_Unitary dim := App1 UPI4_H q.
Definition X {dim} q : gate_app PI4_Unitary dim := App1 UPI4_X q.
Definition CNOT {dim} q1 q2 : gate_app PI4_Unitary dim := App2 UPI4_CNOT q1 q2.

(* Conversion to the base gate set. *)
Local Open Scope ucom.
Fixpoint PI4_to_base {dim} (c : ucom PI4_Unitary dim) : base_ucom dim :=
  match c with
  | c1 ; c2 => PI4_to_base c1 ; PI4_to_base c2
  | uapp1 UPI4_H n => SQIRE.H n
  | uapp1 UPI4_X n => SQIRE.X n
  | uapp1 (UPI4_PI4 k) n => SQIRE.Rz (IZR k * PI / 4)%R n
  | uapp2 UPI4_CNOT m n => SQIRE.CNOT m n
  | _ => SKIP (* unreachable case *)
  end.

Fixpoint PI4_to_base_l {dim} (l : gate_list PI4_Unitary dim) : base_list dim :=
  match l with
  | [] => []
  | (App1 UPI4_H n) :: t => (App1 (U_R (PI/2) 0 PI) n) :: (PI4_to_base_l t)
  | (App1 UPI4_X n) :: t => (App1 (U_R PI 0 PI) n) :: (PI4_to_base_l t)
  | (App1 (UPI4_PI4 k) n) :: t => (App1 (U_R 0 0 (IZR k * PI / 4)%R) n) :: (PI4_to_base_l t)
  | (App2 UPI4_CNOT m n) :: t => (App2 U_CNOT m n) :: (PI4_to_base_l t)
  | _ => [] (* unreachable case *)
  end.

Lemma PI4_to_base_l_app : forall {dim} (l1 l2 : gate_list PI4_Unitary dim),
  PI4_to_base_l (l1 ++ l2) = (PI4_to_base_l l1) ++ (PI4_to_base_l l2).
Proof.
  intros.
  induction l1.
  - reflexivity.
  - simpl; destruct a; dependent destruction p;
    rewrite IHl1; reflexivity.
Qed.    

Lemma PI4_to_base_l_WT : forall {dim} (l : gate_list PI4_Unitary dim), 
  uc_well_typed_l l <-> uc_well_typed_l (PI4_to_base_l l).
Proof.
  intros.
  induction l; simpl.
  - split; intros H; inversion H; constructor; assumption.
  - destruct a; dependent destruction p;
    split; intros H;
    inversion H; subst;
    constructor; try apply IHl; assumption.
Qed.

(** Equivalence **)
(* TODO: We should make general version of the definitions in this section
   (that apply to any gate set), and move them back to ListRepresentation. *)

Definition PI4_list dim := gate_list PI4_Unitary dim.

Definition uc_equiv_l {dim} (l1 l2 : PI4_list dim) := 
  (list_to_ucom (PI4_to_base_l l1)) ≡ (list_to_ucom (PI4_to_base_l l2)).
Infix "=l=" := uc_equiv_l (at level 70).

Lemma uc_equiv_l_refl : forall {dim} (l1 : PI4_list dim), l1 =l= l1.
Proof. easy. Qed.
 
Lemma uc_equiv_l_sym : forall {dim} (l1 l2 : PI4_list dim), l1 =l= l2 -> l2 =l= l1.
Proof. easy. Qed.
 
Lemma uc_equiv_l_trans : forall {dim} (l1 l2 l3 : PI4_list dim), 
  l1 =l= l2 -> l2 =l= l3 -> l1 =l= l3.
Proof. intros dim l1 l2 l3 H12 H23. unfold uc_equiv_l in *. rewrite H12. easy. Qed.

Lemma uc_eval_l_app : forall {dim} (l1 l2 : PI4_list dim),
  uc_eval (list_to_ucom (PI4_to_base_l (l1 ++ l2))) = uc_eval (list_to_ucom (PI4_to_base_l l2)) × uc_eval (list_to_ucom (PI4_to_base_l l1)).
Proof.
  intros.
  rewrite PI4_to_base_l_app.
  rewrite list_to_ucom_append; simpl.
  reflexivity.
Qed.

Lemma cons_congruence : forall {dim} (g : gate_app PI4_Unitary dim)  (l l' : PI4_list dim),
  l =l= l' ->
  g :: l =l= g :: l'.
Proof.
  intros dim g l l' Hl.
  unfold uc_equiv_l, uc_equiv.
  simpl.
  destruct g; dependent destruction p;  
  simpl; rewrite Hl; reflexivity.
Qed.

Lemma app_congruence : forall {dim} (l1 l1' l2 l2' : PI4_list dim),
  l1 =l= l1' ->
  l2 =l= l2' ->
  l1 ++ l2 =l= l1' ++ l2'.
Proof.
  intros dim l1 l1' l2 l2' Hl1 Hl2.
  unfold uc_equiv_l, uc_equiv.
  repeat rewrite uc_eval_l_app.
  rewrite Hl1, Hl2.
  reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (PI4_list dim) (@uc_equiv_l dim)
  reflexivity proved by uc_equiv_l_refl
  symmetry proved by uc_equiv_l_sym
  transitivity proved by uc_equiv_l_trans
  as uc_equiv_l_rel.

Add Parametric Morphism (dim : nat) : (@List.cons (gate_app PI4_Unitary dim))
  with signature eq ==> (@uc_equiv_l dim) ==> (@uc_equiv_l dim) as cons_mor.
Proof. intros y x0 y0 H0. apply cons_congruence; easy. Qed.

Add Parametric Morphism (dim : nat) : (@app (gate_app PI4_Unitary dim))
  with signature (@uc_equiv_l dim) ==> (@uc_equiv_l dim) ==> (@uc_equiv_l dim) as app_mor.
Proof. intros x y H x0 y0 H0. apply app_congruence; easy. Qed.

(** Useful relationship between equivalence and well-typedness **)

Lemma uc_equiv_l_implies_WT : forall {dim} (l l' : PI4_list dim),
  l =l= l' ->
  uc_well_typed_l l ->
  uc_well_typed_l l'.
Proof.
  intros dim l l' H WT.
  apply PI4_to_base_l_WT.
  apply list_to_ucom_WT. 
  apply uc_eval_nonzero_iff.
  apply PI4_to_base_l_WT in WT.
  apply list_to_ucom_WT in WT.
  apply uc_eval_nonzero_iff in WT.
  rewrite <- H; assumption.
Qed.
  
(** Equivalence up to a phase. **)

Definition uc_cong_l {dim} (l1 l2 : PI4_list dim) := 
  (list_to_ucom (PI4_to_base_l l1)) ≅ (list_to_ucom (PI4_to_base_l l2)).
Infix "≅l≅" := uc_cong_l (at level 20).

Lemma uc_cong_l_refl : forall {dim : nat} (l1 : PI4_list dim), l1 ≅l≅ l1.
Proof. intros. exists 0%R. rewrite Cexp_0. rewrite Mscale_1_l. reflexivity. Qed.

Lemma uc_cong_l_sym : forall {dim : nat} (l1 l2 : PI4_list dim), l1 ≅l≅ l2 -> l2 ≅l≅ l1.
Proof. intros dim l1 l2 H. unfold uc_cong_l in *. rewrite H. reflexivity. Qed.

Lemma uc_cong_l_trans : forall {dim : nat} (l1 l2 l3 : PI4_list dim), l1 ≅l≅ l2 -> l2 ≅l≅ l3 -> l1 ≅l≅ l3.
Proof.
  intros dim l1 l2 l3 H1 H2.
  unfold uc_cong_l in *.
  eapply uc_cong_trans. apply H1. apply H2.
Qed.  

Lemma uc_cong_l_cons_congruence : forall {dim : nat} (g : gate_app PI4_Unitary dim) (l l' : PI4_list dim),
  l ≅l≅ l' -> (g :: l) ≅l≅ (g :: l').
Proof.
  intros dim g l l' H. unfold uc_cong_l in *.
  simpl.
  inversion H.
  destruct g; dependent destruction p;
  exists x; simpl; rewrite <- Mscale_mult_dist_l; rewrite H1; reflexivity.
Qed.

Lemma uc_cong_l_app_congruence : forall {dim : nat} (l l' m m': PI4_list dim),
  l ≅l≅ l' -> m ≅l≅ m' -> (m ++ l) ≅l≅ (m' ++ l').
Proof.
  intros dim l l' m m' H1 H2.
  unfold uc_cong_l in *.
  inversion H1. inversion H2.
  exists (x + x0)%R.
  repeat rewrite uc_eval_l_app.
  rewrite <- Mscale_mult_dist_l. rewrite H0. rewrite H3. 
  rewrite Mscale_mult_dist_r.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_assoc.
  rewrite <- Cexp_add.
  rewrite Rplus_comm.
  rewrite Mscale_mult_dist_l.
  reflexivity.
Qed.
    
Add Parametric Relation (dim : nat) : (PI4_list dim) (@uc_cong_l dim)
  reflexivity proved by uc_cong_l_refl
  symmetry proved by uc_cong_l_sym
  transitivity proved by uc_cong_l_trans
  as uc_cong_l_rel.

Add Parametric Morphism (dim : nat) : (@List.cons (gate_app PI4_Unitary dim))
  with signature eq ==> (@uc_cong_l dim) ==> (@uc_cong_l dim) as cons_mor_cong.
Proof. intros. apply uc_cong_l_cons_congruence. easy. Qed.

Add Parametric Morphism (dim : nat) : (@app (gate_app PI4_Unitary dim))
  with signature (@uc_cong_l dim) ==> (@uc_cong_l dim) ==> (@uc_cong_l dim) as app_mor_cong.
Proof. intros x y H x0 y0 H0. apply uc_cong_l_app_congruence; easy. Qed.

Lemma uc_equiv_cong_l : forall {dim : nat} (c c' : PI4_list dim), c =l= c' -> c ≅l≅ c'.
Proof.
  intros dim c c' H.
  exists 0%R. rewrite Cexp_0, Mscale_1_l. 
  apply H.
Qed.

Lemma uc_cong_l_implies_WT : forall {dim} (l l' : PI4_list dim),
  l ≅l≅ l' ->
  uc_well_typed_l l ->
  uc_well_typed_l l'.
Proof.
  intros dim l l' H WT.
  apply PI4_to_base_l_WT.
  apply list_to_ucom_WT. 
  apply uc_eval_nonzero_iff.
  apply PI4_to_base_l_WT in WT.
  apply list_to_ucom_WT in WT.
  apply uc_eval_nonzero_iff in WT.
  destruct H.
  rewrite H0 in WT. 
  intros contra.
  rewrite contra in WT.
  contradict WT.
  Msimpl.
  reflexivity.
Qed.

(* Commutativity lemmas for list representation. *)

Lemma does_not_reference_commutes_app1 : forall {dim} (l : PI4_list dim) u q,
  does_not_reference l q = true ->
  [App1 u q] ++ l =l= l ++ [App1 u q]. 
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl in *.
    destruct a; dependent destruction p;
    apply andb_prop in H0 as [H1 H2];
    repeat match goal with 
    | H : does_not_reference_appl _ _ = true |- _ => apply negb_true_iff in H
    end;
    repeat match goal with 
    | H : (_ || _) = false |- _ => apply orb_false_elim in H as [? ?]
    end;
    repeat match goal with
    | H : (_ =? _)%nat = false |- _ => 
         apply beq_nat_false in H;
         apply not_eq_sym in H
    end;
    rewrite <- IHl; try assumption;
    unfold uc_equiv_l; simpl; dependent destruction u; simpl;
    rewrite <- 2 useq_assoc;
    try rewrite U_V_comm;
    try rewrite (U_CNOT_comm q n n0);
    try reflexivity;
    assumption.
Qed.

Lemma does_not_reference_commutes_app2 : forall {dim} (l : PI4_list dim) u m n,
  does_not_reference l m = true ->
  does_not_reference l n = true ->
  [App2 u m n] ++ l =l= l ++ [App2 u m n]. 
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl in *.
    destruct a; dependent destruction p;
    apply andb_prop in H0 as [? ?];
    apply andb_prop in H1 as [? ?];
    repeat match goal with 
    | H : does_not_reference_appl _ _ = true |- _ => apply negb_true_iff in H
    end;
    repeat match goal with 
    | H : (_ || _) = false |- _ => apply orb_false_elim in H as [? ?]
    end;
    repeat match goal with
    | H : (_ =? _)%nat = false |- _ => apply beq_nat_false in H    
    end;
    rewrite <- IHl; try assumption;
    unfold uc_equiv_l; simpl; dependent destruction u; simpl;
    rewrite <- 2 useq_assoc;
    try rewrite (U_CNOT_comm n0 m n);
    try rewrite (CNOT_CNOT_comm m n n0 n1);
    try reflexivity;
    assumption.
Qed.

Lemma nsqg_commutes : forall {dim} (l : PI4_list dim) q u l1 l2,
  next_single_qubit_gate l q = Some (l1, u, l2) -> 
  l =l= [App1 u q] ++ l1 ++ l2.
Proof.
  intros dim l q u l1 l2 H.
  specialize (nsqg_preserves_structure _ _ _ _ _ H) as H1.
  subst.
  apply nsqg_l1_does_not_reference in H.
  apply (does_not_reference_commutes_app1 _ u _) in H.
  repeat rewrite app_assoc.  
  rewrite H.
  reflexivity.
Qed.

Lemma lsqg_commutes : forall {dim} (l : PI4_list dim) q u l1 l2,
  last_single_qubit_gate l q = Some (l1, u, l2) -> 
  l =l= l1 ++ l2 ++ [App1 u q].
Proof.
  intros dim l q u l1 l2 H.
  specialize (lsqg_preserves_structure _ _ _ _ _ H) as H1.
  subst.
  apply lsqg_l2_does_not_reference in H.
  apply (does_not_reference_commutes_app1 _ u _) in H.
  rewrite H.
  reflexivity.
Qed.

(** Misc. Utilities **)

(* Boolean equality over gates. *)
Definition match_gate {n} (u u' : PI4_Unitary n) : bool :=
  match u, u' with
  | UPI4_H, UPI4_H | UPI4_X, UPI4_X | UPI4_CNOT, UPI4_CNOT => true
  | UPI4_PI4 k, UPI4_PI4 k' => Z.eqb k k'
  | _, _ => false
  end.

Lemma match_gate_refl : forall {n} (u u' : PI4_Unitary n), 
  match_gate u u' = true <-> u = u'. 
Proof.
  intros n u u'.
  split; intros H.
  - dependent destruction u; dependent destruction u';
    inversion H0; try reflexivity.
    apply Z.eqb_eq in H2. subst. reflexivity.    
  - subst. dependent destruction u'; trivial. 
    simpl. apply Z.eqb_refl.
Qed.

(* Check whether a program is well typed. *)
Definition PI4_list_well_typed_b dim (l : PI4_list dim) := uc_well_typed_l_b dim l.

(* Count the gates in (the list representation of) a program. *)
Fixpoint count_H_gates {dim} (l : PI4_list dim) :=
  let fix aux l acc :=
    match l with
    | [] => acc
    | (App1 UPI4_H _) :: t => aux t (acc + 1)
    | _ :: t => aux t acc
    end in
  aux l 0.

Fixpoint count_X_gates {dim} (l : PI4_list dim) :=
  let fix aux l acc :=
    match l with
    | [] => acc
    | (App1 UPI4_X _) :: t => aux t (acc + 1)
    | _ :: t => aux t acc
    end in
  aux l 0.

Fixpoint count_rotation_gates {dim} (l : PI4_list dim) :=
  let fix aux l acc :=
    match l with
    | [] => acc
    | (App1 (UPI4_PI4 _) _) :: t  => aux t (acc + 1)
    | _ :: t => aux t acc
    end in
  aux l 0.

Fixpoint count_CNOT_gates {dim} (l : PI4_list dim) :=
  let fix aux l acc :=
    match l with
    | [] => acc
    | (App2 UPI4_CNOT _ _) :: t => aux t (acc + 1)
    | _ :: t => aux t acc
    end in
  aux l 0.

