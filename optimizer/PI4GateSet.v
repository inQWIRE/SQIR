Require Import core.UnitarySem.
Require Import Equivalences.
Require Export ListRepresentation.
Require Import core.DensitySem.
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

Definition PI4_ucom dim := ucom PI4_Unitary dim.
Definition PI4_ucom_l dim := gate_list PI4_Unitary dim.
Definition PI4_com dim := com PI4_Unitary dim.
Definition PI4_com_l dim := com_list PI4_Unitary dim.

(* Used to convert benchmarks to PI4 set. *)
Definition CCX {dim} a b c : PI4_ucom_l dim :=
  H c :: CNOT b c :: TDAG c :: CNOT a c :: 
  T c :: CNOT b c :: TDAG c :: CNOT a c :: 
  CNOT a b :: TDAG b :: CNOT a b :: 
  T a :: T b :: T c :: H c :: []. 
Definition CCZ {dim} a b c : PI4_ucom_l dim :=
  CNOT b c :: TDAG c :: CNOT a c :: 
  T c :: CNOT b c :: TDAG c :: CNOT a c :: 
  CNOT a b :: TDAG b :: CNOT a b :: 
  T a :: T b :: T c :: []. 

(* Conversion to the base gate set. *)
Definition PI4_to_base {n} (u : PI4_Unitary n) : base_Unitary n :=
  match u with
  | UPI4_H     => U_R (PI/2) 0 PI
  | UPI4_X     => U_R PI 0 PI
  | UPI4_PI4 k => U_R 0 0 (IZR k * PI / 4)%R
  | UPI4_CNOT  => U_CNOT
  end.

Fixpoint PI4_to_base_ucom_l {dim} (l : PI4_ucom_l dim) : base_ucom_l dim :=
  match l with
  | [] => []
  | (App1 u n) :: t => (App1 (PI4_to_base u) n) :: (PI4_to_base_ucom_l t)
  | (App2 u m n) :: t => (App2 (PI4_to_base u) m n) :: (PI4_to_base_ucom_l t)
  | _ => [] (* unreachable case *)
  end.

Fixpoint PI4_to_base_instr {dim} (i : instr PI4_Unitary dim) : instr base_Unitary dim :=
  match i with
  | UC u => UC (PI4_to_base_ucom_l u)
  | Meas n l1 l2 =>
      let fix f l := match l with
                     | [] => []
                     | h :: t => (PI4_to_base_instr h) :: (f t)
                     end in
      Meas n (f l1) (f l2)
  end.
Fixpoint PI4_to_base_com_l {dim} (l : PI4_com_l dim) : base_com_l dim :=
  match l with
  | [] => []
  | h :: t => (PI4_to_base_instr h) :: (PI4_to_base_com_l t)
  end.

Lemma PI4_to_base_instr_UC : forall dim (u : PI4_ucom_l dim),
  PI4_to_base_instr (UC u) = UC (PI4_to_base_ucom_l u).
Proof. intros. reflexivity. Qed.

Lemma PI4_to_base_instr_Meas : forall dim n (l1 : PI4_com_l dim) l2,
  PI4_to_base_instr (Meas n l1 l2) = Meas n (PI4_to_base_com_l l1) (PI4_to_base_com_l l2).
Proof.
  intros.
  simpl.
  apply f_equal2.
  - induction l1; try rewrite IHl1; reflexivity.
  - induction l2; try rewrite IHl2; reflexivity.
Qed.
Global Opaque PI4_to_base_instr.

Lemma PI4_to_base_ucom_l_app : forall {dim} (l1 l2 : PI4_ucom_l dim),
  PI4_to_base_ucom_l (l1 ++ l2) = (PI4_to_base_ucom_l l1) ++ (PI4_to_base_ucom_l l2).
Proof.
  intros.
  induction l1.
  - reflexivity.
  - simpl; destruct a; dependent destruction p;
    rewrite IHl1; reflexivity.
Qed.    

Lemma PI4_to_base_ucom_l_WT : forall {dim} (l : PI4_ucom_l dim), 
  uc_well_typed_l l <-> uc_well_typed_l (PI4_to_base_ucom_l l).
Proof.
  intros.
  induction l; simpl.
  - split; intros H; inversion H; constructor; assumption.
  - destruct a; dependent destruction p;
    split; intros H;
    inversion H; subst;
    constructor; try apply IHl; assumption.
Qed.

Lemma PI4_to_base_com_l_app : forall {dim} (l1 l2 : PI4_com_l dim),
  PI4_to_base_com_l (l1 ++ l2) = (PI4_to_base_com_l l1) ++ (PI4_to_base_com_l l2).
Proof.
  intros.
  induction l1.
  - reflexivity.
  - simpl; rewrite IHl1; reflexivity.
Qed. 

(** Equivalence over PI4_ucom_l. **)

Local Open Scope ucom_scope.
Definition uc_equiv_l {dim} (l1 l2 : PI4_ucom_l dim) := 
  (list_to_ucom (PI4_to_base_ucom_l l1)) ≡ (list_to_ucom (PI4_to_base_ucom_l l2)).
Infix "=l=" := uc_equiv_l (at level 70) : ucom_scope.

Lemma uc_equiv_l_refl : forall {dim} (l1 : PI4_ucom_l dim), l1 =l= l1.
Proof. easy. Qed.
 
Lemma uc_equiv_l_sym : forall {dim} (l1 l2 : PI4_ucom_l dim), l1 =l= l2 -> l2 =l= l1.
Proof. easy. Qed.
 
Lemma uc_equiv_l_trans : forall {dim} (l1 l2 l3 : PI4_ucom_l dim), 
  l1 =l= l2 -> l2 =l= l3 -> l1 =l= l3.
Proof. intros dim l1 l2 l3 H12 H23. unfold uc_equiv_l in *. rewrite H12. easy. Qed.

Lemma uc_cons_congruence : forall {dim} (g : gate_app PI4_Unitary dim)  (l l' : PI4_ucom_l dim),
  l =l= l' ->
  g :: l =l= g :: l'.
Proof.
  intros dim g l l' Hl.
  unfold uc_equiv_l, uc_equiv.
  simpl.
  destruct g; simpl; try rewrite Hl; reflexivity.
Qed.

Lemma uc_app_congruence : forall {dim} (l1 l1' l2 l2' : PI4_ucom_l dim),
  l1 =l= l1' ->
  l2 =l= l2' ->
  l1 ++ l2 =l= l1' ++ l2'.
Proof.
  intros dim l1 l1' l2 l2' Hl1 Hl2.
  unfold uc_equiv_l, uc_equiv.
  simpl.
  repeat rewrite PI4_to_base_ucom_l_app, list_to_ucom_append; simpl.
  rewrite Hl1, Hl2.
  reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (PI4_ucom_l dim) (@uc_equiv_l dim)
  reflexivity proved by uc_equiv_l_refl
  symmetry proved by uc_equiv_l_sym
  transitivity proved by uc_equiv_l_trans
  as uc_equiv_l_rel.

Add Parametric Morphism (dim : nat) : (@List.cons (gate_app PI4_Unitary dim))
  with signature eq ==> (@uc_equiv_l dim) ==> (@uc_equiv_l dim) as uc_cons_mor.
Proof. intros y x0 y0 H0. apply uc_cons_congruence; easy. Qed.

Add Parametric Morphism (dim : nat) : (@app (gate_app PI4_Unitary dim))
  with signature (@uc_equiv_l dim) ==> (@uc_equiv_l dim) ==> (@uc_equiv_l dim) as uc_app_mor.
Proof. intros x y H x0 y0 H0. apply uc_app_congruence; easy. Qed.

(* Useful relationship between equivalence and well-typedness. *)

Lemma uc_equiv_l_implies_WT : forall {dim} (l l' : PI4_ucom_l dim),
  l =l= l' ->
  uc_well_typed_l l ->
  uc_well_typed_l l'.
Proof.
  intros dim l l' H WT.
  apply PI4_to_base_ucom_l_WT.
  apply list_to_ucom_WT. 
  apply uc_eval_nonzero_iff.
  apply PI4_to_base_ucom_l_WT in WT.
  apply list_to_ucom_WT in WT.
  apply uc_eval_nonzero_iff in WT.
  rewrite <- H; assumption.
Qed.

(** Commutativity lemmas **)

Lemma does_not_reference_commutes_app1 : forall {dim} (l : PI4_ucom_l dim) u q,
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

Lemma does_not_reference_commutes_app2 : forall {dim} (l : PI4_ucom_l dim) u m n,
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

Lemma nsqg_commutes : forall {dim} (l : PI4_ucom_l dim) q u l1 l2,
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

Lemma lsqg_commutes : forall {dim} (l : PI4_ucom_l dim) q u l1 l2,
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

(** Equivalence up to a phase over PI4_ucom_l. **)

Definition uc_cong_l {dim} (l1 l2 : PI4_ucom_l dim) := 
  (list_to_ucom (PI4_to_base_ucom_l l1)) ≅ (list_to_ucom (PI4_to_base_ucom_l l2)).
Infix "≅l≅" := uc_cong_l (at level 20).

Lemma uc_cong_l_refl : forall {dim : nat} (l1 : PI4_ucom_l dim), l1 ≅l≅ l1.
Proof. intros. exists 0%R. rewrite Cexp_0. rewrite Mscale_1_l. reflexivity. Qed.

Lemma uc_cong_l_sym : forall {dim : nat} (l1 l2 : PI4_ucom_l dim), l1 ≅l≅ l2 -> l2 ≅l≅ l1.
Proof. intros dim l1 l2 H. unfold uc_cong_l in *. rewrite H. reflexivity. Qed.

Lemma uc_cong_l_trans : forall {dim : nat} (l1 l2 l3 : PI4_ucom_l dim), l1 ≅l≅ l2 -> l2 ≅l≅ l3 -> l1 ≅l≅ l3.
Proof.
  intros dim l1 l2 l3 H1 H2.
  unfold uc_cong_l in *.
  eapply uc_cong_trans. apply H1. apply H2.
Qed.  

Lemma uc_cong_l_cons_congruence : forall {dim : nat} (g : gate_app PI4_Unitary dim) (l l' : PI4_ucom_l dim),
  l ≅l≅ l' -> (g :: l) ≅l≅ (g :: l').
Proof.
  intros dim g l l' H. unfold uc_cong_l in *.
  simpl.
  inversion H.
  destruct g; dependent destruction p;
  exists x; simpl; rewrite <- Mscale_mult_dist_l; rewrite H1; reflexivity.
Qed.

Lemma uc_cong_l_app_congruence : forall {dim : nat} (l l' m m': PI4_ucom_l dim),
  l ≅l≅ l' -> m ≅l≅ m' -> (m ++ l) ≅l≅ (m' ++ l').
Proof.
  intros dim l l' m m' H1 H2.
  unfold uc_cong_l in *.
  inversion H1. inversion H2.
  exists (x + x0)%R.
  repeat rewrite PI4_to_base_ucom_l_app, list_to_ucom_append; simpl.
  rewrite H0. rewrite H3. 
  rewrite Mscale_mult_dist_r.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_assoc.
  rewrite <- Cexp_add.
  rewrite Rplus_comm.
  reflexivity.
Qed.
    
Add Parametric Relation (dim : nat) : (PI4_ucom_l dim) (@uc_cong_l dim)
  reflexivity proved by uc_cong_l_refl
  symmetry proved by uc_cong_l_sym
  transitivity proved by uc_cong_l_trans
  as uc_cong_l_rel.

Add Parametric Morphism (dim : nat) : (@List.cons (gate_app PI4_Unitary dim))
  with signature eq ==> (@uc_cong_l dim) ==> (@uc_cong_l dim) as uc_cons_mor_cong.
Proof. intros. apply uc_cong_l_cons_congruence. easy. Qed.

Add Parametric Morphism (dim : nat) : (@app (gate_app PI4_Unitary dim))
  with signature (@uc_cong_l dim) ==> (@uc_cong_l dim) ==> (@uc_cong_l dim) as uc_app_mor_cong.
Proof. intros x y H x0 y0 H0. apply uc_cong_l_app_congruence; easy. Qed.

Lemma uc_equiv_cong_l : forall {dim : nat} (c c' : PI4_ucom_l dim), c =l= c' -> c ≅l≅ c'.
Proof.
  intros dim c c' H.
  exists 0%R. rewrite Cexp_0, Mscale_1_l. 
  apply H.
Qed.

Lemma uc_cong_l_implies_WT : forall {dim} (l l' : PI4_ucom_l dim),
  l ≅l≅ l' ->
  uc_well_typed_l l ->
  uc_well_typed_l l'.
Proof.
  intros dim l l' H WT.
  apply PI4_to_base_ucom_l_WT.
  apply list_to_ucom_WT. 
  apply uc_eval_nonzero_iff.
  apply PI4_to_base_ucom_l_WT in WT.
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

(* Soundness of replace_single_qubit_pattern. *)

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

Lemma remove_single_qubit_pattern_correct : forall {dim} (l l' : PI4_ucom_l dim) (q : nat) (pat : single_qubit_pattern PI4_Unitary),
  remove_single_qubit_pattern l q pat match_gate = Some l' ->
  l =l= (single_qubit_pattern_to_program dim pat q) ++ l'.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction pat; intros l l' H.
  - inversion H; subst. reflexivity.
  - simpl in H. 
    destruct (next_single_qubit_gate l q) eqn:nsqg; try discriminate.
    repeat destruct p.
    destruct (match_gate a p) eqn:Hmatch; try discriminate.
    rewrite match_gate_refl in Hmatch; subst.
    simpl.
    rewrite <- (IHpat _ _ H). 
    apply (nsqg_commutes _ _ _ _ _ nsqg).
Qed.

(* Equivalence up to a phase .
   (Exact equivalence is also easy to prove, but not used in our development.) *)
Lemma replace_single_qubit_pattern_sound : forall {dim} (l l' : PI4_ucom_l dim) (q : nat) (pat rep : single_qubit_pattern PI4_Unitary),
  single_qubit_pattern_to_program dim pat q ≅l≅ single_qubit_pattern_to_program dim rep q ->
  replace_single_qubit_pattern l q pat rep match_gate = Some l' ->
  l ≅l≅ l'.
Proof.
  intros dim l l' q pat rep H1 H2.
  unfold replace_single_qubit_pattern in H2.
  destruct (remove_single_qubit_pattern l q pat) eqn:rem; try discriminate.
  apply remove_single_qubit_pattern_correct in rem.
  apply uc_equiv_cong_l in rem.
  inversion H2; subst.
  rewrite rem, H1. 
  reflexivity.
Qed.

(** Equivalence over PI4_com_l. **)

Local Close Scope ucom_scope.
Local Open Scope com_scope.
Definition c_equiv_l {dim} (l1 l2 : PI4_com_l dim) := 
  (list_to_com (PI4_to_base_com_l l1)) ≡ (list_to_com (PI4_to_base_com_l l2)).
Infix "=l=" := c_equiv_l (at level 70) : com_scope.

Lemma c_equiv_l_refl : forall {dim} (l1 : PI4_com_l dim), l1 =l= l1.
Proof. easy. Qed.
 
Lemma c_equiv_l_sym : forall {dim} (l1 l2 : PI4_com_l dim), l1 =l= l2 -> l2 =l= l1.
Proof. unfold c_equiv_l. easy. Qed.
 
Lemma c_equiv_l_trans : forall {dim} (l1 l2 l3 : PI4_com_l dim), 
  l1 =l= l2 -> l2 =l= l3 -> l1 =l= l3.
Proof. unfold c_equiv_l. intros dim l1 l2 l3 H12 H23. rewrite H12. easy. Qed.

Lemma c_cons_congruence : forall {dim} (i : instr PI4_Unitary dim)  (l l' : PI4_com_l dim),
  l =l= l' ->
  i :: l =l= i :: l'.
Proof.
  unfold c_equiv_l.
  intros dim i l l' Hl.  
  simpl. rewrite Hl. reflexivity.
Qed.

Lemma c_app_congruence : forall {dim} (l1 l1' l2 l2' : PI4_com_l dim),
  l1 =l= l1' ->
  l2 =l= l2' ->
  l1 ++ l2 =l= l1' ++ l2'.
Proof.
  unfold c_equiv_l.
  intros dim l1 l1' l2 l2' Hl1 Hl2.
  repeat rewrite PI4_to_base_com_l_app, list_to_com_append; simpl.
  rewrite Hl1, Hl2.
  reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (PI4_com_l dim) (@c_equiv_l dim)
  reflexivity proved by c_equiv_l_refl
  symmetry proved by c_equiv_l_sym
  transitivity proved by c_equiv_l_trans
  as c_equiv_l_rel.

Add Parametric Morphism (dim : nat) : (@List.cons (instr PI4_Unitary dim))
  with signature eq ==> (@c_equiv_l dim) ==> (@c_equiv_l dim) as c_cons_mor.
Proof. intros y x0 y0 H0. apply c_cons_congruence; easy. Qed.

Add Parametric Morphism (dim : nat) : (@app (gate_app PI4_Unitary dim))
  with signature (@uc_equiv_l dim) ==> (@uc_equiv_l dim) ==> (@uc_equiv_l dim) as c_app_mor.
Proof. intros x y H x0 y0 H0. apply uc_app_congruence; easy. Qed.

(* Also useful to have a congruence lemma for rewriting inside Meas. *)
Definition c_eval_l {dim} (l : PI4_com_l dim) :=
  c_eval (list_to_com (PI4_to_base_com_l l)).
Local Coercion Nat.b2n : bool >-> nat.
Definition project_onto {dim} ρ n (b : bool) := super (@pad 1 n dim (∣b⟩ × ∣b⟩†)) ρ.
Lemma Meas_cons_congruence : forall dim n (l1 l2 l1' l2' l l' : PI4_com_l dim),
  (forall ρ, WF_Matrix ρ ->
   c_eval_l l1 (project_onto ρ n true) = c_eval_l l1' (project_onto ρ n true)) ->
  (forall ρ, WF_Matrix ρ ->
   c_eval_l l2 (project_onto ρ n false) = c_eval_l l2' (project_onto ρ n false)) ->
  l =l= l' ->
  Meas n l1 l2 :: l =l= Meas n l1' l2' :: l'.
Proof.
  intros.
  unfold c_equiv_l; simpl.
  repeat rewrite PI4_to_base_instr_Meas, instr_to_com_Meas.
  apply seq_congruence; auto.
  unfold c_equiv; simpl.
  intros Hdim ρ WFρ.
  unfold Splus, compose_super; simpl.
  unfold c_eval_l, project_onto in *.
  simpl in *.
  rewrite H0, H1; try assumption.
  reflexivity.
Qed.

(** Commutativity lemmas for com list representation. **)

Lemma uc_equiv_l_implies_c_equiv_l : forall dim (u u' : PI4_ucom_l dim),
  (u =l= u')%ucom ->
  [UC u] =l= [UC u'].
Proof.
  unfold uc_equiv_l, uc_equiv, c_equiv_l, c_equiv.
  intros dim u u' H Hdim ρ WFρ.
  simpl.
  repeat rewrite PI4_to_base_instr_UC, instr_to_com_UC.
  simpl; rewrite H; reflexivity.
Qed.

Lemma UC_append : forall {dim} (l1 l2: PI4_ucom_l dim), 
  [UC (l1 ++ l2)] =l= [UC l1] ++ [UC l2].
Proof. 
  intros.
  unfold c_equiv_l, c_equiv; simpl.
  intros.
  repeat rewrite PI4_to_base_instr_UC, instr_to_com_UC; simpl.
  rewrite PI4_to_base_ucom_l_app, list_to_ucom_append; simpl.
  rewrite compose_super_assoc. 
  unfold compose_super, super. Msimpl.
  repeat rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma UC_nil : forall dim, 
  [UC []] =l= ([] : PI4_com_l dim).
Proof.
  unfold c_equiv_l, c_equiv.
  intros; simpl.
  rewrite PI4_to_base_instr_UC, instr_to_com_UC; simpl.
  unfold compose_super, super. 
  rewrite denote_SKIP; try assumption.
  Msimpl; reflexivity.
Qed.

Lemma cons_to_app : forall {A} (h : A) (t : list A), h :: t = [h] ++ t.
Proof. reflexivity. Qed.

Lemma does_not_reference_c_commutes_app1 : forall {dim} (l : PI4_com_l dim) u q,
  does_not_reference_c l q = true ->
  [UC [App1 u q]] ++ l =l= l ++ [UC [App1 u q]]. 
Proof.
  intros dim l u q H.
  induction l using com_list_ind; try reflexivity.
  - simpl in H.
    apply andb_true_iff in H as [Hu0 Hl].
    rewrite <- (app_comm_cons _ _ (UC u0)).
    rewrite <- IHl; try assumption.
    rewrite (cons_to_app (UC u0)).
    rewrite (cons_to_app (UC u0) (_ ++ l)).
    repeat rewrite app_assoc.
    apply c_app_congruence; try reflexivity.
    rewrite does_not_reference_instr_UC in Hu0.   
    repeat rewrite <- UC_append.
    apply uc_equiv_l_implies_c_equiv_l.
    apply does_not_reference_commutes_app1.
    assumption.
  - simpl in H.
    apply andb_true_iff in H as [Hmeas Hl3].
    rewrite <- (app_comm_cons _ _ (Meas n l1 l2)).
    rewrite <- IHl3; try assumption.
    rewrite (cons_to_app (Meas n l1 l2)).
    rewrite (cons_to_app (Meas n l1 l2) (_ ++ l3)).
    repeat rewrite app_assoc.
    apply c_app_congruence; try reflexivity.
    rewrite does_not_reference_instr_Meas in Hmeas.
    apply andb_true_iff in Hmeas as [Hmeas Hl2].
    apply andb_true_iff in Hmeas as [Hq Hl1].
    apply IHl1 in Hl1.
    apply IHl2 in Hl2.
    apply negb_true_iff in Hq. 
    apply Nat.eqb_neq in Hq. 
    clear - Hq Hl1 Hl2.
    unfold c_equiv_l in *.
    repeat rewrite PI4_to_base_com_l_app, list_to_com_append in Hl1, Hl2.
    simpl in *.
    rewrite PI4_to_base_instr_UC, instr_to_com_UC in *.
    rewrite PI4_to_base_instr_Meas, instr_to_com_Meas in *.
    unfold c_equiv in *; simpl in *.
    intros Hdim ρ WFρ.
    unfold compose_super, Splus in *.
    rewrite denote_SKIP in *; try assumption.
    rewrite Mmult_1_l in *; try auto with wf_db.
    remember (ueval_r dim q (PI4_to_base u)) as U.
    remember (pad n dim (∣1⟩ × (∣1⟩) †)) as pad1.
    remember (pad n dim (∣0⟩ × (∣0⟩) †)) as pad0.
    replace (super pad1 (super U ρ)) with (super U (super pad1 ρ)).
    2: { subst; clear - Hq.
         unfold super.
         autorewrite with eval_db.
         bdestruct (n + 1 <=? dim)%nat; try (Msimpl; reflexivity).
         dependent destruction u; simpl; autorewrite with eval_db.
         all: bdestruct (q + 1 <=? dim)%nat; try (repeat Msimpl; reflexivity).
         all: repeat rewrite Mmult_assoc;
              rewrite <- 2 Mmult_adjoint;
              repeat rewrite <- Mmult_assoc.
         all: gridify; reflexivity. } (* gridify works here too :) *)
    replace (super pad0 (super U ρ)) with (super U (super pad0 ρ)).
    2: { subst; clear - Hq.
         unfold super.
         autorewrite with eval_db.
         bdestruct (n + 1 <=? dim)%nat; try (Msimpl; reflexivity).
         dependent destruction u; simpl; autorewrite with eval_db.
         all: bdestruct (q + 1 <=? dim)%nat; try (repeat Msimpl; reflexivity).
         all: repeat rewrite Mmult_assoc;
              rewrite <- 2 Mmult_adjoint;
              repeat rewrite <- Mmult_assoc.
         all: gridify; reflexivity. }
    rewrite Hl1, Hl2; try assumption.
    2, 3: subst; auto with wf_db.
    unfold super. 
    rewrite <- Mmult_plus_distr_r.
    rewrite <- Mmult_plus_distr_l.
    reflexivity.
Qed.

(** Misc. Utilities **)

(* Check whether a (unitary) program is well typed. *)
Definition PI4_list_well_typed_b dim (l : PI4_ucom_l dim) := uc_well_typed_l_b dim l.

(* Count the gates in the list representation of a (unitary) program. *)
Fixpoint count_H_gates {dim} (l : PI4_ucom_l dim) :=
  let fix aux l acc :=
    match l with
    | [] => acc
    | (App1 UPI4_H _) :: t => aux t (acc + 1)
    | _ :: t => aux t acc
    end in
  aux l 0.

Fixpoint count_X_gates {dim} (l : PI4_ucom_l dim) :=
  let fix aux l acc :=
    match l with
    | [] => acc
    | (App1 UPI4_X _) :: t => aux t (acc + 1)
    | _ :: t => aux t acc
    end in
  aux l 0.

Fixpoint count_rotation_gates {dim} (l : PI4_ucom_l dim) :=
  let fix aux l acc :=
    match l with
    | [] => acc
    | (App1 (UPI4_PI4 _) _) :: t  => aux t (acc + 1)
    | _ :: t => aux t acc
    end in
  aux l 0.

Fixpoint count_CNOT_gates {dim} (l : PI4_ucom_l dim) :=
  let fix aux l acc :=
    match l with
    | [] => acc
    | (App2 UPI4_CNOT _ _) :: t => aux t (acc + 1)
    | _ :: t => aux t acc
    end in
  aux l 0.

