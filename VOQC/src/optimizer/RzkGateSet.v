Require Import UnitarySem.
Require Import Equivalences.
Require Export ListRepresentation.
Require Import DensitySem.
Require Import Setoid.

Local Open Scope Z_scope.

(** Rz_k Gate Set **)

(* In our optimizer we use the gate set {H, X, Rz_k, CNOT} where Rz_k
   is rotation about the z-axis by i * PI / (2 ^ k) for integer i. We'll 
   call this the Rz_k gate set. *)

Inductive Rzk_Unitary : nat -> Set := 
  | URzk_H                 : Rzk_Unitary 1 
  | URzk_X                 : Rzk_Unitary 1
  | URzk_Rz (i : BinInt.Z) : Rzk_Unitary 1
  | URzk_CNOT              : Rzk_Unitary 2.

(* Denominator specifying the precision of our rotations. 

   This can be any multiple of 4 for our proofs to go through. We choose (2 ^ 15)
   because it allows the integer representation of angles between -π and π to be 
   stored using 16 bits. We claim this is enough precision based on the following 
   quote from Nam et al., npj Quantum Information volume 4, 23 (2018): 
   "We choose to omit rotations by angles at most π/2^13 [from our QFT benchmarks] 
    since evidence suggests that using this approximate QFT in the factoring 
    algorithm gives an approach with small failure probability for instances of 
    the sizes we consider."

   Representing large constants in Coq is generally not a good idea. If we run
   into problems we might switch to the following.
   Axiom Rzk_k : nat.
   Extract Constant Rzk_k => "...".
 *)    
Definition Rzk_k := 2 ^ 15.

(* Useful shorthands. *)

Definition URzk_I := URzk_Rz 0.
Definition URzk_T := URzk_Rz (Rzk_k / 4).
Definition URzk_P := URzk_Rz (Rzk_k / 2).
Definition URzk_Z := URzk_Rz Rzk_k.
Definition URzk_PDAG := URzk_Rz (3 * Rzk_k / 2).
Definition URzk_TDAG := URzk_Rz (7 * Rzk_k / 4).
Definition T {dim} q := @App1 _ dim URzk_T q.
Definition TDAG {dim} q := @App1 _ dim URzk_TDAG q.
Definition P {dim} q := @App1 _ dim URzk_P q.
Definition PDAG {dim} q := @App1 _ dim URzk_PDAG q.
Definition Z {dim} q := @App1 _ dim URzk_Z q.
Definition Rz {dim} i q := @App1 _ dim (URzk_Rz i) q.
Definition H {dim} q := @App1 _ dim URzk_H q.
Definition X {dim} q := @App1 _ dim URzk_X q.
Definition CNOT {dim} q1 q2 := @App2 _ dim URzk_CNOT q1 q2.

Definition Rzk_ucom dim := ucom Rzk_Unitary dim.
Definition Rzk_ucom_l dim := gate_list Rzk_Unitary dim.
Definition Rzk_com dim := com Rzk_Unitary dim.
Definition Rzk_com_l dim := com_list Rzk_Unitary dim.

(* Used to convert benchmarks to PI4 set. *)
Definition CCX {dim} a b c : Rzk_ucom_l dim :=
  H c :: CNOT b c :: TDAG c :: CNOT a c :: 
  T c :: CNOT b c :: TDAG c :: CNOT a c :: 
  CNOT a b :: TDAG b :: CNOT a b :: 
  T a :: T b :: T c :: H c :: []. 
Definition CCZ {dim} a b c : Rzk_ucom_l dim :=
  CNOT b c :: TDAG c :: CNOT a c :: 
  T c :: CNOT b c :: TDAG c :: CNOT a c :: 
  CNOT a b :: TDAG b :: CNOT a b :: 
  T a :: T b :: T c :: []. 

(* Conversion to the base gate set. *)
Definition Rzk_to_base {n} (u : Rzk_Unitary n) : base_Unitary n :=
  match u with
  | URzk_H     => U_R (PI/2) 0 PI
  | URzk_X     => U_R PI 0 PI
  | URzk_Rz i  => U_R 0 0 (IZR i * PI / IZR Rzk_k)%R
  | URzk_CNOT  => U_CNOT
  end.

Fixpoint Rzk_to_base_ucom_l {dim} (l : Rzk_ucom_l dim) : base_ucom_l dim :=
  match l with
  | [] => []
  | (App1 u n) :: t => (App1 (Rzk_to_base u) n) :: (Rzk_to_base_ucom_l t)
  | (App2 u m n) :: t => (App2 (Rzk_to_base u) m n) :: (Rzk_to_base_ucom_l t)
  | _ => [] (* unreachable case *)
  end.

Fixpoint Rzk_to_base_instr {dim} (i : instr Rzk_Unitary dim) : instr base_Unitary dim :=
  match i with
  | UC u => UC (Rzk_to_base_ucom_l u)
  | Meas n l1 l2 =>
      let fix f l := match l with
                     | [] => []
                     | h :: t => (Rzk_to_base_instr h) :: (f t)
                     end in
      Meas n (f l1) (f l2)
  end.
Fixpoint Rzk_to_base_com_l {dim} (l : Rzk_com_l dim) : base_com_l dim :=
  match l with
  | [] => []
  | h :: t => (Rzk_to_base_instr h) :: (Rzk_to_base_com_l t)
  end.

Lemma Rzk_to_base_instr_UC : forall dim (u : Rzk_ucom_l dim),
  Rzk_to_base_instr (UC u) = UC (Rzk_to_base_ucom_l u).
Proof. intros. reflexivity. Qed.

Lemma Rzk_to_base_instr_Meas : forall dim n (l1 : Rzk_com_l dim) l2,
  Rzk_to_base_instr (Meas n l1 l2) = Meas n (Rzk_to_base_com_l l1) (Rzk_to_base_com_l l2).
Proof.
  intros.
  simpl.
  apply f_equal2.
  - induction l1; try rewrite IHl1; reflexivity.
  - induction l2; try rewrite IHl2; reflexivity.
Qed.
Global Opaque Rzk_to_base_instr.

Lemma Rzk_to_base_ucom_l_app : forall {dim} (l1 l2 : Rzk_ucom_l dim),
  Rzk_to_base_ucom_l (l1 ++ l2) = (Rzk_to_base_ucom_l l1) ++ (Rzk_to_base_ucom_l l2).
Proof.
  intros.
  induction l1.
  - reflexivity.
  - simpl; destruct a as [u | u | u]; dependent destruction u;
    rewrite IHl1; reflexivity.
Qed.    

Lemma Rzk_to_base_ucom_l_WT : forall {dim} (l : Rzk_ucom_l dim), 
  uc_well_typed_l l <-> uc_well_typed_l (Rzk_to_base_ucom_l l).
Proof.
  intros.
  induction l; simpl.
  - split; intros H; inversion H; constructor; assumption.
  - destruct a as [u | u | u]; dependent destruction u;
    split; intros H;
    inversion H; subst;
    constructor; try apply IHl; assumption.
Qed.

Lemma Rzk_to_base_com_l_app : forall {dim} (l1 l2 : Rzk_com_l dim),
  Rzk_to_base_com_l (l1 ++ l2) = (Rzk_to_base_com_l l1) ++ (Rzk_to_base_com_l l2).
Proof.
  intros.
  induction l1.
  - reflexivity.
  - simpl; rewrite IHl1; reflexivity.
Qed. 

Definition Rzk_eval {dim} (l : Rzk_ucom_l dim) :=
  uc_eval (list_to_ucom (Rzk_to_base_ucom_l l)).

(** Equivalence over Rzk_ucom_l. **)

Local Open Scope ucom_scope.
Definition uc_equiv_l {dim} (l1 l2 : Rzk_ucom_l dim) := 
  (list_to_ucom (Rzk_to_base_ucom_l l1)) ≡ (list_to_ucom (Rzk_to_base_ucom_l l2)).
Infix "=l=" := uc_equiv_l (at level 70) : ucom_scope.

Lemma uc_equiv_l_refl : forall {dim} (l1 : Rzk_ucom_l dim), l1 =l= l1.
Proof. easy. Qed.
 
Lemma uc_equiv_l_sym : forall {dim} (l1 l2 : Rzk_ucom_l dim), l1 =l= l2 -> l2 =l= l1.
Proof. easy. Qed.
 
Lemma uc_equiv_l_trans : forall {dim} (l1 l2 l3 : Rzk_ucom_l dim), 
  l1 =l= l2 -> l2 =l= l3 -> l1 =l= l3.
Proof. intros dim l1 l2 l3 H12 H23. unfold uc_equiv_l in *. rewrite H12. easy. Qed.

Lemma uc_cons_congruence : forall {dim} (g : gate_app Rzk_Unitary dim)  (l l' : Rzk_ucom_l dim),
  l =l= l' ->
  g :: l =l= g :: l'.
Proof.
  intros dim g l l' Hl.
  unfold uc_equiv_l, uc_equiv.
  simpl.
  destruct g; simpl; try rewrite Hl; reflexivity.
Qed.

Lemma uc_app_congruence : forall {dim} (l1 l1' l2 l2' : Rzk_ucom_l dim),
  l1 =l= l1' ->
  l2 =l= l2' ->
  l1 ++ l2 =l= l1' ++ l2'.
Proof.
  intros dim l1 l1' l2 l2' Hl1 Hl2.
  unfold uc_equiv_l, uc_equiv.
  simpl.
  repeat rewrite Rzk_to_base_ucom_l_app, list_to_ucom_append; simpl.
  rewrite Hl1, Hl2.
  reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (Rzk_ucom_l dim) (@uc_equiv_l dim)
  reflexivity proved by uc_equiv_l_refl
  symmetry proved by uc_equiv_l_sym
  transitivity proved by uc_equiv_l_trans
  as uc_equiv_l_rel.

Add Parametric Morphism (dim : nat) : (@List.cons (gate_app Rzk_Unitary dim))
  with signature eq ==> (@uc_equiv_l dim) ==> (@uc_equiv_l dim) as uc_cons_mor.
Proof. intros y x0 y0 H0. apply uc_cons_congruence; easy. Qed.

Add Parametric Morphism (dim : nat) : (@app (gate_app Rzk_Unitary dim))
  with signature (@uc_equiv_l dim) ==> (@uc_equiv_l dim) ==> (@uc_equiv_l dim) as uc_app_mor.
Proof. intros x y H x0 y0 H0. apply uc_app_congruence; easy. Qed.

(* Useful relationship between equivalence and well-typedness. *)

Lemma uc_equiv_l_implies_WT : forall {dim} (l l' : Rzk_ucom_l dim),
  l =l= l' ->
  uc_well_typed_l l ->
  uc_well_typed_l l'.
Proof.
  intros dim l l' H WT.
  apply Rzk_to_base_ucom_l_WT.
  apply list_to_ucom_WT. 
  apply uc_eval_nonzero_iff.
  apply Rzk_to_base_ucom_l_WT in WT.
  apply list_to_ucom_WT in WT.
  apply uc_eval_nonzero_iff in WT.
  rewrite <- H; assumption.
Qed.

(** Commutativity lemmas **)

Lemma does_not_reference_commutes_app1 : forall {dim} (l : Rzk_ucom_l dim) u q,
  does_not_reference l q = true ->
  [App1 u q] ++ l =l= l ++ [App1 u q]. 
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl in *.
    destruct a as [u' | u' | u']; dependent destruction u';
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

Lemma does_not_reference_commutes_app2 : forall {dim} (l : Rzk_ucom_l dim) u m n,
  does_not_reference l m = true ->
  does_not_reference l n = true ->
  [App2 u m n] ++ l =l= l ++ [App2 u m n]. 
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl in *.
    destruct a as [u' | u' | u']; dependent destruction u';
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

Lemma nsqg_commutes : forall {dim} (l : Rzk_ucom_l dim) q u l1 l2,
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

Lemma lsqg_commutes : forall {dim} (l : Rzk_ucom_l dim) q u l1 l2,
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

(** Equivalence up to a phase over Rzk_ucom_l. **)

Definition uc_cong_l {dim} (l1 l2 : Rzk_ucom_l dim) := 
  (list_to_ucom (Rzk_to_base_ucom_l l1)) ≅ (list_to_ucom (Rzk_to_base_ucom_l l2)).
Infix "≅l≅" := uc_cong_l (at level 20).

Lemma uc_cong_l_refl : forall {dim : nat} (l1 : Rzk_ucom_l dim), l1 ≅l≅ l1.
Proof. intros. exists 0%R. rewrite Cexp_0. rewrite Mscale_1_l. reflexivity. Qed.

Lemma uc_cong_l_sym : forall {dim : nat} (l1 l2 : Rzk_ucom_l dim), l1 ≅l≅ l2 -> l2 ≅l≅ l1.
Proof. intros dim l1 l2 H. unfold uc_cong_l in *. rewrite H. reflexivity. Qed.

Lemma uc_cong_l_trans : forall {dim : nat} (l1 l2 l3 : Rzk_ucom_l dim), l1 ≅l≅ l2 -> l2 ≅l≅ l3 -> l1 ≅l≅ l3.
Proof.
  intros dim l1 l2 l3 H1 H2.
  unfold uc_cong_l in *.
  eapply uc_cong_trans. apply H1. apply H2.
Qed.  

Lemma uc_cong_l_cons_congruence : forall {dim : nat} (g : gate_app Rzk_Unitary dim) (l l' : Rzk_ucom_l dim),
  l ≅l≅ l' -> (g :: l) ≅l≅ (g :: l').
Proof.
  intros dim g l l' H. unfold uc_cong_l in *.
  simpl.
  inversion H.
  destruct g as [u | u | u]; dependent destruction u;
  exists x; simpl; rewrite <- Mscale_mult_dist_l; rewrite H1; reflexivity.
Qed.

Lemma uc_cong_l_app_congruence : forall {dim : nat} (l l' m m': Rzk_ucom_l dim),
  l ≅l≅ l' -> m ≅l≅ m' -> (m ++ l) ≅l≅ (m' ++ l').
Proof.
  intros dim l l' m m' H1 H2.
  unfold uc_cong_l in *.
  inversion H1. inversion H2.
  exists (x + x0)%R.
  repeat rewrite Rzk_to_base_ucom_l_app, list_to_ucom_append; simpl.
  rewrite H0. rewrite H3. 
  rewrite Mscale_mult_dist_r.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_assoc.
  rewrite <- Cexp_add.
  rewrite Rplus_comm.
  reflexivity.
Qed.
    
Add Parametric Relation (dim : nat) : (Rzk_ucom_l dim) (@uc_cong_l dim)
  reflexivity proved by uc_cong_l_refl
  symmetry proved by uc_cong_l_sym
  transitivity proved by uc_cong_l_trans
  as uc_cong_l_rel.

Add Parametric Morphism (dim : nat) : (@List.cons (gate_app Rzk_Unitary dim))
  with signature eq ==> (@uc_cong_l dim) ==> (@uc_cong_l dim) as uc_cons_mor_cong.
Proof. intros. apply uc_cong_l_cons_congruence. easy. Qed.

Add Parametric Morphism (dim : nat) : (@app (gate_app Rzk_Unitary dim))
  with signature (@uc_cong_l dim) ==> (@uc_cong_l dim) ==> (@uc_cong_l dim) as uc_app_mor_cong.
Proof. intros x y H x0 y0 H0. apply uc_cong_l_app_congruence; easy. Qed.

Lemma uc_equiv_cong_l : forall {dim : nat} (c c' : Rzk_ucom_l dim), c =l= c' -> c ≅l≅ c'.
Proof.
  intros dim c c' H.
  exists 0%R. rewrite Cexp_0, Mscale_1_l. 
  apply H.
Qed.

Lemma uc_cong_l_implies_WT : forall {dim} (l l' : Rzk_ucom_l dim),
  l ≅l≅ l' ->
  uc_well_typed_l l ->
  uc_well_typed_l l'.
Proof.
  intros dim l l' H WT.
  apply Rzk_to_base_ucom_l_WT.
  apply list_to_ucom_WT. 
  apply uc_eval_nonzero_iff.
  apply Rzk_to_base_ucom_l_WT in WT.
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

Definition match_gate {n} (u u' : Rzk_Unitary n) : bool :=
  match u, u' with
  | URzk_H, URzk_H | URzk_X, URzk_X | URzk_CNOT, URzk_CNOT => true
  | URzk_Rz i, URzk_Rz i' => Z.eqb i i'
  | _, _ => false
  end.

Lemma match_gate_refl : forall {n} (u u' : Rzk_Unitary n), 
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

Lemma remove_single_qubit_pattern_correct : forall {dim} (l l' : Rzk_ucom_l dim) (q : nat) (pat : single_qubit_pattern Rzk_Unitary),
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
    destruct (match_gate a r) eqn:Hmatch; try discriminate.
    rewrite match_gate_refl in Hmatch; subst.
    simpl.
    rewrite <- (IHpat _ _ H). 
    apply (nsqg_commutes _ _ _ _ _ nsqg).
Qed.

(* Equivalence up to a phase. Exact equivalence is also easy to prove, but not used 
   in our development. *)
Lemma replace_single_qubit_pattern_sound : forall {dim} (l l' : Rzk_ucom_l dim) (q : nat) (pat rep : single_qubit_pattern Rzk_Unitary),
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

(** Equivalence over Rzk_com_l. **)

Local Close Scope ucom_scope.
Local Open Scope com_scope.
Definition c_equiv_l {dim} (l1 l2 : Rzk_com_l dim) := 
  (list_to_com (Rzk_to_base_com_l l1)) ≡ (list_to_com (Rzk_to_base_com_l l2)).
Infix "=l=" := c_equiv_l (at level 70) : com_scope.

Lemma c_equiv_l_refl : forall {dim} (l1 : Rzk_com_l dim), l1 =l= l1.
Proof. easy. Qed.
 
Lemma c_equiv_l_sym : forall {dim} (l1 l2 : Rzk_com_l dim), l1 =l= l2 -> l2 =l= l1.
Proof. unfold c_equiv_l. easy. Qed.
 
Lemma c_equiv_l_trans : forall {dim} (l1 l2 l3 : Rzk_com_l dim), 
  l1 =l= l2 -> l2 =l= l3 -> l1 =l= l3.
Proof. unfold c_equiv_l. intros dim l1 l2 l3 H12 H23. rewrite H12. easy. Qed.

Lemma c_cons_congruence : forall {dim} (i : instr Rzk_Unitary dim)  (l l' : Rzk_com_l dim),
  l =l= l' ->
  i :: l =l= i :: l'.
Proof.
  unfold c_equiv_l.
  intros dim i l l' Hl.  
  simpl. rewrite Hl. reflexivity.
Qed.

Lemma c_app_congruence : forall {dim} (l1 l1' l2 l2' : Rzk_com_l dim),
  l1 =l= l1' ->
  l2 =l= l2' ->
  l1 ++ l2 =l= l1' ++ l2'.
Proof.
  unfold c_equiv_l.
  intros dim l1 l1' l2 l2' Hl1 Hl2.
  repeat rewrite Rzk_to_base_com_l_app, list_to_com_append; simpl.
  rewrite Hl1, Hl2.
  reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (Rzk_com_l dim) (@c_equiv_l dim)
  reflexivity proved by c_equiv_l_refl
  symmetry proved by c_equiv_l_sym
  transitivity proved by c_equiv_l_trans
  as c_equiv_l_rel.

Add Parametric Morphism (dim : nat) : (@List.cons (instr Rzk_Unitary dim))
  with signature eq ==> (@c_equiv_l dim) ==> (@c_equiv_l dim) as c_cons_mor.
Proof. intros y x0 y0 H0. apply c_cons_congruence; easy. Qed.

Add Parametric Morphism (dim : nat) : (@app (gate_app Rzk_Unitary dim))
  with signature (@uc_equiv_l dim) ==> (@uc_equiv_l dim) ==> (@uc_equiv_l dim) as c_app_mor.
Proof. intros x y H x0 y0 H0. apply uc_app_congruence; easy. Qed.

(* Also useful to have a congruence lemma for rewriting inside Meas. *)
Definition c_eval_l {dim} (l : Rzk_com_l dim) :=
  c_eval (list_to_com (Rzk_to_base_com_l l)).
Local Coercion Nat.b2n : bool >-> nat.
Definition project_onto {dim} ρ n (b : bool) := super (@pad 1 n dim (∣b⟩ × ∣b⟩†)) ρ.
Lemma Meas_cons_congruence : forall dim n (l1 l2 l1' l2' l l' : Rzk_com_l dim),
  (forall ρ, WF_Matrix ρ ->
   c_eval_l l1 (project_onto ρ n true) = c_eval_l l1' (project_onto ρ n true)) ->
  (forall ρ, WF_Matrix ρ ->
   c_eval_l l2 (project_onto ρ n false) = c_eval_l l2' (project_onto ρ n false)) ->
  l =l= l' ->
  Meas n l1 l2 :: l =l= Meas n l1' l2' :: l'.
Proof.
  intros.
  unfold c_equiv_l; simpl.
  repeat rewrite Rzk_to_base_instr_Meas, instr_to_com_Meas.
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

Lemma uc_equiv_l_implies_c_equiv_l : forall dim (u u' : Rzk_ucom_l dim),
  (u =l= u')%ucom ->
  [UC u] =l= [UC u'].
Proof.
  unfold uc_equiv_l, uc_equiv, c_equiv_l, c_equiv.
  intros dim u u' H Hdim ρ WFρ.
  simpl.
  repeat rewrite Rzk_to_base_instr_UC, instr_to_com_UC.
  simpl; rewrite H; reflexivity.
Qed.

Lemma UC_append : forall {dim} (l1 l2: Rzk_ucom_l dim), 
  [UC (l1 ++ l2)] =l= [UC l1] ++ [UC l2].
Proof. 
  intros.
  unfold c_equiv_l, c_equiv; simpl.
  intros.
  repeat rewrite Rzk_to_base_instr_UC, instr_to_com_UC; simpl.
  rewrite Rzk_to_base_ucom_l_app, list_to_ucom_append; simpl.
  rewrite compose_super_assoc. 
  unfold compose_super, super. Msimpl.
  repeat rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma UC_nil : forall dim, 
  [UC []] =l= ([] : Rzk_com_l dim).
Proof.
  unfold c_equiv_l, c_equiv.
  intros; simpl.
  rewrite Rzk_to_base_instr_UC, instr_to_com_UC; simpl.
  unfold compose_super, super. 
  rewrite denote_SKIP; try assumption.
  Msimpl; reflexivity.
Qed.

Lemma cons_to_app : forall {A} (h : A) (t : list A), h :: t = [h] ++ t.
Proof. reflexivity. Qed.

Lemma does_not_reference_c_commutes_app1 : forall {dim} (l : Rzk_com_l dim) u q,
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
    repeat rewrite Rzk_to_base_com_l_app, list_to_com_append in Hl1, Hl2.
    simpl in *.
    rewrite Rzk_to_base_instr_UC, instr_to_com_UC in *.
    rewrite Rzk_to_base_instr_Meas, instr_to_com_Meas in *.
    unfold c_equiv in *; simpl in *.
    intros Hdim ρ WFρ.
    unfold compose_super, Splus in *.
    rewrite denote_SKIP in *; try assumption.
    rewrite Mmult_1_l in *; try auto with wf_db.
    remember (ueval_r dim q (Rzk_to_base u)) as U.
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
Definition Rzk_list_well_typed_b dim (l : Rzk_ucom_l dim) := uc_well_typed_l_b dim l.

(* Combine Rz rotations; returns [] or [Rz (i + i') q] *)
Definition combine_rotations {dim} i i' q : Rzk_ucom_l dim :=
  let i'' := (i + i') mod (2 * Rzk_k) in
  if i'' =? 0 then [] else [Rz i'' q].

Lemma combine_rotations_semantics : forall {dim} i i' q, 
  (q < dim)%nat ->
  @uc_equiv_l dim (combine_rotations i' i q) ([Rz i' q] ++ [Rz i q]).
Proof.
  intros dim i i' q Hq.
  unfold combine_rotations.
  destruct ((i' + i) mod (2 * Rzk_k) =? 0)%Z eqn:eq;
  unfold uc_equiv_l, uc_equiv; simpl; rewrite Mmult_assoc, pad_mult;
  repeat rewrite phase_shift_rotation; rewrite phase_mul;
  repeat rewrite <- Rmult_div_assoc; rewrite <- Rmult_plus_distr_r, <- plus_IZR.
  rewrite Z.eqb_eq in eq. apply IZR_eq in eq.
  rewrite Rmult_div_assoc, phase_mod_2PI_scaled, Zplus_comm, eq.
  2: unfold Rzk_k; lia.
  autorewrite with R_db.
  rewrite phase_0. 
  autorewrite with eval_db; gridify; reflexivity.
  rewrite 2 Rmult_div_assoc.
  rewrite (phase_mod_2PI_scaled (i + i')), Zplus_comm.
  reflexivity.
  unfold Rzk_k; lia. 
Qed.

(* Invert a z-rotation. *)
Definition invert_rotation {dim} i q : gate_app Rzk_Unitary dim :=
  Rz (((2 * Rzk_k) - i) mod (2 * Rzk_k)) q.

(* Simplify common rotations. *)
Lemma Z_simplifies : phase_shift (IZR Rzk_k * PI / IZR Rzk_k) = phase_shift PI.
Proof. apply f_equal. unfold Rzk_k. lra. Qed.

Lemma P_simplifies : phase_shift (IZR (Rzk_k / 2) * PI / IZR Rzk_k) = phase_shift (PI/2).
Proof.
  apply f_equal.
  unfold Rzk_k.
  simpl. unfold Z.pow_pos, Z.mul. simpl.
  Local Transparent Z.sub.
  unfold Z.div. simpl.
  lra.
Qed.

Lemma T_simplifies : phase_shift (IZR (Rzk_k / 4) * PI / IZR Rzk_k) = phase_shift (PI/4).
Proof.
  apply f_equal.
  unfold Rzk_k.
  simpl. unfold Z.pow_pos, Z.mul. simpl.
  unfold Z.div. simpl.
  lra.
Qed.

Lemma PDAG_simplifies : phase_shift (IZR (3 * Rzk_k / 2) * PI / IZR Rzk_k) = phase_shift (- (PI/2)).
Proof.
  unfold phase_shift, Rzk_k.
  solve_matrix.
  unfold Z.pow_pos, Z.mul. simpl.
  unfold Z.div. simpl.
  replace (49152 * PI / 32768)%R with ((2 * PI) + -(PI/2))%R by lra.
  rewrite Cexp_add, Cexp_2PI. lca.
Qed.  

Lemma TDAG_simplifies : phase_shift (IZR (7 * Rzk_k / 4) * PI / IZR Rzk_k) = phase_shift (- (PI/4)).
Proof.
  unfold phase_shift, Rzk_k.
  solve_matrix.
  unfold Z.pow_pos, Z.mul. simpl.
  unfold Z.div. simpl.
  replace (57344 * PI / 32768)%R with ((2 * PI) + -(PI/4))%R by lra.
  rewrite Cexp_add, Cexp_2PI. lca.
Qed.  

