Require Import UnitarySem.
Require Import PI4GateSet.
Require Import Equivalences.
Require Import Proportional.
Require Import List.
Open Scope ucom.

Local Close Scope C_scope.
Local Close Scope R_scope.

(***********************************)
(** Optimization: not propagation **)
(***********************************)

(* Propagate an X gate on qubit q as far right as possible, cancelling
   the gate if possible.
   
   This will return None if no cancellation is possible or (Some l') 
   where l' is the result of removing the appropriate X gate from l. *)
Fixpoint propagate_not {dim} (l : PI4_list dim) (q : nat) : option (PI4_list dim) :=
  match l with
  | (App1 UPI4_X q') :: t => 
      if q =? q' then Some t 
      else match propagate_not t q with
           | None => None
           | Some l' => Some ((App1 UPI4_X q') :: l')
           end
  | (App2 UPI4_CNOT q1 q2) :: t => 
      if q =? q1 then None 
      else match propagate_not t q with
           | None => None
           | Some l' => Some ((App2 UPI4_CNOT q1 q2) :: l')
           end
  | (App1 u q') :: t => 
      if (q =? q')
      then None
      else match propagate_not t q with
           | None => None
           | Some l' => Some ((App1 u q') :: l')
           end
  | _ => None
  end.

(* Call propagate_not on all X gates in the circuit. 
   
   The extra n argument is to help Coq recognize termination.
   We start with n = (length l), which is the maximum
   number of times that propagate_nots will be called. *)
Fixpoint propagate_nots {dim} (l : PI4_list dim) (n: nat) : PI4_list dim :=
  match n with
  | 0 => l
  | S n' => match l with
           | (App1 UPI4_X q) :: t => 
               match propagate_not t q with
               | None => (App1 UPI4_X q) :: (propagate_nots t n')
               | Some l' => propagate_nots l' n'
               end
           | h :: t => h :: (propagate_nots t n')
           | _ => l
           end
  end.

Definition rm_nots {dim} (l : PI4_list dim) : PI4_list dim := 
  propagate_nots l (List.length l).

(* Small test cases. *)
Definition q0 : nat := 0.
Definition q1 : nat := 1.
Definition q2 : nat := 2.
Definition example1 : PI4_list 3 := (App1 UPI4_X q0) :: (App1 UPI4_H q1) :: (App1 UPI4_X q0) :: (App1 UPI4_X q1) :: (App2 UPI4_CNOT q2 q1) :: (App1 UPI4_X q1) :: [].
Compute (rm_nots example1).
Definition example2 : PI4_list 3 := (App1 UPI4_X q0) :: (App1 UPI4_X q1) :: (App1 UPI4_X q2) :: [].
Compute (rm_nots example2).

(* propagate_not preserves well-typedness. *)
Lemma propagate_not_WT : forall {dim} (l l' : PI4_list dim) q,
  uc_well_typed_l l ->
  propagate_not l q = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  generalize dependent l'.
  induction l; try easy.
  simpl; intros.
  destruct a. 
  dependent destruction p; 
  (* u = H, Z, T, TDAG, P, PDAG *)
  try (destruct (q =? n); try easy;
       destruct (propagate_not l q); try easy;
       inversion H; inversion H0; subst;
       constructor; try apply IHl; easy).
  - (* u = X *)
    destruct (q =? n).
    + inversion H; inversion H0; subst. assumption.
    + destruct (propagate_not l q); try easy.
      inversion H; inversion H0; subst.
      constructor; try apply IHl; easy.
  - (* u = CNOT *)
    dependent destruction p.
    destruct (q =? n); try easy.
    destruct (propagate_not l q); try easy.
    inversion H; inversion H0; subst.
    constructor; try apply IHl; easy.
  - inversion p.
Qed.

(* propagate_not is semantics-preserving. *)
Lemma propagate_not_sound : forall {dim} (l l' : PI4_list dim) q,
  q < dim ->
  propagate_not l q = Some l' ->
  l' =l= (App1 UPI4_X q) :: l.
Proof.
  intros.
  generalize dependent l'.
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
Lemma propagate_nots_sound : forall {dim} (l : PI4_list dim) n, 
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
  try (apply (cons_congruence _ l (propagate_nots l n));
       apply IHn; assumption).
  (* u = X *)
  - specialize (@propagate_not_sound dim) as H4.
    destruct (propagate_not l n0) eqn:prop.
    + specialize (H4 l p n0 H1 prop).
      rewrite <- H4.
      apply IHn.
      apply (propagate_not_WT l p n0); assumption.
    + apply (cons_congruence _ l (propagate_nots l n));
      apply IHn; assumption.
  (* u = CNOT *)
  - inversion WT; subst. 
    apply (cons_congruence _ l (propagate_nots l n)).
    apply IHn; assumption.
  - inversion p.
Qed.

(* rm_nots is semantics-preserving. 
   
   The well-typedness constraint is required because rm_nots can actually
   return a well-typed circuit given a circuit that is not well-typed.
     ==> Consider the program X 4; X 4 where dim = 3
   The output of the denotation function may change in this case. 
*)
Lemma rm_nots_sound : forall {dim} (l : PI4_list dim), 
  uc_well_typed_l l -> l =l= rm_nots l.
Proof.
  intros dim l WT.
  unfold rm_nots.
  rewrite <- propagate_nots_sound.
  reflexivity.
  assumption.
Qed.

