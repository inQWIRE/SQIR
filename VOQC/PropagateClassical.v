Require Import DensitySem.
Require Import RzQGateSet.
Require Import Coq.Reals.ROrderedType.

Module RzQProps := NonUListRepresentationProps RzQGateSet.
Export RzQProps.

Local Open Scope com_scope.

(* 'reset' and measurement put a qubit in a classical state and subsequent X / Rz 
   gates leave the qubit in a classical state. Using this idea, this optimization 
   tracks classical states to determine the effect of subsequent CNOTs and measurements.

   It currently only tracks the state of a single qubit at a time, but could be extended
   to handle qubit interactions.
*)

(** Useful facts about super and pad. *)

Local Coercion Nat.b2n : bool >-> nat.

Lemma super_Zero : forall {n} (ρ : Square n), 
  super Zero ρ = (@Zero n n).
Proof. intros. unfold super. Msimpl. reflexivity. Qed.

Lemma super_I : forall {n} (ρ : Square n), 
  WF_Matrix ρ -> super (I _) ρ = ρ.
Proof. intros. unfold super. Msimpl. reflexivity. Qed.

Lemma super_Mplus : forall {n} (A : Square n) ρ ρ', 
  super A ρ .+ super A ρ' = super A (ρ .+ ρ').
Proof.
  intros. unfold super. 
  rewrite <- Mmult_plus_distr_r.
  rewrite <- Mmult_plus_distr_l.
  reflexivity.
Qed.

Lemma super_Mmult : forall {n} (A B : Square n)  ρ,
  super (A × B) ρ = super A (super B ρ).
Proof. 
  intros. unfold super. 
  Msimpl. repeat rewrite Mmult_assoc. 
  reflexivity. 
Qed.

Lemma double_pad : forall dim n (b : bool) ρ, super (@pad 1 n dim (∣ b ⟩ × (∣ b ⟩) †)) (super (@pad 1 n dim (∣ b ⟩ × (∣ b ⟩) †)) ρ) = super (@pad 1 n dim (∣ b ⟩ × (∣ b ⟩) †)) ρ.
Proof.
  intros.
  rewrite <- super_Mmult. 
  unfold pad; destruct b; simpl; gridify.
  all: Qsimpl; reflexivity.
Qed.

Lemma double_pad01 : forall dim n ρ, super (@pad 1 n dim (∣ 0 ⟩ × (∣ 0 ⟩) †)) (super (@pad 1 n dim (∣ 1 ⟩ × (∣ 1 ⟩) †)) ρ) = Zero.
Proof.
  intros. rewrite <- super_Mmult. 
  unfold pad; simpl; gridify.
  Qsimpl. 
  all: apply super_Zero.
Qed.

Lemma double_pad10 : forall dim n ρ, super (@pad 1 n dim (∣ 1 ⟩ × (∣ 1 ⟩) †)) (super (@pad 1 n dim (∣ 0 ⟩ × (∣ 0 ⟩) †)) ρ) = Zero.
Proof.
  intros. rewrite <- super_Mmult. 
  unfold pad; simpl; gridify.
  Qsimpl. 
  all: apply super_Zero.
Qed.

(** Track classical states to remove unreachable code. **)

(* Inputs: list l, qubit q, classical state b (false = ∣0⟩, true = ∣1⟩)
   Outputs: modified list l', resulting classical state b' of qubit q
            (or None if we don't know whether q is in a classical state) *)
Fixpoint propagate_classical_through_ucom {dim} (l : RzQ_ucom_l dim) q b
    : RzQ_ucom_l dim * option bool :=
  match l with
  | App1 u q' :: t => 
      if q =? q' 
      then match u with
           (* X flips the classical state *)
           | URzQ_X => 
               let (l', b') := propagate_classical_through_ucom t q (negb b) in
               (App1 u q' :: l', b')
           (* Rz maintains the classical state *)
           | URzQ_Rz _ => 
               let (l', b') := propagate_classical_through_ucom t q b in
               (App1 u q' :: l', b')
           (* H takes the qubit out of a classical state *)
           | URzQ_H => (App1 u q' :: t, None)
           end
      else let (l' ,b') := propagate_classical_through_ucom t q b in
           (App1 u q' :: l', b')
  | App2 u q1 q2 :: t =>
      (* If the control of a CNOT is in a classical state, we can either remove 
         the CNOT or replace it with an X gate; being used as the target of a CNOT
         potentially takes q out of a classical state *)
      if q =? q1 
      then let (l', b') := propagate_classical_through_ucom t q b in
           if b 
           then (App1 URzQ_X q2 :: l', b')
           else (l', b')
      else if q =? q2 
           then (App2 u q1 q2 :: t, None)
           else let (l', b') := propagate_classical_through_ucom t q b in
                (App2 u q1 q2 :: l', b')
  | _ => ([], Some b)
  end.

(* Inputs: list l, qubit q, classical state b (false = ∣0⟩, true = ∣1⟩)
   Outputs: modified list l', resulting classical state b' of qubit q
            (or None if we don't know whether q is in a classical state) *)
Fixpoint propagate_classical_through_com {dim} (l : RzQ_com_l dim) q b n
    : RzQ_com_l dim * option bool :=
match n with
| O => (l, None) (* should be unreachable *)
| S n' =>
  match l with
  (* For unitary expressions, use the ucom function above *)
  | UC u :: t => let (u', b') := propagate_classical_through_ucom u q b in
               match b' with
               | None => (UC u' :: t, None)
               | Some b => let (t', b') := propagate_classical_through_com t q b n' in
                          (UC u' :: t', b')
               end
  (* For measurement, if we are measuring q:
     - Determine the branch that will be taken depending on b
     - Track the state of q through this branch, and possibly continue through 
       the rest of the instructions
     Otherwise:
     - Track the state of q through both branches
     - If both branches end up in the same state, continue through the rest of
       the instructions *)
  | Meas n l1 l2 :: t =>
      if q =? n 
      then if b 
           then let (l1', b') := propagate_classical_through_com l1 q b n' in
                match b' with
                | None => (l1' ++ t, None)
                | Some b => let (t', b') := propagate_classical_through_com t q b n' in
                           (l1' ++ t', b')
                end
           else let (l2', b') := propagate_classical_through_com l2 q b n' in
                match b' with
                | None => (l2' ++ t, None)
                | Some b => let (t', b') := propagate_classical_through_com t q b n' in
                           (l2' ++ t', b')
                end
      else let (l1', b1) := propagate_classical_through_com l1 q b n' in
           let (l2', b2) := propagate_classical_through_com l2 q b n' in
           match b1, b2 with
           | Some true, Some true => 
               let (t', b') := propagate_classical_through_com t q true n' in
               (Meas n l1' l2' :: t', b')
           | Some false, Some false =>
               let (t', b') := propagate_classical_through_com t q false n' in
               (Meas n l1' l2' :: t', b')
           | _, _ => (Meas n l1' l2' :: t, None)
           end
  | _ => ([], Some b)
  end
end.

(* Call propagate_classical_through_com for every branch of every measurement. *)
Fixpoint track_classical_state' {dim} (l : RzQ_com_l dim) n :=
match n with 
| O => l (* should be unreachable *)
| S n' =>
  match l with
  | [] => []
  | UC u :: t => UC u :: track_classical_state' t n'
  | Meas n l1 l2 :: t => 
      (* propagate true/false through the appropriate branch *)
      let (l1', b1) := propagate_classical_through_com l1 n true n' in
      let (l2', b2) := propagate_classical_through_com l2 n false n' in
      (* make recursive calls on the optimized branches *)
      let l1'' := track_classical_state' l1' n' in
      let l2'' := track_classical_state' l2' n' in
      match b1, b2 with
      (* in certain cases (e.g. 'reset') both branches will end up with q
         in the same classical state *)
      | Some true, Some true => 
          let (t', _) := propagate_classical_through_com t n true n' in
          Meas n l1'' l2'' :: track_classical_state' t' n'
      | Some false, Some false =>
          let (t', _) := propagate_classical_through_com t n false n' in
          Meas n l1'' l2'' :: track_classical_state' t' n'
      | _, _ => Meas n l1'' l2'' :: track_classical_state' t n'
      end
  end
end.

Definition track_classical_state {dim} (l : RzQ_com_l dim) :=
  track_classical_state' l (count_ops l).

(** Examples **)

(* Output: X 1 ; mif 1 then (H 2; X 0) else skip *)
Definition test1 : RzQ_com_l 3 := UC [X 1] :: Meas 1 [UC (H 2 :: [CNOT 1 0])] [UC [CNOT 1 2]] :: [].
Compute (track_classical_state test1).
(* Output: mif 0 then X 0 else skip *)
Definition test2 : RzQ_com_l 3 := Meas 0 [UC [X 0]] [] :: Meas 0 [UC [X 0]] [] :: [].
Compute (track_classical_state test2).
(* Output: reset 0 ; H 1 ; H 0 ; reset 0 *)
Definition test3 : RzQ_com_l 3 := Meas 0 [UC [X 0]] [] :: UC (H 1 :: [CNOT 0 1]) :: UC [H 0] :: Meas 0 [UC [X 0]] [] :: [].
Compute (track_classical_state test3).
(* Output: mif 1 then (X 2 ; Z 1 ; CNOT 2 0) else (H 0 ; X 1 ; X 2) ; reset 1 *)
Definition test4 : RzQ_com_l 3 := Meas 1 [UC (X 2 :: Z 1 :: [CNOT 2 0])] [UC (H 0 :: X 1 :: [CNOT 1 2])] :: Meas 1 [] [UC [X 1]] :: [].
Compute (track_classical_state test4).
(* Output: mif 0 then T 0 else PDAG 0 *)
Definition test5 : RzQ_com_l 3 := [Meas 0 [Meas 0 [UC [T 0]] [UC [TDAG 0]]] [Meas 0 [UC [P 0]] [UC [PDAG 0]]]].
Compute (track_classical_state test5).

(** Proofs **)

(* If qubit q is initially in classical state b and propagate_classical_through_ucom
   returns boolean b', then qubit q will be in classical state b' after running 
   program u. *)
Lemma propagate_classical_through_ucom_preserves_classical : forall dim (u : RzQ_ucom_l dim) q b u' b' ρ,
  uc_well_typed_l u ->
  WF_Matrix ρ ->
  propagate_classical_through_ucom u q b = (u', Some b') ->
  super (@pad 1 q dim (∣ b ⟩ × (∣ b ⟩)†)) ρ = ρ -> 
  let ρ' := super (uc_eval (list_to_ucom u)) ρ in
  super (@pad 1 q dim (∣ b' ⟩ × (∣ b' ⟩)†)) ρ' = ρ'.
Proof.
  intros dim u q b u' b' ρ WT WFρ res Hρ ρ'.
  generalize dependent ρ.
  generalize dependent u'.
  generalize dependent b.
  induction u; intros b u' res ρ WFρ Hρ ρ'; subst ρ'; rewrite <- Hρ.
  - (* u = [] *)
    apply uc_well_typed_l_implies_dim_nonzero in WT.
    inversion res; subst; simpl.
    rewrite denote_SKIP; auto. 
    rewrite super_I.
    2: destruct b';  auto with wf_db.
    rewrite <- super_Mmult.
    apply f_equal2; try reflexivity.
    unfold pad; destruct b'; simpl; gridify.
    all: Qsimpl; reflexivity.
  - (* u = a :: u *)
    simpl in res; destruct a as [p | p | p]; inversion WT; subst.
    + (* a = App1 p n *)
      bdestruct (q =? n).
      2: { destruct (propagate_classical_through_ucom u q b) eqn:prop.
           inversion res; subst; simpl.
           repeat rewrite super_Mmult.
           erewrite IHu; try apply prop; destruct b; auto with wf_db.
           all: repeat rewrite <- super_Mmult;
                apply f_equal2; try reflexivity;
                autorewrite with eval_db;
                bdestruct (q + 1 <=? dim).
           2,4: Msimpl; reflexivity.
           all: dependent destruction p; simpl.
           all: autorewrite with eval_db. 
           all: gridify; Qsimpl; reflexivity. }
      dependent destruction p; simpl; subst.
      * (* p = H *) 
        inversion res. 
      * (* p = X *)
        destruct (propagate_classical_through_ucom u n (negb b)) eqn:prop.
        inversion res; subst; simpl.
        repeat rewrite super_Mmult.
        erewrite IHu; try apply prop; destruct b;  auto with wf_db.
        all: repeat rewrite <- super_Mmult;
             apply f_equal2; try reflexivity;
             autorewrite with eval_db; gridify. 
        all: rewrite pauli_x_rotation; Qsimpl; reflexivity.
      * (* p = Rz *)
        destruct (propagate_classical_through_ucom u n b) eqn:prop.
        inversion res; subst; simpl.
        repeat rewrite super_Mmult.
        erewrite IHu; try apply prop; destruct b; auto with wf_db.
        all: repeat rewrite <- super_Mmult;
             apply f_equal2; try reflexivity;
             autorewrite with eval_db; gridify. 
        all: do 2 (apply f_equal2; try reflexivity).
        all: rewrite phase_shift_rotation; solve_matrix.
    + (* a = App2 u n n0 *)
      bdestruct (q =? n).
      2: { bdestruct (q =? n0).
           inversion res.
           destruct (propagate_classical_through_ucom u q b) eqn:prop.
           inversion res; subst; simpl.
           repeat rewrite super_Mmult.
           erewrite IHu; try apply prop; destruct b; auto with wf_db.
           all: repeat rewrite <- super_Mmult;
                apply f_equal2; try reflexivity;
                autorewrite with eval_db;
                bdestruct (q + 1 <=? dim).
           2,4: Msimpl; reflexivity.
           all: gridify; Qsimpl; reflexivity. }  
      destruct (propagate_classical_through_ucom u q b) eqn:prop.
      destruct b; inversion res; subst; simpl.
      * repeat rewrite super_Mmult.
        erewrite IHu; try apply prop; auto with wf_db.
        repeat rewrite <- super_Mmult.
        apply f_equal2; try reflexivity.
        autorewrite with eval_db. 
        gridify. 
        all: Qsimpl; reflexivity.
      * repeat rewrite super_Mmult.
        erewrite IHu; try apply prop; auto with wf_db.
        repeat rewrite <- super_Mmult.
        apply f_equal2; try reflexivity.
        autorewrite with eval_db. 
        gridify. 
        all: Qsimpl; reflexivity.
    + dependent destruction p.
Qed.

(* If qubit q is initially in classical state b then the program u' returned by
   propagate_classical_through_ucom will compute the same result as the original 
   program u. *)
Lemma propagate_classical_through_ucom_sound: forall dim (u : RzQ_ucom_l dim) q b u' b' ρ,
  uc_well_typed_l u ->
  propagate_classical_through_ucom u q b = (u', b') ->
  super (@pad 1 q dim (∣ b ⟩ × (∣ b ⟩)†)) ρ = ρ -> 
  super (uc_eval (list_to_ucom u)) ρ = super (uc_eval (list_to_ucom u')) ρ.
Proof.
  intros dim u q b u' b' ρ WT. 
  generalize dependent ρ.
  generalize dependent u'.
  generalize dependent b.
  induction u; intros b u' ρ res Hρ.
  inversion res; reflexivity.
  simpl in res.
  destruct a as [p | p | p].  
  - inversion WT; subst.
    bdestruct (q =? n). 
    2: { destruct (propagate_classical_through_ucom u q b) eqn:prop. 
         inversion res; subst; simpl.
         repeat rewrite super_Mmult.
         erewrite IHu; try apply prop; auto.
         rewrite <- Hρ.
         repeat rewrite <- super_Mmult.
         apply f_equal2; try reflexivity.
         autorewrite with eval_db. 
         bdestruct (q + 1 <=? dim).
         2: Msimpl; reflexivity.
         dependent destruction p; simpl.
         all: autorewrite with eval_db. 
         all: destruct b; gridify; Qsimpl; reflexivity. }
    dependent destruction p; simpl; subst.
    + inversion res; subst; simpl. reflexivity. 
    + destruct (propagate_classical_through_ucom u n (negb b)) eqn:prop.
      inversion res; subst; simpl.
      repeat rewrite super_Mmult.
      erewrite IHu; try apply prop; auto.
      rewrite <- Hρ.
      repeat rewrite <- super_Mmult.
      apply f_equal2; try reflexivity.
      autorewrite with eval_db. 
      destruct b; simpl; gridify. 
      all: rewrite pauli_x_rotation; Qsimpl; reflexivity.
    + destruct (propagate_classical_through_ucom u n b) eqn:prop.
      inversion res; subst; simpl.
      repeat rewrite super_Mmult.
      erewrite IHu; try apply prop; auto.
      rewrite <- Hρ.
      repeat rewrite <- super_Mmult.
      apply f_equal2; try reflexivity.
      autorewrite with eval_db. 
      destruct b; simpl; gridify. 
      all: do 2 (apply f_equal2; try reflexivity).
      all: rewrite phase_shift_rotation; solve_matrix.
  - inversion WT; subst.
    bdestruct (q =? n).
    2: { bdestruct (q =? n0).
         inversion res; subst; simpl. reflexivity.
         destruct (propagate_classical_through_ucom u q b) eqn:prop.
         inversion res; subst; simpl.
         repeat rewrite super_Mmult.
         erewrite IHu; try apply prop; auto.
         rewrite <- Hρ.
         repeat rewrite <- super_Mmult.
         apply f_equal2; try reflexivity.
         autorewrite with eval_db. 
         bdestruct (q + 1 <=? dim).
         2: Msimpl; reflexivity.
         destruct b; gridify; Qsimpl; reflexivity. }  
    destruct (propagate_classical_through_ucom u q b) eqn:prop.
    destruct b; inversion res; subst; simpl.
    all: repeat rewrite super_Mmult;
         erewrite IHu; try apply prop; auto.
    all: rewrite <- Hρ;
         repeat rewrite <- super_Mmult;
         repeat rewrite Mmult_assoc.
    all: apply f_equal2; try reflexivity.
    1, 3: apply f_equal2; try reflexivity.
    all: try rewrite pauli_x_rotation; simpl;
         autorewrite with eval_db.
    all: gridify. 
    all: Qsimpl; reflexivity.
  - dependent destruction p. 
Qed.

Lemma propagate_classical_through_com_preserves_classical : forall dim (l : RzQ_com_l dim) q b n l' b' ρ,
  (dim > 0)%nat ->
  c_well_typed_l l ->
  WF_Matrix ρ ->
  propagate_classical_through_com l q b n = (l', Some b') ->
  super (@pad 1 q dim (∣ b ⟩ × (∣ b ⟩)†)) ρ = ρ -> 
  let ρ' := c_eval (list_to_com l) ρ in
  super (@pad 1 q dim (∣ b' ⟩ × (∣ b' ⟩)†)) ρ' = ρ'.
Proof.
  intros dim l q b n l' b' ρ Hdim WT WFρ res Hρ ρ'.
  generalize dependent ρ.
  generalize dependent b'.
  generalize dependent l'.
  generalize dependent b.
  generalize dependent l.
  induction n; intros l WT b l' b' res ρ WFρ Hρ ρ'. 
  inversion res.
  simpl in res.
  destruct l; subst ρ'.
  inversion res; subst; simpl. assumption.
  destruct i.
  - (* i = UC u *)
    inversion WT; subst.
    simpl.
    rewrite instr_to_com_UC.
    destruct (propagate_classical_through_ucom g q b) eqn:prop_u.
    destruct o.
    2: inversion res.
    destruct (propagate_classical_through_com l q b0) eqn:prop_c.
    inversion res; subst.
    unfold compose_super; simpl.
    eapply IHn; try apply prop_c; auto with wf_db.
    eapply propagate_classical_through_ucom_preserves_classical; try apply prop_u; auto.
  - (* i = Meas n0 l1 l2 *)
    inversion WT; subst.
    simpl.
    rewrite instr_to_com_Meas.
    bdestruct (q =? n0).
    + (* measurement on qubit q *)
      subst. destruct b; simpl; unfold compose_super, Splus.
      all: rewrite <- Hρ; simpl;
           try rewrite double_pad with (b:=true);
           try rewrite double_pad with (b:=false);
           try rewrite double_pad01;
           try rewrite double_pad10;
           repeat rewrite c_eval_0; 
           Msimpl.  
      * (* take the true branch *)
        destruct (propagate_classical_through_com l0 n0 true n) eqn:propl0.
        destruct o.
        2: inversion res.
        destruct (propagate_classical_through_com l n0 b n) eqn:propl.
        inversion res; subst.
        eapply IHn; try apply propl; auto with wf_db.
        eapply IHn; try apply propl0; auto with wf_db.
        apply double_pad.
      * (* take the false branch *)
        destruct (propagate_classical_through_com l1 n0 false n) eqn:propl1.
        destruct o.
        2: inversion res.
        destruct (propagate_classical_through_com l n0 b n) eqn:propl.
        inversion res; subst.
        eapply IHn; try apply propl; auto with wf_db.
        eapply IHn; try apply propl1; auto with wf_db.
        apply double_pad.
    + (* measurement on a different qubit *)
      destruct (propagate_classical_through_com l0 q b n) eqn:propl0.
      destruct (propagate_classical_through_com l1 q b n) eqn:propl1.
      destruct o; destruct o0; try destruct b0; try destruct b1; simpl; unfold compose_super, Splus.
      (* most cases return None instead of Some b *)
      all: inversion res.
      (* two cases require the inductive hypothesis *)
      * destruct (propagate_classical_through_com l q true n) eqn:propl.
        inversion res; subst.
        eapply IHn; try apply propl; auto with wf_db.
        rewrite <- super_Mplus.
        apply f_equal2.
        1: eapply IHn; try apply propl0; auto with wf_db.
        2: eapply IHn; try apply propl1; auto with wf_db.
        all: rewrite <- Hρ; repeat rewrite <- super_Mmult; apply f_equal2; try reflexivity.
        all: unfold pad; destruct b; gridify.
        all: Qsimpl; reflexivity.
      * destruct (propagate_classical_through_com l q false n) eqn:propl.
        inversion res; subst.
        eapply IHn; try apply propl; auto with wf_db.
        rewrite <- super_Mplus.
        apply f_equal2.
        1: eapply IHn; try apply propl0; auto with wf_db.
        2: eapply IHn; try apply propl1; auto with wf_db.
        all: rewrite <- Hρ; repeat rewrite <- super_Mmult; apply f_equal2; try reflexivity.
        all: unfold pad; destruct b; gridify.
        all: Qsimpl; reflexivity.
Qed.

Lemma propagate_classical_through_com_sound: forall dim (l : RzQ_com_l dim) q b n l' b' ρ,
  (dim > 0)%nat ->
  c_well_typed_l l ->
  WF_Matrix ρ ->
  propagate_classical_through_com l q b n = (l', b') ->
  super (@pad 1 q dim (∣ b ⟩ × (∣ b ⟩)†)) ρ = ρ -> 
  c_eval (list_to_com l) ρ = c_eval (list_to_com l') ρ.
Proof.
  intros dim l q b n l' b' ρ Hdim WT WFρ res Hρ.
  generalize dependent ρ.
  generalize dependent b'.
  generalize dependent l'.
  generalize dependent b.
  generalize dependent l.
  induction n; intros l WT b l' b' res ρ WFρ Hρ. 
  inversion res; subst. reflexivity.
  simpl in res.
  destruct l.
  inversion res; subst. reflexivity.
  destruct i.
  - (* i = UC u *)
    inversion WT; subst.
    simpl.
    destruct (propagate_classical_through_ucom g q b) eqn:prop_u.
    destruct o.
    destruct (propagate_classical_through_com l q b0 n) eqn:prop_c.
    all: inversion res; subst; simpl; unfold compose_super.
    all: repeat rewrite instr_to_com_UC; simpl.
    all: erewrite <- propagate_classical_through_ucom_sound with (u:=g) (u':=r); 
         try apply prop_u; auto.
    eapply IHn; try apply prop_c; auto with wf_db.
    eapply propagate_classical_through_ucom_preserves_classical; try apply prop_u; auto.
  - (* i = Meas n0 l1 l2 *)
    inversion WT; subst.
    simpl.
    rewrite instr_to_com_Meas.
    bdestruct (q =? n0).
    + (* measurement on qubit q *)
      subst. destruct b; simpl; unfold compose_super, Splus.
      all: rewrite <- Hρ; simpl;
           try rewrite double_pad with (b:=true);
           try rewrite double_pad with (b:=false);
           try rewrite double_pad01;
           try rewrite double_pad10;
           repeat rewrite c_eval_0;
           Msimpl.  
      * (* take the true branch *)
        destruct (propagate_classical_through_com l0 n0 true n) eqn:propl0.
        destruct o.
        destruct (propagate_classical_through_com l n0 b n) eqn:propl.
        all: inversion res; subst.
        all: rewrite list_to_com_append; auto with wf_db;
             simpl; unfold compose_super.
        all: erewrite <- IHn with (l:=l0) (l':=r); try apply propl0; auto with wf_db.
        erewrite <- propagate_classical_through_com_preserves_classical with (l:=l0); try apply propl0; auto with wf_db.
        all: try apply double_pad with (b:=true).
        eapply IHn; try apply propl; destruct b; auto with wf_db. 
        all: apply double_pad.
      * (* take the false branch *)
        destruct (propagate_classical_through_com l1 n0 false n) eqn:propl1.
        destruct o.
        destruct (propagate_classical_through_com l n0 b n) eqn:propl.
        all: inversion res; subst.
        all: rewrite list_to_com_append; auto with wf_db;
             simpl; unfold compose_super.
        all: erewrite <- IHn with (l:=l1) (l':=r); try apply propl1; auto with wf_db.
        erewrite <- propagate_classical_through_com_preserves_classical with (l:=l1); try apply propl1; auto with wf_db.
        all: try apply double_pad.
        eapply IHn; try apply propl; destruct b; auto with wf_db. 
        all: apply double_pad.
    + (* measurement on a different qubit *)
      destruct (propagate_classical_through_com l0 q b n) eqn:propl0.
      destruct (propagate_classical_through_com l1 q b n) eqn:propl1.
      assert (Haux1 : super (@pad 1 q dim (∣ b ⟩ × (∣ b ⟩) †)) (super (@pad 1 n0 dim (∣1⟩ × (∣1⟩) †)) ρ) = super (@pad 1 n0 dim (∣1⟩ × (∣1⟩) †)) ρ).
      { rewrite <- Hρ; clear - H. 
        repeat rewrite <- super_Mmult; apply f_equal2; try reflexivity.
        unfold pad; destruct b; gridify.
        all: Qsimpl; reflexivity. }
      assert (Haux2 : super (@pad 1 q dim (∣ b ⟩ × (∣ b ⟩) †)) (super (@pad 1 n0 dim (∣0⟩ × (∣0⟩) †)) ρ) = super (@pad 1 n0 dim (∣0⟩ × (∣0⟩) †)) ρ).
      { rewrite <- Hρ; clear - H. 
        repeat rewrite <- super_Mmult; apply f_equal2; try reflexivity.
        unfold pad; destruct b; gridify.
        all: Qsimpl; reflexivity. }
      destruct o; destruct o0; try destruct b0; try destruct b1.
      destruct (propagate_classical_through_com l q true n) eqn:propl.
      4: destruct (propagate_classical_through_com l q false n) eqn:propl.
      all: inversion res; subst; simpl.
      all: rewrite instr_to_com_Meas.
      all: simpl; unfold compose_super, Splus.
      (* most cases only require (IHn l0) and (IHn l1) *)
      all: erewrite <- IHn with (l:=l0) (l':=r); try apply propl0; auto with wf_db.
      all: erewrite <- IHn with (l:=l1) (l':=r0); try apply propl1; auto with wf_db.
      (* two cases require propagate_classical_through_com_preserves_classical *)
      * eapply IHn; try apply propl; auto with wf_db.
        rewrite <- super_Mplus.
        apply f_equal2.
        eapply propagate_classical_through_com_preserves_classical; try apply propl0; auto with wf_db.
        eapply propagate_classical_through_com_preserves_classical; try apply propl1; auto with wf_db.
      * eapply IHn; try apply propl; auto with wf_db.
        rewrite <- super_Mplus.
        apply f_equal2.
        eapply propagate_classical_through_com_preserves_classical; try apply propl0; auto with wf_db.
        eapply propagate_classical_through_com_preserves_classical; try apply propl1; auto with wf_db.
Qed.

Lemma propagate_classical_through_ucom_WT: forall dim (u : RzQ_ucom_l dim) q b u' b',
  uc_well_typed_l u ->
  propagate_classical_through_ucom u q b = (u', b') ->
  uc_well_typed_l u'.
Proof.
  intros dim u q b u' b' WT. 
  generalize dependent u'.
  generalize dependent b.
  induction u; intros b u' res.
  inversion res; constructor.
  apply (uc_well_typed_l_implies_dim_nonzero _ WT).
  simpl in res.
  destruct a as [p | p | p]; inversion WT; subst.  
  - bdestruct (q =? n). 
    2: destruct (propagate_classical_through_ucom u q b) eqn:prop. 
    dependent destruction p; subst.
    2: destruct (propagate_classical_through_ucom u n (negb b)) eqn:prop.
    3: destruct (propagate_classical_through_ucom u n b) eqn:prop.
    all: inversion res; subst; constructor; auto.
    all: eapply IHu; try apply prop; auto.
  - bdestruct (q =? n).
    destruct (propagate_classical_through_ucom u q b) eqn:prop.
    destruct b.
    3: bdestruct (q =? n0).
    4: destruct (propagate_classical_through_ucom u q b) eqn:prop.
    all: inversion res; subst; try constructor; auto.
    all: eapply IHu; try apply prop; auto.
  - dependent destruction p. 
Qed.

Lemma c_well_typed_l_app : forall {dim} (l1 l2 : RzQ_com_l dim),
  c_well_typed_l l1 /\ c_well_typed_l l2 <-> c_well_typed_l (l1 ++ l2).
Proof.
  intros; split.  
  - intros [Hl1 Hl2]. 
    induction Hl1; simpl; try constructor; assumption.
  - intros H.
    induction l1. 
    + split; simpl in H; try constructor; try assumption.
    + inversion H; subst;
      match goal with
      | H : c_well_typed_l (?l1 ++ ?l2) |- _ => apply IHl1 in H as [? ?]
      end;
      split; try constructor; assumption.
Qed.

Lemma propagate_classical_through_com_WT : forall dim (l : RzQ_com_l dim) q b n l' b',
  c_well_typed_l l ->
  propagate_classical_through_com l q b n = (l', b') ->
  c_well_typed_l l'.
Proof.
  intros.
  generalize dependent b'.
  generalize dependent l'.
  generalize dependent b.
  generalize dependent l.
  induction n; intros l WT b l' b' res. 
  inversion res; subst. assumption.
  simpl in res.
  destruct l.
  inversion res; subst. assumption.
  destruct i; inversion WT; subst.
  - (* i = UC u *)
    destruct (propagate_classical_through_ucom g q b) eqn:prop_u.
    destruct o.
    destruct (propagate_classical_through_com l q b0 n) eqn:prop_c.
    all: inversion res; subst; constructor; auto.
    all: try eapply propagate_classical_through_ucom_WT; try apply prop_u; auto.
    eapply IHn; try apply prop_c; auto.
  - (* i = Meas n0 l1 l2 *)
    bdestruct (q =? n0).
    + destruct b.
      all: try destruct (propagate_classical_through_com l0 q true n) eqn:propl0.
      all: try destruct (propagate_classical_through_com l1 q false n) eqn:propl1.
      all: try destruct o; try destruct o0.
      all: try destruct (propagate_classical_through_com l q b n) eqn:propl.
      all: try destruct (propagate_classical_through_com l q b0 n) eqn:propl'.
      all: inversion res; subst.
      all: try (apply c_well_typed_l_app; split). 
      all: try constructor; auto.
      all: eapply IHn; try apply propl0; try apply propl1; try apply propl; try apply propl'; auto.
    + destruct (propagate_classical_through_com l0 q b n) eqn:propl0.
      destruct (propagate_classical_through_com l1 q b n) eqn:propl1.
      destruct o; try destruct o0; try destruct b0; try destruct b1.
      all: try destruct (propagate_classical_through_com l q true n) eqn:proplT.
      all: try destruct (propagate_classical_through_com l q false n) eqn:proplF.
      all: inversion res; subst; constructor; auto.
      all: eapply IHn; try apply propl0; try apply propl1; try apply proplT; try apply proplF; auto.
Qed.

Lemma track_classical_state_sound : forall dim (l : RzQ_com_l dim),
  c_well_typed_l l ->
  track_classical_state l =l= l.
Proof.
  intros.
  unfold track_classical_state.
  remember (count_ops l) as n; clear Heqn.
  generalize dependent l.
  induction n; try reflexivity.
  intros l WT; simpl.
  destruct l; try reflexivity.
  destruct i.
  inversion WT; subst.
  rewrite IHn; try assumption; reflexivity.
  inversion WT; subst.
  destruct (propagate_classical_through_com l0 n0 true n) eqn:propl0.
  destruct (propagate_classical_through_com l1 n0 false n) eqn:propl1.
  unfold c_equiv_l, c_equiv.
  intros Hdim ρ WFρ.
  destruct o; destruct o0; try destruct b; try destruct b0.
  (* two cases where we call propagate on the tail of the list *)
  1: destruct (propagate_classical_through_com l n0 true n) eqn:propl.
  4: destruct (propagate_classical_through_com l n0 false n) eqn:propl.
  1,4: simpl;
       repeat rewrite instr_to_com_Meas;
       simpl; unfold compose_super, Splus;
       repeat rewrite IHn; auto with wf_db.
  all: try eapply propagate_classical_through_com_WT;
       try apply propl0; try apply propl1; try apply propl; auto.
  1,2: erewrite <- propagate_classical_through_com_sound with (l':=r);
       try apply propl0; auto with wf_db; try apply double_pad.
  1,2: erewrite <- propagate_classical_through_com_sound with (l':=r0); 
       try apply propl1; auto with wf_db; try apply double_pad.
  1,2: erewrite propagate_classical_through_com_sound with (l:=l); 
       try apply propl; auto with wf_db.
  1,2: erewrite <- propagate_classical_through_com_preserves_classical with (l:=l0);
       try apply propl0; auto with wf_db; try apply double_pad.
  1,2: erewrite <- propagate_classical_through_com_preserves_classical with (l:=l1);
       try apply propl1; auto with wf_db; try apply double_pad.
  1,2: rewrite super_Mplus.
  1,2: apply double_pad.
  (* all other cases are the same *)
  all: apply Meas_cons_congruence; try apply IHn; auto.
  all: intros; unfold c_eval_l, project_onto. 
  all: try rewrite (IHn r); auto with wf_db.
  all: try eapply propagate_classical_through_com_WT with (l:=l0) (l':=r); try apply propl0; auto.
  all: try erewrite propagate_classical_through_com_sound with (l:=l0) (l':=r); try apply propl0; auto with wf_db.
  all: try apply double_pad.
  all: try rewrite (IHn r0); auto with wf_db.
  all: try eapply propagate_classical_through_com_WT with (l:=l1) (l':=r0); try apply propl1; auto.
  all: try erewrite propagate_classical_through_com_sound with (l:=l1) (l':=r0); try apply propl1; auto with wf_db.
  all: try apply double_pad.
Qed.