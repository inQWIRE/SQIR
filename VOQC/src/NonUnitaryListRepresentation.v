Require Export UnitaryListRepresentation.
Require Export DensitySem. 

Local Open Scope com_scope.
Local Close Scope R_scope.
Local Open Scope signature_scope.

(* This file extends UnitaryListrepresentation with a 'list of lists' 
   representation for non-unitary programs. *)

(** List-of-lists representation for non-unitary programs. **)

Inductive instr (U : nat -> Set) (dim : nat): Set :=
| UC : gate_list U dim -> instr U dim
| Meas : nat -> list (instr U dim) -> list (instr U dim) -> instr U dim.

Definition com_list U dim := list (instr U dim).

Arguments UC {U} {dim}.
Arguments Meas {U} {dim}.

(** Useful operations on the com list representation. **)

Fixpoint does_not_reference_instr {U dim} q (i : instr U dim) :=
  match i with 
  | UC u => does_not_reference u q
  | Meas n l1 l2 => 
      negb (q =? n) && 
      forallb (does_not_reference_instr q) l1 && 
      forallb (does_not_reference_instr q) l2
  end.
Definition does_not_reference_c {U dim} (l : com_list U dim) (q : nat) :=
  forallb (does_not_reference_instr q) l.

(* Get the next measurement operation on qubit q. *)
Fixpoint next_measurement {U dim} (l : com_list U dim) q :=
  match l with
  | [] => None
  | UC u :: t => 
      if does_not_reference u q 
      then match next_measurement t q with
           | None => None
           | Some (l1, l1', l2', l2) => 
               Some (UC u :: l1, l1', l2', l2)
           end
      else None
  | Meas n l1 l2 :: t => 
      if q =? n
      then Some ([], l1, l2, t)
      else if does_not_reference_c l1 q && does_not_reference_c l2 q
           then match next_measurement t q with
                | None => None
                | Some (l1', l1'', l2'', l2') => 
                    Some (Meas n l1 l2 :: l1', l1'', l2'', l2')
                end
           else None
  end.

(* Count the number of UC/Meas operations in a non-unitary program. This is useful
   when we're too lazy to write functions in a nested recursive style & use the
   special induction principle 'com_list_ind'. Instead, we can use the result of
   this function as initial fuel to a function and recurse on the size of the fuel.
   (This only works if the function in question performs N operations where N
   can be over-approximated by an expression involving count_ops.) *)
Fixpoint count_ops_instr {U dim} (i : instr U dim) :=
  match i with
  | UC u => 1%nat
  | Meas n l1 l2 =>
      let fix f l := match l with
                     | [] => O
                     | h :: t => (count_ops_instr h + f t)%nat
                     end in
      (1 + f l1 + f l2)%nat
  end.
Fixpoint count_ops {U dim} (l : com_list U dim) :=
  match l with
  | [] => O
  | h :: t => (count_ops_instr h + count_ops t)%nat
  end.

(* 'canonicalize' a non-unitary program by combining adjacent UC terms and
   removing empty UC terms. This will allow for more effective application 
   of unitary optimizations (and nicer printing). *)
Fixpoint canonicalize_com_l' {U dim} (l : com_list U dim) n : com_list U dim :=
  match n with
  | O => l
  | S n' => match l with
           | [] => []
           | Meas n l1 l2 :: t => 
               let l1' := canonicalize_com_l' l1 n' in
               let l2' := canonicalize_com_l' l2 n' in
               Meas n l1' l2' :: (canonicalize_com_l' t n')
           | UC [] :: t => canonicalize_com_l' t n'
           | UC u1 :: UC u2 :: t => canonicalize_com_l' ((UC (u1 ++ u2)) :: t) n'
           
           | h :: t => h :: (canonicalize_com_l' t n')
           end
  end.
Definition canonicalize_com_l {U dim} (l : com_list U dim) :=
  canonicalize_com_l' l (count_ops l).

Module NonUListRepresentationProps (G : GateSet).

Module UProps := UListRepresentationProps G.
Export UProps.

(** Correctness properties for non-unitary programs. **)

(* Well-typedness *)
Inductive c_well_typed_l {dim} : com_list G.U dim -> Prop :=
| WT_nilc : c_well_typed_l []
| WT_UC : forall u t, uc_well_typed_l u -> c_well_typed_l t -> c_well_typed_l ((UC u) :: t)
| WT_Meas : forall n l1 l2 t, (n < dim)%nat -> c_well_typed_l l1 -> c_well_typed_l l2 
            -> c_well_typed_l t -> c_well_typed_l ((Meas n l1 l2) :: t).

(* Induction principle for com_list *)
Section com_list_ind.
  Variable U : nat -> Set.
  Variable dim : nat.
  Variable P : com_list U dim -> Prop.

  Hypothesis Nil_case : P ([] : com_list U dim).
  Hypothesis UC_case : forall (u : gate_list U dim) t,
    P t -> P ((UC u) :: t).
  Hypothesis Meas_case : forall n (l1 l2 : com_list U dim) t,
    P l1 -> P l2 -> P t -> P ((Meas n l1 l2) :: t).

  Fixpoint instr_ind_aux (i : instr U dim) :=
    match i with
    | UC u => (fun t Pft => UC_case u t Pft)
    | Meas n l1 l2 => 
        let fix f (l : com_list U dim) :=
           match l with
           | [] => Nil_case
           | h :: t => instr_ind_aux h t (f t)
           end in
        (fun t Pft => Meas_case n l1 l2 t (f l1) (f l2) Pft)
    end.

  Fixpoint com_list_ind (l : com_list U dim) : P l :=
    match l with
    | [] => Nil_case
    | h :: t => instr_ind_aux h t (com_list_ind t)
    end.

End com_list_ind.

(* Conversion to the base gate set - written awkwardly to convince Coq of 
   termination. *)
Fixpoint instr_to_com {dim} (i : instr G.U dim) : base_com dim :=
  match i with 
  | UC u => uc (list_to_ucom u)
  | Meas n l1 l2 => 
      let fix f l := match l with
                     | [] => skip
                     | h :: t => instr_to_com h ; f t
                     end in
      meas n (f l1) (f l2)
  end.
Fixpoint list_to_com {dim} (l : com_list G.U dim) : base_com dim :=
  match l with
  | [] => skip
  | h :: t => instr_to_com h ; list_to_com t
  end.

Lemma instr_to_com_UC : forall dim (u : gate_list G.U dim),
  instr_to_com (UC u) = uc (list_to_ucom u).
Proof. intros. reflexivity. Qed.

Lemma instr_to_com_Meas : forall dim n (l1 : com_list G.U dim) l2,
  instr_to_com (Meas n l1 l2) = meas n (list_to_com l1) (list_to_com l2).
Proof.
  intros.
  simpl.
  apply f_equal2.
  - induction l1; try rewrite IHl1; reflexivity.
  - induction l2; try rewrite IHl2; reflexivity.
Qed.
Global Opaque instr_to_com.
Hint Rewrite instr_to_com_UC instr_to_com_Meas.

Lemma list_to_com_append : forall {dim} (l1 l2 : com_list G.U dim),
  list_to_com (l1 ++ l2) ≡ list_to_com l1 ; list_to_com l2.
Proof.
  intros dim l1 l2.
  unfold c_equiv.
  induction l1; simpl; try reflexivity.
  destruct a; simpl; intros;
  unfold compose_super; rewrite IHl1; 
  auto with wf_db.
Qed.

Lemma list_to_com_WT : forall {dim} (l : com_list G.U dim), 
  c_well_typed_l l <-> c_well_typed (list_to_com l).
Proof.
  intros; split; intros H.
  - induction H; constructor; 
    try rewrite instr_to_com_UC; try rewrite instr_to_com_Meas; try constructor; 
    auto.
    apply list_to_ucom_WT. assumption.
  - induction l using com_list_ind;inversion H; subst;
    try rewrite instr_to_com_UC in H2; try rewrite instr_to_com_Meas in H2; try inversion H2; subst;
    constructor; auto.
    apply list_to_ucom_WT. assumption.
Qed.

(** Equivalences over non-unitary programs. **)

Definition c_equiv_l {dim} (l1 l2 : com_list G.U dim) := 
  list_to_com l1 ≡ list_to_com l2.
Infix "=l=" := c_equiv_l (at level 70) : com_scope.

Lemma c_equiv_l_refl : forall {dim} (l1 : com_list G.U dim), l1 =l= l1.
Proof. easy. Qed.
 
Lemma c_equiv_l_sym : forall {dim} (l1 l2 : com_list G.U dim), l1 =l= l2 -> l2 =l= l1.
Proof. unfold c_equiv_l. easy. Qed.
 
Lemma c_equiv_l_trans : forall {dim} (l1 l2 l3 : com_list G.U dim), 
  l1 =l= l2 -> l2 =l= l3 -> l1 =l= l3.
Proof. unfold c_equiv_l. intros dim l1 l2 l3 H12 H23. rewrite H12. easy. Qed.

Lemma c_cons_congruence : forall {dim} (i : instr G.U dim)  (l l' : com_list G.U dim),
  l =l= l' ->
  i :: l =l= i :: l'.
Proof.
  unfold c_equiv_l.
  intros dim i l l' Hl.  
  simpl. rewrite Hl. reflexivity.
Qed.

Lemma c_app_congruence : forall {dim} (l1 l1' l2 l2' : com_list G.U dim),
  l1 =l= l1' ->
  l2 =l= l2' ->
  l1 ++ l2 =l= l1' ++ l2'.
Proof.
  unfold c_equiv_l.
  intros dim l1 l1' l2 l2' Hl1 Hl2.
  repeat rewrite list_to_com_append; simpl.
  rewrite Hl1, Hl2.
  reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (com_list G.U dim) (@c_equiv_l dim)
  reflexivity proved by c_equiv_l_refl
  symmetry proved by c_equiv_l_sym
  transitivity proved by c_equiv_l_trans
  as c_equiv_l_rel.

Add Parametric Morphism (dim : nat) : (@List.cons (instr G.U dim))
  with signature eq ==> (@c_equiv_l dim) ==> (@c_equiv_l dim) as c_cons_mor.
Proof. intros y x0 y0 H0. apply c_cons_congruence; easy. Qed.

Add Parametric Morphism (dim : nat) : (@app (instr G.U dim))
  with signature (@c_equiv_l dim) ==> (@c_equiv_l dim) ==> (@c_equiv_l dim) as c_app_mor.
Proof. intros x y H x0 y0 H0. apply c_app_congruence; easy. Qed.

Lemma uc_equiv_l_implies_c_equiv_l : forall dim (u u' : gate_list G.U dim),
  (u =l= u')%ucom ->
  [UC u] =l= [UC u'].
Proof.
  unfold uc_equiv_l, uc_equiv, c_equiv_l, c_equiv.
  intros dim u u' H Hdim ρ WFρ.
  simpl.
  repeat rewrite instr_to_com_UC.
  simpl; rewrite H; reflexivity.
Qed.

Lemma UC_append : forall {dim} (l1 l2: gate_list G.U dim), 
  [UC (l1 ++ l2)] =l= [UC l1] ++ [UC l2].
Proof. 
  intros.
  unfold c_equiv_l, c_equiv; simpl.
  intros.
  repeat rewrite instr_to_com_UC; simpl.
  rewrite list_to_ucom_append; simpl.
  rewrite compose_super_assoc. 
  unfold compose_super, super. Msimpl.
  repeat rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma UC_nil : forall dim, 
  [UC []] =l= ([] : com_list G.U dim).
Proof.
  unfold c_equiv_l, c_equiv.
  intros; simpl.
  rewrite instr_to_com_UC; simpl.
  unfold compose_super, super. 
  rewrite denote_SKIP; try assumption.
  Msimpl; reflexivity.
Qed.

(* Also useful to have a congruence lemma for rewriting inside Meas. *)
Definition c_eval_l {dim} (l : com_list G.U dim) := c_eval (list_to_com l).
Local Coercion Nat.b2n : bool >-> nat.
Definition project_onto {dim} ρ n (b : bool) := super (@pad 1 n dim (∣b⟩ × ∣b⟩†)) ρ.
Lemma Meas_cons_congruence : forall dim n (l1 l2 l1' l2' l l' : com_list G.U dim),
  (forall ρ, WF_Matrix ρ ->
   c_eval_l l1 (project_onto ρ n true) = c_eval_l l1' (project_onto ρ n true)) ->
  (forall ρ, WF_Matrix ρ ->
   c_eval_l l2 (project_onto ρ n false) = c_eval_l l2' (project_onto ρ n false)) ->
  l =l= l' ->
  Meas n l1 l2 :: l =l= Meas n l1' l2' :: l'.
Proof.
  intros.
  unfold c_equiv_l; simpl.
  repeat rewrite instr_to_com_Meas.
  apply seq_congruence; auto.
  unfold c_equiv; simpl.
  intros Hdim ρ WFρ.
  unfold Splus, compose_super; simpl.
  unfold c_eval_l, project_onto in *.
  simpl in *.
  rewrite H, H0; auto.
Qed.

Lemma does_not_reference_instr_UC : forall dim q (u : gate_list G.U dim),
  does_not_reference_instr q (UC u) = does_not_reference u q.
Proof. intros. reflexivity. Qed.

Lemma does_not_reference_instr_Meas : forall dim q n (l1 : com_list G.U dim) l2,
  does_not_reference_instr q (Meas n l1 l2) = negb (q =? n) && does_not_reference_c l1 q && does_not_reference_c l2 q.
Proof.
  intros.
  simpl.
  apply f_equal2; [apply f_equal2 |].
  - reflexivity.
  - induction l1; simpl; try rewrite IHl1; reflexivity.
  - induction l2; simpl; try rewrite IHl2; reflexivity.
Qed.
Global Opaque does_not_reference_instr.

Lemma next_measurement_preserves_structure : forall dim (l : com_list G.U dim) q l1 l1' l2' l2,
  next_measurement l q = Some (l1, l1', l2', l2) ->
  l = l1 ++ [Meas q l1' l2'] ++ l2.
Proof.
  intros.
  generalize dependent l1.
  induction l; intros.
  - inversion H.
  - simpl in H.
    destruct a.
    + destruct (does_not_reference g q); try discriminate.
      destruct (next_measurement l q); try discriminate.
      do 3 destruct p.
      inversion H; subst.
      rewrite IHl with (l1:=l4); reflexivity.
    + bdestruct (q =? n).
      inversion H; subst. reflexivity.
      destruct (does_not_reference_c l0 q && does_not_reference_c l3 q); try discriminate.
      destruct (next_measurement l q); try discriminate.
      do 3 destruct p.
      inversion H; subst.
      rewrite IHl with (l1:=l6); reflexivity.
Qed.  

Lemma next_measurement_l1_does_not_reference : forall {dim} (l : com_list G.U dim) q l1 l1' l2' l2,
  next_measurement l q = Some (l1, l1', l2', l2) ->
  does_not_reference_c l1 q = true.
Proof.
  intros.
  generalize dependent l1.
  induction l; intros.
  - inversion H.
  - simpl in H.
    destruct a.
    + destruct (does_not_reference g q) eqn:dnr; try discriminate.
      destruct (next_measurement l q) eqn:nm; try discriminate.
      do 3 destruct p.
      inversion H; subst.
      simpl.
      apply andb_true_intro; split.
      assumption.
      rewrite IHl with (l1:=l4); reflexivity.
    + bdestruct (q =? n).
      inversion H; subst. reflexivity.
      destruct (does_not_reference_c l0 q) eqn:dnrl0. 
      destruct (does_not_reference_c l3 q) eqn:dnrl3.
      all: simpl in H; try discriminate.
      destruct (next_measurement l q) eqn:Hnm; try discriminate.
      do 3 destruct p.
      inversion H; subst.
      simpl.
      rewrite does_not_reference_instr_Meas.
      repeat (try apply andb_true_intro; split).
      apply negb_true_iff; apply eqb_neq; assumption.
      all: try assumption.
      rewrite IHl with (l1:=l6); reflexivity.
Qed.

Lemma does_not_reference_c_commutes_app1 : forall {dim} (l : com_list G.U dim) u q,
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
    repeat rewrite list_to_com_append in Hl1, Hl2.
    simpl in *.
    rewrite instr_to_com_UC in *.
    rewrite instr_to_com_Meas in *.
    unfold c_equiv in *; simpl in *.
    intros Hdim ρ WFρ.
    unfold compose_super, Splus in *.
    rewrite denote_SKIP in *; try assumption.
    rewrite Mmult_1_l in *; try auto with wf_db.
    remember (ueval_r dim q (G.to_base u)) as U.
    remember (pad n dim (∣1⟩ × (∣1⟩) †)) as pad1.
    remember (pad n dim (∣0⟩ × (∣0⟩) †)) as pad0.
    replace (super pad1 (super U ρ)) with (super U (super pad1 ρ)).
    2: { subst; clear - Hq.
         unfold super.
         autorewrite with eval_db.
         bdestruct (n + 1 <=? dim)%nat; try (Msimpl; reflexivity).
         remember (G.to_base u) as u'.
         dependent destruction u'.
         autorewrite with eval_db.
         bdestruct (q + 1 <=? dim)%nat; try (repeat Msimpl; reflexivity).
         repeat rewrite Mmult_assoc.
         rewrite <- 2 Mmult_adjoint.
         repeat rewrite <- Mmult_assoc.
         gridify; reflexivity. }
    replace (super pad0 (super U ρ)) with (super U (super pad0 ρ)).
    2: { subst; clear - Hq.
         unfold super.
         autorewrite with eval_db.
         bdestruct (n + 1 <=? dim)%nat; try (Msimpl; reflexivity).
         remember (G.to_base u) as u'.
         dependent destruction u'.
         autorewrite with eval_db.
         bdestruct (q + 1 <=? dim)%nat; try (repeat Msimpl; reflexivity).
         repeat rewrite Mmult_assoc.
         rewrite <- 2 Mmult_adjoint.
         repeat rewrite <- Mmult_assoc.
         gridify; reflexivity. }
    rewrite Hl1, Hl2; auto.
    2, 3: subst; auto with wf_db.
    unfold super. 
    rewrite <- Mmult_plus_distr_r.
    rewrite <- Mmult_plus_distr_l.
    reflexivity.
Qed.

End NonUListRepresentationProps.