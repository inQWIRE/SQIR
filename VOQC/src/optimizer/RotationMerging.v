Require Import UnitarySem.
Require Import ClassicalStates.
Require Export RzkGateSet.
Require Import FSets.FMapAVL.
Require Import FSets.FMapFacts.

Module FSetProps := FSetProperties.Properties FSet.
Module FMap := FMapAVL.Make(Coq.Structures.OrderedTypeEx.Nat_as_OT).
Module FMapFacts := FMapFacts.Facts FMap.

Local Open Scope ucom_scope.
Local Close Scope C_scope.
Local Close Scope R_scope.

(* Combine rotations that act on the same terms in the phase polynomial 
   representation. For a thorough description of this optimization, see the
   "Rotation merging using phase polynomials" section of [1], Sec. 6.4 
   of [2], or Sec. 3 of [3].
 
   [1] Nam et al., "Automated optimization of large quantum circuits with continuous parameters"
   [2] Amy et al., "A meet-in-the-middle algorithm for fast synthesis of depth-optimal
quantum circuits"
   [3] Amy et al., "Polynomial-time T-depth Optimization of Clifford+T circuits via
Matroid Partitioning"
*)
  
(** Find subcircuit for rotation merging. **)

(* Find a subcircuit consisting of {CNOT, X, Rz} gates starting from a particular
   qubit q. (Actually, our subcircuits include some H gates as well because we want 
   to allow H gates on qubits that are not later used as the control of a CNOT.)
   The subcircuits are structured so that they maintain the following property:
   - Assuming that every qubit begins in a classical state, for every gate in the
     circuit, any qubit that is not in the set 'blst' remains in a classical state.

   We terminate when (qs == blst) because after this point no qubit is guaranteed
   to be in a classical state. The only purpose of 'blst' in this function is track 
   this termination condition ('blst' is used in a more interesting way in the merge
   operation).  *)

Fixpoint get_subcircuit' {dim} (l : Rzk_ucom_l dim) (qs blst : FSet.t) n :=
  match n with
  | O => ([], [], l) (* unreachable with n = length l *)
  | S n' =>
      if (FSet.equal qs blst)
      then ([], [], l)
      else match next_gate l qs with
           | Some (l1, App1 URzk_H q, l2) => 
               match get_subcircuit' l2 qs (FSet.add q blst) n' with
               | (l1', s, l2') => (l1 ++ l1', [H q] ++ s, l2')
               end
           | Some (l1, App1 u q, l2) => 
               match get_subcircuit' l2 qs blst n' with
               | (l1', s, l2') => (l1 ++ l1', [@App1 _ dim u q] ++ s, l2')
               end
           | Some (l1, App2 URzk_CNOT q1 q2, l2) =>
               let qs' := FSet.add q1 (FSet.add q2 qs) in
               let blst' := if FSet.mem q1 blst then (FSet.add q2 blst) else blst in
               match get_subcircuit' l2 qs' blst' n' with
               | (l1', s, l2') => (l1 ++ l1', [CNOT q1 q2] ++ s, l2')
               end
           | _ => ([], [], l) (* unreachable for the Rzk gate set*)
           end
  end.

Definition get_subcircuit {dim} (l : Rzk_ucom_l dim) q := 
  get_subcircuit' l (FSet.add q FSet.empty) FSet.empty (List.length l).

(* Examples *)

Definition test1 : Rzk_ucom_l 1 := T 0 :: H 0 :: X 0 :: [].
Definition test2 : Rzk_ucom_l 2 := T 0 :: CNOT 0 1 :: H 0 :: CNOT 0 1 :: T 1 :: H 1 :: [].
Definition test3 : Rzk_ucom_l 3 := T 0 :: H 1 :: H 2 :: X 1 :: CNOT 0 2 :: T 0 :: X 2 :: CNOT 2 1 :: H 1 :: T 2 :: [].
Definition test4 : Rzk_ucom_l 3 := T 1 :: T 2 :: CNOT 1 0 :: T 0 :: CNOT 1 2 :: CNOT 0 1 :: H 2 :: CNOT 1 2 :: CNOT 0 1 :: T 1 :: H 0 :: H 1 :: [].

(* Result: l1 = [], s = [T 0; H 0], l2 = [X 0] *)
Compute (get_subcircuit test1 0). 
(* Result: l1 = [], s = [T 0; CNOT 0 1; H 0; CNOT 0 1], l2 = [T 1; H 1] *)
Compute (get_subcircuit test2 0).
(* Result: l1 = [T 0], s = [CNOT 0 1; H 0; CNOT 0 1], l2 = [T 1; H 1] *)
Compute (get_subcircuit test2 1).
(* Result: l1 = [H 1; H 2; X 1]
           s = [T 0; CNOT 0 2; T 0; X 2; CNOT 2 1; H 1; T 2]
           l2 = [] *)
Compute (get_subcircuit test3 0).
(* Result: l1 = [T 0]
           s = [H 1]
           l2 = [H 2; X 1; CNOT 0 2; T 0; X 2; CNOT 2 1; H 1; T 2] *)
Compute (get_subcircuit test3 1).
(* Result: l1 = [T 1; T 2]
           s = [CNOT 1 0; T 0; CNOT 1 2; CNOT 0 1; H 2; CNOT 1 2; CNOT 0 1; T 1; H 0; H 1]
           l2 = [] *)
Compute (get_subcircuit test4 0).
(* Result: l1 = [T 2]
           s = [T 1; CNOT 1 0; T 0; CNOT 1 2; CNOT 0 1; H 2; CNOT 1 2; CNOT 0 1; T 1; H 0; H 1]
           l2 = [] *)
Compute (get_subcircuit test4 1).
(* Result: l1 = [T 1; CNOT 1 0; T 0]
           s = [T 2; CNOT 1 2; CNOT 0 1; H 2; CNOT 1 2; CNOT 0 1; T 1; H 0; H 1]
           l2 = [] *)
Compute (get_subcircuit test4 2).  

(* Proofs *)

Lemma get_subcircuit'_l1_does_not_reference : forall {dim} (l : Rzk_ucom_l dim) qs blst n l1 s l2,
  get_subcircuit' l qs blst n = (l1, s, l2) ->
  forall q, FSet.In q qs -> does_not_reference l1 q = true.
Proof. 
  intros dim l qs blst n.
  generalize dependent blst.
  generalize dependent qs.
  generalize dependent l.
  induction  n; intros l qs blst l1 s l2 res q Hq; simpl in res.
  inversion res; subst. reflexivity.
  destruct (FSet.equal qs blst).
  inversion res; subst. reflexivity.
  destruct (next_gate l qs) eqn:ng.
  2: { inversion res; subst. reflexivity. }
  repeat destruct p.
  destruct g1 as [u | u | u].
  - dependent destruction u;
    [ destruct (get_subcircuit' g qs (FSet.add n0 blst) n) eqn:subc
    | destruct (get_subcircuit' g qs blst n) eqn:subc
    | destruct (get_subcircuit' g qs blst n) eqn:subc ];
    destruct p;
    inversion res; subst.
    all: eapply IHn in subc; eapply next_gate_l1_does_not_reference in ng.
    all: try apply Hq.
    all: apply does_not_reference_app; apply andb_true_intro; split; assumption.
  - dependent destruction u.
    destruct (get_subcircuit' g (FSet.add n0 (FSet.add n1 qs))
             (if FSet.mem n0 blst then FSet.add n1 blst else blst) n) eqn:subc.
    destruct p.
    inversion res; subst.
    eapply IHn in subc.
    eapply next_gate_l1_does_not_reference in ng.
    apply does_not_reference_app; apply andb_true_intro; split.
    apply ng. apply subc. apply Hq. 
    do 2 (apply FSetFacts.add_iff; right). 
    apply Hq.
  - dependent destruction u.
Qed.

Lemma get_subcircuit'_preserves_semantics : forall {dim} (l : Rzk_ucom_l dim) qs blst n l1 s l2,
  get_subcircuit' l qs blst n = (l1, s, l2) ->
  l =l= l1 ++ s ++ l2.
Proof. 
  intros dim l qs blst n.
  generalize dependent blst.
  generalize dependent qs.
  generalize dependent l.
  induction  n; intros l qs blst l1 s l2 res; simpl in res.
  inversion res; subst. reflexivity.
  destruct (FSet.equal qs blst).
  inversion res; subst. reflexivity.
  destruct (next_gate l qs) eqn:ng.
  2: { inversion res; subst. reflexivity. }
  repeat destruct p.
  destruct g1 as [u | u | u].
  - specialize (next_gate_app1_returns_q _ _ _ _ _ _ ng) as Hn0. 
    apply next_gate_preserves_structure in ng; subst l.
    dependent destruction u;
    [ destruct (get_subcircuit' g qs (FSet.add n0 blst) n) eqn:subc
    | destruct (get_subcircuit' g qs blst n) eqn:subc
    | destruct (get_subcircuit' g qs blst n) eqn:subc ];
    destruct p;
    inversion res; subst.
    all: apply (get_subcircuit'_l1_does_not_reference _ _ _ _ _ _ _ subc) in Hn0;   
         apply IHn in subc; rewrite subc.
    all: rewrite (app_assoc _ l); 
         rewrite does_not_reference_commutes_app1;
         try apply Hn0.
    all: repeat rewrite <- app_assoc; reflexivity.
  - dependent destruction u.
    destruct (get_subcircuit' g (FSet.add n0 (FSet.add n1 qs))
             (if FSet.mem n0 blst then FSet.add n1 blst else blst) n) eqn:subc.
    destruct p.
    inversion res; subst.
    apply next_gate_preserves_structure in ng; subst l.
    specialize (get_subcircuit'_l1_does_not_reference _ _ _ _ _ _ _ subc) as dnr.
    apply IHn in subc; rewrite subc.   
    rewrite (app_assoc _ l0).
    rewrite does_not_reference_commutes_app2.
    repeat rewrite <- app_assoc; reflexivity.
    apply dnr. 
    apply FSetFacts.add_iff. left; reflexivity.
    apply dnr. 
    apply FSetFacts.add_iff. right. 
    apply FSetFacts.add_iff. left; reflexivity.
  - dependent destruction u.
Qed.

Lemma get_subcircuit_l1_does_not_reference : forall {dim} (l : Rzk_ucom_l dim) q l1 s l2,
  get_subcircuit l q = (l1, s, l2) ->
  does_not_reference l1 q = true.
Proof.
  intros dim l q l1 s l2 H.
  unfold get_subcircuit in H.
  eapply get_subcircuit'_l1_does_not_reference in H.
  apply H.
  apply FSetFacts.add_iff. left; reflexivity.
Qed.

Lemma get_subcircuit_preserves_semantics : forall {dim} (l : Rzk_ucom_l dim) q l1 s l2,
  get_subcircuit l q = (l1, s, l2) ->
  l =l= l1 ++ s ++ l2.
Proof. 
  intros dim l q l1 s l2 H.
  unfold get_subcircuit in H.
  eapply get_subcircuit'_preserves_semantics in H.
  assumption.
Qed.

(** Merge a single rotation gate. **)

(* To perform rotation merging, we track the classical boolean state of every
   qubit not in blst. We describe the  classical state of a single qubit using
   a set of nats - qubit q is in the set if q is in the boolean expression
   x ⊕ y ⊕ ... ⊕ z. To describe the state of the entire system, we use a map
   from nats to sets.  

   Note that we stop analysis once we reach an X gate. We could instead include
   negation in our boolean expressions, but this is unnecessary because of the
   earlier not_propagation pass. *)

Definition xor (s1 s2 : FSet.t) := 
  FSet.diff (FSet.union s1 s2) (FSet.inter s1 s2).

(* Get the set associated with qubit q, with the default being {q} *)
Definition get_set smap q := 
  match FMap.find q smap with
  | Some s => s
  | None => FSet.add q FSet.empty
  end.

(* Inputs:
   - gate list l
   - qubit blacklist blst
   - starting qubit q
   - classical state map smap

   This function splits the input list into three parts: l1, [Rz i q'], and l2.
   The (Rz i q') gate can be moved before l1, or a Rz gate on q can be moved to
   after l1. *)
Fixpoint find_merge {dim} (l : Rzk_ucom_l dim) (blst : FSet.t) q smap
  : option (Rzk_ucom_l dim * _ * _ * Rzk_ucom_l dim) :=
  match l with
  | App1 URzk_H q' :: t =>
      match find_merge t (FSet.add q' blst) q smap with
      | Some (l1, i, q'', l2) => Some (H q' :: l1, i, q'', l2)
      | _ => None
      end
  | App1 (URzk_Rz i) q' :: t => 
      let s := get_set smap q' in
      let sorig := FSet.add q FSet.empty in
      if negb (FSet.mem q' blst) && FSet.equal s sorig 
      then Some ([], i, q', t)
      else match find_merge t blst q smap with
           | Some (l1, i', q'', l2) => Some (Rz i q' :: l1, i', q'', l2)
           | _ => None
            end
  | App2 URzk_CNOT q1 q2 :: t =>
      if (FSet.mem q1 blst) || (FSet.mem q2 blst) 
      then let blst' := if FSet.mem q1 blst then (FSet.add q2 blst) else blst in
           match find_merge t blst' q smap with
           | Some (l1, i, q', l2) => Some (CNOT q1 q2 :: l1, i, q', l2)
           | _ => None
           end
      else let s1 := get_set smap q1 in
           let s2 := get_set smap q2 in
           let smap' := FMap.add q2 (xor s1 s2) smap in   
           match find_merge t blst q smap' with
           | Some (l1, i, q', l2) => Some (CNOT q1 q2 :: l1, i, q', l2)
           | _ => None
           end
  | _ => None (* failed to merge *)
  end.

Definition merge_at_beginning {dim} (l : Rzk_ucom_l dim) i q :=
  match find_merge l FSet.empty q (FMap.empty _) with
  | Some (l1, i', q', l2) => Some ((combine_rotations i i' q) ++ l1 ++ l2)
  | None => None
  end.

Definition merge_at_end {dim} (l : Rzk_ucom_l dim) i q :=
  match find_merge l FSet.empty q (FMap.empty _) with
  | Some (l1, i', q', l2) => Some (l1 ++ (combine_rotations i i' q') ++ l2)
  | None => None
  end.

(* Examples *)

Definition test5 : Rzk_ucom_l 3 := CNOT 0 2 :: T 0 :: X 2 :: CNOT 2 1 :: T 2 :: [].
(* Result: Some [P 0; CNOT 0 2; X 2; CNOT 2 1; T 2]
           Some [CNOT 0 2; P 0; X 2; CNOT 2 1; T 2] *)
Compute (merge_at_beginning test5 (Rzk_k / 4) 0).
Compute (merge_at_end test5 (Rzk_k / 4) 0).

Definition test6 : Rzk_ucom_l 3 := CNOT 1 0 :: T 0 :: CNOT 1 2 :: CNOT 0 1 :: H 2 :: CNOT 1 2 :: CNOT 0 1 :: T 1 :: [].
(* Result: Some [P 1; CNOT 1 0; T 0; CNOT 1 2; CNOT 0 1; H 2; CNOT 1 2; CNOT 0 1]
           Some [CNOT 1 0; T 0; CNOT 1 2; CNOT 0 1; H 2; CNOT 1 2; CNOT 0 1; P 1] *)
Compute (merge_at_beginning test6 (Rzk_k / 4) 1).
Compute (merge_at_end test6 (Rzk_k / 4) 1).

(* Proofs *)

Lemma find_merge_preserves_structure : forall {dim} (l : Rzk_ucom_l dim) blst q smap l1 i q' l2,
  find_merge l blst q smap = Some (l1, i, q', l2) ->
  l = l1 ++ [Rz i q'] ++ l2.
Proof.
  intros dim l blst q smap l1 i q' l2 H.
  generalize dependent l1.
  generalize dependent smap.
  generalize dependent blst.
  induction l; intros blst smap l1 H; simpl in H.
  discriminate.
  destruct a as [u | u | u]; dependent destruction u; try discriminate.
  - destruct (find_merge l (FSet.add n blst) q smap) eqn:fm; try discriminate.
    do 3 destruct p. 
    inversion H; subst.
    apply IHl in fm.
    subst; reflexivity.
  - destruct (negb (FSet.mem n blst) && FSet.equal (get_set smap n) (FSet.add q FSet.empty)).
    inversion H; subst. reflexivity.
    destruct (find_merge l blst q smap) eqn:fm; try discriminate.
    do 3 destruct p. 
    inversion H; subst.
    apply IHl in fm.
    subst; reflexivity.
  - destruct (FSet.mem n blst || FSet.mem n0 blst).
    destruct (find_merge l (if FSet.mem n blst then FSet.add n0 blst else blst) q smap) eqn:fm; try discriminate.
    do 3 destruct p.  
    inversion H; subst. 
    apply IHl in fm.
    subst; reflexivity.
    destruct (find_merge l blst q (FMap.add n0 (xor (get_set smap n) (get_set smap n0)) smap)) eqn:fm; try discriminate.
    do 3 destruct p.  
    inversion H; subst. 
    apply IHl in fm.
    subst; reflexivity. 
Qed.

(* Given our map-of-set representation (smap), get the boolean expression
   associated with qubit q using the mapping from variables to boolean values 
   given in f. *)
Definition get_boolean_expr smap f q :=
  FSet.fold (fun q => xorb (f q)) (get_set smap q) false.

(* I found the proofs below easier when I expanded out out the set function defns,
   but the proofs are still messier than they should be. -KH *)
Ltac unfold_set_defns := 
  repeat match goal with
  | |- context[FSet.In _ (FSet.diff _ _)] => rewrite FSetFacts.diff_iff
  | |- context[FSet.In _ (FSet.inter _ _)] => rewrite FSetFacts.inter_iff
  | |- context[FSet.In _ (FSet.union _ _)] => rewrite FSetFacts.union_iff
  | H : context[FSet.In _ (FSet.diff _ _)] |- _ => rewrite FSetFacts.diff_iff in H
  | H : context[FSet.In _ (FSet.inter _ _)] |- _ => rewrite FSetFacts.inter_iff in H
  | H : context[FSet.In _ (FSet.union _ _)] |- _ => rewrite FSetFacts.union_iff in H
  end.

Lemma get_boolean_expr_xor : forall smap f q1 q2,
  let s1 := get_set smap q1 in
  let s2 := get_set smap q2 in
  let smap' := FMap.add q2 (xor s1 s2) smap in
  get_boolean_expr smap' f q2 = xorb (get_boolean_expr smap f q1) (get_boolean_expr smap f q2) .
Proof.
  intros smap f q1 q2 s1 s2 smap'.
  subst s1 s2 smap'.
  unfold get_boolean_expr, xor.
  remember (get_set smap q1) as s1; clear Heqs1.
  remember (get_set smap q2) as s2; clear Heqs2.
  (* some facts needed for rewriting with FSetProps.fold_equal *)
  assert (Hcompat : compat_op eq eq (fun q : FSet.elt => xorb (f q))).
  { unfold compat_op. solve_proper. }
  assert (Htranspose : transpose eq (fun q : FSet.elt => xorb (f q))).
  { unfold transpose. 
    intros; rewrite <- xorb_assoc, (xorb_comm (f x)), xorb_assoc; auto. }
  unfold get_set. rewrite FMapFacts.add_eq_o; auto.
  pattern s1. apply FSetProps.set_induction; clear s1.
  - (* case where s1 is empty *)
    intros s1 H. 
    erewrite (FSetProps.fold_1 _ _ _ H).
    rewrite xorb_false_l.
    assert (FSet.Equal (FSet.diff (FSet.union s1 s2) (FSet.inter s1 s2)) s2).
    { rewrite (FSetProps.empty_union_1 _ H).
      rewrite FSetProps.empty_diff_2.
      reflexivity.
      apply (FSetProps.empty_inter_1 H). }
    rewrite FSetProps.fold_equal; auto. 
  - (* case where s1 is (add x s1') *)
    intros s1 s1' H x H1 H2.
    bdestruct (FSet.mem x s2).
    + assert (FSet.Equal (FSet.add x (FSet.diff (FSet.union s1' s2) (FSet.inter s1' s2))) (FSet.diff (FSet.union s1 s2) (FSet.inter s1 s2))). 
      { clear - H0 H1 H2.
        unfold FSet.Equal.
        intros e.
        rewrite FSetFacts.add_iff.
        split; intros He; specialize (H2 e); unfold_set_defns.      
        destruct He as [He | [[He1 | He1] He2]].
        subst; split; auto.
        intro contra; destruct contra as [contra1 contra2]; auto.
        apply H2 in He1 as [He1 | He1].
        1,2,3: split; subst; auto.
        1,2,3: intro contra; destruct contra as [contra1 contra2];
               contradict He2; split; auto;
               apply H2; auto.
        destruct He as [[He1 | He1] He2].
        right. split; auto. left. apply H2; auto.
        intro contra; destruct contra as [contra1 contra2].
        contradict He2; split; auto.
        apply Classical_Prop.not_and_or in He2 as [He2 | He2]; auto.
        bdestruct (x =? e); auto.
        right. split; auto.
        intro contra; destruct contra as [contra1 contra2].
        apply H2 in contra1 as [contra1 | contra1]; auto. }
      rewrite <- FSetProps.fold_equal in H; try apply H3; auto.
      rewrite (FSetProps.fold_2 _ _ Hcompat Htranspose H1 H2).
      rewrite xorb_assoc.
      rewrite <- H. 
      erewrite FSetProps.fold_add; auto.
      rewrite <- xorb_assoc, xorb_nilpotent, xorb_false_l; auto.
      unfold_set_defns.
      intro contra; destruct contra as [[contra1 | contra1] contra2];
      contradict contra2; split; auto.
      apply H2; auto.
    + assert (FSet.Equal (FSet.diff (FSet.union s1' s2) (FSet.inter s1' s2)) (FSet.add x (FSet.diff (FSet.union s1 s2) (FSet.inter s1 s2)))). 
      { clear - H0 H1 H2.
        unfold FSet.Equal.
        intros e.
        rewrite FSetFacts.add_iff.
        split; intros He; specialize (H2 e); unfold_set_defns.      
        destruct He as [[He1 | He1] He2].
        apply H2 in He1 as [He1 | He1]; auto. right. split; auto.
        intro contra; destruct contra as [contra1 contra2].
        contradict He2; split; auto. apply H2; auto.
        apply Classical_Prop.not_and_or in He2 as [He2 | He2]; auto.
        rewrite H2 in He2.
        bdestruct (x =? e); auto.
        right. split; auto.
        intro contra; destruct contra as [contra1 contra2].
        contradict He2; auto. 
        destruct He as [He | [[He1 | He1] He2]].
        subst; split. left; apply H2; auto.
        intro contra; destruct contra as [contra1 contra2]; auto.
        apply Classical_Prop.not_and_or in He2 as [He2 | He2]; split; auto.
        1,2: left; apply H2; auto.
        intro contra; destruct contra as [contra1 contra2]; auto.
        apply Classical_Prop.not_and_or in He2 as [He2 | He2]; split; auto.
        intro contra; destruct contra as [contra1 contra2].
        apply H2 in contra1 as [contra1 | contra1]; subst; auto. }
      rewrite FSetProps.fold_equal; try apply H3; auto.
      rewrite (FSetProps.fold_2 _ _ Hcompat Htranspose H1 H2).
      erewrite FSetProps.fold_add; auto.      
      rewrite xorb_assoc.
      rewrite H; auto.
      unfold_set_defns.
      intros contra; destruct contra as [[contra | contra] _]; auto.
Qed.

Lemma get_boolean_expr_f_q : forall smap f q q',
  let s := get_set smap q in
  FSet.equal s (FSet.add q' FSet.empty) = true ->
  get_boolean_expr smap f q = f q'.
Proof.
  intros smap f q q' s H. subst s.
  unfold get_boolean_expr.
  remember (get_set smap q) as s; clear Heqs.
  apply FSet.equal_2 in H.
  eapply FSetProps.fold_equal in H; try rewrite H; auto.
  rewrite FSet.fold_1; simpl.
  apply xorb_false_r.
  unfold compat_op; solve_proper. 
  unfold transpose; intros.
  rewrite <- xorb_assoc, (xorb_comm (f x)), xorb_assoc; auto.
Qed.

Definition b2R (b : bool) : R := if b then 1%R else 0%R.
Local Coercion b2R : bool >-> R.

(* In English, this says that if (find_merge l blst q smap) splits l into
   l1 ++ [Rz i q'] ++ l2, then the rotation (Rz i q') can be replaced by
   a (Rz i q) rotation placed before l1. *)
Local Opaque ueval_r.
Lemma find_merge_move_rotation' : forall {dim} (l : Rzk_ucom_l dim) blst q smap l1 i q' l2 f i' (ψ : Vector (2 ^ dim)),
  uc_well_typed_l l ->
  find_merge l blst q smap = Some (l1, i, q', l2) ->
  (forall q, (q < dim)%nat -> not (FSet.In q blst) -> 
        classical q (get_boolean_expr smap f q) ψ) ->
  Rzk_eval l1 × ((Cexp (f q * (IZR i' * PI / IZR Rzk_k))) .* ψ) = Rzk_eval (l1 ++ [Rz i' q']) × ψ.
Proof.
  intros dim l blst q smap l1 i q' l2 f i' ψ WT H Hψ.
  generalize dependent ψ.
  generalize dependent l1.
  generalize dependent smap.
  generalize dependent blst.
  induction l; try discriminate.
  intros blst smap l1 H ψ Hψ.
  simpl in H.
  destruct a as [u | u | u]; dependent destruction u; 
  try discriminate; inversion WT; subst.
  - (* H gate *)
    destruct (find_merge l (FSet.add n blst) q smap) eqn:fm; try discriminate.
    do 3 destruct p.
    inversion H; subst.
    unfold Rzk_eval in *; simpl.
    rewrite 2 Mmult_assoc, Mscale_mult_dist_r.
    eapply IHl; try apply fm; auto.
    intros q0 Hq01 Hq02. unfold classical.
    rewrite <- Mmult_assoc, proj_commutes_1q_gate, Mmult_assoc, Hψ; auto.
    all: rewrite FSetFacts.add_iff in Hq02; auto.
  - (* Rzk gate *)
    destruct (negb (FSet.mem n blst) && FSet.equal (get_set smap n) (FSet.add q FSet.empty)) eqn:cond.
    + apply andb_true_iff in cond as [Hinb seq].
      bdestruct (FSet.mem n blst); try discriminate; clear Hinb.
      specialize (Hψ _ H2 H0). unfold classical in Hψ.
      apply get_boolean_expr_f_q with (f:=f) in seq.
      rewrite seq in Hψ.
      inversion H; subst.
      unfold Rzk_eval in *; simpl.
      rewrite <- Hψ at 2.
      rewrite Mmult_assoc, <- (Mmult_assoc _ _ ψ).
      replace (ueval_r dim q' (U_R 0 0 (IZR i' * PI / IZR Rzk_k))) with (@uc_eval dim (SQIR.Rz (IZR i' * PI / IZR Rzk_k) q')) by reflexivity.
      rewrite proj_Rz, Mscale_mult_dist_l, Hψ; auto.
    + destruct (find_merge l blst q smap) eqn:fm; try discriminate.
      do 3 destruct p.
      inversion H; subst.
      unfold Rzk_eval in *; simpl.
      rewrite 2 Mmult_assoc, Mscale_mult_dist_r.
      eapply IHl; try apply fm; auto.
      intros q0 Hq01 Hq02. unfold classical.
      rewrite <- Mmult_assoc.
      replace (ueval_r dim n (U_R 0 0 (IZR i * PI / IZR Rzk_k))) with (@uc_eval dim (SQIR.Rz (IZR i * PI / IZR Rzk_k) n)) by reflexivity.
      rewrite proj_Rz_comm, Mmult_assoc, Hψ; auto.
  - (* CNOT gate *)
    bdestruct (FSet.mem n blst); bdestruct (FSet.mem n0 blst); simpl in H;
    [ destruct (find_merge l (FSet.add n0 blst) q smap) eqn:fm
    | destruct (find_merge l (FSet.add n0 blst) q smap) eqn:fm
    | destruct (find_merge l blst q smap) eqn:fm 
    | destruct (find_merge l blst q (FMap.add n0 (xor (get_set smap n) (get_set smap n0)) smap)) eqn:fm ];
    try discriminate; do 3 (destruct p); inversion H; subst;
    unfold Rzk_eval in *; simpl; repeat rewrite Mmult_assoc;
    rewrite Mscale_mult_dist_r; eapply IHl; try apply fm; auto;
    intros q0 Hq01 Hq02; unfold classical; rewrite <- Mmult_assoc;
    replace (ueval_cnot dim n n0) with (@uc_eval dim (SQIR.CNOT n n0)) by auto.
    (* first, the cases where we don't update the boolean state *)
    1,2,3: rewrite proj_CNOT_control; try rewrite Mmult_assoc; try rewrite Hψ; 
           try rewrite FSetFacts.add_iff in Hq02; auto.
    left; intro contra; subst; auto.   
    (* next, the case where we use proj_CNOT_target *)
    bdestruct (q0 =? n0); subst.
    rewrite get_boolean_expr_xor.
    rewrite <- (Hψ n) at 1; auto.
    rewrite <- (Mmult_assoc _ _ ψ), (Mmult_assoc (proj _ _ _)).
    rewrite <- proj_CNOT_control, <- (Mmult_assoc (proj _ _ _)).
    rewrite xorb_comm.
    rewrite proj_CNOT_target, proj_CNOT_control.
    repeat rewrite Mmult_assoc. 
    unfold classical in Hψ.
    rewrite 2 Hψ; auto.
    1,2: specialize (Nat.eq_dec n n0) as Hdec; destruct Hdec; auto.
    rewrite proj_CNOT_control; auto.
    rewrite Mmult_assoc. 
    unfold get_boolean_expr, get_set.
    rewrite FMapFacts.add_neq_o; auto.
    rewrite Hψ; auto.
Qed.

Lemma find_merge_move_rotation : forall {dim} (l : Rzk_ucom_l dim) blst q smap l1 i q' l2 i' f (ψ : Vector (2 ^ dim)),
  uc_well_typed_l l ->
  q < dim -> q' < dim ->
  not (FSet.In q blst) ->
  get_boolean_expr smap f q = f q ->
  find_merge l blst q smap = Some (l1, i, q', l2) ->
  (forall q, (q < dim)%nat -> not (FSet.In q blst) -> 
        classical q (get_boolean_expr smap f q) ψ) ->
  Rzk_eval ([Rz i' q] ++ l1) × ψ = Rzk_eval (l1 ++ [Rz i' q']) × ψ.
Proof.
  intros dim l blst q smap l1 i q' l2 i' f ψ WT Hq Hq' H1 H2 res Hψ.
  unfold Rzk_eval; simpl.
  rewrite Mmult_assoc.
  unfold classical in Hψ.
  rewrite <- (Hψ q); auto.
  rewrite <- (Mmult_assoc _ _ ψ).
  replace (ueval_r dim q (U_R 0 0 (IZR i' * PI / IZR Rzk_k))) with (uc_eval (@SQIR.Rz dim (IZR i' * PI / IZR Rzk_k) q)) by reflexivity.
  rewrite proj_Rz, Mscale_mult_dist_l, Hψ; auto.
  rewrite H2.
  eapply find_merge_move_rotation'; try apply res; auto.
Qed.
Local Transparent ueval_r.

Lemma merge_at_beginning_preserves_semantics : forall {dim} (l : Rzk_ucom_l dim) i q l',
  q < dim -> uc_well_typed_l l ->
  merge_at_beginning l i q = Some l' ->
  l' =l= Rz i q :: l.
Proof.
  intros dim l i q l' Hq WT H.
  unfold merge_at_beginning in H.
  eapply equal_on_basis_states_implies_equal; auto with wf_db.
  intro f.
  destruct (find_merge l FSet.empty q (FMap.empty FSet.t)) eqn:fm; try discriminate.
  do 3 (destruct p).
  specialize (find_merge_preserves_structure _ _ _ _ _ _ _ _ fm); intro.  
  inversion H; subst.
  eapply find_merge_move_rotation with (f0:=f) in fm; auto.
  rewrite Rzk_to_base_ucom_l_app, list_to_ucom_append; simpl.
  rewrite combine_rotations_semantics; auto.
  unfold Rzk_eval in fm.
  repeat rewrite Rzk_to_base_ucom_l_app, list_to_ucom_append in *; simpl in *.
  rewrite denote_SKIP in *; try lia; Msimpl_light.
  repeat rewrite Mmult_assoc in *.
  apply f_equal2; try reflexivity.
  rewrite 2 Mmult_1_l in fm.
  rewrite <- fm.
  2,3: auto with wf_db. 
  reflexivity.
  apply uc_well_typed_l_app in WT as [_ WT].
  simpl in WT; inversion WT; subst; auto.
  rewrite FSetFacts.empty_iff; auto.
  apply get_boolean_expr_f_q. 
  unfold get_set. rewrite FMapFacts.empty_o. 
  apply FSetFacts.equal_iff. reflexivity.
  intros q0 Hq01 Hq02.
  erewrite get_boolean_expr_f_q. 
  2: { unfold get_set. rewrite FMapFacts.empty_o. 
       apply FSetFacts.equal_iff. reflexivity. }
  unfold classical.
  rewrite <- Mmult_assoc.
  replace (pad q dim (rotation 0 0 (IZR i * PI / IZR Rzk_k))) with (@uc_eval dim (SQIR.Rz (IZR i * PI / IZR Rzk_k) q)) by reflexivity.
  rewrite proj_Rz_comm.
  rewrite Mmult_assoc.
  rewrite f_to_vec_classical; auto.
Qed.

Lemma merge_at_beginning_WT : forall {dim} (l : Rzk_ucom_l dim) i q l',
  q < dim -> uc_well_typed_l l ->
  merge_at_beginning l i q = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros dim l i q l' Hq WT H.
  apply merge_at_beginning_preserves_semantics in H; auto.
  symmetry in H.
  apply uc_equiv_l_implies_WT in H; auto.
  constructor; auto.
Qed.

Lemma merge_at_end_preserves_semantics : forall {dim} (l : Rzk_ucom_l dim) i q l',
  q < dim -> uc_well_typed_l l ->
  merge_at_end l i q = Some l' ->
  l' =l= Rz i q :: l.
Proof.
  intros dim l i q l' Hq WT H.
  unfold merge_at_end in H.
  destruct (find_merge l FSet.empty q (FMap.empty FSet.t)) eqn:fm; try discriminate.
  do 3 (destruct p).
  specialize (find_merge_preserves_structure _ _ _ _ _ _ _ _ fm); intro.  
  inversion H; subst.
  rewrite app_comm_cons. repeat rewrite app_assoc. 
  apply uc_app_congruence; try reflexivity.
  eapply equal_on_basis_states_implies_equal; auto with wf_db.
  intro f.
  repeat (try rewrite Rzk_to_base_ucom_l_app; try rewrite list_to_ucom_append; simpl).
  eapply find_merge_move_rotation with (f0:=f) in fm; auto.
  rewrite combine_rotations_semantics; auto.
  unfold Rzk_eval in fm.
  repeat (try rewrite Rzk_to_base_ucom_l_app in fm; 
          try rewrite list_to_ucom_append in fm; simpl in fm).
  rewrite Rzk_to_base_ucom_l_app, list_to_ucom_append; simpl.
  rewrite denote_SKIP in *; try lia; Msimpl_light.
  repeat rewrite Mmult_assoc in *.
  rewrite 2 Mmult_1_l in fm.
  rewrite fm.
  2,3: auto with wf_db.
  reflexivity.
  1,2: apply uc_well_typed_l_app in WT as [_ WT];
       simpl in WT; inversion WT; subst; auto.
  rewrite FSetFacts.empty_iff; auto.
  apply get_boolean_expr_f_q. 
  unfold get_set. rewrite FMapFacts.empty_o. 
  apply FSetFacts.equal_iff. reflexivity.
  intros q0 Hq01 Hq02.
  erewrite get_boolean_expr_f_q. 
  2: { unfold get_set. rewrite FMapFacts.empty_o. 
       apply FSetFacts.equal_iff. reflexivity. }
  apply f_to_vec_classical; auto.
Qed.

Lemma merge_at_end_WT : forall {dim} (l : Rzk_ucom_l dim) i q l',
  q < dim -> uc_well_typed_l l ->
  merge_at_end l i q = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros dim l i q l' Hq WT H.
  apply merge_at_end_preserves_semantics in H; auto.
  symmetry in H.
  apply uc_equiv_l_implies_WT in H; auto.
  constructor; auto.
Qed.

(** Final optimization definition. **)

Fixpoint merge_rotations_at_beginning {dim} (l : Rzk_ucom_l dim) n :=
  match n with
  | O => l
  | S n' => match l with
           | [] => []
           | App1 (URzk_Rz i) q :: t =>
               match get_subcircuit t q with
               | (l1, s, l2) => 
                   match merge_at_beginning s i q with
                   | Some s' => merge_rotations_at_beginning (l1 ++ s' ++ l2) n'
                   | None => Rz i q :: merge_rotations_at_beginning t n'
                   end
               end
           | g :: t => g :: merge_rotations_at_beginning t n'
           end
  end.

Fixpoint merge_rotations_at_end {dim} (l : Rzk_ucom_l dim) n :=
  match n with
  | O => l
  | S n' => match l with
           | [] => []
           | App1 (URzk_Rz i) q :: t =>
               match get_subcircuit t q with
               | (l1, s, l2) => 
                   match merge_at_end s i q with
                   | Some s' => merge_rotations_at_end (l1 ++ s' ++ l2) n'
                   | None => Rz i q :: merge_rotations_at_end t n'
                   end
               end
           | g :: t => g :: merge_rotations_at_end t n'
           end
  end.

Definition invert_gate {dim} (g : gate_app _ dim) :=
  match g with
  | App1 (URzk_Rz i) q => invert_rotation i q
  | _ => g
  end.

Definition invert {dim} (l : Rzk_ucom_l dim) :=
  List.map invert_gate (List.rev l).

Definition merge_rotations {dim} (l : Rzk_ucom_l dim) := 
  (* forward pass *)
  let l' := merge_rotations_at_beginning l (List.length l) in
  (* backward pass *)
  let l'' := merge_rotations_at_end (invert l') (List.length l') in
  (* final result *)
  invert l''.

(* Examples *)

Definition test7 : Rzk_ucom_l 4 := T 3 :: CNOT 0 3 :: P 0 :: CNOT 1 2 :: CNOT 0 1 :: TDAG 2 :: T 0 :: CNOT 1 2 :: CNOT 2 1 :: TDAG 1 :: CNOT 3 0 :: CNOT 0 3 :: T 0 :: T 3 :: [].
Definition test8 : Rzk_ucom_l 2 := T 1 :: CNOT 0 1 :: Z 1 :: CNOT 0 1 :: Z 0 :: T 1 :: CNOT 1 0 :: [].
Definition test9 : Rzk_ucom_l 4 := CNOT 2 3 :: T 0 :: T 3 :: CNOT 0 1 :: CNOT 2 3 :: CNOT 1 2 :: CNOT 1 0 :: CNOT 3 2 :: CNOT 1 2 :: CNOT 0 1 :: T 2 :: TDAG 1 :: [].
Definition test10 : Rzk_ucom_l 3 := T 1 :: T 2 :: CNOT 0 1 :: CNOT 1 2 :: CNOT 1 0 :: T 0 :: CNOT 2 1 :: TDAG 1 :: [].

(* Result: [CNOT 1 2; P 3; CNOT 0 3; PDAG 2; Z 4; CNOT 0 1; CNOT 1 2; CNOT 2 1; CNOT 3 0; CNOT 0 3]  *)
Compute (merge_rotations test7).
(* Result: [P 1; CNOT 0 1; Z 1; CNOT 0 1; Z 0; CNOT 1 0] *)
Compute (merge_rotations test8).
(* Result: [CNOT 2 3; CNOT 0 1; P 3; CNOT 2 3; CNOT 1 2; CNOT 1 0; CNOT 3 2; CNOT 1 2; CNOT 0 1] *)
Compute (merge_rotations test9).
(* Result: [P 1; CNOT 0 1; CNOT 1 2; CNOT 1 0; CNOT 2 1] *)
Compute (merge_rotations test10).

(* Proofs *)

Lemma merge_rotations_at_beginning_preserves_semantics : forall {dim} (l : Rzk_ucom_l dim) n,
  uc_well_typed_l l -> merge_rotations_at_beginning l n =l= l.
Proof.
  intros.
  generalize dependent l.
  induction n; simpl. reflexivity. 
  intros l WT.  
  destruct l; try reflexivity.
  destruct g as [u | |]; inversion WT; subst; try rewrite IHn; try reflexivity; auto.
  dependent destruction u; try rewrite IHn; try reflexivity; auto.
  destruct (get_subcircuit l n0) eqn:subc.
  destruct p.
  destruct (merge_at_beginning l1 i n0) eqn:mer.
  2: rewrite IHn; try reflexivity; auto.
  specialize (get_subcircuit_l1_does_not_reference _ _ _ _ _ subc) as dnr.
  apply get_subcircuit_preserves_semantics in subc.
  rewrite subc.
  apply uc_equiv_l_implies_WT in subc; auto.
  apply uc_well_typed_l_app in subc as [WTl0 subc].
  apply uc_well_typed_l_app in subc as [WTl1 WTp0].
  specialize (merge_at_beginning_WT _ _ _ _ H1 WTl1 mer) as WTl2.
  apply merge_at_beginning_preserves_semantics in mer; auto.
  rewrite cons_to_app. 
  repeat rewrite app_assoc. 
  rewrite does_not_reference_commutes_app1; auto.
  rewrite <- (app_assoc _ _ l1).
  rewrite cons_to_app in mer.
  rewrite <- mer.
  apply IHn.  
  apply uc_well_typed_l_app; split; [apply uc_well_typed_l_app; split |]; auto.
Qed.

Lemma merge_rotations_at_beginning_WT : forall {dim} (l : Rzk_ucom_l dim) n,
  uc_well_typed_l l -> uc_well_typed_l (merge_rotations_at_beginning l n).
Proof.
  intros dim l n WT.
  specialize (merge_rotations_at_beginning_preserves_semantics _ n WT) as H.
  symmetry in H.
  apply uc_equiv_l_implies_WT in H; auto.
Qed.

Lemma merge_rotations_at_end_preserves_semantics : forall {dim} (l : Rzk_ucom_l dim) n,
  uc_well_typed_l l -> merge_rotations_at_end l n =l= l.
Proof.
  intros.
  generalize dependent l.
  induction n; simpl. reflexivity. 
  intros l WT.
  destruct l; try reflexivity.
  destruct g as [u | |]; inversion WT; subst; simpl; try rewrite IHn; try reflexivity; auto.
  dependent destruction u; simpl; try rewrite IHn; try reflexivity; auto.
  destruct (get_subcircuit l n0) eqn:subc.
  destruct p.
  destruct (merge_at_end l1 i n0) eqn:mer.
  2: simpl; rewrite IHn; try reflexivity; auto.
  specialize (get_subcircuit_l1_does_not_reference _ _ _ _ _ subc) as dnr.
  apply get_subcircuit_preserves_semantics in subc.
  rewrite subc.
  apply uc_equiv_l_implies_WT in subc; auto.
  apply uc_well_typed_l_app in subc as [WTl0 subc].
  apply uc_well_typed_l_app in subc as [WTl1 WTp0].
  specialize (merge_at_end_WT _ _ _ _ H1 WTl1 mer) as WTl2.
  apply merge_at_end_preserves_semantics in mer; auto.
  rewrite cons_to_app. 
  repeat rewrite app_assoc. 
  rewrite does_not_reference_commutes_app1; auto.
  rewrite <- (app_assoc _ _ l1).
  rewrite cons_to_app in mer.
  rewrite <- mer.
  apply IHn.  
  apply uc_well_typed_l_app; split; [apply uc_well_typed_l_app; split |]; auto.
Qed.

Lemma invert_eq_invert_ucom : forall {dim} (l : Rzk_ucom_l dim),
  dim > 0 ->
  uc_eval (list_to_ucom (Rzk_to_base_ucom_l (invert l))) = uc_eval (invert_ucom (list_to_ucom (Rzk_to_base_ucom_l l))).
Proof.
  intros dim l Hdim.
  Local Transparent ID.
  induction l; simpl.
  rewrite Ropp_0. reflexivity.
  Local Opaque ID Z.sub.
  destruct a as [u | u | u]; dependent destruction u; unfold invert; simpl.
  all: rewrite map_app, Rzk_to_base_ucom_l_app, list_to_ucom_append; simpl.
  all: rewrite <- IHl; apply f_equal2; try reflexivity.
  3: rewrite phase_shift_rotation;
     replace 65536%Z with (2 * Rzk_k)%Z by reflexivity;
     rewrite <- phase_mod_2PI_scaled. 
  4: unfold Rzk_k; lia.
  all: autorewrite with eval_db; gridify; auto.
  all: do 2 (apply f_equal2; try reflexivity).
  (* some annoying proofs with complex numbers because there are many ways to
     write the same matrix using our 'rotation' function *)
  all: unfold rotation; solve_matrix.
  all: autorewrite with R_db C_db trig_db; try lca.
  all: try rewrite Cexp_neg; try rewrite Cexp_0; try rewrite Cexp_PI; try lca. 
  rewrite minus_IZR.
  autorewrite with R_db.
  repeat rewrite Rmult_plus_distr_r.
  rewrite Cexp_add, <- Cexp_neg.
  replace (65536 * PI * / IZR Rzk_k)%R with (2 * PI)%R. 
  rewrite Cexp_2PI.
  autorewrite with C_db R_db; reflexivity.
  unfold Rzk_k; lra.
Qed.

Lemma invert_WT : forall {dim} (l : Rzk_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (invert l).
Proof.
  intros dim l WT.
  induction WT.
  constructor; auto.
  all: unfold invert; simpl; rewrite map_app, <- uc_well_typed_l_app.
  all: split; auto.
  all: simpl; dependent destruction u; constructor; auto; constructor; lia.
Qed.

Lemma merge_rotations_sound : forall {dim} (l : Rzk_ucom_l dim),
  uc_well_typed_l l -> merge_rotations l =l= l.
Proof. 
  intros dim l WT.
  specialize (uc_well_typed_l_implies_dim_nonzero _ WT) as Hdim.  
  unfold merge_rotations.
  remember (length l) as n; clear Heqn.
  remember (length (merge_rotations_at_beginning l n)) as m; clear Heqm.
  unfold uc_equiv_l, uc_equiv.
  rewrite invert_eq_invert_ucom, <- invert_ucom_correct; auto.
  rewrite merge_rotations_at_end_preserves_semantics.
  rewrite invert_eq_invert_ucom, <- invert_ucom_correct; auto.
  rewrite adjoint_involutive.
  apply merge_rotations_at_beginning_preserves_semantics; auto.
  apply invert_WT, merge_rotations_at_beginning_WT; auto.  
Qed.

Lemma merge_rotations_WT: forall {dim} (l : Rzk_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (merge_rotations l).
Proof.
  intros dim l WT.
  specialize (merge_rotations_sound l WT) as H.
  symmetry in H.
  apply uc_equiv_l_implies_WT in H; assumption.
Qed.


