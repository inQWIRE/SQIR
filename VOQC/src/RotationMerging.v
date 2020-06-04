Require Import UnitaryOps.
Require Export RzQGateSet.
Require Import FSets.FSetAVL.
Require Import FSets.FSetFacts.
Require Import FSets.FMapAVL.
Require Import FSets.FMapFacts.

Module FSet := FSetAVL.Make(Coq.Structures.OrderedTypeEx.Nat_as_OT).
Module FSetFacts := FSetFacts.Facts FSet.
Module FSetProps := FSetProperties.Properties FSet.
Module FMap := FMapAVL.Make(Coq.Structures.OrderedTypeEx.Nat_as_OT).
Module FMapFacts := FMapFacts.Facts FMap.

Lemma mem_reflect : forall x s, reflect (FSet.In x s) (FSet.mem x s).
Proof. intros x l. apply iff_reflect. apply FSetFacts.mem_iff. Qed.
Hint Resolve mem_reflect : bdestruct.

Local Open Scope ucom_scope.
Local Close Scope C_scope.
Local Close Scope R_scope.
Local Close Scope Q_scope.

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
  
(** Utilities for tracking classical states. **)

(* To perform rotation merging, we need to track the classical boolean states
   of a set of qubits. We describe the  classical state of a single qubit using
   a set of nats - qubit q is in the set if q is in the boolean expression
   x ⊕ y ⊕ ... ⊕ z. To describe the state of the entire system, we use a map
   from nats to sets. *)

(* Compute the xor of two boolean expressions represented as sets *)
Definition xor (s1 s2 : FSet.t) := 
  FSet.diff (FSet.union s1 s2) (FSet.inter s1 s2).

(* Get the set associated with qubit q, with the default being {q} *)
Definition get_set smap q := 
  match FMap.find q smap with
  | Some s => s
  | None => FSet.add q FSet.empty
  end.

(* Some useful lemmas *)

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

(** find_merge operation: identify a single opportunity for merging. **)

(* Inputs:
   - l    : input gate list
   - qs   : qubits under consideration
   - blst : qubit blacklist
   - q    : starting qubit
   - smap : classical state map
   - n    : fuel to convince Coq of termination

   This function splits the input list into three parts: l1, [Rz a q'], and l2.
   The property we will want to prove is that
       forall a', l1 ++ [Rz a' q'] ++ l2 = [Rz a' q] ++ l1 ++ l2.

   Our proof will rely on the fact that assuming that all q s.t. (q ∉ blst)
   start in a classical state, all q s.t. (q ∈ qs ∧ q ∉ blst) will end up in
   a classical state.

   First we give the tail recursive definition that will be extracted to OCaml.
   Next we give a non-tail recursive definition that is easier to reason about.
   This second definition is split into two parts: get_subcircuit', which removes
   gates that acts on qubits not in qs, and find_merge_alt', which performs
   rotation merging by iterating through the list directly (rather than using
   next_X_qubit_gate). We will prove correctness properties about this second
   definition and then prove its equivalence to the first.*)
Fixpoint find_merge' {dim} (l : RzQ_ucom_l dim) (qs blst : FSet.t) q smap n acc :=
  match n with
  | O => None
  | S n' =>
      if (FSet.equal qs blst)
      then None
      else match next_gate l (fun q => FSet.mem q qs) with
           | Some (l1, App1 URzQ_H q', l2) => 
               find_merge' l2 qs (FSet.add q' blst) q smap n' 
                           ([H q'] ++ rev_append l1  acc)
           | Some (l1, App1 (URzQ_Rz a) q', l2) => 
               let s := get_set smap q' in
               let sorig := FSet.add q FSet.empty in
               if negb (FSet.mem q' blst) && FSet.equal s sorig 
               then Some (rev_append acc l1, a, q', l2)
               else find_merge' l2 qs blst q smap n' 
                                ([Rz a q'] ++ rev_append l1 acc)
           | Some (l1, App2 URzQ_CNOT q1 q2, l2) =>
               let qs' := FSet.add q1 (FSet.add q2 qs) in
               if (FSet.mem q1 blst) || (FSet.mem q2 blst) 
               then let blst' := if FSet.mem q1 blst 
                                 then (FSet.add q2 blst) 
                                 else blst in
                    find_merge' l2 qs' blst' q smap n' 
                                ([CNOT q1 q2] ++ rev_append l1 acc)
               else let s1 := get_set smap q1 in
                    let s2 := get_set smap q2 in
                    let smap' := FMap.add q2 (xor s1 s2) smap in   
                    find_merge' l2 qs' blst q smap' n' 
                                ([CNOT q1 q2] ++ rev_append l1 acc)
           | _ => None (* failed to merge *)
           (* Note: We stop analysis once we reach an X gate. We could instead
              include negation in our boolean expressions, but this is not needed
              because of the earlier not_propagation pass. *)
           end
  end.

Definition find_merge {dim} (l : RzQ_ucom_l dim) q :=
  find_merge' l (FSet.add q FSet.empty) FSet.empty q (FMap.empty _) (List.length l) [].

(* Wrappers around find_merge *)

Definition merge_at_beginning {dim} (l : RzQ_ucom_l dim) a q :=
  match find_merge l q with
  | Some (l1, a', q', l2) => Some ((combine_rotations a a' q) ++ l1 ++ l2)
  | None => None
  end.

Definition merge_at_end {dim} (l : RzQ_ucom_l dim) a q :=
  match find_merge l q with
  | Some (l1, a', q', l2) => Some (l1 ++ (combine_rotations a a' q') ++ l2)
  | None => None
  end.

(* Examples *)

Definition test1 : RzQ_ucom_l 3 := CNOT 0 2 :: T 0 :: X 2 :: CNOT 2 1 :: T 2 :: [].
(* Result: Some [P 0; CNOT 0 2; X 2; CNOT 2 1; T 2]
           Some [CNOT 0 2; P 0; X 2; CNOT 2 1; T 2] *)
Compute (merge_at_beginning test1 (1/4) 0).
Compute (merge_at_end test1 (1/4) 0).

Definition test2 : RzQ_ucom_l 3 := CNOT 1 0 :: T 0 :: CNOT 1 2 :: CNOT 0 1 :: H 2 :: CNOT 1 2 :: CNOT 0 1 :: T 1 :: [].
(* Result: Some [P 1; CNOT 1 0; T 0; CNOT 1 2; CNOT 0 1; H 2; CNOT 1 2; CNOT 0 1]
           Some [CNOT 1 0; T 0; CNOT 1 2; CNOT 0 1; H 2; CNOT 1 2; CNOT 0 1; P 1] *)
Compute (merge_at_beginning test2 (1/4) 1).
Compute (merge_at_end test2 (1/4) 1).

(* Alternate definition *)

Fixpoint get_subcircuit' {dim} (l : RzQ_ucom_l dim) (qs blst : FSet.t) n :=
  match n with
  | O => ([], [], l) (* unreachable with n = length l *)
  | S n' =>
      if (FSet.equal qs blst)
      then ([], [], l)
      else match next_gate l (fun q => FSet.mem q qs) with
           | Some (l1, App1 URzQ_H q, l2) => 
               match get_subcircuit' l2 qs (FSet.add q blst) n' with
               | (l1', s, l2') => (l1 ++ l1', [H q] ++ s, l2')
               end
           | Some (l1, App1 u q, l2) => 
               match get_subcircuit' l2 qs blst n' with
               | (l1', s, l2') => (l1 ++ l1', [@App1 _ dim u q] ++ s, l2')
               end
           | Some (l1, App2 URzQ_CNOT q1 q2, l2) =>
               let qs' := FSet.add q1 (FSet.add q2 qs) in
               let blst' := if FSet.mem q1 blst then (FSet.add q2 blst) else blst in
               match get_subcircuit' l2 qs' blst' n' with
               | (l1', s, l2') => (l1 ++ l1', [CNOT q1 q2] ++ s, l2')
               end
           | _ => ([], [], l) (* unreachable for the RzQ gate set*)
           end
  end.

Fixpoint find_merge_alt' {dim} (l : RzQ_ucom_l dim) (blst : FSet.t) q smap
  : option (RzQ_ucom_l dim * _ * _ * RzQ_ucom_l dim) :=
  match l with
  | App1 URzQ_H q' :: t =>
      match find_merge_alt' t (FSet.add q' blst) q smap with
      | Some (l1, a, q'', l2) => Some (H q' :: l1, a, q'', l2)
      | _ => None
      end
  | App1 (URzQ_Rz a) q' :: t => 
      let s := get_set smap q' in
      let sorig := FSet.add q FSet.empty in
      if negb (FSet.mem q' blst) && FSet.equal s sorig 
      then Some ([], a, q', t)
      else match find_merge_alt' t blst q smap with
           | Some (l1, a', q'', l2) => Some (Rz a q' :: l1, a', q'', l2)
           | _ => None
            end
  | App2 URzQ_CNOT q1 q2 :: t =>
      if (FSet.mem q1 blst) || (FSet.mem q2 blst) 
      then let blst' := if FSet.mem q1 blst then (FSet.add q2 blst) else blst in
           match find_merge_alt' t blst' q smap with
           | Some (l1, a, q', l2) => Some (CNOT q1 q2 :: l1, a, q', l2)
           | _ => None
           end
      else let s1 := get_set smap q1 in
           let s2 := get_set smap q2 in
           let smap' := FMap.add q2 (xor s1 s2) smap in   
           match find_merge_alt' t blst q smap' with
           | Some (l1, a, q', l2) => Some (CNOT q1 q2 :: l1, a, q', l2)
           | _ => None
           end
  | _ => None (* failed to merge *)
  end.

Definition find_merge_alt {dim} (l : RzQ_ucom_l dim) q := 
  match (get_subcircuit' l (FSet.add q FSet.empty) FSet.empty (List.length l)) with
  | (l1, s, l2) => 
      match find_merge_alt' s FSet.empty q (FMap.empty _) with
      | Some (l1', a, q', l2') => Some (l1 ++ l1', a, q', l2' ++ l2)
      | _ => None
     end
  end.

(* Proofs *)

(* Basic properties of get_subcircuit'. *)

Lemma get_subcircuit'_l1_does_not_reference : forall {dim} (l : RzQ_ucom_l dim) qs blst n l1 s l2,
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
  destruct (next_gate l (fun q : nat => FSet.mem q qs)) eqn:ng.
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
    all: try (eapply FSetFacts.mem_iff; apply Hq).
    all: apply does_not_reference_app; apply andb_true_intro; split; assumption.
  - dependent destruction u.
    destruct (get_subcircuit' g (FSet.add n0 (FSet.add n1 qs))
             (if FSet.mem n0 blst then FSet.add n1 blst else blst) n) eqn:subc.
    destruct p.
    inversion res; subst.
    eapply IHn in subc.
    eapply next_gate_l1_does_not_reference in ng.
    apply does_not_reference_app; apply andb_true_intro; split.
    apply ng. apply subc. eapply FSetFacts.mem_iff; apply Hq. 
    do 2 (apply FSetFacts.add_iff; right). 
    apply Hq.
  - dependent destruction u.
Qed.

Lemma get_subcircuit'_preserves_semantics : forall {dim} (l : RzQ_ucom_l dim) qs blst n l1 s l2,
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
  destruct (next_gate l (fun q : nat => FSet.mem q qs)) eqn:ng.
  2: { inversion res; subst. reflexivity. }
  repeat destruct p.
  destruct g1 as [u | u | u].
  - specialize (next_gate_app1_returns_q _ _ _ _ _ _ ng) as Hn0. 
    apply next_gate_preserves_structure in ng; subst l.
    simpl in Hn0. apply FSetFacts.mem_iff in Hn0.
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

(* If find_merge and find_merge_alt both return Some (...) then the two results
   are equivalent. The conclusion has a strange form, but every piece of the 
   conjuction is useful later. Note that it is not true that 
   (l1 =l= rev acc ++ l1' ++ l1'') and (l2 =l= l2'' ++ l2'). *)
Lemma find_merge_alt'_returns_equiv : forall {dim} (l : RzQ_ucom_l dim) qs blst q smap n acc l1 a q' l2 l1' s l2' l1'' a' q'' l2'',
  find_merge' l qs blst q smap n acc = Some (l1, a, q', l2) ->
  get_subcircuit' l qs blst n = (l1', s, l2') ->
  find_merge_alt' s blst q smap = Some (l1'', a', q'', l2'') ->
  a = a' /\ q' = q'' /\ 
  (forall α, l1 ++ [Rz α q'] ++ l2 =l= rev acc ++ l1' ++ l1'' ++ [Rz α q''] ++ l2'' ++ l2').
Proof.
  intros dim l qs blst q smap n.
  generalize dependent smap.
  generalize dependent blst.
  generalize dependent qs.
  generalize dependent l.
  induction n; 
  intros l qs blst smap acc l1 a q' l2 l1' s l2' l1'' a' q'' l2'';
  intros Hfind_merge' Hget_subcircuit' Hfind_merge_alt'; simpl in *.
  discriminate.
  destruct (FSet.equal qs blst); try discriminate.
  destruct (next_gate l (fun q : nat => FSet.mem q qs)) eqn:ng; try discriminate. 
  repeat destruct p.
  specialize (next_gate_preserves_structure _ _ _ _ _ ng) as ngeq.
  destruct g1 as [u | u | u]; dependent destruction u; try discriminate.
  - destruct (get_subcircuit' g qs (FSet.add n0 blst) n) eqn:gs; destruct p.
    inversion Hget_subcircuit'; subst.
    simpl in Hfind_merge_alt'.
    destruct (find_merge_alt' l3 (FSet.add n0 blst) q smap) eqn:fma; try discriminate.
    repeat destruct p.
    inversion Hfind_merge_alt'; subst.
    assert (dnr: does_not_reference l0 n0 = true).
    { eapply get_subcircuit'_l1_does_not_reference. apply gs. 
      apply FSetFacts.mem_iff. 
      specialize (next_gate_app1_returns_q _ _ _ _ _ _ ng); auto. }
    specialize (IHn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfind_merge' gs fma) as [? [? IH]].
    repeat split; auto.
    intro; rewrite IH.
    simpl; rewrite rev_append_rev, rev_app_distr, rev_involutive.
    repeat rewrite app_comm_cons; rewrite (cons_to_app _ r0).
    rewrite (app_assoc _ ([RzQGateSet.H n0] ++ r0)), <- (app_assoc g0), (app_assoc _ _ r0).    
    rewrite <- (does_not_reference_commutes_app1 _ URzQ_H _ dnr).
    repeat rewrite <- app_assoc; reflexivity.
  - destruct (get_subcircuit' g qs blst n) eqn:gs; destruct p.
    inversion Hget_subcircuit'; subst.
    simpl in Hfind_merge_alt'.
    assert (dnr: does_not_reference l0 n0 = true).
    { eapply get_subcircuit'_l1_does_not_reference. apply gs. 
      apply FSetFacts.mem_iff. 
      specialize (next_gate_app1_returns_q _ _ _ _ _ _ ng); auto. }
    destruct (negb (FSet.mem n0 blst) && FSet.equal (get_set smap n0) (FSet.add q FSet.empty)).
    + inversion Hfind_merge_alt'; inversion Hfind_merge'; subst. 
      assert (Hequiv: l2 =l= l0 ++ l2'' ++ l2').
      { eapply get_subcircuit'_preserves_semantics. apply gs. }
      repeat split; auto.
      intro.
      rewrite rev_append_rev; simpl; repeat rewrite app_comm_cons.
      rewrite Hequiv.
      repeat rewrite app_comm_cons; rewrite (cons_to_app _ l0).
      rewrite (does_not_reference_commutes_app1 _ (URzQ_Rz α) _ dnr).
      repeat rewrite <- app_assoc; reflexivity.
    + destruct (find_merge_alt' l3 blst q smap) eqn:fma; try discriminate.
      repeat destruct p.
      inversion Hfind_merge_alt'; inversion Hfind_merge'; subst.       
      specialize (IHn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfind_merge' gs fma) as [? [? IH]].
      repeat split; auto.
      intro; rewrite IH.
      simpl; rewrite rev_append_rev, rev_app_distr, rev_involutive.
      repeat rewrite app_comm_cons; rewrite (cons_to_app _ r0).
      rewrite (app_assoc _ ([Rz a0 n0] ++ r0)), <- (app_assoc g0), (app_assoc _ _ r0).    
      rewrite <- (does_not_reference_commutes_app1 _ (URzQ_Rz a0) _ dnr).
      repeat rewrite <- app_assoc; reflexivity.
  - remember (if FSet.mem n0 blst then FSet.add n1 blst else blst) as blst'.
    destruct (get_subcircuit' g (FSet.add n0 (FSet.add n1 qs)) blst' n) eqn:gs; destruct p.
    inversion Hget_subcircuit'; subst.
    simpl in Hfind_merge_alt'.
    assert (dnrn0: does_not_reference l0 n0 = true).
    { eapply get_subcircuit'_l1_does_not_reference. apply gs. 
      apply FSetFacts.add_iff; auto. }
    assert (dnrn1: does_not_reference l0 n1 = true).
    { eapply get_subcircuit'_l1_does_not_reference. apply gs. 
      apply FSetFacts.add_iff; right; apply FSetFacts.add_iff; auto. }
    destruct (FSet.mem n0 blst || FSet.mem n1 blst) eqn:cond.
    + remember (if FSet.mem n0 blst then FSet.add n1 blst else blst) as blst'.
      destruct (find_merge_alt' l3 blst' q smap) eqn:fma; try discriminate.
      repeat destruct p.
      inversion Hfind_merge_alt'; subst.
      specialize (IHn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfind_merge' gs fma) as [? [? IH]].
      repeat split; auto.
      intro; rewrite IH.
      simpl; rewrite rev_append_rev, rev_app_distr, rev_involutive.
      repeat rewrite app_comm_cons; rewrite (cons_to_app _ r0).
      rewrite (app_assoc _ ([CNOT n0 n1] ++ r0)), <- (app_assoc g0), (app_assoc _ _ r0).    
      rewrite <- (does_not_reference_commutes_app2 _ URzQ_CNOT _ _ dnrn0 dnrn1).
      repeat rewrite <- app_assoc; reflexivity.
    + remember (FMap.add n1 (xor (get_set smap n0) (get_set smap n1)) smap) as smap'.
      destruct (find_merge_alt' l3 blst q smap') eqn:fma; try discriminate.
      repeat destruct p.
      inversion Hfind_merge_alt'; subst. 
      apply orb_false_elim in cond as [cond _].
      rewrite cond in gs; simpl in gs.
      specialize (IHn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfind_merge' gs fma) as [? [? IH]].
      repeat split; auto.
      intro; rewrite IH.
      simpl; rewrite rev_append_rev, rev_app_distr, rev_involutive.
      repeat rewrite app_comm_cons; rewrite (cons_to_app _ r0).
      rewrite (app_assoc _ ([CNOT n0 n1] ++ r0)), <- (app_assoc g0), (app_assoc _ _ r0).    
      rewrite <- (does_not_reference_commutes_app2 _ URzQ_CNOT _ _ dnrn0 dnrn1).
      repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma find_merge_alt_returns_equiv : forall {dim} (l : RzQ_ucom_l dim) q l1 a q' l2 l1' a' q'' l2',
  find_merge l q = Some (l1, a, q', l2) ->
  find_merge_alt l q = Some (l1', a', q'', l2') ->
  a = a' /\ q' = q'' /\
  forall α, l1 ++ [Rz α q'] ++ l2 =l= l1' ++ [Rz α q''] ++ l2'.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? Hfind_merge Hfind_merge_alt.
  unfold find_merge, find_merge_alt in *.
  destruct (get_subcircuit' l (FSet.add q FSet.empty) FSet.empty) eqn:gs.
  destruct p.
  destruct (find_merge_alt' l3 FSet.empty q (FMap.empty FSet.t)) eqn:fma.
  2: discriminate.
  repeat destruct p.
  inversion Hfind_merge_alt; subst.
  eapply find_merge_alt'_returns_equiv in Hfind_merge as [H1 [H2 H3]].
  2: apply gs.
  2: apply fma.
  repeat split; auto.
  intro. rewrite H3; simpl.
  repeat rewrite app_assoc; reflexivity.
Qed.

(* If find_merge returns Some then find_merge_alt will also return Some. *)

Lemma find_merge_alt'_returns_Some : forall {dim} (l : RzQ_ucom_l dim) qs blst q smap n acc l1 a q' l2 l1' s l2',
  find_merge' l qs blst q smap n acc = Some (l1, a, q', l2) ->
  get_subcircuit' l qs blst n = (l1', s, l2') ->
  exists l1'' a' q'' l2'', find_merge_alt' s blst q smap = Some (l1'', a', q'', l2'').
Proof.
  intros dim l qs blst q smap n.
  generalize dependent smap.
  generalize dependent blst.
  generalize dependent qs.
  generalize dependent l.
  induction n; 
  intros l qs blst smap acc l1 a q' l2 l1' s l2';
  intros Hfind_merge' Hget_subcircuit'; simpl in *.
  discriminate.
  destruct (FSet.equal qs blst); try discriminate.
  destruct (next_gate l (fun q : nat => FSet.mem q qs)) eqn:ng; try discriminate. 
  repeat destruct p.
  specialize (next_gate_preserves_structure _ _ _ _ _ ng) as ngeq.
  destruct g1 as [u | u | u]; dependent destruction u; try discriminate.
  - destruct (get_subcircuit' g qs (FSet.add n0 blst) n) eqn:gs; destruct p.
    inversion Hget_subcircuit'; subst.
    simpl.
    eapply IHn in Hfind_merge' as [l1'' [a' [q'' [l2'' fma]]]].
    2: apply gs.
    rewrite fma.
    exists (H n0 :: l1''), a', q'', l2''.
    reflexivity.
  - destruct (get_subcircuit' g qs blst n) eqn:gs; destruct p.
    inversion Hget_subcircuit'; subst.
    simpl.
    destruct (negb (FSet.mem n0 blst) && FSet.equal (get_set smap n0) (FSet.add q FSet.empty)).
    + exists [], a0, n0, l3.
      reflexivity.
    + eapply IHn in Hfind_merge' as [l1'' [a' [q'' [l2'' fma]]]].
      2: apply gs.
      rewrite fma.
      exists (Rz a0 n0 :: l1''), a', q'', l2''.
      reflexivity.
  - remember (if FSet.mem n0 blst then FSet.add n1 blst else blst) as blst'.
    destruct (get_subcircuit' g (FSet.add n0 (FSet.add n1 qs)) blst' n) eqn:gs; destruct p.
    inversion Hget_subcircuit'; subst.
    simpl.
    destruct (FSet.mem n0 blst || FSet.mem n1 blst) eqn:cond.
    + eapply IHn in Hfind_merge' as [l1'' [a' [q'' [l2'' fma]]]].
      2: apply gs.
      rewrite fma.
      exists (CNOT n0 n1 :: l1''), a', q'', l2''.
      reflexivity.
    + apply orb_false_elim in cond as [cond _].
      rewrite cond in gs; simpl in gs.
      eapply IHn in Hfind_merge' as [l1'' [a' [q'' [l2'' fma]]]].
      2: apply gs.
      rewrite fma.
      exists (CNOT n0 n1 :: l1''), a', q'', l2''.
      reflexivity.
Qed.

Lemma find_merge_alt_returns_Some : forall {dim} (l : RzQ_ucom_l dim) q l1 a q' l2,
  find_merge l q = Some (l1, a, q', l2) ->
  exists l1' a' q'' l2', find_merge_alt l q = Some (l1', a', q'', l2').
Proof.
  intros dim l q l1 a q' l2 H.
  unfold find_merge, find_merge_alt in *.
  destruct (get_subcircuit' l (FSet.add q FSet.empty) FSet.empty (length l)) eqn:gs.
  destruct p.
  destruct (find_merge' l (FSet.add q FSet.empty) FSet.empty q (FMap.empty FSet.t) (length l) []) eqn:fm.
  2: discriminate.
  repeat destruct p.
  eapply find_merge_alt'_returns_Some in fm as [l1' [a' [q'' [l2' fma]]]].
  2: apply gs.
  rewrite fma.
  exists (l0 ++ l1'), a', q'', (l2' ++ r).
  reflexivity.
Qed.

(* find_merge preserves the structure of l. *)

Lemma find_merge'_preserves_structure : forall {dim} (l : RzQ_ucom_l dim) qs blst q smap n acc l1 a q' l2,
  find_merge' l qs blst q smap n acc = Some (l1, a, q', l2) ->
  rev acc ++ l = l1 ++ [Rz a q'] ++ l2.
Proof.
  intros dim l qs blst q smap n.
  generalize dependent smap.
  generalize dependent blst.
  generalize dependent qs.
  generalize dependent l.
  induction n; intros l qs blst smap acc l1 a0 q' l2 H; simpl in H.
  discriminate.
  destruct (FSet.equal qs blst); try discriminate.
  destruct (next_gate l (fun q : nat => FSet.mem q qs)) eqn:ng; try discriminate. 
  repeat destruct p.
  apply next_gate_preserves_structure in ng.
  destruct g1 as [u | u | u]; dependent destruction u; try discriminate.
  - destruct (find_merge' g qs (FSet.add n0 blst) q smap n (RzQGateSet.H n0 :: rev_append g0 acc)) eqn:fm; try discriminate.
    repeat destruct p. 
    inversion H; subst.
    apply IHn in fm. 
    rewrite <- fm; simpl. 
    rewrite rev_append_rev, rev_app_distr, rev_involutive. 
    repeat rewrite <- app_assoc; reflexivity.
  - destruct (negb (FSet.mem n0 blst) && FSet.equal (get_set smap n0) (FSet.add q FSet.empty)).
    inversion H; subst. 
    rewrite rev_append_rev, app_assoc; reflexivity.
    destruct (find_merge' g qs blst q smap n (Rz a n0 :: rev_append g0 acc)) eqn:fm; try discriminate.
    repeat destruct p. 
    inversion H; subst.
    apply IHn in fm.
    rewrite <- fm; simpl.
    rewrite rev_append_rev, rev_app_distr, rev_involutive. 
    repeat rewrite <- app_assoc; reflexivity.
  - destruct (FSet.mem n0 blst || FSet.mem n1 blst).
    remember (if FSet.mem n0 blst then FSet.add n1 blst else blst) as blst'.
    destruct (find_merge' g (FSet.add n0 (FSet.add n1 qs)) blst' q smap n (CNOT n0 n1 :: rev_append g0 acc)) eqn:fm; try discriminate.
    repeat destruct p.  
    inversion H; subst. 
    apply IHn in fm.
    rewrite <- fm; simpl.
    rewrite rev_append_rev, rev_app_distr, rev_involutive. 
    repeat rewrite <- app_assoc; reflexivity.
    remember (FMap.add n1 (xor (get_set smap n0) (get_set smap n1)) smap) as smap'.
    destruct (find_merge' g (FSet.add n0 (FSet.add n1 qs)) blst q smap' n (CNOT n0 n1 :: rev_append g0 acc)) eqn:fm; try discriminate.
    repeat destruct p.  
    inversion H; subst. 
    apply IHn in fm.
    rewrite <- fm; simpl.
    rewrite rev_append_rev, rev_app_distr, rev_involutive. 
    repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma find_merge_preserves_structure : forall {dim} (l : RzQ_ucom_l dim) q l1 a q' l2,
  find_merge l q = Some (l1, a, q', l2) ->
  l = l1 ++ [Rz a q'] ++ l2.
Proof.
  intros ? ? ? ? ? ? ? H.
  eapply find_merge'_preserves_structure in H.
  rewrite <- H; reflexivity.
Qed.

(* The main correctness property for rotation merging. This says that if 
   find_merge_alt' splits l into l1 ++ [Rz a q'] ++ l2, then the rotation 
   (Rz a q') can be replaced by (Rz a q) placed before l1. Note that we prove
   this over the alternate definition of find_merge. *)
Definition b2R (b : bool) : R := if b then 1%R else 0%R.
Local Coercion b2R : bool >-> R.
Local Opaque ueval_r.
Lemma find_merge_alt'_move_rotation : forall {dim} (l : RzQ_ucom_l dim) blst q smap l1 a q' l2 f a' (ψ : Vector (2 ^ dim)),
  uc_well_typed_l l ->
  find_merge_alt' l blst q smap = Some (l1, a, q', l2) ->
  (forall q, (q < dim)%nat -> not (FSet.In q blst) -> 
        classical q (get_boolean_expr smap f q) ψ) ->
  eval l1 × ((Cexp (f q * (Qreals.Q2R a' * PI))) .* ψ) = eval (l1 ++ [Rz a' q']) × ψ.
Proof.
  intros dim l blst q smap l1 a q' l2 f a' ψ WT H Hψ.
  generalize dependent ψ.
  generalize dependent l1.
  generalize dependent smap.
  generalize dependent blst.
  induction l; try discriminate.
  intros blst smap l1 H ψ Hψ.
  simpl in H.
  destruct a0 as [u | u | u]; dependent destruction u; 
  try discriminate; inversion WT; subst.
  - (* H gate *)
    destruct (find_merge_alt' l (FSet.add n blst) q smap) eqn:fm; try discriminate.
    do 3 destruct p.
    inversion H; subst.
    unfold eval in *; simpl.
    rewrite 2 Mmult_assoc, Mscale_mult_dist_r.
    eapply IHl; try apply fm; auto.
    intros q0 Hq01 Hq02. unfold classical.
    rewrite <- Mmult_assoc, proj_commutes_1q_gate, Mmult_assoc, Hψ; auto.
    all: rewrite FSetFacts.add_iff in Hq02; auto.
  - (* RzQ gate *)
    destruct (negb (FSet.mem n blst) && FSet.equal (get_set smap n) (FSet.add q FSet.empty)) eqn:cond.
    + apply andb_true_iff in cond as [Hinb seq].
      bdestruct (FSet.mem n blst); try discriminate; clear Hinb.
      specialize (Hψ _ H2 H0). unfold classical in Hψ.
      apply get_boolean_expr_f_q with (f:=f) in seq.
      rewrite seq in Hψ.
      inversion H; subst.
      unfold eval in *; simpl.
      rewrite <- Hψ at 2.
      rewrite Mmult_assoc, <- (Mmult_assoc _ _ ψ).
      replace (ueval_r dim q' (U_R 0 0 (Qreals.Q2R a' * PI))) with (@uc_eval dim (SQIR.Rz (Qreals.Q2R a' * PI) q')) by reflexivity.
      rewrite proj_Rz, Mscale_mult_dist_l, Hψ; auto.
    + destruct (find_merge_alt' l blst q smap) eqn:fm; try discriminate.
      do 3 destruct p.
      inversion H; subst.
      unfold eval in *; simpl.
      rewrite 2 Mmult_assoc, Mscale_mult_dist_r.
      eapply IHl; try apply fm; auto.
      intros q0 Hq01 Hq02. unfold classical.
      rewrite <- Mmult_assoc.
      replace (ueval_r dim n (U_R 0 0 (Qreals.Q2R a * PI))) with (@uc_eval dim (SQIR.Rz (Qreals.Q2R a * PI) n)) by reflexivity.
      rewrite proj_Rz_comm, Mmult_assoc, Hψ; auto.
  - (* CNOT gate *)
    bdestruct (FSet.mem n blst); bdestruct (FSet.mem n0 blst); simpl in H;
    [ destruct (find_merge_alt' l (FSet.add n0 blst) q smap) eqn:fm
    | destruct (find_merge_alt' l (FSet.add n0 blst) q smap) eqn:fm
    | destruct (find_merge_alt' l blst q smap) eqn:fm 
    | destruct (find_merge_alt' l blst q (FMap.add n0 (xor (get_set smap n) (get_set smap n0)) smap)) eqn:fm ];
    try discriminate; do 3 (destruct p); inversion H; subst;
    unfold eval in *; simpl; repeat rewrite Mmult_assoc;
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
Local Transparent ueval_r.

(* Main lemma restated (and prettified) for find_merge. *)

Lemma find_merge_move_rotation_left : forall {dim} (l : RzQ_ucom_l dim) q l1 a0 q0 l2 a,
  q < dim -> q0 < dim ->
  uc_well_typed_l l ->
  find_merge l q = Some (l1, a0, q0, l2) ->
  [Rz a q] ++ l1 ++ [Rz a0 q0] ++ l2 =l= [Rz a q] ++ [Rz a0 q] ++ l1 ++ l2.
Proof.
  intros dim l q l1 a0 q0 l2 a Hq Hq0 WT fm.
  apply uc_app_congruence; try reflexivity.
  specialize (find_merge_alt_returns_Some _ _ _ _ _ _ fm) as [l1' [a0' [q0' [l2' H]]]].
  specialize (find_merge_alt_returns_equiv _ _ _ _ _ _ _ _ _ _ fm H) as [? [? eq]].
  subst.
  unfold find_merge_alt in H.
  destruct (get_subcircuit' l (FSet.add q FSet.empty) FSet.empty (length l)) eqn:gs.
  destruct p.
  destruct (find_merge_alt' l3 FSet.empty q (FMap.empty FSet.t)) eqn:fma.
  2: discriminate.
  repeat destruct p.
  inversion H; subst; clear H.
  assert (nil_rotation : @uc_equiv_l dim [Rz 0 q0'] []).
  { unfold uc_equiv_l, uc_equiv; simpl.
    rewrite phase_shift_rotation.
    replace (Qreals.Q2R 0 * PI)%R with 0%R by lra.
    rewrite phase_0. 
    autorewrite with eval_db; try lia.
    gridify; trivial. }
  assert (eq': l1 ++ l2 =l= l1 ++ [Rz 0 q0'] ++ l2).
  { replace (l1 ++ l2) with (l1 ++ [] ++ l2) by reflexivity. 
    rewrite <- nil_rotation at 1. reflexivity. }
  rewrite eq'; rewrite 2 eq.
  rewrite nil_rotation; clear nil_rotation eq'.
  rewrite (app_assoc [Rz a0' q]), (app_assoc _ l0).
  assert (dnr: does_not_reference l0 q = true).
  { eapply get_subcircuit'_l1_does_not_reference. apply gs. 
    apply FSetFacts.add_iff; auto. }
  rewrite (does_not_reference_commutes_app1 _ (URzQ_Rz a0') _ dnr).
  apply_app_congruence. 
  rewrite app_nil_r.
  eapply equal_on_basis_states_implies_equal; auto with wf_db.
  intro f.
  simpl.
  replace (pad q dim (rotation 0 0 (Qreals.Q2R a0' * PI))) with (uc_eval (@SQIR.Rz dim (Qreals.Q2R a0' * PI) q)) by reflexivity.
  specialize f_to_vec_classical as cla.
  unfold classical in cla.
  rewrite <- cla with (q:=q) at 2 by lia.
  rewrite <- (Mmult_assoc _ (proj q dim (f q))).
  rewrite (Mmult_assoc _ _ (proj q dim (f q))). 
  rewrite proj_Rz. 
  rewrite Mmult_assoc, Mscale_mult_dist_l.
  rewrite cla by lia. symmetry.
  eapply find_merge_alt'_move_rotation.
  2: apply fma.
  apply get_subcircuit'_preserves_semantics in gs.
  apply uc_equiv_l_implies_WT in gs; auto.
  apply uc_well_typed_l_app in gs as [_ gs].
  apply uc_well_typed_l_app in gs as [? _]; auto.
  intros.
  erewrite get_boolean_expr_f_q. 
  apply f_to_vec_classical; auto.
  unfold get_set. rewrite FMapFacts.empty_o. 
  apply FSetFacts.equal_iff. reflexivity.
Qed.

Lemma find_merge_move_rotation_right : forall {dim} (l : RzQ_ucom_l dim) q l1 a0 q0 l2 a,
  q < dim -> q0 < dim ->
  uc_well_typed_l l ->
  find_merge l q = Some (l1, a0, q0, l2) ->
  [Rz a q] ++ l1 ++ [Rz a0 q0] ++ l2 =l= l1 ++ [Rz a q0] ++ [Rz a0 q0] ++ l2.
Proof.
  intros dim l q l1 a0 q0 l2 a Hq Hq0 WT fm.
  specialize (find_merge_alt_returns_Some _ _ _ _ _ _ fm) as [l1' [a0' [q0' [l2' H]]]].
  specialize (find_merge_alt_returns_equiv _ _ _ _ _ _ _ _ _ _ fm H) as [? [? eq]].
  subst.
  unfold find_merge_alt in H.
  destruct (get_subcircuit' l (FSet.add q FSet.empty) FSet.empty (length l)) eqn:gs.
  destruct p.
  destruct (find_merge_alt' l3 FSet.empty q (FMap.empty FSet.t)) eqn:fma.
  2: discriminate.
  repeat destruct p.
  inversion H; subst; clear H.
  assert (double_rotation : @uc_equiv_l dim ([Rz a q0'] ++ [Rz a0' q0']) [Rz (a + a0') q0']).
  { unfold uc_equiv_l, uc_equiv; simpl.
    repeat rewrite phase_shift_rotation.
    autorewrite with eval_db; try lia.
    gridify.
    all: rewrite phase_mul, <- Rmult_plus_distr_r, Qreals.Q2R_plus, Rplus_comm.
    all: reflexivity. }
  rewrite (app_assoc [Rz a q0']).
  rewrite double_rotation; rewrite 2 eq.
  rewrite <- double_rotation; clear double_rotation.
  repeat rewrite app_assoc.
  assert (dnr: does_not_reference l0 q = true).
  { eapply get_subcircuit'_l1_does_not_reference. apply gs. 
    apply FSetFacts.add_iff; auto. }
  rewrite (does_not_reference_commutes_app1 _ (URzQ_Rz a) _ dnr).
  apply_app_congruence.
  eapply equal_on_basis_states_implies_equal; auto with wf_db.
  intro f.
  simpl.
  replace (pad q dim (rotation 0 0 (Qreals.Q2R a * PI))) with (uc_eval (@SQIR.Rz dim (Qreals.Q2R a * PI) q)) by reflexivity.
  specialize f_to_vec_classical as cla.
  unfold classical in cla.
  rewrite <- cla with (q:=q) at 1 by lia.
  rewrite <- (Mmult_assoc _ (proj q dim (f q))).
  rewrite (Mmult_assoc _ _ (proj q dim (f q))). 
  rewrite proj_Rz. 
  rewrite Mmult_assoc, Mscale_mult_dist_l.
  rewrite cla by lia. 
  eapply find_merge_alt'_move_rotation.
  2: apply fma.
  apply get_subcircuit'_preserves_semantics in gs.
  apply uc_equiv_l_implies_WT in gs; auto.
  apply uc_well_typed_l_app in gs as [_ gs].
  apply uc_well_typed_l_app in gs as [? _]; auto.
  intros.
  erewrite get_boolean_expr_f_q. 
  apply f_to_vec_classical; auto.
  unfold get_set. rewrite FMapFacts.empty_o. 
  apply FSetFacts.equal_iff. reflexivity.
Qed.

(* Correctness of find_merge wrappers. *)

Lemma merge_at_beginning_preserves_semantics : forall {dim} (l : RzQ_ucom_l dim) a q l',
  q < dim -> uc_well_typed_l l ->
  merge_at_beginning l a q = Some l' ->
  l' =l= [Rz a q] ++ l.
Proof.
  intros dim l a q l' Hq WT H.
  unfold merge_at_beginning in H.
  destruct (find_merge l q) eqn:fm; try discriminate.
  repeat destruct p.
  inversion H; subst; clear H.
  specialize (find_merge_preserves_structure _ _ _ _ _ _ fm); intro; subst.
  assert (Hn: n < dim).
  apply uc_well_typed_l_app in WT as [_ WT].
  apply uc_well_typed_l_app in WT as [WT _].
  inversion WT; subst; auto.
  rewrite (find_merge_move_rotation_left _ _ _ _ _ _ _ Hq Hn WT fm).
  rewrite combine_rotations_semantics; auto.
  rewrite <- app_assoc. 
  reflexivity.
Qed.

Lemma merge_at_beginning_WT : forall {dim} (l : RzQ_ucom_l dim) a q l',
  q < dim -> uc_well_typed_l l ->
  merge_at_beginning l a q = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros dim l a q l' Hq WT H.
  apply merge_at_beginning_preserves_semantics in H; auto.
  symmetry in H.
  apply uc_equiv_l_implies_WT in H; auto.
  constructor; auto.
Qed.

Lemma merge_at_end_preserves_semantics : forall {dim} (l : RzQ_ucom_l dim) a q l',
  q < dim -> uc_well_typed_l l ->
  merge_at_end l a q = Some l' ->
  l' =l= [Rz a q] ++ l.
Proof.
  intros dim l a q l' Hq WT H.
  unfold merge_at_end in H.
  destruct (find_merge l q) eqn:fm; try discriminate.
  repeat destruct p.
  inversion H; subst; clear H.
  specialize (find_merge_preserves_structure _ _ _ _ _ _ fm); intro; subst.
  assert (Hn: n < dim).
  apply uc_well_typed_l_app in WT as [_ WT].
  apply uc_well_typed_l_app in WT as [WT _].
  inversion WT; subst; auto.
  rewrite (find_merge_move_rotation_right _ _ _ _ _ _ _ Hq Hn WT fm).
  rewrite combine_rotations_semantics; auto.
  rewrite <- app_assoc. 
  reflexivity.
Qed.

Lemma merge_at_end_WT : forall {dim} (l : RzQ_ucom_l dim) a q l',
  q < dim -> uc_well_typed_l l ->
  merge_at_end l a q = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros dim l a q l' Hq WT H.
  apply merge_at_end_preserves_semantics in H; auto.
  symmetry in H.
  apply uc_equiv_l_implies_WT in H; auto.
  constructor; auto.
Qed.

(** Final optimization definition. **)

Fixpoint merge_rotations_at_beginning {dim} (l : RzQ_ucom_l dim) n acc :=
  match n with
  | O => rev_append acc l
  | S n' => match l with
           | [] => rev_append acc []
           | App1 (URzQ_Rz a) q :: t =>
               match merge_at_beginning t a q with
               | Some t' => merge_rotations_at_beginning t' n' acc
               | None => merge_rotations_at_beginning t n' (Rz a q :: acc)
               end
           | g :: t => merge_rotations_at_beginning t n' (g :: acc)
           end
  end.

Fixpoint merge_rotations_at_end {dim} (l : RzQ_ucom_l dim) n acc :=
  match n with
  | O => rev_append acc l
  | S n' => match l with
           | [] => rev_append acc []
           | App1 (URzQ_Rz a) q :: t =>
               match merge_at_end t a q with
               | Some t' => merge_rotations_at_end t' n' acc
               | None => merge_rotations_at_end t n' (Rz a q :: acc)
               end
           | g :: t => merge_rotations_at_end t n' (g :: acc)
           end
  end.

Definition invert_gate {dim} (g : gate_app RzQ_Unitary dim) :=
  match g with
  | App1 (URzQ_Rz a) q => invert_rotation a q
  | _ => g
  end.

Fixpoint rev_append_w_map {A : Type} (f : A -> A) (l l': list A) : list A :=
  match l with
  | [] => l'
  | a::l => rev_append_w_map f l ((f a) :: l')
  end.

Definition invert {dim} (l : RzQ_ucom_l dim) :=
  rev_append_w_map invert_gate l [].

Definition merge_rotations {dim} (l : RzQ_ucom_l dim) := 
  (* forward pass *)
  let l' := merge_rotations_at_beginning l (List.length l) [] in
  (* backward pass *)
  let l'' := merge_rotations_at_end (invert l') (List.length l') [] in
  (* final result *)
  invert l''.

(* Examples *)

Definition test3 : RzQ_ucom_l 4 := T 3 :: CNOT 0 3 :: P 0 :: CNOT 1 2 :: CNOT 0 1 :: TDAG 2 :: T 0 :: CNOT 1 2 :: CNOT 2 1 :: TDAG 1 :: CNOT 3 0 :: CNOT 0 3 :: T 0 :: T 3 :: [].
Definition test4 : RzQ_ucom_l 2 := T 1 :: CNOT 0 1 :: Z 1 :: CNOT 0 1 :: Z 0 :: T 1 :: CNOT 1 0 :: [].
Definition test5 : RzQ_ucom_l 4 := CNOT 2 3 :: T 0 :: T 3 :: CNOT 0 1 :: CNOT 2 3 :: CNOT 1 2 :: CNOT 1 0 :: CNOT 3 2 :: CNOT 1 2 :: CNOT 0 1 :: T 2 :: TDAG 1 :: [].
Definition test6 : RzQ_ucom_l 3 := T 1 :: T 2 :: CNOT 0 1 :: CNOT 1 2 :: CNOT 1 0 :: T 0 :: CNOT 2 1 :: TDAG 1 :: [].

(* Result: [P 3; CNOT 0 3; Z 0; CNOT 1 2; CNOT 0 1; PDAG 2; CNOT 1 2; CNOT 2 1; CNOT 3 0; CNOT 0 3]  *)
Compute (merge_rotations test3).
(* Result: [P 1; CNOT 0 1; Z 1; CNOT 0 1; Z 0; CNOT 1 0] *)
Compute (merge_rotations test4).
(* Result: [CNOT 2 3; P 3; CNOT 0 1; CNOT 2 3; CNOT 1 2; CNOT 1 0; CNOT 3 2; CNOT 1 2; CNOT 0 1] *)
Compute (merge_rotations test5).
(* Result: [P 1; CNOT 0 1; CNOT 1 2; CNOT 1 0; CNOT 2 1] *)
Compute (merge_rotations test6).

(* Proofs *)

Lemma merge_rotations_at_beginning_preserves_semantics : forall {dim} (l : RzQ_ucom_l dim) n acc,
  uc_well_typed_l l -> merge_rotations_at_beginning l n acc =l= rev acc ++ l.
Proof.
  intros dim l n.
  generalize dependent l.
  induction n; intros l acc WT; simpl.
  rewrite rev_append_rev. reflexivity.
  destruct l.
  rewrite rev_append_rev. reflexivity.
  destruct g as [u | |]; inversion WT; subst. 
  dependent destruction u. 
  all: try rewrite IHn; auto.
  all: simpl; try rewrite rev_append_rev.
  all: repeat rewrite <- app_assoc; try reflexivity.
  destruct (merge_at_beginning l a n0) eqn:mer.
  2: rewrite IHn; simpl; repeat rewrite <- app_assoc; auto; reflexivity.
  specialize (merge_at_beginning_WT _ _ _ _ H1 H3 mer) as WTl2.
  apply merge_at_beginning_preserves_semantics in mer; auto.
  simpl in mer; rewrite <- mer.
  apply IHn; auto.
Qed.

Lemma merge_rotations_at_beginning_WT : forall {dim} (l : RzQ_ucom_l dim) n acc,
  uc_well_typed_l acc -> uc_well_typed_l l -> 
  uc_well_typed_l (merge_rotations_at_beginning l n acc).
Proof.
  intros dim l n acc WTacc WTl.
  specialize (merge_rotations_at_beginning_preserves_semantics _ n acc WTl) as H.
  symmetry in H.
  apply uc_equiv_l_implies_WT in H; auto.
  apply uc_well_typed_l_app; split; auto.
  rewrite <- uc_well_typed_l_rev; auto.
Qed.

Lemma merge_rotations_at_end_preserves_semantics : forall {dim} (l : RzQ_ucom_l dim) n acc,
  uc_well_typed_l l -> merge_rotations_at_end l n acc =l= rev acc ++ l.
Proof.
  intros dim l n.
  generalize dependent l.
  induction n; intros l acc WT; simpl.
  rewrite rev_append_rev. reflexivity.
  destruct l.
  rewrite rev_append_rev. reflexivity.
  destruct g as [u | |]; inversion WT; subst. 
  dependent destruction u. 
  all: try rewrite IHn; auto.
  all: simpl; try rewrite rev_append_rev.
  all: repeat rewrite <- app_assoc; try reflexivity.
  destruct (merge_at_end l a n0) eqn:mer.
  2: rewrite IHn; simpl; repeat rewrite <- app_assoc; auto; reflexivity.
  specialize (merge_at_end_WT _ _ _ _ H1 H3 mer) as WTl2.
  apply merge_at_end_preserves_semantics in mer; auto.
  simpl in mer; rewrite <- mer.
  apply IHn; auto.
Qed.

(* Equivalent, non-tail recursive version of invert. *)
Lemma invert_alt : forall {dim} (l : RzQ_ucom_l dim),
  invert l = map invert_gate (rev l).
Proof.
  intros dim l.
  assert (H: forall f acc, rev_append_w_map f l acc = (map f (rev l)) ++ acc).
  { intro f.
    induction l; intro acc; simpl; try reflexivity.
    rewrite IHl, map_app; simpl.
    rewrite <- app_assoc. reflexivity. }  
  unfold invert. 
  rewrite H, app_nil_r.  
  reflexivity.
Qed.

Lemma invert_eq_SQIR_invert : forall {dim} (l : RzQ_ucom_l dim),
  dim > 0 ->
  uc_eval (list_to_ucom (invert l)) = uc_eval (UnitaryOps.invert (list_to_ucom l)).
Proof.
  intros dim l Hdim.
  rewrite invert_alt.
  Local Transparent ID.
  induction l; simpl.
  rewrite Ropp_0. reflexivity.
  Local Opaque ID Z.sub. 
  destruct a as [u | u | u]; dependent destruction u; unfold invert; simpl.
  all: rewrite map_app, list_to_ucom_append; simpl.
  all: rewrite <- IHl; apply f_equal2; try reflexivity.
  all: autorewrite with eval_db; gridify; auto.
  all: do 2 (apply f_equal2; try reflexivity).
  (* some annoying proofs with complex numbers because there are many ways to
     write the same matrix using our 'rotation' function *)
  all: unfold rotation; solve_matrix.
  all: autorewrite with R_db C_db trig_db; try lca.
  all: try rewrite Cexp_neg; try rewrite Cexp_0; try rewrite Cexp_PI; try lca. 
  rewrite Qreals.Q2R_minus.
  autorewrite with R_db.
  repeat rewrite Rmult_plus_distr_r.
  rewrite Cexp_add, <- Cexp_neg.
  replace (Qreals.Q2R two_Q * PI)%R with (2 * PI)%R. 
  2: unfold Qreals.Q2R, two_Q; simpl; lra. 
  simpl. rewrite Cexp_2PI.
  autorewrite with C_db R_db; reflexivity.
Qed.

Lemma invert_WT : forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (invert l).
Proof.
  intros dim l WT.
  rewrite invert_alt.
  induction WT.
  constructor; auto.
  all: unfold invert; simpl; rewrite map_app, <- uc_well_typed_l_app.
  all: split; auto.
  all: simpl; dependent destruction u; constructor; auto; constructor; lia.
Qed.

Lemma merge_rotations_sound : forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> merge_rotations l =l= l.
Proof. 
  intros dim l WT.
  specialize (uc_well_typed_l_implies_dim_nonzero _ WT) as Hdim.  
  unfold merge_rotations.
  remember (length l) as n; clear Heqn.
  remember (length (merge_rotations_at_beginning l n [])) as m; clear Heqm.
  unfold uc_equiv_l, uc_equiv.
  rewrite invert_eq_SQIR_invert, <- invert_correct; auto.
  rewrite merge_rotations_at_end_preserves_semantics.
  simpl.
  rewrite invert_eq_SQIR_invert, <- invert_correct; auto.
  rewrite adjoint_involutive.
  apply merge_rotations_at_beginning_preserves_semantics; auto.
  apply invert_WT, merge_rotations_at_beginning_WT; auto.  
  constructor; auto.
Qed.

Lemma merge_rotations_WT: forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (merge_rotations l).
Proof.
  intros dim l WT.
  specialize (merge_rotations_sound l WT) as H.
  symmetry in H.
  apply uc_equiv_l_implies_WT in H; assumption.
Qed.


