Require Import UnitarySem.
Require Import core.Utilities.
Require Export PI4GateSet.

Local Open Scope ucom_scope.

(* Combine rotations that act on the same terms in the phase polynomial 
   representation of a program. For a thorough description of this optimization, 
   see the "Rotation merging using phase polynomials" section of [1], Sec. 6.4 
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

   We terminate when (length qs) =? (length blst) to keep the size of the subcircuit
   as small as possible. Because every element of 'blst' is first added to 'qs',
   once the two sets are equal in size, rotation merging will no longer be 
   applicable. The only purpose of 'blst' in this function is track this 
   termination condition ('blst' is used in a more interesting way in the merge
   operation).  *)

Definition add x l :=
  if inb x l then l else (x :: l).

Fixpoint get_subcircuit' {dim} (l : PI4_ucom_l dim) (qs blst : list nat) n :=
  match n with
  | O => ([], [], l) (* unreachable with n = length l *)
  | S n' =>
      if (length qs) =? (length blst)
      then ([], [], l)
      else match next_gate l qs with
           | Some (l1, App1 UPI4_H q, l2) => 
               match get_subcircuit' l2 qs (add q blst) n' with
               | (l1', s, l2') => (l1 ++ l1', [H q] ++ s, l2')
               end
           | Some (l1, App1 u q, l2) => 
               match get_subcircuit' l2 qs blst n' with
               | (l1', s, l2') => (l1 ++ l1', [@App1 _ dim u q] ++ s, l2')
               end
           | Some (l1, App2 UPI4_CNOT q1 q2, l2) =>
               let qs' := add q1 (add q2 qs) in
               let blst' := if inb q1 blst then (add q2 blst) else blst in
               match get_subcircuit' l2 qs' blst' n' with
               | (l1', s, l2') => (l1 ++ l1', [CNOT q1 q2] ++ s, l2')
               end
           | _ => ([], [], l) (* unreachable for the PI4 gate set*)
           end
  end.

Definition get_subcircuit {dim} (l : PI4_ucom_l dim) q := 
  get_subcircuit' l [q] [] (List.length l).

(* Examples *)

Definition test1 : PI4_ucom_l 1 := T 0 :: H 0 :: X 0 :: [].
Definition test2 : PI4_ucom_l 2 := T 0 :: CNOT 0 1 :: H 0 :: CNOT 0 1 :: T 1 :: H 1 :: [].
Definition test3 : PI4_ucom_l 3 := T 0 :: H 1 :: H 2 :: X 1 :: CNOT 0 2 :: T 0 :: X 2 :: CNOT 2 1 :: H 1 :: T 2 :: [].
Definition test4 : PI4_ucom_l 3 := T 1 :: T 2 :: CNOT 1 0 :: T 0 :: CNOT 1 2 :: CNOT 0 1 :: H 2 :: CNOT 1 2 :: CNOT 0 1 :: T 1 :: H 0 :: H 1 :: [].

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

Lemma add_In_x : forall x l, List.In x (add x l).
Proof.
  intros.
  unfold add.
  bdestruct (inb x l). 
  assumption.
  left; reflexivity.
Qed.

Lemma add_In_l : forall x y l, List.In x l -> List.In x (add y l).
Proof.
  intros.
  unfold add.
  bdestruct (inb y l).
  assumption.
  right; assumption.
Qed.

Lemma get_subcircuit'_l1_does_not_reference : forall {dim} (l : PI4_ucom_l dim) qs blst n l1 s l2,
  get_subcircuit' l qs blst n = (l1, s, l2) ->
  forall q, List.In q qs -> does_not_reference l1 q = true.
Proof. 
  intros dim l qs blst n.
  generalize dependent blst.
  generalize dependent qs.
  generalize dependent l.
  induction  n; intros l qs blst l1 s l2 res q Hq; simpl in res.
  inversion res; subst. reflexivity.
  destruct (length qs =? length blst).
  inversion res; subst. reflexivity.
  destruct (next_gate l qs) eqn:ng.
  2: { inversion res; subst. reflexivity. }
  repeat destruct p.
  destruct g1.
  - dependent destruction p;
    [ destruct (get_subcircuit' g qs (add n0 blst) n) eqn:subc
    | destruct (get_subcircuit' g qs blst n) eqn:subc
    | destruct (get_subcircuit' g qs blst n) eqn:subc ];
    destruct p;
    inversion res; subst.
    all: eapply IHn in subc; eapply next_gate_l1_does_not_reference in ng.
    all: try apply Hq.
    all: apply does_not_reference_app; apply andb_true_intro; split; assumption.
  - dependent destruction p.
    destruct (get_subcircuit' g (add n0 (add n1 qs))
             (if inb n0 blst then add n1 blst else blst) n) eqn:subc.
    destruct p.
    inversion res; subst.
    eapply IHn in subc.
    eapply next_gate_l1_does_not_reference in ng.
    apply does_not_reference_app; apply andb_true_intro; split.
    apply ng. apply subc. apply Hq. 
    do 2 apply add_In_l. apply Hq.
  - dependent destruction p.
Qed.

Lemma get_subcircuit'_preserves_semantics : forall {dim} (l : PI4_ucom_l dim) qs blst n l1 s l2,
  get_subcircuit' l qs blst n = (l1, s, l2) ->
  l =l= l1 ++ s ++ l2.
Proof. 
  intros dim l qs blst n.
  generalize dependent blst.
  generalize dependent qs.
  generalize dependent l.
  induction  n; intros l qs blst l1 s l2 res; simpl in res.
  inversion res; subst. reflexivity.
  destruct (length qs =? length blst).
  inversion res; subst. reflexivity.
  destruct (next_gate l qs) eqn:ng.
  2: { inversion res; subst. reflexivity. }
  repeat destruct p.
  destruct g1.
  - specialize (next_gate_app1_returns_q _ _ _ _ _ _ ng) as Hn0. 
    apply next_gate_preserves_structure in ng; subst l.
    dependent destruction p;
    [ destruct (get_subcircuit' g qs (add n0 blst) n) eqn:subc
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
  - dependent destruction p.
    destruct (get_subcircuit' g (add n0 (add n1 qs))
             (if inb n0 blst then add n1 blst else blst) n) eqn:subc.
    destruct p.
    inversion res; subst.
    apply next_gate_preserves_structure in ng; subst l.
    specialize (get_subcircuit'_l1_does_not_reference _ _ _ _ _ _ _ subc) as dnr.
    apply IHn in subc; rewrite subc.   
    rewrite (app_assoc _ l0).
    rewrite does_not_reference_commutes_app2.
    repeat rewrite <- app_assoc; reflexivity.
    apply dnr. apply add_In_x.
    apply dnr. apply add_In_l. apply add_In_x.
  - dependent destruction p.
Qed.

Lemma get_subcircuit_l1_does_not_reference : forall {dim} (l : PI4_ucom_l dim) q l1 s l2,
  get_subcircuit l q = (l1, s, l2) ->
  does_not_reference l1 q = true.
Proof.
  intros dim l q l1 s l2 H.
  unfold get_subcircuit in H.
  eapply get_subcircuit'_l1_does_not_reference in H.
  apply H.
  left; reflexivity.
Qed.

Lemma get_subcircuit_preserves_semantics : forall {dim} (l : PI4_ucom_l dim) q l1 s l2,
  get_subcircuit l q = (l1, s, l2) ->
  l =l= l1 ++ s ++ l2.
Proof. 
  intros dim l q l1 s l2 H.
  unfold get_subcircuit in H.
  eapply get_subcircuit'_preserves_semantics in H.
  assumption.
Qed.

(** Merge a single rotation gate. **)

(* To perform rotation merging, we will need to keep track of the current (boolean) 
   state of each qubit. We will describe the classical state of a single qubit using
   a (nat -> bool) function. Because we are considering {CNOT, X, Rz} subcircuits, 
   we only need to consider boolean expressions of the form x ⊕ y ⊕ ... ⊕ 1, where 
   each term in the XOR is optional.  

   Assume some upper bound N (in practice: the dimension of the global register).
   - For i <= N - 1, (f i) indicates whether variable i is involved in the XOR.
     (f N) indicates whether the XOR includes a 1 term (i.e. is negated).

   We maintain a list of these functions to describe the state of the entire system.
   The element at index i describes the current boolean function on qubit i. *)

(* Check for equality of two boolean expressions. *)
Fixpoint f_eqb f1 f2 n := 
  match n with
  | O => true
  | S n' => eqb (f1 n') (f2 n') && (f_eqb f1 f2 n')
  end.

(* Negate a boolean expression. *)
Definition neg f dim :=
  fun i => if i =? dim then negb (f i) else (f i).

(* Compute the XOR of two boolean expressions. *)
Definition xor f1 f2 :=
  fun (i : nat) => xorb (f1 i) (f2 i).

(* If we assume that all qubits begin in a classical state, then blst tracks the
   'blacklisted' qubits that are (potentially) no longer in a classical state.
  
   Merging algorithm:
   1. If the next gate is (H q'), add q' to the blacklist and continue
   2. If the next gate is (X q'), negate q' in the representation of the 
      global state and continue
   3. If the next gate is (Rz k' q'), check if this gate can be merged with 
      the original rotation (Rz k q). If so, return the result of merging.
      Otherwise, continue.  
   4. If the next gate is (CNOT q1 q2), if neither q1 nor q2 is in the blacklist
      then update the state of q2 to be (q1 ⊕ q2) and continue. If q2 is in the 
      blacklist (but q1 is not) then continue. If q1 is in the blacklist then add
      both q1 and q2 to the blacklist and continue. *)
Fixpoint merge' {dim} (l : PI4_ucom_l dim) (blst : list nat) k q f :=
  match l with
  | App1 UPI4_H q' :: t =>
      match merge' t (add q' blst) k q f with
      | Some l => Some (H q' :: l)
      | _ => None
      end
  | App1 UPI4_X q' :: t => 
      let f' := if (inb q' blst) then f else update f q' (neg (f q') dim) in
      match merge' t blst k q f' with
      | Some l => Some (X q' :: l)
      | _ => None
      end
  | App1 (UPI4_PI4 k') q' :: t => 
      if ((negb (inb q' blst)) && (f_eqb (f q') (fun x => if x =? q then true else false) (dim + 1)))
      then let k'' := (k + k')%Z in
           if (k'' =? 8)%Z then Some t
           else if (k'' <? 8)%Z 
                then Some (App1 (UPI4_PI4 k'') q' :: t)
                else Some (App1 (UPI4_PI4 (k'' - 8)%Z) q' :: t) 
      else match merge' t blst k q f with
           | Some l => Some (App1 (UPI4_PI4 k') q' :: l)
           | _ => None
           end
  | App2 UPI4_CNOT q1 q2 :: t =>
      if ((inb q1 blst) || (inb q2 blst)) 
      then let blst' := if inb q1 blst then (add q2 blst) else blst in
           match merge' t blst' k q f with
           | Some l => Some (CNOT q1 q2 :: l)
           | _ => None
           end
      else let f' := update f q2 (xor (f q1) (f q2)) in   
           match merge' t blst k q f' with
           | Some l => Some (CNOT q1 q2 :: l)
           | _ => None
           end
  | _ => None (* failed to merge *)
  end.

Definition merge {dim} (l : PI4_ucom_l dim) k q :=
  let finit := fun i => fun j => if j =? i then true else false in
  merge' l [] k q finit.

(* Proofs *)

(* Convert from our representation of a boolean expression (b) to
   an actual boolean expression, using the mapping from variables
   to boolean values given in f. *)
Fixpoint get_boolean_expr' (b : nat -> bool) f n :=
  match n with
  | 0 => false
  | S n' => if (b n') 
           then xorb (f n') (get_boolean_expr' b f n')
           else get_boolean_expr' b f n'
  end.

Definition get_boolean_expr (b : nat -> (nat -> bool)) f n :=
  fun i =>
    if (b i n) 
    then negb (get_boolean_expr' (b i) f n)
    else get_boolean_expr' (b i) f n.

Lemma get_boolean_expr_update_neg : forall dim b f n,
  get_boolean_expr (update b n (neg (b n) dim)) f dim =
  update (get_boolean_expr b f dim) n (¬ (get_boolean_expr b f dim n)).
Proof. 
  intros.
  apply functional_extensionality.
  intros x.
  unfold get_boolean_expr, update, neg.
  bdestruct (x =? n).
  - subst.
    bdestructΩ (dim =? dim).
    assert (H1: forall f1 f2 f n, (forall i, (i < n)%nat -> f1 i = f2 i) -> 
                get_boolean_expr' f1 f n = get_boolean_expr' f2 f n).
    { clear. intros.
      induction n; try reflexivity.
      simpl.
      rewrite H; try lia.
      destruct (f2 n);
      rewrite IHn; try reflexivity;
      intros; apply H; lia. }      
    destruct (b n dim) eqn:bvn; simpl.
    + rewrite negb_involutive.
      apply H1.
      intros.
      bdestructΩ (i =? dim); reflexivity.
    + erewrite H1; try reflexivity.
      intros.
      bdestructΩ (i =? dim); reflexivity.
  - destruct (b x dim); reflexivity.
Qed.

Lemma get_boolean_expr'_xor : forall b1 b2 f n,
  get_boolean_expr' (xor b1 b2) f n = xorb (get_boolean_expr' b1 f n) (get_boolean_expr' b2 f n) .
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    unfold xor. 
    destruct (b1 n) eqn:b1n; destruct (b2 n) eqn:b2n; simpl.
    + rewrite xorb_assoc. 
      rewrite <- (xorb_assoc _ (f n)).
      rewrite (xorb_comm _ (f n)).
      repeat rewrite <- xorb_assoc. 
      rewrite xorb_nilpotent.
      rewrite xorb_false_l.
      apply IHn.
    + rewrite xorb_assoc.
      rewrite <- IHn.
      reflexivity.
    + rewrite <- xorb_assoc.
      rewrite (xorb_comm _ (f n)).
      rewrite xorb_assoc.
      rewrite <- IHn.
      reflexivity.
    + apply IHn.
Qed.

Lemma get_boolean_expr_update_xor : forall dim b f n1 n2,
  get_boolean_expr (update b n1 (xor (b n2) (b n1))) f dim =
  update (get_boolean_expr b f dim) n1
         (get_boolean_expr b f dim n1 ⊕ get_boolean_expr b f dim n2).
Proof.
  intros.
  apply functional_extensionality.
  intros x.
  replace (xor (b n2) (b n1)) with (xor (b n1) (b n2)).
  2: { unfold xor; apply functional_extensionality; intros.
       apply xorb_comm. }
  unfold get_boolean_expr, update, xor.
  bdestruct (x =? n1).
  - destruct (b n1 dim) eqn:bn1; destruct (b n2 dim) eqn:bn2; simpl.
    + rewrite xorb_negb_negb.
      apply get_boolean_expr'_xor.
    + rewrite <- negb_xorb_l. 
      rewrite <- get_boolean_expr'_xor.
      reflexivity.
    + rewrite <- negb_xorb_r. 
      rewrite <- get_boolean_expr'_xor.
      reflexivity.
    + apply get_boolean_expr'_xor.
  - reflexivity.
Qed.

Hint Resolve eqb_spec : bdestruct.
Lemma f_eqb_implies_eq : forall f1 f2 n,
  f_eqb f1 f2 n = true -> 
  forall x, (x < n)%nat -> f1 x = f2 x.
Proof.
  intros f1 f2 n H x Hx.
  induction n; try lia.
  simpl in H. 
  apply andb_prop in H as [H1 H2].
  bdestruct (x =? n).
  - subst.
    bdestruct (eqb (f1 n) (f2 n)); try discriminate. 
    assumption.
  - apply IHn; try assumption.
    lia.
Qed.

Lemma eq_implies_f_eqb : forall f n,
  f_eqb f f n = true.
Proof.
  intros. induction n. reflexivity.
  simpl. apply andb_true_intro.
  split. bdestruct (eqb (f n) (f n)); auto. 
  assumption.
Qed.

Lemma get_boolean_expr'_finit_q_large : forall b f n q,
  let finit := fun x : nat => if x =? q then true else false in
  (q >= n)%nat ->
  (forall x, (x < n)%nat -> b x = finit x) ->
  get_boolean_expr' b f n = false.
Proof.
  intros.
  induction n; try reflexivity.
  subst finit; simpl in *.
  destruct q; try lia.
  destruct (b n) eqn:bn.
  rewrite H0 in bn; try lia.
  bdestruct (n =? S q); [lia | discriminate].
  apply IHn; try lia.  
  intros. apply H0. lia.
Qed.

Lemma get_boolean_expr_finit : forall dim b f n q,
  let finit := fun x : nat => if x =? q then true else false in
  (q < dim)%nat ->
  f_eqb (b n) finit (dim + 1) = true ->
  get_boolean_expr b f dim n = f q.
Proof.
  intros.
  unfold get_boolean_expr.
  specialize (f_eqb_implies_eq _ _ _ H0) as feqb.
  clear - H feqb.
  subst finit; simpl in *.
  destruct (b n dim) eqn:bn.
  - rewrite feqb in bn; try lia.
    bdestruct (dim =? q); [lia | discriminate].
  - clear bn.
    induction dim; try lia.
    simpl.
    destruct (b n dim) eqn:bndim.
    + rewrite feqb in bndim; try lia.
      bdestruct (dim =? q); try discriminate; subst.
      erewrite get_boolean_expr'_finit_q_large.
      apply xorb_false_r.
      2: { intros. apply feqb. lia. }
      lia.
    + rewrite feqb in bndim; try lia. 
      bdestruct (dim =? q); try discriminate.
      apply IHdim.
      lia.
      intros. apply feqb. lia.
Qed.

(* To begin, we define some utilities for describing classical states. *)

Definition b2R (b : bool) : R := if b then 1%R else 0%R.
Local Coercion b2R : bool >-> R.
Local Coercion Nat.b2n : bool >-> nat.

(* Projector onto the space where qubit q is in classical state b. *)
Definition proj q dim (b : bool) := @pad 1 q dim (∣ b ⟩ × (∣ b ⟩)†).

Lemma proj_commutes_1q_gate : forall dim u q n b,
  q <> n ->
  proj q dim b × ueval_r dim n u = ueval_r dim n u × proj q dim b. 
Proof.
  intros dim u q n b neq.
  dependent destruction u; simpl.
  unfold proj, pad.
  gridify; trivial.
  all: destruct b; auto with wf_db.
Qed.

Lemma proj_commutes_2q_gate : forall dim q n1 n2 b,
  q <> n1 ->
  q <> n2 ->
  proj q dim b × ueval_cnot dim n1 n2 = ueval_cnot dim n1 n2 × proj q dim b. 
Proof.
  intros dim q n1 n2 b neq1 neq2.
  unfold proj, ueval_cnot, pad.
  gridify; trivial.
  all: destruct b; auto with wf_db.
Qed.

(*Lemma proj_commutes : forall dim q1 q2 b1 b2,
  proj q1 dim b1 × proj q2 dim b2 = proj q2 dim b2 × proj q1 dim b1.
Proof.
  intros dim q1 q2 b1 b2.
  unfold proj, pad.
  gridify; trivial.
  all: destruct b1; destruct b2; auto with wf_db.
  all: Qsimpl; reflexivity.
Qed.

Lemma proj_twice_eq : forall dim q b,
  proj q dim b × proj q dim b = proj q dim b.
Proof.
  intros dim q b.
  unfold proj, pad.
  gridify.
  destruct b; Qsimpl; reflexivity.
Qed.

Lemma proj_twice_neq : forall dim q b1 b2,
  b1 <> b2 -> proj q dim b1 × proj q dim b2 = Zero.
Proof.
  intros dim q b1 b2 neq.
  unfold proj, pad.
  gridify.
  destruct b1; destruct b2; try contradiction; Qsimpl; reflexivity.
Qed.*)

Lemma proj_X : forall dim f q n,
  proj q dim (update f n (¬ (f n)) q) × uc_eval (SQIR.X n) = uc_eval (SQIR.X n) × proj q dim (f q).
Proof.
  intros dim f q n.
  bdestruct (q =? n).
  subst. rewrite update_index_eq.
  unfold proj.
  autorewrite with eval_db.
  gridify.
  destruct (f n); Qsimpl; reflexivity.    
  rewrite update_index_neq; [| lia].
  replace (@uc_eval dim (SQIR.X n)) with (ueval_r dim n (U_R PI 0 PI)) by reflexivity.
  rewrite proj_commutes_1q_gate; [| lia].
  reflexivity.
Qed.

(* should already be defined somewhere? *)
Lemma phase_shift_on_basis_state_adj : forall (θ : R) (b : bool),
  (∣ b ⟩)† × phase_shift θ = (Cexp (b * θ)) .* (∣ b ⟩)†.
Proof.
  intros.
  destruct b; solve_matrix; autorewrite with R_db.
  reflexivity.
  rewrite Cexp_0; reflexivity.
Qed.

Lemma proj_Rz_comm : forall dim q n b k,
  proj q dim b × uc_eval (SQIR.Rz k n) = uc_eval (SQIR.Rz k n) × proj q dim b. 
Proof.
  intros dim q n b k.
  unfold proj.
  autorewrite with eval_db.
  gridify.
  all: destruct b; auto with wf_db.
  all: repeat rewrite <- Mmult_assoc; rewrite phase_shift_on_basis_state.
  all: repeat rewrite Mmult_assoc; rewrite phase_shift_on_basis_state_adj. 
  all: rewrite Mscale_mult_dist_r, Mscale_mult_dist_l; reflexivity.
Qed.

Lemma proj_Rz : forall dim q b θ,
  uc_eval (SQIR.Rz θ q) × proj q dim b = Cexp (b * θ) .* proj q dim b. 
Proof.
  intros dim q b θ.
  unfold proj.
  autorewrite with eval_db.
  gridify.
  destruct b.
  all: repeat rewrite <- Mmult_assoc; rewrite phase_shift_on_basis_state.
  all: rewrite Mscale_mult_dist_l, Mscale_kron_dist_r, Mscale_kron_dist_l; 
       reflexivity.
Qed.

Lemma proj_CNOT_control : forall dim q m n b,
  (q <> n \/ m = n) ->
  proj q dim b × uc_eval (SQIR.CNOT m n) = uc_eval (SQIR.CNOT m n) × proj q dim b.
Proof.
  intros dim q m n b H.
  destruct H.
  bdestruct (m =? n).
  (* badly typed case *)
  1,3: subst; replace (uc_eval (SQIR.CNOT n n)) with (@Zero (2 ^ dim) (2 ^ dim));
       Msimpl_light; try reflexivity.
  1,2: autorewrite with eval_db; bdestructΩ (n <? n); reflexivity.
  bdestruct (q =? m).
  (* q = control *)
  subst. unfold proj.
  autorewrite with eval_db.
  gridify.
  destruct b; Qsimpl; reflexivity.
  destruct b; Qsimpl; reflexivity.
  (* disjoint qubits *)
  bdestructΩ (q =? n).
  apply proj_commutes_2q_gate; assumption.
Qed.

Lemma proj_CNOT_target : forall dim f q n,
  proj q dim ((f q) ⊕ (f n)) × proj n dim (f n) × uc_eval (SQIR.CNOT n q) = proj n dim (f n) × uc_eval (SQIR.CNOT n q) × proj q dim (f q).
Proof.
  intros dim f q n.
  unfold proj.
  autorewrite with eval_db.
  gridify. (* slow! *)
  all: try (destruct (f n); destruct (f (n + 1 + d)%nat));        
       try (destruct (f q); destruct (f (q + 1 + d)%nat));   
       auto with wf_db.
  all: simpl; Qsimpl; reflexivity.
Qed.

(* We can use 'proj' to state that qubit q is in classical state b. *)
Definition classical {dim} q b (ψ : Vector (2 ^ dim)) := proj q dim b × ψ = ψ.

Lemma merge'_preserves_semantics_on_basis_vecs : forall {dim} (l : PI4_ucom_l dim) blst k q b l' f (ψ : Vector (2 ^ dim)),
  (q < dim)%nat ->
  uc_well_typed_l l ->
  merge' l blst k q b = Some l' ->
  let A := uc_eval (list_to_ucom (PI4_to_base_ucom_l l')) in
  let B := uc_eval (list_to_ucom (PI4_to_base_ucom_l l)) in
  (forall q, (q < dim)%nat -> not (List.In q blst) -> 
        classical q (get_boolean_expr b f dim q) ψ) ->
  A × ψ = (Cexp (f q * (IZR k * PI / 4))) .* (B × ψ).
Proof.
  intros dim l blst k q b l' f ψ Hq WT H A B Hψ.
  subst A B.
  generalize dependent ψ.
  generalize dependent l'.
  generalize dependent b.
  generalize dependent blst.
  induction l; try discriminate.
  intros blst b l' H ψ Hψ.
  simpl in H.
  destruct a; dependent destruction p.
  Local Opaque ueval_r.
  - (* H gate *)
    destruct (merge' l (add n blst) k q b) eqn:mer; try discriminate.
    inversion H; subst. simpl.
    repeat rewrite Mmult_assoc.
    eapply IHl; try apply mer.
    inversion WT; auto.
    intros q0 Hq01 Hq02. unfold classical.
    rewrite <- Mmult_assoc.
    rewrite proj_commutes_1q_gate.
    rewrite Mmult_assoc.
    rewrite (Hψ q0); auto.
    contradict Hq02. apply add_In_l. assumption. 
    contradict Hq02. subst. apply add_In_x.
  - (* X gate *)
    remember (if inb n blst then b else update b n (neg (b n) dim)) as b'.
    destruct (merge' l blst k q b') eqn:mer; try discriminate.
    inversion H; subst. simpl.
    repeat rewrite Mmult_assoc.
    eapply IHl; try apply mer.
    inversion WT; auto.
    intros q0 Hq01 Hq02. unfold classical.
    rewrite <- Mmult_assoc.
    bdestruct (inb n blst).
    + rewrite proj_commutes_1q_gate.
      rewrite Mmult_assoc.
      rewrite (Hψ q0); auto.
      intro contra. subst. contradiction.
    + replace (ueval_r dim n (U_R PI 0 PI)) with (@uc_eval dim (SQIR.X n)) by reflexivity.
      rewrite get_boolean_expr_update_neg.
      rewrite proj_X.
      rewrite Mmult_assoc.
      rewrite (Hψ q0); auto.
  - (* PI4 gate *)
    destruct (negb (inb n blst) && f_eqb (b n) (fun x : nat => if x =? q then true else false) (dim + 1)) eqn:cond.
    + apply andb_true_iff in cond as [Hinb feqb].
      bdestruct (inb n blst); try discriminate; clear Hinb.
      inversion WT; subst.
      specialize (Hψ _ H3 H0). unfold classical in Hψ.
      eapply get_boolean_expr_finit in feqb; try assumption.
      destruct (k0 + k =? 8)%Z eqn:k0k8;
      [| destruct (k0 + k <? 8)%Z eqn:k0k];
      inversion H; subst; simpl.
      2: replace (ueval_r dim n (U_R 0 0 (IZR (k0 + k) * PI / 4))) with (@uc_eval dim (SQIR.Rz (IZR (k0 + k) * PI / 4) n)) by reflexivity.
      3: replace (ueval_r dim n (U_R 0 0 (IZR (k0 + k - 8) * PI / 4))) with (@uc_eval dim (SQIR.Rz (IZR (k0 + k - 8) * PI / 4) n)) by reflexivity.
      all: replace (ueval_r dim n (U_R 0 0 (IZR k * PI / 4))) with (@uc_eval dim (SQIR.Rz (IZR k * PI / 4) n)) by reflexivity.
      all: repeat rewrite Mmult_assoc; rewrite <- Mscale_mult_dist_r;
           apply f_equal2; try reflexivity.
      all: rewrite <- Hψ.
      all: repeat rewrite <- Mmult_assoc; repeat rewrite proj_Rz.
      all: repeat rewrite Mscale_mult_dist_l; rewrite Mscale_assoc. 
      rewrite <- (Mscale_1_l _ _ (proj _ _ _ × _)) at 1.
      all: apply f_equal2; try reflexivity.
      all: rewrite feqb; rewrite <- Cexp_add.
      all: repeat rewrite <- Rmult_div_assoc;
           rewrite <- Rmult_plus_distr_l; rewrite <- Rmult_plus_distr_r;
           rewrite <- plus_IZR.
      rewrite Z.eqb_eq in k0k8.
      rewrite k0k8.
      replace (8 * (PI / 4))%R with (2 * PI)%R by lra.
      destruct (f q); simpl; autorewrite with R_db; autorewrite with Cexp_db; auto.
      reflexivity.
      rewrite minus_IZR.
      unfold Rminus. rewrite Rmult_plus_distr_r, Rmult_plus_distr_l.
      replace (- (8) * (PI / 4))%R with (-(2 * PI))%R by lra.
      rewrite Cexp_add.
      destruct (f q); simpl; autorewrite with R_db; autorewrite with Cexp_db; lca.
    + destruct (merge' l blst k0 q b) eqn:mer; try discriminate.
      inversion H; subst. simpl.
      repeat rewrite Mmult_assoc.
      eapply IHl; try apply mer.
      inversion WT; auto.
      intros q0 Hq01 Hq02. unfold classical.
      rewrite <- Mmult_assoc.
      replace (ueval_r dim n (U_R 0 0 (IZR k * PI / 4))) with (@uc_eval dim (SQIR.Rz (IZR k * PI / 4) n)) by reflexivity.
      rewrite proj_Rz_comm.
      rewrite Mmult_assoc.
      rewrite (Hψ q0); auto.
  - (* CNOT gate *)
    bdestruct (inb n blst); bdestruct (inb n0 blst); simpl in H;
    [ destruct (merge' l (add n0 blst) k q b) eqn:mer
    | destruct (merge' l (add n0 blst) k q b) eqn:mer
    | destruct (merge' l blst k q b) eqn:mer
    | destruct (merge' l blst k q (update b n0 (xor (b n) (b n0)))) eqn:mer];
    try discriminate; inversion H; subst; simpl;
    repeat rewrite Mmult_assoc;
    eapply IHl; try apply mer; inversion WT; subst; auto;
    intros q0 Hq01 Hq02; unfold classical;
    rewrite <- Mmult_assoc;
    replace (ueval_cnot dim n n0) with (@uc_eval dim (SQIR.CNOT n n0)) by reflexivity.
    (* first, the cases where we do not update the boolean state *)
    1,2,3: rewrite proj_CNOT_control. 
    1,3,5: rewrite Mmult_assoc; rewrite (Hψ q0); auto.
    1,2: contradict Hq02; apply add_In_l; assumption.
    1,2,3: left; contradict Hq02; subst; try apply add_In_x; assumption.
    (* next, the case where we need to use proj_CNOT_target *)
    rewrite get_boolean_expr_update_xor.
    bdestruct (q0 =? n0).
    2: { rewrite update_index_neq; try lia.
         rewrite proj_CNOT_control; try (left; assumption).
         rewrite Mmult_assoc; rewrite (Hψ q0); auto. }
    subst. rewrite update_index_eq.
    unfold classical in Hψ.
    rewrite <- (Hψ n H6 H0) at 1.
    rewrite <- (Mmult_assoc _ _ ψ).
    rewrite (Mmult_assoc (proj _ _ _)).
    rewrite <- proj_CNOT_control.
    rewrite <- (Mmult_assoc (proj _ _ _)).
    rewrite proj_CNOT_target.
    rewrite proj_CNOT_control.
    repeat rewrite Mmult_assoc. 
    rewrite 2 Hψ; auto.
    all: specialize (Nat.eq_dec n n0) as Hdec; destruct Hdec; auto.
Qed.

Lemma f_to_vec_classical : forall n q f,
  (q < n)%nat -> classical q (f q) (f_to_vec 0 n f).
Proof.
  intros n q f Hq.
  unfold classical, proj.
  induction n; try lia.
  unfold pad.
  replace (q + 1)%nat with (S q) by lia. 
  bdestructΩ (S q <=? S n); clear H.
  bdestruct (q =? n).
  - subst. replace (n - n)%nat with O by lia.
    simpl. Msimpl_light.
    restore_dims.
    rewrite kron_mixed_product.
    Msimpl_light; apply f_equal2; auto.
    destruct (f n); solve_matrix.
  - remember (n - q - 1)%nat as x.
    replace (n - q)%nat with (x + 1)%nat by lia.
    replace n with (q + 1 + x)%nat by lia.
    replace (2 ^ (x + 1))%nat with (2 ^ x * 2)%nat by unify_pows_two.
    rewrite <- id_kron.
    rewrite <- kron_assoc.
    replace (2 ^ (q + 1 + x) + (2 ^ (q + 1 + x) + 0))%nat with (2 ^ (q + 1 + x) * 2)%nat by lia.
    repeat rewrite Nat.pow_add_r.
    replace 1%nat with (1 * 1)%nat by lia. 
    rewrite kron_mixed_product; simpl.
    replace (q + 1 + x)%nat with n by lia.
    subst.
    Msimpl_light.
    2: destruct (f n); auto with wf_db.
    rewrite <- IHn at 2; try lia.
    unfold pad. 
    bdestructΩ (q + 1 <=? n); clear H0.
    replace (n - (q + 1))%nat with (n - q - 1)%nat by lia.
    restore_dims. reflexivity.
Qed.

Lemma merge_preserves_semantics : forall {dim} (s : PI4_ucom_l dim) k q l',
  uc_well_typed_l (App1 (UPI4_PI4 k) q :: s) ->
  merge s k q = Some l' ->
  l' =l= App1 (UPI4_PI4 k) q :: s.
Proof.
  intros dim s k q l' WT H.
  inversion WT; subst.
  unfold merge in H.
  unfold uc_equiv_l, uc_equiv.
  eapply equal_on_basis_states_implies_equal; auto with wf_db.
  intros f.
  remember (fun i j : nat => if j =? i then true else false) as finit.
  assert (forall x, (x < dim)%nat -> get_boolean_expr finit f dim x = f x).
  { clear - Heqfinit.
    intros.
    apply get_boolean_expr_finit; try assumption.
    subst finit; simpl. apply eq_implies_f_eqb. }
  simpl PI4_to_base_ucom_l; simpl list_to_ucom.
  replace (uapp1 (U_R 0 0 (IZR k * PI / 4)) q) with (@SQIR.Rz dim (IZR k * PI / 4) q) by reflexivity.
  simpl.
  repeat rewrite Mmult_assoc.
  rewrite f_to_vec_Rz; try assumption.
  rewrite Mscale_mult_dist_r.
  rewrite <- Mscale_mult_dist_l.
  rewrite Mscale_mult_dist_l.
  eapply merge'_preserves_semantics_on_basis_vecs; auto.
  apply H. intros q0 Hq0 _.
  unfold classical.
  rewrite H0; auto.
  apply f_to_vec_classical; auto.
Qed.

(* Examples *)

Definition test5 : PI4_ucom_l 3 := CNOT 0 2 :: T 0 :: X 2 :: CNOT 2 1 :: T 2 :: [].
(* Result: Some [CNOT 0 2; P 0; X 2; CNOT 2 1; T 2] *)
Compute (merge test5 1 0).

Definition test6 : PI4_ucom_l 3 := CNOT 1 0 :: T 0 :: CNOT 1 2 :: CNOT 0 1 :: H 2 :: CNOT 1 2 :: CNOT 0 1 :: T 1 :: [].
(* Result: Some [CNOT 1 0; T 0; CNOT 1 2; CNOT 0 1; H 2; CNOT 1 2; CNOT 0 1; P 1] *)
Compute (merge test6 1 1).

(** Final optimization definition. **)

Definition merge_rotation {dim} (l : PI4_ucom_l dim) k q :=
  let (tmp, l2) := get_subcircuit l q in
  let (l1, s) := tmp in
  match merge s k q with
  | Some s' => Some (l1 ++ s' ++ l2)
  | _ => None
  end.

Fixpoint merge_rotations' {dim} (l : PI4_ucom_l dim) n :=
  match n with
  | O => l
  | S n' => match l with
           | [] => []
           | App1 (UPI4_PI4 k) q :: t =>
               match merge_rotation t k q with
               | None => App1 (UPI4_PI4 k) q :: (merge_rotations' t n') 
               | Some l' => merge_rotations' l' n'
               end
           | g :: t => g :: (merge_rotations' t n')
           end
  end.

Definition merge_rotations {dim} (l : PI4_ucom_l dim) := 
  merge_rotations' l (List.length l).

(* Proofs *)

Lemma merge_rotation_preserves_semantics : forall {dim} (l : PI4_ucom_l dim) k q l',
  (q < dim)%nat ->
  uc_well_typed_l l ->
  merge_rotation l k q = Some l' ->
  l' =l= App1 (UPI4_PI4 k) q :: l.
Proof.
  intros dim l k q l' Hq WT H.
  unfold merge_rotation in H. 
  destruct (get_subcircuit l q) eqn:subc.
  destruct p.
  destruct (merge l1 k q) eqn:mer; try discriminate.
  specialize (get_subcircuit_l1_does_not_reference _ _ _ _ _ subc) as dnr.
  apply get_subcircuit_preserves_semantics in subc.
  apply merge_preserves_semantics in mer.
  2: { constructor; try assumption.
       apply (uc_equiv_l_implies_WT _ _ subc) in WT. 
       apply uc_well_typed_l_app in WT as [_ WT].
       apply uc_well_typed_l_app in WT as [WT _].
       assumption. }
  inversion H; subst.
  rewrite subc.
  rewrite mer.
  rewrite app_comm_cons.
  rewrite (cons_to_app _ l1).
  rewrite (cons_to_app _ l0).
  rewrite (does_not_reference_commutes_app1 _ _ _ dnr).
  repeat rewrite app_assoc.
  reflexivity.
Qed.   

Lemma merge_rotations_sound : forall {dim} (l : PI4_ucom_l dim),
  uc_well_typed_l l ->
  merge_rotations l ≅l≅ l.
Proof. 
  intros.
  unfold merge_rotations.
  (* the value of n is unimportant for correctness *)
  remember (length l) as n; clear Heqn.
  generalize dependent l.
  induction n; try reflexivity.
  intros. simpl.
  destruct l; try reflexivity.
  inversion H; subst.
  dependent destruction u. 
  all: try (rewrite IHn; try assumption; reflexivity).
  destruct (merge_rotation l k n0) eqn:mr.
  2: rewrite IHn; try assumption; reflexivity.
  apply merge_rotation_preserves_semantics in mr; try assumption.
  rewrite IHn.
  apply uc_equiv_cong_l in mr.
  apply mr.
  eapply uc_equiv_l_implies_WT. 
  symmetry in mr; apply mr.
  constructor; assumption.
Qed.

Lemma merge_rotations_WT: forall {dim} (l : PI4_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (merge_rotations l).
Proof.
  intros dim l WT.
  specialize (merge_rotations_sound l WT) as H.
  symmetry in H.
  apply uc_cong_l_implies_WT in H; assumption.
Qed.

(* Examples *)

Definition test7 : PI4_ucom_l 4 := T 3 :: CNOT 0 3 :: P 0 :: CNOT 1 2 :: CNOT 0 1 :: TDAG 2 :: T 0 :: CNOT 1 2 :: CNOT 2 1 :: TDAG 1 :: CNOT 3 0 :: CNOT 0 3 :: T 0 :: T 3 :: [].
Definition test8 : PI4_ucom_l 2 := T 1 :: CNOT 0 1 :: Z 1 :: CNOT 0 1 :: Z 0 :: T 1 :: CNOT 1 0 :: [].
Definition test9 : PI4_ucom_l 4 := CNOT 2 3 :: T 0 :: T 3 :: CNOT 0 1 :: CNOT 2 3 :: CNOT 1 2 :: CNOT 1 0 :: CNOT 3 2 :: CNOT 1 2 :: CNOT 0 1 :: T 2 :: TDAG 1 :: [].
Definition test10 : PI4_ucom_l 3 := T 1 :: T 2 :: CNOT 0 1 :: CNOT 1 2 :: CNOT 1 0 :: T 0 :: CNOT 2 1 :: TDAG 1 :: [].

(* Result: [CNOT 1 2; CNOT 0 3; CNOT 0 1; CNOT 1 2; CNOT 2 1; PDAG 1; CNOT 3 0; CNOT 0 3; P 0; Z 3] *)
Compute (merge_rotations test7).
(* Result: [CNOT 0 1; Z 1; CNOT 0 1; Z 0; P 1; CNOT 1 0] *)
Compute (merge_rotations test8).
(* Result: [CNOT 2 3; CNOT 0 1; CNOT 2 3; CNOT 1 2; CNOT 1 0; CNOT 3 2; CNOT 1 2; CNOT 0 1; P 2] *)
Compute (merge_rotations test9).
(* Result: [CNOT 0 1; CNOT 1 2; CNOT 1 0; P 0; CNOT 2 1] *)
Compute (merge_rotations test10).
