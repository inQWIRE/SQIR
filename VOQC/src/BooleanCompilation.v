Require Import UnitaryOps.

Require Import RCIR.
Open Scope ucom.

(*********************************)
(** Boolean Circuit Compilation **)
(*********************************)
(* This file defines a 'compile' function that converts an arbitrary
   boolean expression into a reversible circuit that (provably) uncomputes 
   its ancillae. We use eager ancilla cleanup, which requires fewer qubits,
   but more gates, than the lazy approach. Because SQIR does not allow
   initializing / discarding qubits, we precompute the number of ancillae
   needed and include them in the global register.
 
   The boolean expression language and compilation strategy are modelled 
   after the Oracles.v file in (Re)QWIRE, which is based on the ReVerC 
   reversible circuit compiler. 

   We prove that compilation is correct by showing that the output circuit
   has the expected behavior on any basis state. The proof requires some
   new formalisms for describing classical states (see 'f_to_vec'). *)

(** Boolean expressions **)


Inductive bexp := 
| b_t   : bexp
| b_f   : bexp
| b_var : nat -> bexp
| b_and : bexp -> bexp -> bexp 
| b_xor : bexp -> bexp -> bexp
| b_or : bexp -> bexp -> bexp.

Fixpoint interpret_bexp (b : bexp) (f : nat -> bool) : bool :=
  match b with
  | b_t         => true 
  | b_f         => false 
  | b_var v     => f v 
  | b_and b1 b2 => (interpret_bexp b1 f) && (interpret_bexp b2 f)
  | b_xor b1 b2 => (interpret_bexp b1 f) ⊕ (interpret_bexp b2 f)
  | b_or b1 b2 => (interpret_bexp b1 f) || (interpret_bexp b2 f)
  end.  

Inductive bexp_well_typed : nat -> bexp -> Prop :=
  | WT_b_t : forall n, bexp_well_typed n b_t
  | WT_b_f : forall n, bexp_well_typed n b_f
  | WT_b_var : forall n q, (q < n)%nat -> bexp_well_typed n (b_var q)
  | WT_b_and : forall n b1 b2, bexp_well_typed n b1 -> bexp_well_typed n b2 -> bexp_well_typed n (b_and b1 b2)
  | WT_b_xor : forall n b1 b2, bexp_well_typed n b1 -> bexp_well_typed n b2 -> bexp_well_typed n (b_xor b1 b2)
  | WT_b_or : forall n b1 b2, bexp_well_typed n b1 -> bexp_well_typed n b2 -> bexp_well_typed n (b_or b1 b2) .

Lemma well_typed_increase_dim : forall b n n',
  (n <= n')%nat ->
  bexp_well_typed n b ->
  bexp_well_typed n' b.
Proof.
  intros.
  induction H0; try constructor; try lia;
  try apply IHbexp_well_typed1; 
  try apply IHbexp_well_typed2; 
  assumption.
Qed.

Lemma interpret_bexp_f : forall i b f f',
  bexp_well_typed i b ->
  (forall k, (k < i)%nat -> f k = f' k) ->
  interpret_bexp b f = interpret_bexp b f'.
Proof.
  intros.
  induction H; simpl; try reflexivity.
  - apply H0. assumption.
  - rewrite IHbexp_well_typed1; try assumption.
    rewrite IHbexp_well_typed2; try assumption.
    reflexivity.
  - rewrite IHbexp_well_typed1; try assumption.
    rewrite IHbexp_well_typed2; try assumption.
    reflexivity.
    - rewrite IHbexp_well_typed1; try assumption.
    rewrite IHbexp_well_typed2; try assumption.
    reflexivity.
Qed.

Lemma interpret_bexp_update : forall b f i j r,
  (i <= j)%nat ->
  bexp_well_typed i b ->
  interpret_bexp b f = interpret_bexp b (update f j r).
Proof.
  intros.
  apply interpret_bexp_f with (i:=i); try assumption.
  intros.
  rewrite update_index_neq; try lia.
  reflexivity.
Qed.

(** Compilation of boolean expressions to oracles **)

(* How many input variables does this expression use? *)
Fixpoint max_var b v :=
  match b with 
  | b_var v' => max v v'
  | b_and b1 b2 => max (max_var b1 v) (max_var b2 v)
  | b_xor b1 b2 => max (max_var b1 v) (max_var b2 v)
  | b_or b1 b2 => max (max_var b1 v) (max_var b2 v)
  | _ => v
  end.

Fixpoint no_vars b :=
  match b with
  | b_var _ => false
  | b_and b1 b2 => no_vars b1 && no_vars b2
  | b_xor b1 b2 => no_vars b1 && no_vars b2
  | b_or b1 b2 => no_vars b1 && no_vars b2
  | _ => true
  end.

Definition num_inputs b : nat := if (no_vars b) then 0 else (max_var b 0) + 1.

Lemma num_inputs_well_typed : forall b,
  bexp_well_typed (num_inputs b) b.
Proof.
  induction b.
  - constructor.
  - constructor.
  - unfold num_inputs; simpl.
    constructor. lia.
  - constructor.
    + apply well_typed_increase_dim with (n:=num_inputs b1); try assumption.
      unfold num_inputs.
      simpl; destruct (no_vars b1); destruct (no_vars b2); simpl; lia.
    + apply well_typed_increase_dim with (n:=num_inputs b2); try assumption.
      unfold num_inputs.
      simpl; destruct (no_vars b1); destruct (no_vars b2); simpl; lia.
  - constructor.
    + apply well_typed_increase_dim with (n:=num_inputs b1); try assumption.
      unfold num_inputs.
      simpl; destruct (no_vars b1); destruct (no_vars b2); simpl; lia.
    + apply well_typed_increase_dim with (n:=num_inputs b2); try assumption.
      unfold num_inputs.
      simpl; destruct (no_vars b1); destruct (no_vars b2); simpl; lia.
        - constructor.
    + apply well_typed_increase_dim with (n:=num_inputs b1); try assumption.
      unfold num_inputs.
      simpl; destruct (no_vars b1); destruct (no_vars b2); simpl; lia.
    + apply well_typed_increase_dim with (n:=num_inputs b2); try assumption.
      unfold num_inputs.
      simpl; destruct (no_vars b1); destruct (no_vars b2); simpl; lia.
Qed.

(* How many ancillary qubits are needed to represent this expression? *)
Fixpoint num_ancillae b : nat :=
  match b with
  | b_and b1 b2 => 2 + (max (num_ancillae b1) (num_ancillae b2))
  | b_xor b1 b2 => max (num_ancillae b1) (num_ancillae b2)
  | b_or b1 b2 => 2 + (max (num_ancillae b1) (num_ancillae b2))
  | _ => 0
  end.

(* Total number of qubits required. *)
Definition b_dim (b : bexp) : nat := (num_inputs b) + 1 + (num_ancillae b).
Notation "p1 ; p2" := (bcseq p1 p2) (at level 50).

(* Translate a boolean expression into a reversible circuit. The produced 
   program should only modify the qubit at index i.
   - i is the index of the result
   - j is the index of the next available ancilla. *)
 
Fixpoint compile'  (b : bexp) (i j : nat) : bccom :=
  match b with
  | b_t         => bcx i
  | b_f         => bcskip
  | b_var v     => bccnot v i
  | b_and b1 b2 => compile' b1 j (j+2); 
                  compile' b2 (j+1) (j+2);
                  bcccnot j (j+1) i;
                  compile' b2 (j+1) (j+2); 
                  compile' b1 j (j+2)
  | b_xor b1 b2 => compile' b1 i j; 
                   compile' b2 i j
  | b_or b1 b2 => compile' b1 j (j + 2);
                  compile' b2 (j+1) (j + 2);
                 bcccnot  j (j+1) i;
                compile' b2 (j+1) (j +2 );
                  compile' b1 j (j + 2);
                  compile' b1 i (j + 2);
                  compile' b2 i (j + 2)
  end.

Definition compile b : bccom := 
  compile' b (num_inputs b) ((num_inputs b) + 1).

(* Correctness of compile':
   1. The value at index i is xor-ed with the desired boolean expression.
   2. All other values remain unchanged.

   Notes:
   * The well-typedness constraint is used in the b_var case.
   * 'i < j' is used when applying f_to_vec_X, f_to_vec_CNOT, and f_to_vec_TOFF.
   * 'j + (num_ancillae b) < n + 1' and 'forall k ...' are used in the b_and 
     case -- note that this is the only case where the ancilla matter.
*)(*
Lemma cnot_false : forall (n i : nat) (f : nat -> bool),
    (fun j0 : nat => if j0 =? i then f i ⊕ false else f j0
   *)

Local Opaque CCX.

Lemma and_xor_xor : forall (b1 b2 : bool),
    xorb (b1 && b2) (xorb b1 b2) = orb b1 b2.
Proof.
  intros.
  destruct b1; 
    destruct b2;
    auto.
Qed.   

Lemma bcseq_assoc : forall (b1 b2 b3 : bccom) (f : nat -> bool),
    bcexec(bcseq (bcseq b1 b2) b3) f = bcexec( bcseq b1 ( bcseq b2 b3)) f.
  Proof. 
    intros.
    generalize dependent b2.
    generalize dependent b3.
    generalize dependent f. 
    induction b1; intros; simpl; reflexivity. 
    Qed. 
(* 
 bcexec
    (compile' b1 j (j + 2);
     (compile' b2 (j + 1) (j + 2);
      (bcccnot j (j + 1) i; (compile' b2 (j + 1) (j + 2); compile' b1 j (j + 2))))) f =
  f [i |-> f i ⊕ (interpret_bexp b1 f && interpret_bexp b2 f)]
 *)

  Lemma bcseq_update : forall (b1 b2 : bccom) (f : nat -> bool),
      bcexec ( bcseq b1 b2 ) f = bcexec b2 (bcexec b1 f).
  Proof.
    intros.
    generalize dependent b2.
    generalize dependent f.
    induction b1; simpl; reflexivity. 
    Qed. 


Lemma compile'_and_correct : forall dim (b1 b2 : bexp) (f : nat -> bool) (i j : nat),
  bexp_well_typed i (b_and b1 b2) -> 
  (i < j)%nat ->
  (j + (num_ancillae (b_and b1 b2)) < dim + 1)%nat ->
  (forall k, (k > i)%nat -> f k = false) ->
  (forall i : nat,
         bexp_well_typed i b1 ->
         forall j : nat,
         (i < j)%nat ->
         (j + num_ancillae b1 < dim + 1)%nat ->
         forall f : nat -> bool,
         (forall k : nat, (k > i)%nat -> f k = false) ->
         bcexec (compile' b1 i j) f = f [i |-> f i ⊕ interpret_bexp b1 f]) ->
  (forall i : nat,
         bexp_well_typed i b2 ->
         forall j : nat,
         (i < j)%nat ->
         (j + num_ancillae b2 < dim + 1)%nat ->
         forall f : nat -> bool,
         (forall k : nat, (k > i)%nat -> f k = false) ->
         bcexec (compile' b2 i j) f = f [i |-> f i ⊕ interpret_bexp b2 f]) ->
  (bcexec (compile' b1 j (j+2); 
                  compile' b2 (j+1) (j+2);
                  bcccnot j (j+1) i;
                  compile' b2 (j+1) (j+2); 
                  compile' b1 j (j+2))) f
    = (update f i ((f i) ⊕ (interpret_bexp (b_and b1 b2) f))).
Proof.
    intros dim b1 b2 f i j H H0 H1 H2 IHb1 IHb2.
    inversion H; subst; clear H.
    assert (bexp_well_typed j b1).
    { apply (well_typed_increase_dim b1 i j); try assumption; lia. }
    assert (bexp_well_typed (j+1) b2).
    { apply (well_typed_increase_dim b2 i (j+1)); try assumption; lia. }
    assert (j < j + 2)%nat by lia.
    assert (j + 1 < j + 2)%nat by lia.
    simpl in H1.
    assert ((j + 2) + num_ancillae b1 < dim + 1)%nat by lia.
    assert ((j + 2) + num_ancillae b2 < dim + 1)%nat by lia.
    specialize (IHb1 j H (j+2)%nat H4 H8).
    specialize (IHb2 (j+1)%nat H3 (j+2)%nat H5 H9).
    clear H H3 H4 H5 H8 H9. (* difficult because it isn't multiplying *)
    
    simpl compile'.
    simpl interpret_bexp.
    (*repeat rewrite Mmult_assoc.*)
    repeat rewrite bcseq_assoc.
    rewrite bcseq_update; try lia. 
    rewrite IHb1.
    
    rewrite bcseq_update.
    rewrite IHb2; try lia.

    rewrite update_index_neq; try lia.
    
    rewrite bcseq_update.         
    rewrite bcccnot_correct; try lia.
    rewrite update_index_eq; try lia.
    rewrite update_twice_neq; try lia.
  
    rewrite bcseq_update.
    rewrite IHb2.
    repeat rewrite update_twice_eq; try lia.

    rewrite <-  interpret_bexp_f with (i:= j) (f:=f) (f' := f [j |-> f j ⊕ interpret_bexp b1 f]).
    repeat rewrite update_index_eq.
    rewrite update_index_neq; try lia.

    rewrite IHb1.
    rewrite update_index_neq; try lia.
    rewrite update_index_neq; try lia.
    rewrite update_twice_neq; try lia.
    rewrite update_index_eq; try lia.
    rewrite update_index_neq; try lia.
    rewrite update_index_neq; try lia.
    assert ((f (j + 1) %nat) = false).
    apply H2; try lia.
    assert ((f (j) %nat) = false).
    apply H2; try lia.
    rewrite H.
    rewrite H3.

    rewrite xorb_false_l.
    rewrite xorb_false_l.
    rewrite update_index_eq.
    
    rewrite (update_twice_neq _ (j)); try lia.
    rewrite (update_twice_neq _ (j)); try lia.
    rewrite <-  interpret_bexp_f with (i:= i) (f:=f)
             (f' := (((f [i |-> f i ⊕ (interpret_bexp b2 f && interpret_bexp b1 f)]) [j
             |-> interpret_bexp b1 f]) [j + 1 |-> interpret_bexp b2 f])).
    rewrite <-  interpret_bexp_f with (i:= i) (f:=f)
             (f' := (((f [i |-> f i ⊕ (interpret_bexp b2 f && interpret_bexp b1 f)]) [j
            |-> interpret_bexp b1 f]) [j + 1 |-> interpret_bexp b2 f ⊕ interpret_bexp b2 f])).
    rewrite xorb_nilpotent.
    rewrite xorb_nilpotent.
    rewrite update_twice_neq; try lia.
    rewrite update_twice_eq; try lia.
    rewrite update_same; try lia.
    rewrite update_same; try lia.
    rewrite andb_comm.    
    reflexivity.

    rewrite update_index_neq; try lia.
    rewrite H3.
    reflexivity.

    rewrite update_index_neq; try lia.
    rewrite update_index_neq; try lia.
    rewrite H2; try lia.
    reflexivity.

    apply H6.

    intros; repeat (rewrite update_index_neq; try lia); try reflexivity.

    apply H7.

    intros; repeat (rewrite update_index_neq; try lia); try reflexivity.

    intros.
    rewrite update_twice_neq; try lia.
    rewrite update_index_neq; try lia.
    rewrite update_twice_neq; try lia.
    rewrite update_index_neq; try lia.
    assert ((f (j + 1) %nat) = false).
    apply H2; try lia.
    assert ((f (j) %nat) = false).
    apply H2; try lia.
    rewrite H3.
    rewrite H4.
    rewrite xorb_false_l.
    rewrite xorb_false_l.
    rewrite <-  interpret_bexp_f with (i:= i) (f:=f)
             (f' := (((f [j |-> interpret_bexp b1 f]) [i
             |-> (f [j |-> interpret_bexp b1 f]) i
                 ⊕ (interpret_bexp b2 f &&
                    ((f [j |-> interpret_bexp b1 f]) [j + 1 |-> interpret_bexp b2 f]) j)]) [
            j + 1 |-> interpret_bexp b2 f])); try lia.
    rewrite xorb_nilpotent.
    rewrite update_same.
    apply H2; lia.
    symmetry. apply H3.

    apply H7.

    intros.
    rewrite update_index_neq; try lia.
    rewrite update_index_neq; try lia.
    rewrite update_index_neq; try lia.
    reflexivity.

    apply well_typed_increase_dim with (n:=i)(n':=j); try lia. apply H7.

    intros.
    rewrite update_index_neq; try lia; reflexivity.

    intros.
    rewrite update_twice_neq; try lia.
    rewrite update_index_neq; try lia.
    rewrite update_twice_neq; try lia.
    rewrite update_index_neq; try lia.
    assert ((f (j + 1) %nat) = false).
    apply H2; try lia.
    assert ((f (j) %nat) = false).
    apply H2; try lia.
    rewrite H3.
    rewrite H4.
    rewrite xorb_false_l.
    rewrite xorb_false_l.
    rewrite update_index_neq; try lia.
    apply H2; try lia.

    intros.
    rewrite update_index_neq; try lia.
    apply H2; try lia.

    intros.
    apply H2; try lia.
Qed.    (* END AND *)

  
Lemma compile'_correct : forall dim (b : bexp) (f : nat -> bool) (i j : nat),
  bexp_well_typed i b -> 
  (i < j)%nat ->
  (j + (num_ancillae b) < dim + 1)%nat ->
  (forall k, (k > i)%nat -> f k = false) ->
  (bcexec (@compile' b i j)) f
    = (update f i ((f i) ⊕ (interpret_bexp b f))).
Proof.
  intros.
  generalize dependent f.
  generalize dependent j.
  generalize dependent i. 
  induction b; intros.
  - (* b_t *)
    unfold compile'. 

    simpl. reflexivity. 

  - (* b_f *)
    simpl.
    rewrite xorb_false_r.
    rewrite update_same; reflexivity. 

  - (* b_var v *)
    inversion H; subst.
    unfold compile'.
    simpl.
    destruct (f n).
    + reflexivity.
    + rewrite xorb_false_r.
      rewrite update_same;
        reflexivity.

      
  - (* b_and b1 b2 *)
    simpl compile'.
    apply compile'_and_correct with (dim:= dim); auto.

  - (* b_xor b1 b2 *)
    inversion H; subst; clear H.
    simpl.

    
    simpl in H1.
    rewrite IHb1; try assumption; try lia.
    rewrite IHb2; try assumption; try lia.
    2: { intros. rewrite update_index_neq; try apply H2; lia. }
    rewrite update_twice_eq.
    rewrite update_index_eq.
    rewrite <- interpret_bexp_update with (i:=i);
      try assumption; try lia.
    rewrite xorb_assoc.
    reflexivity.

  -
    simpl compile'.
    rewrite bcseq_assoc.
    rewrite bcseq_update.
    
    inversion H; subst; clear H.
    assert (bexp_well_typed j b1).
    { apply (well_typed_increase_dim b1 i j); try assumption; lia. }
    assert (bexp_well_typed (j+1) b2).
    { apply (well_typed_increase_dim b2 i (j+1)); try assumption; lia. }
    assert (j < j + 2)%nat by lia.
    assert (j + 1 < j + 2)%nat by lia.
    simpl in H1.
    assert ((j + 2) + num_ancillae b1 < dim + 1)%nat by lia.
    assert ((j + 2) + num_ancillae b2 < dim + 1)%nat by lia.
    clear H H3 H4 H5 H8 H9. (* difficult because it isn't multiplying *)

    
    rewrite compile'_and_correct with (dim:= dim); auto; try constructor; try assumption.
    rewrite bcseq_update.
    rewrite IHb1;  auto;  try lia.
    rewrite update_index_eq.
    rewrite update_twice_eq.
    simpl interpret_bexp.
    rewrite <- interpret_bexp_update with (i:=i); try assumption; try lia.
    
        
    rewrite IHb2;  auto;  try lia.
    rewrite update_index_eq.
    rewrite update_twice_eq.
    rewrite <- interpret_bexp_update with (i:=i); try assumption; try lia.

    rewrite xorb_assoc.
    rewrite xorb_assoc.
    rewrite and_xor_xor.
    reflexivity.

    intros.
    rewrite update_index_neq; auto; try lia.

    intros.
    rewrite update_index_neq; auto; try lia.
Qed.
(*
Lemma compile_correct : forall (b : bexp) (f : nat -> bool) (r : bool), 
  let in_s := fun i => if i <? (num_inputs b) then f i else false in
  let out_s := update in_s (num_inputs b) (interpret_bexp b f) in
  (@uc_eval (b_dim b) (compile b)) × f_to_vec (b_dim b) in_s
  = f_to_vec (b_dim b) out_s.
 
Proof.
  intros.
  unfold compile, out_s.
  rewrite <- (xorb_false_l (interpret_bexp b f)).
  replace false with (in_s (num_inputs b)).
  2: { unfold in_s. bdestruct (num_inputs b <? num_inputs b). 
       contradict H. lia. reflexivity. }
  rewrite interpret_bexp_f with (i:=num_inputs b) (f':=in_s);
    try apply compile'_correct;
    try apply num_inputs_well_typed;
    unfold b_dim; try lia.
  intros k Hk. unfold in_s. bdestruct (k <? num_inputs b);
    try (contradict H; lia); reflexivity.
  intros k Hk. unfold in_s. bdestruct (k <? num_inputs b);
    try (contradict H; lia); reflexivity.
Qed.*)

(** Examples **)
(* Small examples taken from (Re)QWIRE's Arithmetic.v file.
   
   TODO: Port over n-qubit adder examples. (I don't think this will cause
   any problems, but precomputing the number of ancillae might get a bit
   weird.) *)

Infix "⊻" := b_xor (at level 40).
Infix "∧" := b_and (at level 40).
Coercion b_var : nat >-> bexp.

Local Close Scope R_scope.

(*
Input : var 1 : y
        var 2 : x
        var 3 : cin
Output : cout = cin(x ⊕ y) ⊕ xy
*)
Definition adder_cout_bexp : bexp := (3 ∧ (2 ⊻ 1)) ⊻ (2 ∧ 1).
Eval cbv in (compile adder_cout_bexp).

(*
Input : var 0 : y
        var 1 : x
        var 2 : cin
Output : sum = cin ⊕ (x ⊕ y)
 *)
Definition adder_sum_bexp : bexp := 2 ⊻ (1 ⊻ 0).
Eval cbv in (compile adder_sum_bexp).

(*
Input : var 0 : x
        var 1 : y
Output : xor = x ⊕ y
*)
Definition xor_bexp : bexp := 0 ⊻ 1.
Eval cbv in (compile xor_bexp).

(*
Input : var 0 : x
Output : x' = x
*)
Definition id_bexp : bexp := 0.
Eval cbv in (compile id_bexp).

Definition fun_with_var : bexp := (4).
Eval cbv in (compile' fun_with_var 2 6).
