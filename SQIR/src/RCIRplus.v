Require Import VectorStates UnitaryOps Coq.btauto.Btauto Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
Require Export ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.
Local Open Scope string.
(* The language for RCIR+, a target language for QLLVM to compile to. *)
Local Open Scope nat_scope.

(* We first define two types variables appearing in an expression.
    global variables and local variables. *)

Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.

Definition ivar := nat.


Definition evar := nat.
(*For whatever reason QuickChick does not want to derive these *)


Inductive rtype := Q (n:nat).
Derive Show for rtype.

Definition genRtype (min max : nat) : G rtype :=
  liftM Q (choose (min, max)).
Locate "<-".
Locate "freq".
Definition genEvar (min max : nat ) : G evar :=
  choose (min, max).
Definition genIvar (min max : nat ) : G ivar :=
  choose (min, max).
Fixpoint genListRtypeEvar (size : nat): G (list (rtype * evar)) :=
  match size with
  | 0 => ret []
  | S size' =>   (bind (genListRtypeEvar size')
                         (fun xs => bind (genRtype 4 8)
                                      (fun x => bind (genEvar 1 4)
                                                  (fun e => ret ((x, e):: xs)))))
                    end. 
Fixpoint genListRtypeIvar (size : nat): G (list (rtype * ivar)) :=
  match size with
  | 0 => ret []
  | S size' =>   (bind (genListRtypeIvar size')
                         (fun xs => bind (genRtype 4 8)
                                      (fun x => bind (genIvar 1 4)
                                                  (fun e => ret ((x, e):: xs)))))
                    end. 

Sample (genListRtypeIvar 3).
Inductive avar := lvar : ivar -> avar | gvar : evar -> avar.
Notation " 'freq' [ x ;;; y ] " := (freq_ (snd x) (cons x (cons y nil))) .
Notation " 'freq' [ x ;;; y ;;; .. ;;; z ] " := (freq_ (snd x) (cons x (cons y .. (cons z nil) ..))).
Notation " 'oneOf' ( x ;;; l ) " := (oneOf_ x (cons x l)) .
Notation " 'oneOf' [ x ;;; y ;;; .. ;;; z ] " := (oneOf_ (snd x) (cons x (cons y .. (cons z nil) ..))).
(*This isn't working Properly *)
Definition genAvar (min max : nat) : G avar :=
  freq [ (1, (bind (genIvar min max) (fun i => ret (lvar i)))) ;;;
         (1,  (bind (genEvar min max) (fun e => ret (gvar e))))
        ].

Definition genAvarConst (label : nat) : G avar :=
  freq [ (1, ret (lvar label)) ;;;
          (1, ret (gvar label)) ]. 


Derive Show for avar.
Sample (genAvar 1 6).
(* Warning: The following logical axioms were
encountered: semBindOptSizeMonotonicIncl_r semBindOptSizeMonotonicIncl_l.
Having invalid logical
axiom in the environment when extracting may lead to incorrect or non-terminating ML terms.
 [extraction-logical-axiom,extraction] 
[lvar 4; lvar 2; lvar 5; lvar 3; gvar 4; lvar 4; lvar 5; gvar 5; gvar 2; lvar 6; lvar 4]*)


Sample (genAvarConst 3).
(* Warning: The following logical axioms were
encountered: semBindOptSizeMonotonicIncl_r semBindOptSizeMonotonicIncl_l.
Having invalid logical
axiom in the environment when extracting may lead to incorrect or non-terminating ML terms.
 [extraction-logical-axiom,extraction]
[gvar 3; gvar 3; gvar 3; lvar 3; gvar 3; lvar 3; gvar 3; gvar 3; lvar 3; gvar 3; lvar 3] *)
Locate "oneOf".
Definition genAvarOneOf (min max : nat) : G avar :=
  oneOf [  (bind (genIvar min max) (fun i => ret (lvar i))) ;;
         (bind (genEvar min max) (fun e => ret (gvar e)))
        ].
Sample (genAvarOneOf 1 6).
(* [gvar 5; gvar 2; gvar 1; gvar 6; gvar 5; gvar 6; gvar 3; gvar 3; gvar 2; gvar 4; gvar 1]
 *)
Print genAvar.
Definition avar_eq (r1 r2 : avar) : bool := 
                match r1 with lvar a1 
                            => match r2
                               with lvar a2
                                     => (a1 =? a2)
                                  | gvar a2 => false
                                 end
                     | (gvar a1) => match r2 with (gvar a2) => (a1 =? a2)
                                                   | (lvar a2) => false
                                       end
                end.

Notation "i '==?' j" := (avar_eq i j) (at level 50).

Tactic Notation "inv" hyp(H) := inversion H; subst; clear H.
Tactic Notation "inv" hyp(H) "as" simple_intropattern(p) :=
  inversion H as p; subst; clear H.

Lemma avar_eqb_eq : forall a b, a ==? b = true -> a = b.
Proof.
 intros. unfold avar_eq in H.
 destruct a. destruct b.
 apply Nat.eqb_eq in H. rewrite H. easy.
 inv H.
 destruct b.
 inv H.
 apply Nat.eqb_eq in H. rewrite H. easy.
Qed.

Lemma avar_eqb_neq : forall a b, a ==? b = false -> a <> b.
Proof.
 intros. unfold avar_eq in H.
 destruct a. destruct b.
 apply Nat.eqb_neq in H. intros R. injection R as eq1.
 rewrite eq1 in H. easy.
 inv H. easy.
 destruct b.
 inv H. easy.
 apply Nat.eqb_neq in H. intros R. injection R as eq1.
 rewrite eq1 in H. easy.
Qed.

Lemma avar_eq_reflect : forall r1 r2, reflect (r1 = r2) (avar_eq r1 r2). 
Proof.
  intros.
  destruct (r1 ==? r2) eqn:eq1.
  apply  ReflectT.
  apply avar_eqb_eq in eq1.
  assumption. 
  constructor. 
  apply avar_eqb_neq in eq1.
  assumption. 
Qed.

Hint Resolve avar_eq_reflect : bdestruct.


(* This is the expression in a function in the RCIR+ language. 
   It does not contain quantum gates. quantum gates will be foreign functions. *)
Definition pos : Type := (avar * nat).
(* The semantic definition of expressions for RCIR+ including some well-formedness requirement. *)
Definition pos_eq (r1 r2 : pos) : bool := 
                match r1 with (lvar a1,b1) 
                            => match r2
                               with (lvar a2,b2)
                                     => (a1 =? a2) && (b1 =? b2)
                                  | (gvar a2,b2) => false
                                 end
                     | (gvar a1,b1) => match r2 with (gvar a2,b2) => (a1 =? a2) && (b1 =? b2)
                                                   | (lvar a2, b2) => false
                                       end
                end.


Notation "i '=pos' j" := (pos_eq i j) (at level 50).

Lemma pos_eqb_eq : forall a b, a =pos b = true -> a = b.
Proof.
 intros. unfold pos_eq in H.
 destruct a. destruct a. destruct b. destruct a.
 apply andb_true_iff in H.
 destruct H. apply Nat.eqb_eq in H.
 apply Nat.eqb_eq in H0. subst. easy.
 inv H.
 destruct b. destruct a.
 inv H.
 apply andb_true_iff in H.
 destruct H. apply Nat.eqb_eq in H.
 apply Nat.eqb_eq in H0. subst. easy.
Qed.

Lemma pos_eqb_neq : forall a b, a =pos b = false -> a <> b.
Proof.
 intros. unfold pos_eq in H.
 destruct a. destruct a. destruct b. destruct a.
 apply andb_false_iff in H.
 destruct H. apply Nat.eqb_neq in H.
 intros R. injection R as eq1.
 rewrite eq1 in H. easy.
 apply Nat.eqb_neq in H.
 intros R. injection R as eq1.
 rewrite H0 in H. easy.
 intros R. injection R as eq1.
 easy.
 destruct b. destruct a.
 intros R. injection R as eq1.
 easy.
 apply andb_false_iff in H.
 destruct H. apply Nat.eqb_neq in H.
 intros R. injection R as eq1.
 rewrite eq1 in H. easy.
 apply Nat.eqb_neq in H.
 intros R. injection R as eq1.
 rewrite H0 in H. easy.
Qed.

Lemma pos_eq_reflect : forall r1 r2, reflect (r1 = r2) (pos_eq r1 r2). 
Proof.
  intros.
  destruct (r1 =pos r2) eqn:eq1.
  apply  ReflectT.
  apply pos_eqb_eq in eq1.
  assumption. 
  constructor. 
  apply pos_eqb_neq in eq1.
  assumption. 
Qed.

Hint Resolve pos_eq_reflect : bdestruct.

Instance showPair {A B : Type} `{Show A} `{Show B} : Show (A * B) :=
  {
    show p :=
      let (a,b) := p in
        "(" ++ show a ++ "," ++ show b ++ ")"
  }.
Fixpoint gen_pos (min max : nat) : G pos :=
  (bind (choose (min, max)) (fun n =>
           (bind (genAvarConst n) (fun a =>
                (bind (choose (min, n)) (fun m => ret (a, m)))) )  )).
Sample (gen_pos 1 6). 
Inductive rexp :=
             | Skip : rexp | X : pos -> rexp | CU : pos -> rexp -> rexp 
             | Seq : rexp -> rexp -> rexp | Copyto : avar -> avar -> rexp.
Derive Show for rexp.

Declare Scope rexp_scope.
Delimit Scope rexp_scope with rexp.
Local Open Scope rexp.
Notation "p1 ; p2" := (Seq p1 p2) (at level 50) : rexp_scope.

Definition RCNOT (x y : pos) := CU x (X y).
Definition RSWAP (x y : pos) := if (x =pos y) then Skip else (RCNOT x y; RCNOT y x; RCNOT x y).
Definition RCCX (x y z : pos) := CU x (RCNOT y z).

(* The following defines the initialization of a register set for the expression in a function. *)
Definition allfalse := fun (_ : nat) => false.

(* The following defines the registers. *)
Require Import Map.
Require Import OrderedTypeEx.

Module Heap := Map.Make(Nat_as_OT).

Definition heap := Heap.t (rtype * (nat -> bool)).

Definition empty_heap := @Heap.empty (rtype * (nat -> bool)).

Module Regs := Map.Make(Nat_as_OT).

Definition regs := Regs.t (rtype * (nat -> bool)).

Definition empty_regs := @Regs.empty (rtype * (nat -> bool)).

Definition lookup (hr : heap * regs) (x:avar) : option (rtype * (nat -> bool)) :=
  match hr with (h,r) =>
    match x with gvar u => Heap.find u h
               | lvar u => Regs.find u r
     end
  end.

Definition get (hr : heap * regs)  (x:pos) : option bool :=
     match x with (u,a) => match lookup hr u with None => None
                                 | Some (Q n, g) => Some (g a)
                         end
     end.

Definition nupdate {A} (f : nat -> A) (i : nat) (x : A) :=
  fun j => if j =? i then x else f j.

Definition update_type_heap (h:heap) (x:evar) (t:rtype) : heap := Heap.add x (t,allfalse) h.

Definition update_type_regs (r:regs) (x:ivar) (t:rtype) : regs := Regs.add x (t,allfalse) r.

Definition update_val_heap (h:heap) (x:evar) (g:(nat -> bool)) : heap :=
               match Heap.find x h with Some (t,v) => Heap.add x (t,g) h | None => h end.

Definition update_val_regs (r:regs) (x:ivar) (g:(nat -> bool)) : regs :=
               match Regs.find x r with Some (t,v) => Regs.add x (t,g) r | None => r end.

Definition put_all (hr : heap * regs) (x:avar) (g:(nat-> bool)) : (heap * regs) :=
  match hr with (h,r) =>
    match x with (gvar u) => (update_val_heap h u g,r)
               | (lvar u) => (h,update_val_regs r u g)
    end
  end.

Definition update_bit_heap (h:heap) (u:evar) (b:nat) (v:bool) : heap :=
              match Heap.find u h with Some (t,g) => Heap.add u (t,nupdate g b v) h | None => h end.

Definition update_bit_regs (h:regs) (u:ivar) (b:nat) (v:bool) : regs :=
              match Regs.find u h with Some (t,g) => Regs.add u (t,nupdate g b v) h | None => h end.

Definition put (hr : heap * regs) (x:pos) (v:bool) : (heap * regs) :=
   match hr with (h,r) =>
     match x with (gvar u,a) => (update_bit_heap h u a v,r)
               | (lvar u,a) => (h,update_bit_regs r u a v)
     end
   end.

Notation "f '[' i '|->' x ']'" := (put f i x) (at level 10).

Lemma map_ext : forall hr hr', (forall x, get hr x = get hr' x) -> hr = hr'.
Proof.
Admitted.

Lemma get_same : forall hr x v1 v2,
        get hr x = Some v1 -> get hr x = Some v2 -> v1 = v2.
    Proof.
      intros.
      unfold get,lookup in *.
      destruct x. destruct hr.
      destruct a.
      destruct (Regs.find (elt:=rtype * (nat -> bool)) i r).
      destruct p. destruct r0.
      rewrite H in H0.
      injection H0 as eq1. assumption. inv H.
      destruct (Heap.find (elt:=rtype * (nat -> bool)) e h).
      destruct p. destruct r0.
      rewrite H in H0. injection H0 as eq1. assumption.
      inv H.
    Qed.

Lemma get_1 : forall hr x v, get hr x <> None -> get (put hr x v) x = Some v.
    Proof.
      intros.
      unfold get,lookup,put,update_bit_regs,update_bit_heap,nupdate in *.
      destruct x. destruct hr.
      destruct a.
      destruct (Regs.find (elt:=rtype * (nat -> bool)) i r) eqn:eq1.
      destruct p.
      destruct (Regs.find (elt:=rtype * (nat -> bool)) i
    (Regs.add i (r0, fun j : nat => if j =? n then v else b j) r)) eqn:eq2.
      destruct p. destruct r1.
      apply Regs.find_2 in eq2.
      apply Regs.mapsto_add1 in eq2.
      inv eq2.
      bdestruct (n=?n). reflexivity. lia.
      rewrite Regs.find_add in eq2. inv eq2.
      contradiction.
      destruct (Heap.find (elt:=rtype * (nat -> bool)) e h) eqn:eq1.
      destruct p. destruct r0.
      destruct (Heap.find (elt:=rtype * (nat -> bool)) e
    (Heap.add e (Q n0, fun j : nat => if j =? n then v else b j) h)) eqn:eq2.
      destruct p. destruct r0.
      apply Heap.find_2 in eq2.
      apply Heap.mapsto_add1 in eq2.
      inv eq2.
      bdestruct (n=?n). reflexivity. lia.
      rewrite Heap.find_add in eq2. inv eq2.
      contradiction.
    Qed.

Lemma get_neq : forall hr x y v,
        x <> y -> get (put hr y v) x = get hr x.
    Proof.
      intros.
      unfold get,lookup,put,update_bit_regs,update_bit_heap,nupdate in *.
      destruct x. destruct hr. destruct y.
      destruct a. destruct a0.
      destruct (Regs.find (elt:=rtype * (nat -> bool)) i0 r) eqn:eq1.
      destruct p. destruct r0.
      destruct (Regs.find (elt:=rtype * (nat -> bool)) i
      (Regs.add i0 (Q n1, fun j : nat => if j =? n0 then v else b j) r)) eqn:eq2.
      destruct p. destruct r0.
      destruct (Regs.find (elt:=rtype * (nat -> bool)) i r) eqn:eq3.
      destruct p. destruct r0.
      bdestruct (i =? i0). subst.
      bdestruct (n=?n0). subst. contradiction.
      apply Regs.find_2 in eq2.
      apply Regs.mapsto_add1 in eq2.
      rewrite eq1 in eq3.
      inv eq2. inv eq3.
      bdestruct (n=?n0). lia. reflexivity.
      apply Regs.find_2 in eq2.
      apply Regs.add_3 in eq2.
      apply Regs.find_2 in eq3.
      apply (Regs.mapsto_always_same (rtype * (nat -> bool)) i (Q n2, b0) (Q n3, b1)) in eq2.
      inv eq2. reflexivity. assumption. lia.
      apply Regs.find_2 in eq2.
      bdestruct (i =? i0). subst.
      rewrite eq1 in eq3. inv eq3.
      apply Regs.add_3 in eq2.
      apply Regs.find_1 in eq2. rewrite eq2 in eq3. inv eq3.
      apply Regs.add_3 in eq2.
      apply Regs.find_1 in eq2. rewrite eq2 in eq3. inv eq3.
      lia.
      bdestruct (i =? i0). subst.
      rewrite Regs.find_add in eq2. inv eq2.
      destruct (Regs.find (elt:=rtype * (nat -> bool)) i r) eqn:eq3.
      apply Regs.find_2 in eq3.
      assert (i0 <> i) by lia.
      specialize (@Regs.add_2 (rtype * (nat -> bool)) r i0 i p
                    (Q n1, fun j : nat => if j =? n0 then v else b j) H1 eq3) as eq4.
      apply Regs.find_1 in eq4. rewrite eq4 in eq2. inv eq2.
      reflexivity.
      destruct (Regs.find (elt:=rtype * (nat -> bool)) i r) eqn:eq2.
      bdestruct (i =? i0). subst. rewrite eq1 in eq2. inv eq2.
      reflexivity. reflexivity.
      reflexivity.
      destruct a0. reflexivity.
      destruct (Heap.find (elt:=rtype * (nat -> bool)) e0 h) eqn:eq1.
      destruct p. destruct r0.
      destruct (Heap.find (elt:=rtype * (nat -> bool)) e
       (Heap.add e0 (Q n1, fun j : nat => if j =? n0 then v else b j) h)) eqn:eq2.
      destruct p. destruct r0.
      destruct (Heap.find (elt:=rtype * (nat -> bool)) e h) eqn:eq3.
      destruct p. destruct r0.
      bdestruct (e =? e0). subst.
      bdestruct (n=?n0). subst. contradiction.
      apply Heap.find_2 in eq2.
      apply Heap.mapsto_add1 in eq2.
      rewrite eq1 in eq3.
      inv eq2. inv eq3.
      bdestruct (n=?n0). lia. reflexivity.
      apply Heap.find_2 in eq2.
      apply Heap.add_3 in eq2.
      apply Heap.find_2 in eq3.
      apply (Heap.mapsto_always_same (rtype * (nat -> bool)) e (Q n2, b0) (Q n3, b1)) in eq2.
      inv eq2. reflexivity. assumption. lia.
      apply Heap.find_2 in eq2.
      bdestruct (e =? e0). subst.
      rewrite eq1 in eq3. inv eq3.
      apply Heap.add_3 in eq2.
      apply Heap.find_1 in eq2. rewrite eq2 in eq3. inv eq3.
      lia.
      bdestruct (e =? e0). subst.
      rewrite Heap.find_add in eq2. inv eq2.
      destruct (Heap.find (elt:=rtype * (nat -> bool)) e h) eqn:eq3.
      apply Heap.find_2 in eq3.
      assert (e0 <> e) by lia.
      specialize (@Heap.add_2 (rtype * (nat -> bool)) h e0 e p
                    (Q n1, fun j : nat => if j =? n0 then v else b j) H1 eq3) as eq4.
      apply Heap.find_1 in eq4. rewrite eq4 in eq2. inv eq2.
      reflexivity.
      reflexivity. 
Qed.

Lemma get_index_eq : forall hr y v1 v2,
         get hr y <> None -> (hr[y |-> v1][ y |-> v2]) = hr[y |-> v2].
Proof.
  intros. apply map_ext.
  intros.
  bdestruct (x =pos y).
  subst. rewrite get_1. rewrite get_1. reflexivity.
  assumption.
  apply (get_1 hr y v1) in H. rewrite H. easy.
  rewrite get_neq. rewrite get_neq. rewrite get_neq.
  reflexivity. 1 - 3: assumption.
Qed.

Lemma get_index_neq : forall hr x y v1 v2,
         x <> y -> get hr x <> None -> get hr y <> None -> 
           (hr[y |-> v1][ x |-> v2]) = (hr[x |-> v2][ y |-> v1]).
Proof.
  intros. apply map_ext.
  intros.
  bdestruct (x =pos x0).
  bdestruct (y =pos x0).
  subst. contradiction.
  subst. rewrite get_1.
  rewrite get_neq. rewrite get_1. reflexivity.
  1-2:assumption.
  rewrite get_neq. assumption.
  intros R. subst. contradiction.
  bdestruct (y =pos x0). subst.
  rewrite get_neq.
  rewrite get_1. rewrite get_1.
  reflexivity.
  rewrite get_neq. assumption.
  intros R. subst. contradiction.
  assumption.
  intros R. subst. contradiction.
  rewrite get_neq. rewrite get_neq.
  rewrite get_neq. rewrite get_neq.
  reflexivity.
  intros R. subst. contradiction.
  intros R. subst. contradiction.
  intros R. subst. contradiction.
  intros R. subst. contradiction.
Qed.


Lemma put_val_same : forall hr x v, get hr x = Some v -> put hr x v = hr.
Proof.
 intros. 
 apply map_ext.
 intros.
 bdestruct (x =pos x0). subst.
 rewrite H. rewrite get_1.
 reflexivity. rewrite H. easy.
 rewrite get_neq.
 reflexivity.
 intros R. subst. contradiction.
Qed.


(*Just a sample generator, could be improved *)

(* Defining the CNOT and CCX gate. *)
Definition CNOT (p1 p2 : pos) := CU p1 (X p2).

Definition CCX (p1 p2 p3 : pos) := CU p1 (CNOT p2 p3).


(* well-formedness of a predicate based on the relation of
    the input dimension number and the specified predicate type and number. *)

Inductive freevar_exp : pos -> rexp -> Prop := 
   freevar_skip : forall v, freevar_exp v Skip
 | freevar_x_eq : forall a x b, a <> b -> freevar_exp (x,b) (X (x,a))
 | freevar_x_neq : forall a x b y, x <> y -> freevar_exp (x,b) (X (y,a))
 | freevar_cu_eq : forall a x b e, a <> b -> freevar_exp (x,b) e -> freevar_exp (x,b) (CU (x,a) e)
 | freevar_cu_neq : forall a x y b e, x <> y -> freevar_exp (x,b) e -> freevar_exp (x,b) (CU (y,a) e)
 | freevar_seq : forall v e1 e2, freevar_exp v e1 -> freevar_exp v e2 -> freevar_exp v (Seq e1 e2)
 |  freevar_copyto : forall v a b, freevar_exp v (Copyto a b).

Inductive well_defined : (heap * regs) -> pos -> Prop :=
     | well_defined_heap : forall h r x a n g, Heap.MapsTo x (Q n,g) h
                                   -> a < n -> well_defined (h,r) (gvar x,a)
     | well_defined_regs : forall h r x a n g, Regs.MapsTo x (Q n, g) r
                                    -> a < n -> well_defined (h,r) (lvar x,a).

Definition well_defined_all (hr : heap * regs) (x:avar) (n:nat) : Prop := forall i, i < n -> well_defined hr (x,i).

Definition well_formed_heap (h:heap) : Prop :=
            forall x n g, Heap.MapsTo x (Q n, g) h -> 0 < n.

Definition well_formed_regs (r:regs) : Prop :=
          forall x n g, Regs.MapsTo x (Q n, g) r -> 0 < n.

Definition well_formed_mem (hr: heap * regs) : Prop :=
       well_formed_heap (fst hr) /\ well_formed_regs (snd hr).

Inductive WF_rexp : (heap * regs) -> rexp -> Prop := 
  | WF_skip : forall hr, WF_rexp hr Skip
  | WF_x : forall hr v, well_defined hr v -> WF_rexp hr (X v)
  | WF_cu : forall hr v e, well_defined hr v -> freevar_exp v e -> WF_rexp hr e -> WF_rexp hr (CU v e)
  | WF_rseq : forall hr e1 e2,  WF_rexp hr e1 -> WF_rexp hr e2 -> WF_rexp hr (Seq e1 e2)
  | WF_copy : forall hr x y n m g1 g2, lookup hr x = Some (Q n, g1) -> lookup hr y = Some (Q m, g2) 
                     -> n <= m -> WF_rexp hr (Copyto x y).

Lemma freevar_exp_rx : 
    forall x y, x <> y -> 
         freevar_exp x (X y).
Proof.
  intros. 
  destruct x. destruct y.
  destruct (a ==? a0) eqn:eq1.
  apply avar_eqb_eq in eq1.
  rewrite eq1 in H.
  assert (n <> n0).
  intros R. rewrite R in H.
  contradiction.
  rewrite eq1.
  apply freevar_x_eq.
  lia.
  apply avar_eqb_neq in eq1.
  apply freevar_x_neq. assumption.
Qed.

Lemma freevar_exp_rcnot : 
    forall x y z,  x <> y -> x <> z ->
    freevar_exp x (RCNOT y z).
Proof.
  intros. unfold RCNOT.
  destruct x. destruct y.
  destruct (a ==? a0) eqn:eq1.
  apply avar_eqb_eq in eq1.
  rewrite eq1 in H.
  assert (n <> n0).
  intros R. rewrite R in H.
  contradiction.
  rewrite eq1.
  apply freevar_cu_eq.
  lia.
  destruct z. subst.
  destruct (a0 ==? a1) eqn:eq1.
  apply avar_eqb_eq in eq1.
  rewrite eq1 in H0.
  assert (n <> n1).
  intros R. rewrite R in H0.
  contradiction.
  rewrite eq1.
  apply freevar_x_eq.
  lia.
  apply avar_eqb_neq in eq1.
  apply freevar_x_neq. assumption.
  apply avar_eqb_neq in eq1.
  apply freevar_cu_neq. assumption.
  destruct z. subst.
  destruct (a ==? a1) eqn:eq2.
  apply avar_eqb_eq in eq2.
  rewrite eq2 in H0.
  assert (n <> n1).
  intros R. rewrite R in H0.
  contradiction.
  rewrite eq2.
  apply freevar_x_eq.
  lia.
  apply avar_eqb_neq in eq2.
  apply freevar_x_neq. assumption.
Qed.

Lemma RCNOT_WF :
  forall hr x y,
    x <> y -> well_formed_mem hr ->
    well_defined hr x -> well_defined hr y ->
    WF_rexp hr (RCNOT x y).
Proof.
  intros. unfold RCNOT. constructor. easy.
  apply freevar_exp_rx. assumption.
  constructor. easy.
Qed.

Lemma RSWAP_WF :
  forall hr x y,
    x <> y -> well_formed_mem hr ->
    well_defined hr x -> well_defined hr y ->
    WF_rexp hr (RSWAP x y).
Proof.
  intros. unfold RSWAP.
  destruct (x =pos y) eqn:eq1.
  constructor. 
  apply pos_eqb_neq in eq1.
  constructor.  constructor. 
  apply RCNOT_WF; assumption.
  apply RCNOT_WF; auto.
  apply RCNOT_WF; assumption.
Qed.

Lemma RCCX_WF :
  forall hr x y z,
    x <> y -> y <> z -> x <> z -> well_formed_mem hr ->
    well_defined hr x -> well_defined hr y -> well_defined hr z ->
    WF_rexp hr (RCCX x y z).
Proof.
  intros. unfold RCCX. constructor. easy.
  apply freevar_exp_rcnot; assumption.
  constructor. assumption.
  apply freevar_exp_rx. assumption.
  constructor. assumption. 
Qed.

(* A RCIR+ function can be a function with a RCIR+ expression or a cast oeration,
    or a RCIR+ foreign expression that might contain quantum gates.
    The requirement of quantum foreign gates in RCIR+ is that the input of registers
    for the functions to be all 0/1 bits, while the output also contains only 0/1 bits. *)
Inductive rfun A :=
          (* list of input evar, and the return evar, and the ivar.
             return evar cannot appear in the Fun.
              the final avar is the return statement in the function.
               After a function is returned. The value of avar will be written to the value of evar. *)
       Fun : (list (rtype * evar)) -> evar -> (list (rtype * ivar)) -> rexp -> avar -> rfun A
     | Cast : rtype ->  evar -> rtype -> rfun A
      (* init is to initialize a local variable with a number. 
         A local variable refers to a constant in QSSA. *)
     | Init : rtype -> evar -> option (nat -> bool) -> rfun A
     | Inv : evar -> rfun A
     | Foreign : (list (rtype * evar)) -> (list (rtype * ivar)) -> A -> rfun A.

Fixpoint gen_heap (l : list (rtype * evar)) : heap := 
  match l with [] => empty_heap
            | (Q n, x)::xl => Heap.add x (Q n, allfalse) (gen_heap xl)
  end.

Fixpoint gen_regs (l: list (rtype * ivar)) : regs :=
   match l with [] => empty_regs
         | (Q n, x)::xl => Regs.add x (Q n, allfalse) (gen_regs xl)
   end.

(* The following defines the well-formedness of rfun that depends on an input register set
    having all variables being global variables. *)
Fixpoint type_match (l: list (rtype * evar)) (r : heap) : Prop :=
    match l with [] => True
          | (Q n, x)::xl => 
         (match Heap.find x r with Some (Q m, f) => n = m | None => False end) /\  type_match xl r
    end.

(* Define the top level of the language. Every program is a list of global variable definitions plus a list of rfun functions. *)
Inductive rtop A := Prog : list (rfun A) -> rtop A.

(*
Definition update_type (f : regs) (i : avar) (x : rtype) :=
  fun y => if y ==? i then Some (x,allfalse) else f y.
*)

(* The well-formedness of a program is based on a step by step type checking on the wellfi*)
Definition WF_type (t:rtype) : Prop := match t with Q 0 => False | _ => True end.

(* We require every global variables are different *)
Inductive WF_rfun {A} : heap -> (rfun A) -> heap -> Prop := 
    | WF_fun : forall h l1 x t v y l2 e s v', Heap.MapsTo x (t, v) h -> s = gen_regs l2 ->
                well_formed_regs s -> lookup (Heap.remove x h, s) y = Some (t,v') -> WF_rexp (Heap.remove x h, s) e
                -> type_match ((t,x)::l1) h -> WF_rfun h (Fun A l1 x l2 e y) h
    | WF_cast : forall h n m x g, Heap.MapsTo x (Q n, g) h -> 0 < n -> 0 < m ->
            WF_rfun h (Cast A (Q n) x (Q m)) (update_type_heap h x (Q m))
    | WF_init : forall h x g t, WF_type t -> ~ Heap.In x h -> WF_rfun h (Init A t x g) (update_type_heap h x t)
    | WF_inv : forall h x e, Heap.MapsTo x e h -> WF_rfun h (Inv A x) h.

Inductive WF_rfun_list {A} : heap -> list (rfun A) -> heap -> Prop :=
    | WF_empty : forall h, WF_rfun_list h [] h
    | WF_many : forall h h' h'' x xs, WF_rfun h x h' -> WF_rfun_list h' xs h'' -> WF_rfun_list h (x::xs) h''.

Inductive WF_rtop {A} : rtop A -> Prop := 
    | WF_prog : forall h fl,  WF_rfun_list empty_heap fl h -> WF_rtop (Prog A fl).


(*
Definition nupdate {A} (f : nat -> A) (i : nat) (x : A) :=
  fun j => if j =? i then x else f j.

Definition eupdate (f : regs) (x: pos) (v : bool) :=
 match x with (a,b) => 
  fun j => if j ==? a then (match f j with None => None
                                | Some (tv,gv) =>  Some (tv, nupdate gv b v) end) else f j
 end.


Notation "f '[' i '|->' x ']'" := (eupdate f i x) (at level 10).


Definition eget (f : regs) (x: pos) : option bool :=
   match x with (a,b) => match f a with None => None
                                      | Some (Q n,g) => Some (g b)
                         end
   end.

Fixpoint gup {A} (f : nat -> A) (g : nat -> A) (n : nat) :=
  match n with 0 => f
             | S m => gup (update f m (g m)) g m
  end.

Definition pupdate (f : regs) (x: avar) (g: nat -> bool) :=
  fun j => if j ==? x then (match f j with None => None | Some (tv,gv) => Some (tv,g) end) else f j.
Definition emptyregs : regs :=
  fun j => None.
(* regs :  avar -> option (rtype * (nat -> bool)) *)

Definition emptyfun : nat -> bool :=
  fun j => false.
Definition emptyreg : (rtype * (nat -> bool)) :=
  (Q 3, emptyfun).
*)


Definition genBool : G bool :=
  freq [ (1, ret false) ;;;
         (1, ret true)

      ].
  
Fixpoint genRandomSizedFun (size : nat) : G (nat -> bool) :=
  match size with
  |0 => bind (genBool) (fun v =>  ret (update allfalse 0 v))
  | S s' => bind (genBool) (fun v =>
                (bind (genRandomSizedFun s') (fun g => ret ( update g s' v))))
                                     end.
Eval compute in show empty_regs.
Sample (genRandomSizedFun 3).
Sample genBool.

Fixpoint show_reg_aux (reg : (rtype * (nat -> bool))) : string :=
  let (rl, f) := reg in match rl with
                          |Q n =>("(Q " ++ show n ++ ", " ++ show (funbool_to_list n f) ++ ")")end. 
                                                                  
Instance show_reg 
  : Show (rtype * (nat -> bool)) :=
  {
    show p :=
      show_reg_aux p 
  }.

Fixpoint genReg (min_size max_size : nat ) : G (rtype * (nat -> bool)) := 
  (bind (choose (min_size, max_size)) (fun s => (bind (genRandomSizedFun s)
                                               (fun f => ret (Q s, f))) )).
Sample (genReg 2 6).

(*
Fixpoint show_regs_aux (regs :  ivar -> option (rtype * (nat -> bool)))
         (max_var_num : nat) : string :=
  let (l, e) := (lvar max_var_num, gvar max_var_num) in match max_var_num with
        | 0 => "{" ++ show l ++ ": " ++ show (regs l) ++ "}{" ++ show e ++ ": " ++ show (regs e) ++ "}"
        | S s'=> "{" ++ show l ++ ": " ++ show (regs l) ++ "}{" ++ show e ++ ": " ++ show (regs e) ++ "}, " ++ (show_regs_aux regs s')
                                                               end. 
                                                                  
  (* arbitrarily choosing 10 as the max register *)
Instance show_regs 
  : Show (regs) :=
  {
    show p :=
      show_regs_aux p 1
  }.
Fixpoint genRegsSized (fuel reg_size_min reg_size_max : nat) : G regs :=
  let reg := (genReg reg_size_min reg_size_max)
    in match fuel with
      |0 =>  freq [ (1, (bind (genIvar fuel fuel)
          (fun i => (bind reg                                                                               
               (fun r => ret (update_regs emptyregs (lvar i) r) ))))) ;;;
             (1, (bind (genEvar fuel fuel)
          (fun e => (bind reg                                                                               
     (fun r => ret (update_regs emptyregs (gvar e) r) )))))  ;;;
             (1, ret emptyregs)                                                               
                  ]
      |S s' =>    let regs := (genRegsSized s' reg_size_min reg_size_max) in
          freq [ (1, (bind (genIvar fuel fuel)
          (fun i => (bind reg                                                                               
                          (fun r => (bind regs (fun rs => ret (update_regs rs (lvar i) r)) )))))) ;;;
             (1, (bind (genEvar fuel fuel)
          (fun e => (bind reg                                                                              
                             (fun r => bind regs (fun rs => ret (update_regs rs (gvar e) r))) ))))  ;;;
             (1, (bind regs (fun rs => ret rs)))                                                               
                  ]

                  end.
(* genposfromregs? *)
Sample (genRegsSized 1 4 4).
(* TODO: Fix how it shows the functions *)
Fixpoint app_inv p :=
  match p with
  | Skip => Skip
  | X n => X n
  | CU n p => CU n (app_inv p)
  | Seq p1 p2 => Seq (app_inv p2) (app_inv p1)
  | Copyto a b => Copyto a b
  | Inv e => e
  end.
*)

Definition mask_bits (f : nat -> bool) m :=
    fun i => if i <? m then f i else false.

Definition xor_all (f: nat -> bool) (g:nat -> bool) :=
   fun i => xorb (f i) (g i).

Inductive estep : (heap * regs) -> rexp -> (heap * regs) -> Prop := 
  | skip_rule : forall hr , estep hr Skip hr
  | x_rule : forall hr x b, get hr x = Some b -> estep hr (X x) (hr[x |-> (¬ b)])
  | if_true : forall hr x e hr', get hr x = Some true ->
                            estep hr e hr' -> estep hr (CU x e) hr'
  | if_false : forall hr x e, get hr x = Some false  -> estep hr (CU x e) hr
  | seq_rule : forall hr e1 e2 hr' hr'', estep hr e1 hr'
                        -> estep hr' e2 hr'' -> estep hr (Seq e1 e2) hr''
  | copy_rule : forall hr x y m n f g,  lookup hr x = Some (Q m,f) -> lookup hr y = Some (Q n, g) ->
                estep hr (Copyto x y) (put_all hr y (xor_all (mask_bits f m) g)).

Fixpoint remove_all (l:list evar) (h:heap) : heap :=
   match l with [] => h
             | (x::xl) => remove_all xl (Heap.remove x h)
   end.

Inductive step_rfun {A} : list evar -> heap -> rfun A -> list evar -> heap -> Prop :=
   | fun_step : forall el r h h' l1 l2 e x a v n m fv, lookup (h',r) a = Some (Q n,v) -> 
              Heap.MapsTo x (Q m, fv) h' -> estep (h,(gen_regs l2)) e (h',r)
              -> step_rfun el h (Fun A l1 x l2 e a) el (update_val_heap h' x (xor_all v fv))
   | cast_step : forall el h nt mt x, step_rfun el h (Cast A nt x mt) el (update_type_heap h x mt)
   | init_step1 : forall el h t x, step_rfun el h (Init A t x None) el (update_val_heap (update_type_heap h x t) x allfalse)
   | init_step2 : forall el h t x n, step_rfun el h (Init A t x (Some n)) el (update_val_heap (update_type_heap h x t) x n)
   | inv_step : forall l h x, step_rfun l h (Inv A x) (x::l) h.

Inductive step_rfun_list {A} : list evar -> heap -> list (rfun A) -> list evar -> heap -> Prop :=
   | empty_step : forall el h, step_rfun_list el h [] el h
   | many_step : forall el el' el'' h h' h'' x xs, step_rfun el h x el' h' ->
                      step_rfun_list el' h' xs el'' h'' -> step_rfun_list el h (x::xs) el'' h''.

Inductive step_top {A} : rtop A -> heap -> Prop :=
  | the_top_step : forall fl el h, step_rfun_list nil empty_heap fl el h -> step_top (Prog A fl) (remove_all el h).


Lemma RCNOT_correct :
  forall hr x y fx fy,
    x <> y ->
    get hr x = Some fx -> get hr y = Some fy ->
    estep hr (RCNOT x y) (hr[y |-> (fy ⊕ fx)]).
Proof.
  intros.
  unfold RCNOT.
  destruct fx.
  apply if_true. assumption.
  apply x_rule. assumption.
  assert (fy ⊕ false = fy) by btauto.
  rewrite H2. 
  rewrite put_val_same.
  apply if_false. assumption. assumption.
Qed.

Lemma RSWAP_correct :
  forall hr x y fx fy,
    get hr x = Some fx -> get hr y = Some fy ->
    estep hr (RSWAP x y) (hr[y |-> fx][x |-> fy]).
Proof.
  intros.
  unfold RSWAP.
  bdestruct (x =pos y).
  subst. rewrite H in H0.
  injection H0 as eq1.
  rewrite eq1.
  rewrite put_val_same.
  rewrite put_val_same.
  constructor. subst. assumption.
  rewrite put_val_same; subst;assumption.
  eapply seq_rule.
  eapply seq_rule.
  apply RCNOT_correct. 
  assumption. apply H. apply H0.
  apply RCNOT_correct.
  intros R. rewrite R in H1. contradiction.
  apply get_1. rewrite H0. easy.
  rewrite get_neq. apply H. assumption.
  assert (fx ⊕ (fy ⊕ fx) = fy) by btauto.
  rewrite H2.
  assert (get ((hr [y |-> fy ⊕ fx]) [x |-> fy]) x = Some fy).
  apply get_1.
  rewrite get_neq. rewrite H. easy. assumption.
  assert (get ((hr [y |-> fy ⊕ fx]) [x |-> fy]) y = Some (fy ⊕ fx)).
  rewrite get_neq.
  apply get_1. rewrite H0. easy.
  intros R. rewrite R in H1. contradiction.
  specialize (RCNOT_correct ((hr [y |-> fy ⊕ fx]) [x |-> fy])
                       x y fy (fy ⊕ fx) H1 H3 H4) as eq1.
  assert ((fy ⊕ fx) ⊕ fy = fx) by btauto.
  rewrite H5 in eq1.
  assert ((((hr [y |-> fy ⊕ fx]) [x |-> fy]) [y |-> fx])
       = ((hr [y |-> fx]) [x |-> fy])).
  rewrite get_index_neq.
  rewrite get_index_eq. reflexivity.
  rewrite H0. easy.
  intros R. subst. contradiction.
  rewrite get_1. easy. rewrite H0. easy.
  rewrite get_neq. rewrite H. easy.
  assumption.
  rewrite H6 in eq1. assumption.
Qed.

Lemma RCCX_correct :
  forall hr x y z fx fy fz,
    x <> y ->
    y <> z ->
    x <> z ->
    get hr x = Some fx -> get hr y = Some fy -> get hr z = Some fz ->
    estep hr (RCCX x y z) (hr[z |-> (fz ⊕ (fy && fx))]).
Proof.
  intros. 
  unfold RCCX.
  destruct fx.
  apply if_true. assumption.
  assert ((fy && true) = fy) by btauto.
  rewrite H5.
  apply RCNOT_correct.
  1-3:assumption.
  assert (fz ⊕ (fy && false) = fz) by btauto.
  rewrite H5.
  rewrite put_val_same.
  apply if_false. assumption.
  assumption.
Qed.

