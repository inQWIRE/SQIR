Require Import VectorStates UnitaryOps Coq.btauto.Btauto Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
Require Export ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.
(* The language for RCIR+, a target language for QLLVM to compile to. *)
Require Import Dirac.
Require Import VectorStates.

Local Open Scope C_scope.
Local Open Scope nat_scope.

(* We first create a map for quamtum qubits that 
       are equivalent to the vector representations of quantum registers. *)
Definition vector := list bool.

Inductive qop := H (n:nat) | X (n:nat) | T (n:nat) | S (n:nat)
               | CNOT (n1:nat) (n2:nat) | seq (q1:qop) (q2:qop).

Inductive op_val := Hv | Xv | Tv | Sv | CNv (n:nat).

Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.

Module Env := FMapList.Make Nat_as_OT.

Definition opmap := Env.t (list op_val).

Definition update_op (n:nat) (v:op_val) (mp:opmap) :=
   match Env.find n mp with None => Env.add n [v] mp
                          | Some l => Env.add n (l++[v]) mp
   end.

Fixpoint trans_sem (inst : qop ) (m:opmap) : opmap :=
   match inst with H n => update_op n Hv m
                 | X n => update_op n Xv m
                 | T n => update_op n Tv m
                 | S n => update_op n Sv m
                 | CNOT n1 n2 => update_op n1 (CNv n2) m
                 | seq q1 q2 => trans_sem q2 (trans_sem q1 m)
   end.

(* The state map is mapping from a qubit to its entanglement map group number. *)
Definition smap := Env.t nat.

(* An abstract datatype for entanglement state. *)
Parameter state : Type.

Parameter slength : state -> nat.

Definition skey : Type := list bool.

Parameter keys : state -> list skey.

Axiom length_key : forall s x, In x (keys s) -> slength s = length x.

Axiom keys_size : forall s, length (keys s) = 2 ^ (slength s).

Parameter supdate : skey -> C -> state -> state.

Parameter slookup : skey -> state -> option C.

Axiom slookup_update : forall s x v, In x (keys s) -> slookup x (supdate x v s) = Some v.

Parameter qkmap : state -> (nat -> option nat).

Parameter qkmap_keys : state -> list nat.

Axiom qkmap_size_match : forall s x, In x (qkmap_keys s) -> (exists v, (qkmap s) x = Some v).

Axiom qkmap_size_good : forall s, length (qkmap_keys s) = slength s.

Axiom qkmap_valid : forall s x v, In x (qkmap_keys s)
         -> (qkmap s) x = Some v -> 0 <= v < (slength s).

Axiom qkmap_inj : forall s x y, In x (qkmap_keys s) ->
                     In y (qkmap_keys s) -> x <> y -> (qkmap s) x <> (qkmap s) y.

Tactic Notation "inv" hyp(H) := inversion H; subst; clear H.
Tactic Notation "inv" hyp(H) "as" simple_intropattern(p) :=
  inversion H as p; subst; clear H.

Fixpoint flip (l:list bool) (n:nat) := 
   match l with [] => []
           | x::xs => (if n =? 0 then (¬ x)::xs else (x::(flip xs (n-1))))
   end.

Check flip.

Lemma flip_correct_1 : forall (l:list bool) n m, n < length l ->
                n <> m -> nth_error l m = nth_error (flip l n) m.
Proof.
  intro l.
  induction l;intros;simpl.
  reflexivity.
  bdestruct (n =? 0).
  destruct m.
  subst. contradiction.
  simpl. reflexivity.
  destruct m.
  simpl. reflexivity.
  simpl.
  apply IHl.
  simpl in H0. lia.
  lia.
Qed.

Lemma flip_correct_2 : forall (l:list bool) n v, n < length l ->
                (nth_error l n) = Some v -> nth_error (flip l n) n = Some (¬ v).
Proof.
  intro l.
  induction l;intros;simpl.
  apply nth_error_In in H1.
  apply in_nil in H1.
  inv H1.
  bdestruct (n =? 0).
  subst. simpl in *.
  inv H1. reflexivity.
  destruct n.
  contradiction.
  simpl in *.
  assert ((n - 0) = n) by lia.
  rewrite H3.
  apply IHl. lia.
  assumption.
Qed.

(* The semantics of permutation for X gates. *)
Parameter permute : nat -> state -> option state.

Axiom permite_sem : forall s s' x n, 
       In x (keys s) -> n < slength s -> permute n s = Some s' -> 
        slookup x s = slookup (flip x n) s'.

(* The semantics of control permutation for CNOT. *)
Parameter cpermute : nat -> nat -> state -> option state.

Axiom cpermute_sem_1 : forall s s' n m x,
        In x (keys s) -> n < slength s -> m < slength s -> n <> m -> 
      cpermute n m s = Some s' -> nth_error x n = Some false ->
           slookup x s = slookup x s'.

Axiom cpermute_sem_2 : forall s s' n m x,
        In x (keys s) -> n < slength s -> m < slength s -> n <> m -> 
      cpermute n m s = Some s' -> nth_error x n = Some true ->
          slookup x s = slookup (flip x m) s'.

(* This operartion is used for defining the correctness meaing of H gates. *)
Parameter hup : nat -> state -> option state.

Axiom hup_sem : forall s s' x n v v', 
       In x (keys s) -> n < slength s -> hup n s = Some s' -> 
        slookup x s = Some v -> slookup (flip x n) s = Some v' ->
          slookup x s' = Some (Cmult (C1 / sqrt 2)%C (Cplus v v')).

(* This operartion is used for defining the correctness meaing of S gates. *)
Parameter sup : nat -> state -> option state.

Axiom sup_sem_1 : forall s s' x n v, 
       In x (keys s) -> n < slength s -> hup n s = Some s' -> 
        slookup x s = Some v ->  nth_error x n = Some true ->
          slookup x s' = Some (Cmult Ci v).

Axiom sup_sem_2 : forall s s' x n v, 
       In x (keys s) -> n < slength s -> hup n s = Some s' -> 
        slookup x s = Some v ->  nth_error x n = Some false ->
           slookup x s' = slookup x s.

Parameter join : state -> state -> option state.

Axiom join_WF1 : forall s s' s'', join s s' = Some s'' ->
         (length (qkmap_keys s)) + length (qkmap_keys s') = length (qkmap_keys s'').

Axiom join_WF2 : forall s s' s'', join s s' = Some s'' 
                    -> slength s + slength s' = slength s''.

Axiom join_WF3 : forall s s' s'' x, join s s' = Some s'' ->
             In x (qkmap_keys s) -> In x (qkmap_keys s'') 
                 /\ In x (qkmap_keys s') -> In x (qkmap_keys s'').

Axiom join_WF4 : forall s s' s'' x, join s s' = Some s'' ->
             In x (qkmap_keys s'') -> In x (qkmap_keys s) \/ In x (qkmap_keys s').

Inductive emap := ENil | ECons (n1: nat) (s:state) (m:emap).

Fixpoint elookup (n : nat) (m:emap) :=
  match m with ENil => None
             | ECons x y mp => if x =? n then Some y else elookup n mp
  end.

Fixpoint eupdate (n:nat) (v:state) (m:emap) :=
      match m with ENil => ENil
               | ECons x y mp => if x =? n then ECons x v mp else ECons x y (eupdate n v mp)
      end.

Fixpoint delete (n:nat) (m:emap) :=
     match m with ENil => ENil
             | ECons x y mp => if x =? n then mp else ECons x y (delete n mp)
     end.

Fixpoint update_all (l : list nat) (en:nat) (sm:smap) :=
     match l with [] => sm
               | x::xs => Env.add x en (update_all xs en sm)
     end.

Inductive sem : smap -> emap -> nat -> op_val -> smap -> emap -> Prop :=
   semX : forall sm mp s n en i s', Env.find n sm = Some en
           -> elookup en mp = Some s -> (qkmap s) n = Some i -> 
                permute i s = Some s' -> sem sm mp n Xv sm (eupdate en s' mp)
   | semH : forall sm mp s n en i s', Env.find n sm = Some en
           -> elookup en mp = Some s -> (qkmap s) n = Some i -> 
                hup i s = Some s' -> sem sm mp n Hv sm (eupdate en s' mp)
   | semS : forall sm mp s n en i s', Env.find n sm = Some en
           -> elookup en mp = Some s -> (qkmap s) n = Some i -> 
                sup i s = Some s' -> sem sm mp n Sv sm (eupdate en s' mp)
   | semCN1 : forall sm mp s n m en i j s', Env.find n sm = Some en
           -> elookup en mp = Some s -> (qkmap s) n = Some i -> (qkmap s) m = Some j ->
                cpermute i j s = Some s' -> sem sm mp n (CNv m) sm (eupdate en s' mp)
   | semCN2 : forall sm mp s n m en en' i j s' s'' s3, Env.find n sm = Some en
            -> Env.find m sm = Some en' -> en <> en' -> elookup en mp = Some s
           -> elookup en' mp = Some s' -> join s s' = Some s'' ->
               (qkmap s'') n = Some i -> (qkmap s'') m = Some j ->
             cpermute i j s'' = Some s3
         -> sem sm mp n (CNv m) (update_all (qkmap_keys s') en sm) (eupdate en s'' (delete m mp)).





