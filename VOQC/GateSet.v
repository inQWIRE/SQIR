Require Export UnitaryOps.

Local Open Scope ucom_scope.
Local Close Scope R_scope.

Inductive only_uses {U dim} : ucom U dim -> list nat -> Prop :=
| ou_seq : forall c1 c2 qs, only_uses c1 qs -> only_uses c2 qs -> only_uses (c1; c2) qs
| ou_app1 : forall u q qs, List.In q qs -> only_uses (uapp1 u q) qs
| ou_app2 : forall u q1 q2 qs, List.In q1 qs -> List.In q2 qs -> only_uses (uapp2 u q1 q2) qs 
| ou_app3 : forall u q1 q2 q3 qs, List.In q1 qs -> List.In q2 qs -> List.In q3 qs -> only_uses (uapp3 u q1 q2 q3) qs.

Definition bounded_list (l : list nat) n := forall x, List.In x l -> x < n.

Lemma one_elem_list : forall (m : nat), List.length (m :: []) = 1. 
Proof. easy. Qed.
Lemma two_elem_list : forall (m n : nat), List.length (m :: n :: []) = 2. 
Proof. easy. Qed.
Lemma three_elem_list : forall (m n p : nat), List.length (m :: n :: p :: []) = 3. 
Proof. easy. Qed.

Lemma map_nth_In : forall l n d0 d1 (f : nat -> nat),
  n < length l -> nth n (map f l) d0 = f (nth n l d1).
Proof.
  intros l n d0 d1 f H.
  generalize dependent n.
  induction l; simpl in *.
  lia.
  intros n Hn.
  destruct n.
  reflexivity.
  apply IHl.
  lia.
Qed.

(* General definition of a gate set used in ListRepresentation.v. *)
Module Type GateSet.

  (* Gates are parameterized by a number of arguments. *)
  Parameter U : nat -> Set.
  
  (* Given a gate in set U + input arguments, produce a program using 
     the base_Unitary set defined in SQIR's UnitarySem.v. *)
  Parameter to_base : forall (n dim : nat) (u : U n) 
        (qs : list nat) (pf : List.length qs = n), 
    base_ucom dim.
  Arguments to_base {n} {dim}.

  (* Any reasonable definition of to_base should satisfy:
     1. (to_base G qs) shouldn't use any qubits besides those in qs; this is
        important so we can say that (to_base G1 [q1]) commutes with 
        (to_base G2 [q2]) when q1 ≠ q2
     2. (to_base G qs) should be well-typed iff qs is the correct length 
        and has no duplicates
     3. (to_base G (List.map f qs)) should be the same as 
        (SQIR.map_qubits f (to_base G qs))

     TODO: Is there some more general property that ensures 1-3? Or does some
     some subset of these imply the others? *)
  Axiom to_base_only_uses_qs : forall {n} (dim : nat) (u : U n) 
        (qs : list nat) (pf : List.length qs = n),
    @only_uses _ dim (to_base u qs pf) qs.
  Axiom to_base_WT : forall {n} (dim : nat) (u : U n) 
        (qs : list nat) (pf : List.length qs = n),
    @uc_well_typed _ dim (to_base u qs pf) <-> (bounded_list qs dim /\ List.NoDup qs).
  Axiom to_base_map_commutes : forall {n} (dim : nat) (u : U n)
        (qs : list nat) (pf : List.length qs = n) 
        (f : nat -> nat) (pfm : List.length (map f qs) = n),
    @to_base _ dim u (map f qs) pfm = map_qubits f (to_base u qs pf).

  (* Boolean equality over gates. *)
  Parameter match_gate : forall (n : nat), U n -> U n -> bool.
  Arguments match_gate {n}.
  Axiom match_gate_implies_eq : forall {n} (dim : nat) (u u': U n) 
        (qs : list nat) (pf : List.length qs = n), 
    match_gate u u' = true -> @to_base _ dim u qs pf ≡ to_base u' qs pf.

End GateSet.
