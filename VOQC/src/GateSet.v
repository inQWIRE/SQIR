Require Export UnitarySem.

Local Open Scope ucom_scope.
  Inductive uses {dim} : base_ucom dim -> list nat -> Prop :=
  | uses_seq : forall c1 c2 qs, uses c1 qs -> uses c2 qs -> uses (c1; c2) qs
  | uses_app1 : forall u q qs, List.In q qs -> uses (uapp1 u q) qs
  | uses_app2 : forall u q1 q2 qs, List.In q1 qs -> List.In q2 qs -> uses (uapp2 u q1 q2) qs 
  | uses_app3 : forall u q1 q2 q3 qs, List.In q1 qs -> List.In q2 qs -> List.In q3 qs -> uses (uapp3 u q1 q2 q3) qs.

(* General definition of a gate set used in ListRepresentation.v.
   An example gate set, commonly use in our optimizations, is in RzQGateSet.v. *)

Module Type GateSet.

  (* Gates are parameterized by a number of arguments. *)
  Parameter U : nat -> Set.
  
  (* Given a gate in set U + input arguments, produce a program using 
     the base_Unitary set defined in SQIR's UnitarySem.v. *)
  Parameter to_base : forall (dim n : nat) (u : U n) 
        (qs : list nat) (pf : List.length qs = n), 
    base_ucom dim.
  Arguments to_base {dim} {n}.

  (* As a technicality, we require that the output of to_base only uses the
     input qubits. So "G [q1; q2; q3]" will be translated into some program
     involving qubits q1, q2, and q3. *)
  Axiom to_base_uses_q : forall (dim n : nat) (u : U n) 
        (qs : list nat) (pf : List.length qs = n),
    @uses dim (to_base u qs pf) qs.

  (* Boolean equality over gates. *)
  Parameter match_gate : forall (n : nat), U n -> U n -> bool.
  Arguments match_gate {n}.
  Axiom match_gate_implies_eq : forall (dim n : nat) (u u': U n) 
        (qs : list nat) (pf : List.length qs = n), 
    match_gate u u' = true -> @to_base dim n u qs pf ≡ to_base u' qs pf.

End GateSet.
