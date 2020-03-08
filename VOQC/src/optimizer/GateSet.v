Require Export UnitarySem.

(* General definition of a gate set used in ListRepresentation.v.
   An example gate set, commonly use in our optimizations, is in RzQGateSet.v. *)

Module Type GateSet.

  (* Gates are parameterized by a number of arguments. *)
  Parameter U : nat -> Set.
  
  (* Convert U to the base_Unitary set defined in SQIR's UnitarySem.v. *)
  Parameter to_base : forall (n : nat), U n -> base_Unitary n.
  Arguments to_base {n}.

  (* Boolean equality over gates. *)
  Parameter match_gate : forall (n : nat), U n -> U n -> bool.
  Arguments match_gate {n}.
  Axiom match_gate_implies_eq : forall {n} (u u': U n), 
    match_gate u u' = true -> to_base u = to_base u'.

End GateSet.
