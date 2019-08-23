Require Import Equivalences.
Require Export ListRepresentation.
Require Import PI4GateSet.

Local Open Scope ucom_scope.

(* This file contains current progress on a 'list of list of gates' (grid) 
   representation for unitary programs. This representation should be
   useful for mapping.
*)

(**************************)
(** Grid representation  **)
(**************************)

(* Represent a unitary circuit as a list of time slices of operations
   that can be performed in parallel. This representation is a little
   closer to the circuit presentation of quantum programs.
 
   This representation is useful for circuit mapping, which typically 
   performs routing between circuit time slices. *)
Definition grid U dim := list (gate_list U dim). 

(* The goal is to break the program into lists of operations that can be
   performed in parallel. The dumb way to do this would be to put each
   operation in its own time slice. We have tried to be a little smarter 
   by putting as many operations as possible in the same slice.

   It would be interesting to prove that the length of the resulting grid 
   is actually equal to the depth of the circuit. (Although defining the 
   depth of a circuit may require a DAG representation.) *)

Fixpoint build_slice' {U dim} (l acc : gate_list U dim) (n : nat) :
    (gate_list U dim * gate_list U dim) :=
  match n with
  | O => (acc, l)
  | S n' => match (next_single_qubit_gate l n') with
           | Some (l1, u, l2) => build_slice' (l1 ++ l2) (App1 u n' :: acc) n'
           | None => match (next_two_qubit_gate l n') with
                    | Some (l1, u, m, n, l2) =>
                        if m =? n'
                        then (* u n' n *)
                          if (n' <? n) && (does_not_reference l1 n)
                          then build_slice' (l1 ++ l2) (App2 u n' n :: acc) n'
                          else build_slice' l acc n'
                        else (* u m n' *)
                          if (m <? n') && (does_not_reference l1 m)
                          then build_slice' (l1 ++ l2) (App2 u m n' :: acc) n'
                          else build_slice' l acc n'
                    | _ => build_slice' l acc n'
                    end
           end
  end.

Definition build_slice {U dim} (l : gate_list U dim) : (gate_list U dim * gate_list U dim) := 
  build_slice' l [] dim.

(* The n argument is used to prove termination. we begin with n = (length l)
   because this is the maximum number of time slices in the program. *)
Fixpoint list_to_grid' {U dim} (l : gate_list U dim) (n : nat) : grid U dim :=
  match n with
  | O => []
  | S n' => match l with 
           | [] => []
           | _ => match build_slice l with
                | (s, l') => s :: (list_to_grid' l' n')
                end
           end
  end.

Definition list_to_grid {U dim} (l : gate_list U dim) := list_to_grid' l (List.length l).

Fixpoint grid_to_list {U dim} (g : grid U dim) :=
  match g with
  | [] => []
  | s :: g' => s ++ (grid_to_list g')
  end.

Lemma list_grid_equiv : forall {dim} (l : base_list dim),
  list_to_ucom (grid_to_list (list_to_grid l)) ≡ list_to_ucom l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - unfold uc_equiv_l; simpl.
    destruct a.
    + unfold list_to_grid. simpl.
  (* We'll need to prove some more lemmas before we can do this. *)
Admitted.

(* Simple tests. -- Why aren't list notations working? *)
Definition test1 : PI4_list 3 := (App1 UPI4_H 0) :: (App2 UPI4_CNOT 1 2) :: (App2 UPI4_CNOT 0 1) :: (App1 UPI4_X 1) :: [].
Compute (list_to_grid test1).
Compute (grid_to_list (list_to_grid test1)).

Definition test2 : PI4_list 3 := (App1 UPI4_H 0) :: (App1 UPI4_H 0) :: (App1 UPI4_H 0) :: (App1 UPI4_H 0) :: [].
Compute (list_to_grid test2).
Compute (grid_to_list (list_to_grid test2)).

Definition test3 : PI4_list 3 := (App1 UPI4_H 0) :: (App1 UPI4_H 0) :: (App1 UPI4_H 0) :: (App2 UPI4_CNOT 1 2) :: (App2 UPI4_CNOT 0 1) :: (App1 UPI4_X 1) :: (App1 UPI4_X 2) :: (App1 UPI4_X 2) :: [].
Compute (list_to_grid test3).
Compute (grid_to_list (list_to_grid test3)).