Require Import QuantumLib.VectorStates.
Require Import MappingGateSet.
Require Import Layouts.

Require Import FSets.FSetAVL.
Require Import FSets.FSetFacts.
Require Import FSets.FSetProperties.

Module FSet := FSetAVL.Make(Coq.Structures.OrderedTypeEx.Nat_as_OT).
Module FSetFacts := FSetFacts.Facts FSet.
Module FSetProps := FSetProperties.Properties FSet.

(** Choose an initial logical->physical qubit mapping (i.e., layout) for a
    program that puts qubits close together on the architecture if they are 
    used together in a two-qubit gate. *)

(** Choose an unused qubit based on the given preferences. *)
Fixpoint get_default (prefs : list nat) (alloc : FSet.t) :=
  match prefs with
  | [] => O (* unreachable unless all qubits are allocated *)
  | p :: prefs => 
      if FSet.mem p alloc 
      then get_default prefs alloc 
      else p
  end.

(** Choose an unused qubit given a list of cadidates (ordered best -> worst)
    and a set of used qubits. *)
Fixpoint get_unused (cands : list nat) (prefs : list nat) (alloc : FSet.t) :=
  match cands with 
  | [] => get_default prefs alloc
  | c :: cands => 
      if FSet.mem c alloc 
      then get_unused cands prefs alloc 
      else c
  end.

(** Build a layout based on the structure of the input program.
   - l: input program
   - alloc: current allocated physical qubits
   - lay: current layout
 
   For every gate (CNOT m n), if logical qubits m or n are not already mapped 
   to physical qubits, we choose physical qubits m_phys and n_phys to be nearby
   in the returned layout. Note that the layout may change during mapping 
   (due to inserted swaps) so this strategy will not always choose the best 
   placement. *)
Fixpoint build_layout {U dim} (l : gate_list (Map_Unitary U) dim) (alloc : FSet.t) (lay : layout) (get_nearby : nat -> list nat) (q_ordering : list nat) : FSet.t * layout:=
  match l with
  | [] => (alloc, lay)
  | App2 UMap_CNOT m n :: t => 
      match find_phys lay m, find_phys lay m with
      | Some _, Some _ => build_layout t alloc lay get_nearby q_ordering
      | Some m_phys, None =>
          let n_phys := get_unused (get_nearby m_phys) q_ordering alloc in
          let alloc' := FSet.add n_phys alloc in
          let lay' := add lay n n_phys in
          build_layout t alloc' lay' get_nearby q_ordering
      | None, Some n_phys =>
          let m_phys := get_unused (get_nearby n_phys) q_ordering alloc in
          let alloc' := FSet.add m_phys alloc in
          let lay' := add lay m m_phys in
          build_layout t alloc' lay' get_nearby q_ordering
      | None, None =>
          let m_phys := get_default q_ordering alloc in
          let n_phys := get_unused (get_nearby m_phys) q_ordering alloc in
          let alloc' := FSet.add n_phys (FSet.add m_phys alloc) in
          let lay' := add (add lay m m_phys) n n_phys in
          build_layout t alloc' lay' get_nearby q_ordering
      end
  | _ :: t => build_layout t alloc lay get_nearby q_ordering
  end.

(** Choose a physical qubit for any unallocated logical qubits. n is the number
    of physical qubits available. *)
Fixpoint extend_layout (n : nat) (alloc : FSet.t) (lay : layout) (q_ordering : list nat)  :=
  match n with
  | O => lay
  | S n' => 
      match find_phys lay n' with 
      | Some _ => extend_layout n' alloc lay q_ordering
      | None => let m := get_default q_ordering alloc in
               extend_layout n' (FSet.add m alloc) (add lay n' m) q_ordering
      end
  end. 

(** dim is the number of qubits used in the program l and n is the number of
   qubits available on the machine *)
Definition greedy_layout {U dim} (l : gate_list (Map_Unitary U) dim) (n : nat) (get_nearby : nat -> list nat) (q_ordering : list nat) : layout :=
  let (alloc, lay) := build_layout l FSet.empty empty get_nearby q_ordering in
  extend_layout n alloc lay q_ordering.

Lemma greedy_layout_bijective : forall U dim (l : gate_list (Map_Unitary U) dim) n get_nearby q_ordering,
  (* some preconditions ... *)
  layout_bijective n (greedy_layout l n get_nearby q_ordering).
Proof.
(* TODO *)
Admitted.
