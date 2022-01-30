(** 'validate' takes two SQIR programs as input
   + an input and output log->phys mapping
   + an architecture description
   returns True if the 2nd prog has the same semantics as the first (w/ mappings)
   and respects architectural constraints
   
insensitive to "syntactic" gate reorderings (e.g., X 1 ; X 2 ≡ X 2 ; X 1)
but it will fail with "semantics" gate reorderings (e.g., X 2 ; CNOT 1 2 ≡ CNOT 1 2 ; X 2)

   Limitations:
   - This is not a general equivalence checker for quantum circuits. It is only designed to recognize equivalence between two circuits where one is the result of inserting SWAPs into the other, which is a common output from circuit mapping. If our 'validate' function returns true, then the two circuits are guaranteed to be equivalent. If it returns false, then the circuits may or may not be equivalent; we provide no guarantees. 
   - (CNOT a b; CNOT b a; CNOT a b) is not the same as (SWAP a b). This means that if SWAPs are decomposed into CNOTs, then translation validation will fail.
  - it will fail if you do optimization while mapping, thereby changig gates

input program shouldn't have any SWAPs
   *)

Require Import MappingGateSet.
Require Import SimpleMapping2.

Module MappingValidation (CG : ConnectivityGraph).

Module SM := SimpleMap CG.
Import SM.

Definition validate {U dim} (l_in l_out : ucom_l U dim) (m_in m_out : layout) (match_gate : forall {n}, Map_Unitary U n -> Map_Unitary U n -> bool) : bool :=
  let fix f l_in l_out m_in :=
    match l_out with
    | [] => (length l_in =? 0) && layout_eqb dim m_in m_out
    | App1 u q :: t =>
        match next_single_qubit_gate l_in (get_log m_in q) with
        | None => false
        | Some (l1, u', l2) =>
            if match_gate u u'
            then f (l1 ++ l2) t m_in
            else false
        end
    | App2 U_CX q1 q2 :: t =>
        let pq1 := get_log m_in q1 in
        let pq2 := get_log m_in q2 in
        match next_gate l_in (fun q => (q =? q1) || (q =? q2)) with
        | Some (l1, App2 U_CX q1' q2', l2) =>
            (* todo: also check that cnot is between valid qubits *)
            if (q1 =? q1') && (q2 =? q2')
            then f (l1 ++ l2) t m_in
            else false
        | _ => false
        end
    | App2 U_SWAP q1 q2 :: t => 
        (* todo: also check that swap is between valid qubits *)
        f l_in t (swap_log m_in q1 q2)
    | _ => false (* unreachable *)
    end in
  f l_in l_out m_in.

End MappingValidation.


Module MappingValidationProofs (G : GateSet) (CG : ConnectivityGraph).

Module MV := MappingValidation CG.
Import MV.

Module SM := SimpleMap CG.
Import SM.

Module SMP := SimpleMappingProofs G CG.
Import SMP.

Module MapG := MappingGateSet G.
Import MapG.

Module MapList := UListProofs MapG.
Import MapList.

(** if is_valid_mapping returns true then l_in and l_out are equivalent programs 
    wrt to layouts m_in and m_out, and l_out respects connectivity constraints. *)

Lemma valid_implies_equivalence : forall l l' m m',
  validate l l' m m' (fun n => @match_gate n) = true ->
  l ≡ l' with (get_log m) and (get_phys m').
Proof.
Admitted.

Lemma valid_implies_respect_constraints : forall (l : ucom_l dim) l' m m',
  validate l l' m m' (fun n => @match_gate n) = true ->
  respects_constraints_undirected CG.is_in_graph l'.
Proof.
Admitted.

(** simple_map produces a program that will pass validation. *)

Lemma simple_map_valid : forall (l : ucom_l dim) (m : layout) l' m',
  simple_map l m = (l', m') -> 
  validate l l' m m' (fun n => @match_gate n) = true.
Proof.
Admitted.

End MappingValidationProofs.