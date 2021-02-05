open GateCancellation
open HadamardReduction
open Layouts
open NotPropagation
open RotationMerging
open SimpleMapping
open UnitaryListRepresentation

(** val optimize : RzQGateSet.coq_RzQ_ucom_l -> RzQGateSet.coq_RzQ_ucom_l **)

let optimize l =
  cancel_single_qubit_gates
    (cancel_two_qubit_gates
      (merge_rotations
        (cancel_single_qubit_gates
          (hadamard_reduction
            (cancel_two_qubit_gates
              (cancel_single_qubit_gates
                (cancel_two_qubit_gates
                  (hadamard_reduction (not_propagation l)))))))))

(** val optimize_lcr :
    RzQGateSet.coq_RzQ_ucom_l -> ((RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_app list * RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app
    list) * RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_list) option **)

let optimize_lcr l =
  coq_LCR l optimize RzQGateSet.RzQGateSet.match_gate

(** val optimize_light :
    RzQGateSet.coq_RzQ_ucom_l -> RzQGateSet.coq_RzQ_ucom_l **)

let optimize_light l =
  cancel_single_qubit_gates
    (hadamard_reduction
      (cancel_two_qubit_gates
        (cancel_single_qubit_gates
          (cancel_two_qubit_gates (hadamard_reduction (not_propagation l))))))

(** val optimize_light_lcr :
    RzQGateSet.coq_RzQ_ucom_l -> ((RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_app list * RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app
    list) * RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_list) option **)

let optimize_light_lcr l =
  coq_LCR l optimize_light RzQGateSet.RzQGateSet.match_gate

(** val simple_map_rzq :
    RzQGateSet.coq_RzQ_ucom_l -> qmap -> (int -> int -> int list) -> (int ->
    int -> bool) -> RzQGateSet.coq_RzQ_ucom_l * qmap **)

let simple_map_rzq l m get_path is_in_graph =
  simple_map l m get_path is_in_graph RzQGateSet.coq_CNOT RzQGateSet.coq_SWAP
    RzQGateSet.coq_H

(** val only_map :
    int -> RzQGateSet.coq_RzQ_ucom_l -> qmap -> (int -> int -> int list) ->
    (int -> int -> bool) -> (RzQGateSet.coq_RzQ_ucom_l * qmap) option **)

let only_map dim l m get_path is_in_graph =
  if (&&) (layout_well_formed_b dim m) (uc_well_typed_l_b dim l)
  then Some (simple_map_rzq l m get_path is_in_graph)
  else None

(** val optimize_then_map :
    int -> RzQGateSet.coq_RzQ_ucom_l -> qmap -> (int -> int -> int list) ->
    (int -> int -> bool) -> (RzQGateSet.coq_RzQ_ucom_l * qmap) option **)

let optimize_then_map dim l m get_path is_in_graph =
  if (&&) (layout_well_formed_b dim m) (uc_well_typed_l_b dim l)
  then Some (simple_map_rzq (optimize l) m get_path is_in_graph)
  else None

(** val map_then_optimize :
    int -> RzQGateSet.coq_RzQ_ucom_l -> qmap -> (int -> int -> int list) ->
    (int -> int -> bool) -> (RzQGateSet.coq_RzQ_ucom_l * qmap) option **)

let map_then_optimize dim l m get_path is_in_graph =
  if (&&) (layout_well_formed_b dim m) (uc_well_typed_l_b dim l)
  then let (l', m') = simple_map_rzq l m get_path is_in_graph in
       Some ((optimize l'), m')
  else None

(** val optimize_then_map_then_optimize :
    int -> RzQGateSet.coq_RzQ_ucom_l -> qmap -> (int -> int -> int list) ->
    (int -> int -> bool) -> (RzQGateSet.coq_RzQ_ucom_l * qmap) option **)

let optimize_then_map_then_optimize dim l m get_path is_in_graph =
  if (&&) (layout_well_formed_b dim m) (uc_well_typed_l_b dim l)
  then let (l', m') = simple_map_rzq (optimize l) m get_path is_in_graph in
       Some ((optimize l'), m')
  else None
