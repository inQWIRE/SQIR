open GateCancellation
open HadamardReduction
open NotPropagation
open RotationMerging
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
