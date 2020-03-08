open GateCancellation
open HadamardReduction
open NotPropagation
open RotationMerging

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
