open GateCancellation
open HadamardReduction
open NotPropagation
open RotationMerging
open RzQGateSet

(** val optimize : coq_RzQ_ucom_l -> coq_RzQ_ucom_l **)

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
