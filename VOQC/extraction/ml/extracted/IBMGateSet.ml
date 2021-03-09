open ChangeRotationBasis
open UnitaryListRepresentation

module IBMGateSet =
 struct
  type coq_IBM_Unitary =
  | UIBM_U1 of float
  | UIBM_U2 of float * float
  | UIBM_U3 of float * float * float
  | UIBM_CNOT
 end

(** val coq_U1 : float -> int -> IBMGateSet.coq_IBM_Unitary gate_app **)

let coq_U1 a q =
  App1 ((IBMGateSet.UIBM_U1 a), q)

(** val coq_U2 :
    float -> float -> int -> IBMGateSet.coq_IBM_Unitary gate_app **)

let coq_U2 a b q =
  App1 ((IBMGateSet.UIBM_U2 (a, b)), q)

(** val coq_U3 :
    float -> float -> float -> int -> IBMGateSet.coq_IBM_Unitary gate_app **)

let coq_U3 a b c q =
  App1 ((IBMGateSet.UIBM_U3 (a, b, c)), q)

type coq_IBM_ucom_l = IBMGateSet.coq_IBM_Unitary gate_list

(** val compose_u3 :
    float -> float -> float -> float -> float -> float ->
    IBMGateSet.coq_IBM_Unitary **)

let compose_u3 x1 y1 z1 x2 y2 z2 =
  let (p, z) = yzy_to_zyz x1 (( +. ) y1 z2) x2 in
  let (x, y) = p in IBMGateSet.UIBM_U3 (y, (( +. ) z y2), (( +. ) z1 x))
