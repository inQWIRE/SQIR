module RzQGateSet :  
  sig
    type coq_RzQ_Unitary = URzQ_H | URzQ_X | URzQ_Rz of Q.t | URzQ_CNOT
    type coq_U = coq_RzQ_Unitary
    val match_gate : 'a -> coq_RzQ_Unitary -> coq_RzQ_Unitary -> bool
    
  end

val coq_URzQ_T : RzQGateSet.coq_RzQ_Unitary
val coq_URzQ_P : RzQGateSet.coq_RzQ_Unitary
val coq_URzQ_Z : RzQGateSet.coq_RzQ_Unitary
val coq_URzQ_PDAG : RzQGateSet.coq_RzQ_Unitary
val coq_URzQ_TDAG : RzQGateSet.coq_RzQ_Unitary
val coq_T :
  int -> RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
val coq_TDAG :
  int -> RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
val coq_P :
  int -> RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
val coq_PDAG :
  int -> RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
val coq_Z :
  int -> RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
val coq_Rz :
  Q.t -> int -> RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
val coq_H :
  int -> RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
val coq_X :
  int -> RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
val coq_CNOT :
  int -> int -> RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
type coq_RzQ_ucom_l =
    RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_list
val coq_CCX :
  int ->
  int ->
  int -> RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app list
val coq_CCZ :
  int ->
  int ->
  int -> RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app list
val remove_prefix :
  RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app list ->
  RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app list ->
  RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app list option
val replace_pattern :
  RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app list ->
  RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app list ->
  RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app list ->
  RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app list option
val bound : Q.t -> Q.t
val combine_rotations :
  Q.t ->
  Q.t ->
  int -> RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app list
val invert_rotation :
  Q.t -> int -> RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
