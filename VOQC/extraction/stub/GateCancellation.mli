val coq_Rz_commute_rule1 :
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  (RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list *
   RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list)
  option
val coq_Rz_commute_rule2 :
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  (RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list *
   RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list)
  option
val coq_Rz_commute_rule3 :
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  (RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list *
   RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list)
  option
val coq_Rz_commute_rules :
  int ->
  (RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list ->
   (RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
    list *
    RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
    list)
   option)
  list
val coq_Rz_cancel_rule :
  int ->
  Q.t ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list option
val coq_H_cancel_rule :
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list option
val coq_X_commute_rule :
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  (RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list *
   RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list)
  option
val coq_X_cancel_rule :
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list option
val coq_CNOT_commute_rule1 :
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  (RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list *
   RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list)
  option
val coq_CNOT_commute_rule2 :
  int ->
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  (RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list *
   RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list)
  option
val coq_CNOT_commute_rule3 :
  int ->
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  (RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list *
   RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list)
  option
val coq_CNOT_commute_rule4 :
  int ->
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  (RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list *
   RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list)
  option
val coq_CNOT_commute_rule5 :
  int ->
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  (RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list *
   RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list)
  option
val coq_CNOT_commute_rules :
  int ->
  int ->
  (RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list ->
   (RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
    list *
    RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
    list)
   option)
  list
val coq_CNOT_cancel_rule :
  int ->
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list option
val propagate_Rz :
  Q.t ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list option
val propagate_H :
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list option
val propagate_X :
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list option
val propagate_CNOT :
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  int ->
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list option
val cancel_single_qubit_gates' :
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list
val cancel_single_qubit_gates :
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list
val cancel_two_qubit_gates' :
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list
val cancel_two_qubit_gates :
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list
