open UnitaryListRepresentation
open IBMGateSet

(** TODO: merge with RzQGateCount **)

let get_u1_count l = 
  let f a x = match x with
              | App1 (IBMGateSet.UIBM_U1(_), _) -> a + 1
              | _ -> a in
  List.fold_left f 0 l;;

let get_u2_count l = 
  let f a x = match x with
              | App1 (IBMGateSet.UIBM_U2(_,_), _) -> a + 1
              | _ -> a in
  List.fold_left f 0 l;;
  
let get_u3_count l = 
  let f a x = match x with
              | App1 (IBMGateSet.UIBM_U3(_,_,_), _) -> a + 1
              | _ -> a in
  List.fold_left f 0 l;;
  
let get_cnot_count l = 
  let f a x = match x with
              | App2 (IBMGateSet.UIBM_CNOT, _, _) -> a + 1
              | _ -> a in
  List.fold_left f 0 l;;

