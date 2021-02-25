open IBMGateSet
open OpenQASM.AST
open Printf
open Qasm2sqir
open UnitaryListRepresentation

(** Utilities for the IBM gate set **)

let cnot q1 q2 = App2 (IBMGateSet.UIBM_CNOT, q1, q2)
let u1 r1 q = App1 (IBMGateSet.UIBM_U1(r1), q)
let u2 r1 r2 q = App1 (IBMGateSet.UIBM_U2(r1,r2), q)
let u3 r1 r2 r3 q = App1 (IBMGateSet.UIBM_U3(r1,r2,r3), q)

let qasm_to_sqir_gate uop qmap sym_tab =
  match uop with
  | CX (ctrl, tgt) -> apply_c_gate cnot ctrl tgt qmap sym_tab
  | U _ -> raise (Failure "NYI: Generic Unitary")
  | Gate (id, params, qargs) ->
     (match StringMap.find_opt id sym_tab with
      | Some TGate _ -> 
         (match id with
         | "cx" -> apply_c_gate cnot (List.hd qargs) (List.nth qargs 1) qmap sym_tab
         | "h"  -> apply_gate (u2 0. Float.pi) (List.hd qargs) qmap sym_tab
         | "x"  -> apply_gate (u3 Float.pi 0. Float.pi) (List.hd qargs) qmap sym_tab
         | "u1" -> let r1 = interp_float_exp (List.nth params 0) in
                   apply_gate (u1 r1) (List.hd qargs) qmap sym_tab
         | "u2" -> let r1 = interp_float_exp (List.nth params 0) in
                   let r2 = interp_float_exp (List.nth params 1) in
                   apply_gate (u2 r1 r2) (List.hd qargs) qmap sym_tab
         | "u3" -> let r1 = interp_float_exp (List.nth params 0) in
                   let r2 = interp_float_exp (List.nth params 1) in
                   let r3 = interp_float_exp (List.nth params 2) in
                   apply_gate (u3 r1 r2 r3) (List.hd qargs) qmap sym_tab
          | g -> raise (Failure ("NYI: Unsupported gate: " ^ g)))
      | Some _ -> raise (Failure ("ERROR: Not a gate: " ^ id))
      | None -> raise (Failure ("ERROR: Undefined gate: " ^ id)))

let get_gate_list f = Qasm2sqir.get_gate_list f qasm_to_sqir_gate

let sqir_to_qasm_gate oc g =
  match g with
  | App1 (IBMGateSet.UIBM_U1(r1), n) -> 
      fprintf oc "u1(%f) q[%d];\n" r1 n
  | App1 (IBMGateSet.UIBM_U2(r1,r2), n) ->
      if r1 = 0. && r2 = Float.pi
      then fprintf oc "h q[%d];\n" n
      else fprintf oc "u2(%f,%f) q[%d];\n" r1 r2 n
  | App1 (IBMGateSet.UIBM_U3(r1,r2,r3), n) -> 
      if r1 = Float.pi && r2 = 0. && r3 = Float.pi
      then fprintf oc "x q[%d];\n" n
      else fprintf oc "u3(%f,%f,%f) q[%d];\n" r1 r2 r3 n
  | App2 (IBMGateSet.UIBM_CNOT, m, n) -> fprintf oc "cx q[%d], q[%d];\n" m n
  (* badly typed case (e.g. App2 of H) -- should be unreachable *)
  | _ -> raise (Failure ("ERROR: Failed to write qasm file; unexpected gate in sqir_to_qasm_gate"))

let write_qasm_file fname p dim = Qasm2sqir.write_qasm_file fname p dim sqir_to_qasm_gate 

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

