open OpenQASM.AST
open Printf
open Qasm2sqir
open RzQGateSet
open UnitaryListRepresentation

(** Utilities for the RzQ gate set **)

let qasm_to_sqir_gate uop qmap sym_tab =
  match uop with
  | CX (ctrl, tgt) -> apply_c_gate coq_CNOT ctrl tgt qmap sym_tab
  | U _ -> raise (Failure "NYI: Generic Unitary")
  | Gate (id, params, qargs) ->
     (match StringMap.find_opt id sym_tab with
      | Some TGate _ -> 
         (match id with
          | "ccz" -> apply_double_c_gate coq_CCZ (List.hd qargs) (List.nth qargs 1) (List.nth qargs 2) qmap sym_tab
          | "ccx" -> apply_double_c_gate coq_CCX (List.hd qargs) (List.nth qargs 1) (List.nth qargs 2) qmap sym_tab
          | "cx"  -> apply_c_gate coq_CNOT (List.hd qargs) (List.nth qargs 1) qmap sym_tab
          | "x"   -> apply_gate coq_X (List.hd qargs) qmap sym_tab
          | "z"   -> apply_gate coq_Z (List.hd qargs) qmap sym_tab
          | "h"   -> apply_gate coq_H (List.hd qargs) qmap sym_tab
          | "s"   -> apply_gate coq_P (List.hd qargs) qmap sym_tab
          | "sdg" -> apply_gate coq_PDAG (List.hd qargs) qmap sym_tab
          | "t"   -> apply_gate coq_T (List.hd qargs) qmap sym_tab
          | "tdg" -> apply_gate coq_TDAG (List.hd qargs) qmap sym_tab
          | "rzq" -> let param = Q.of_ints (interp_int_exp (List.nth params 0)) (interp_int_exp (List.nth params 1)) in
                     apply_gate (coq_Rz param) (List.hd qargs) qmap sym_tab
          | "rz" -> let param = Q.of_float (interp_float_exp (List.nth params 0) /. Float.pi) in
                    apply_gate (coq_Rz param) (List.hd qargs) qmap sym_tab
          | g -> raise (Failure ("NYI: Unsupported gate: " ^ g)))
      | Some _ -> raise (Failure ("ERROR: Not a gate: " ^ id))
      | None -> raise (Failure ("ERROR: Undefined gate: " ^ id)))

let get_gate_list f = Qasm2sqir.get_gate_list f qasm_to_sqir_gate

let sqir_to_qasm_gate oc g =
  match g with
  | App1 (RzQGateSet.URzQ_H, n) -> fprintf oc "h q[%d];\n" n
  | App1 (RzQGateSet.URzQ_X, n) -> fprintf oc "x q[%d];\n" n
  | App1 (RzQGateSet.URzQ_Rz(q), n) -> 
      if Q.equal q (Q.of_ints 1 4)
      then fprintf oc "t q[%d];\n" n
      else if Q.equal q (Q.of_ints 1 2)
      then fprintf oc "s q[%d];\n" n
      else if Q.equal q (Q.of_int 1)
      then fprintf oc "z q[%d];\n" n
      else if Q.equal q (Q.of_ints 3 2)
      then fprintf oc "sdg q[%d];\n" n
      else if Q.equal q (Q.of_ints 7 4)
      then fprintf oc "tdg q[%d];\n" n
      else fprintf oc "rzq(%a,%a) q[%d];\n" Z.output (Q.num q) Z.output (Q.den q) n
  | App2 (RzQGateSet.URzQ_CNOT, m, n) -> fprintf oc "cx q[%d], q[%d];\n" m n
  (* badly typed case (e.g. App2 of H) -- should be unreachable *)
  | _ -> raise (Failure ("ERROR: Failed to write qasm file; unexpected gate in sqir_to_qasm_gate"))

let write_qasm_file fname p dim = Qasm2sqir.write_qasm_file fname p dim sqir_to_qasm_gate 

let sqir_to_qasm_gate_str g =
  match g with
  | App1 (RzQGateSet.URzQ_H, n) -> sprintf "h q[%d];\n" n
  | App1 (RzQGateSet.URzQ_X, n) -> sprintf "x q[%d];\n" n
  | App1 (RzQGateSet.URzQ_Rz(q), n) -> 
      if Q.equal q (Q.of_ints 1 4)
      then sprintf "t q[%d];\n" n
      else if Q.equal q (Q.of_ints 1 2)
      then sprintf "s q[%d];\n" n
      else if Q.equal q (Q.of_int 1)
      then sprintf "z q[%d];\n" n
      else if Q.equal q (Q.of_ints 3 2)
      then sprintf "sdg q[%d];\n" n
      else if Q.equal q (Q.of_ints 7 4)
      then sprintf "tdg q[%d];\n" n
      else sprintf "rzq(%a,%a) q[%d];\n" Z.sprint (Q.num q) Z.sprint (Q.den q) n
  | App2 (RzQGateSet.URzQ_CNOT, m, n) -> sprintf "cx q[%d], q[%d];\n" m n
  | _ -> raise (Failure ("ERROR: Failed to write qasm file"))

let write_qasm_file_str p dim =
   let header = sprintf "OPENQASM 2.0;\ninclude \"qelib1.inc\";\n\ngate rzq(a,b) q {rz((a/b)*pi) q;}\nqreg q[%d];\n\n" dim in 
   let i = (List.map sqir_to_qasm_gate_str p) in
   header ^ String.concat "" i

let get_rz_count l = 
  let f a x = match x with
              | App1 (RzQGateSet.URzQ_Rz(_), _) -> a + 1
              | _ -> a in
  List.fold_left f 0 l;;

let get_x_count l = 
  let f a x = match x with
              | App1 (RzQGateSet.URzQ_X, _) -> a + 1
              | _ -> a in
  List.fold_left f 0 l;;
  
let get_h_count l = 
  let f a x = match x with
              | App1 (RzQGateSet.URzQ_H, _) -> a + 1
              | _ -> a in
  List.fold_left f 0 l;;
  
let get_cnot_count l = 
  let f a x = match x with
              | App2 (RzQGateSet.URzQ_CNOT, _, _) -> a + 1
              | _ -> a in
  List.fold_left f 0 l;;

(* Returns (Some true) if a is an odd multiple of 1/4 and (Some false) if a 
   is an even mulitple of 1/4. Returns None if a does not correspond to a 
   rotation by 1/4. *)
let is_odd_multiple_of_1_4 a =
  let prod = Q.mul a (Q.of_int 4) in
  let (num, den) = (Q.num prod, Q.den prod) in
  if Z.equal den (Z.of_int 1)
  then Some (Z.equal (Z.rem num (Z.of_int 2)) Z.one) 
  else None;;

(* Only relevant for the benchmarks using the Clifford+T set. *)
let rec get_t_count' l acc = 
  match l with
  | [] -> Some acc
  | App1 (RzQGateSet.URzQ_Rz(a), _) :: t ->
      (match is_odd_multiple_of_1_4 a with
       | Some true -> get_t_count' t (1 + acc)
       | Some false -> get_t_count' t acc
       | None -> None)
  | _ :: t -> get_t_count' t acc;;
  
let get_t_count l = get_t_count' l 0;;

(* Counts Clifford rotation gates (multiples of pi/2). *)
let is_multiple_of_2 a =
  let prod = Q.mul a (Q.of_int 2) in
  let den = Q.den prod in
  Z.equal den (Z.of_int 1)
 
let rec get_clifford_rot_count' l acc = 
  match l with
  | [] -> acc
  | App1 (RzQGateSet.URzQ_Rz(a), _) :: t ->
      if is_multiple_of_2 a 
      then get_clifford_rot_count' t (1 + acc) 
      else get_clifford_rot_count' t acc
  | _ :: t -> get_clifford_rot_count' t acc;;
  
let get_clifford_rot_count l = get_clifford_rot_count' l 0;;



