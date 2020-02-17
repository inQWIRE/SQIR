open OpenQASM
open OpenQASM.AST

open Printf

module E = ExtractedCode
module StringMap = Map.Make(String)

(* This file contains details for converting between OpenQASM and SQIR programs. *)

(** Gate set definition **)

let qelib1 = [
  ("u3",  TGate(3,1));
  ("u2",  TGate(2,1));
  ("u1",  TGate(1,1));
  ("cx",  TGate(0,2));
  ("id",  TGate(0,1));
  ("x",   TGate(0,1));
  ("y",   TGate(0,1));
  ("z",   TGate(0,1));
  ("h",   TGate(0,1));
  ("s",   TGate(0,1));
  ("sdg", TGate(0,1));
  ("t",   TGate(0,1));
  ("tdg", TGate(0,1));
  ("rx",  TGate(1,1));
  ("ry",  TGate(1,1));
  ("rz",  TGate(1,1));
  ("cz",  TGate(0,2));
  ("cy",  TGate(0,2));
  ("ch",  TGate(0,2));
  ("ccx", TGate(0,3));
  ("ccz", TGate(0,3));
  ("crz", TGate(1,2));
  ("cu1", TGate(1,2));
  ("cu3", TGate(3,2));
  
  (* not standard *)
  ("rz15", TGate(1,1))
]

let check_stmt symTab stmt =
  match stmt with
  | Include "qelib1.inc" -> List.fold_left
                              (fun map (gate, typ) -> StringMap.add gate typ map)
                              symTab qelib1
  | Include _ -> raise (Failure "Unsupported include")
  | Decl (QReg (id, size)) -> StringMap.add id (TQReg size) symTab
  | Decl (CReg (id, size)) -> StringMap.add id (TCReg size) symTab
  | GateDecl ((id, params, qargs), _) ->
    StringMap.add id (TGate (List.length params, List.length qargs)) symTab
  | OpaqueDecl (id, params, qargs) ->
    StringMap.add id (TGate (List.length params, List.length qargs)) symTab
  | _ -> symTab

let check program = List.fold_left check_stmt StringMap.empty program


(** Convert OpenQASM AST to SQIR program **)

(* For qubit mapping *)
module QbitIdx =
struct
  type t = string * int
  let compare (q0, i0) (q1, i1) =
    match Stdlib.compare q0 q1 with
    | 0 -> Stdlib.compare i0 i1
    | c -> c
end

module QbitMap = Map.Make(QbitIdx)

(* Controlled gate application *)
let apply_c_gate gate ctrl tgt qmap sym_tab =
  let (cid, cidx) = ctrl in
  let (tid, tidx) = tgt in
  match cidx, tidx with
  | Some ci, Some ti ->
    [gate (QbitMap.find (cid, ci) qmap) (QbitMap.find (tid, ti) qmap)]
  | None, Some ti ->
    (match StringMap.find cid sym_tab with
     | TQReg csize ->
       let tgt_idx = (QbitMap.find (tid, ti) qmap) in
       List.init csize (fun i -> gate (QbitMap.find (cid, i) qmap) tgt_idx)
     | _ -> raise (Failure "ERROR: Not a qubit register!"))
  | Some ci, None ->
    (match StringMap.find tid sym_tab with
     | TQReg tsize ->
       let ctrl_idx = (QbitMap.find (cid, ci) qmap) in
       List.init tsize (fun i -> gate ctrl_idx (QbitMap.find (tid, i) qmap))
     | _ -> raise (Failure "ERROR: Not a qubit register!"))
  | None, None -> (* parallel application *)
    (match StringMap.find cid sym_tab, StringMap.find tid sym_tab with
     | TQReg csize, TQReg tsize ->
       if csize != tsize
       then raise (Failure "ERROR: register sizes do not match")
       else List.init csize (fun i ->
           gate (QbitMap.find (cid, i) qmap) (QbitMap.find (tid, i) qmap))
     | _ -> raise (Failure "ERROR: Not a qubit register!"))

(* Doubly-controlled gate application (partial) *)
let apply_double_c_gate gate ctrl1 ctrl2 tgt qmap sym_tab =
  let _ = ignore sym_tab in
  let (cid1, cidx1) = ctrl1 in
  let (cid2, cidx2) = ctrl2 in
  let (tid, tidx) = tgt in
  match cidx1, cidx2, tidx with
  | Some ci1, Some ci2, Some ti ->
    gate (QbitMap.find (cid1, ci1) qmap) (QbitMap.find (cid2, ci2) qmap) (QbitMap.find (tid, ti) qmap)
  (* ignore other cases... *)
  | _ -> raise (Failure "ERROR: Not a qubit register!")

let apply_gate gate (id, idx) qmap sym_tab =
  match idx with
  | Some i  -> [gate (QbitMap.find (id, i) qmap)]
  | None    ->
    match StringMap.find id sym_tab with
    | TQReg size -> List.init size (fun i -> gate (QbitMap.find (id, i) qmap))
    | _ -> raise (Failure "ERROR: Not a qubit register!")

let _CNOT m n = E.App2 (E.URzk_CNOT, m, n)
let _X    n = E.App1 (E.URzk_X,    n)
let _Z    n = E.App1 (E.uRzk_Z,    n)
let _H    n = E.App1 (E.URzk_H,    n)
let _P    n = E.App1 (E.uRzk_P,    n)
let _PDAG n = E.App1 (E.uRzk_PDAG, n)
let _T    n = E.App1 (E.uRzk_T,    n)
let _TDAG n = E.App1 (E.uRzk_TDAG, n)
let _Rz i n = E.App1 (E.URzk_Rz(i), n)

let translate_statement s qmap sym_tab =
  match s with
  | Qop qop ->
    (match qop with
     | Uop uop ->
       (match uop with
        | CX (ctrl, tgt) -> apply_c_gate _CNOT ctrl tgt qmap sym_tab
        | U _ -> raise (Failure "NYI: generic Unitary!")
        | Gate (id, params, qargs) ->
          (match StringMap.find_opt id sym_tab with
           | Some TGate _ -> (match id with
               | "ccz" -> apply_double_c_gate E.cCZ (List.hd qargs) (List.nth qargs 1) (List.nth qargs 2) qmap sym_tab
               | "ccx" -> apply_double_c_gate E.cCX (List.hd qargs) (List.nth qargs 1) (List.nth qargs 2) qmap sym_tab
               | "cx"  -> apply_c_gate _CNOT (List.hd qargs) (List.nth qargs 1) qmap sym_tab
               | "x"   -> apply_gate _X     (List.hd qargs) qmap sym_tab
               | "z"   -> apply_gate _Z     (List.hd qargs) qmap sym_tab
               | "h"   -> apply_gate _H     (List.hd qargs) qmap sym_tab
               | "s"   -> apply_gate _P     (List.hd qargs) qmap sym_tab
               | "sdg" -> apply_gate _PDAG  (List.hd qargs) qmap sym_tab
               | "t"   -> apply_gate _T     (List.hd qargs) qmap sym_tab
               | "tdg" -> apply_gate _TDAG  (List.hd qargs) qmap sym_tab
               | "rz15" -> (match List.hd params with
                           | Nninteger i -> apply_gate (_Rz i) (List.hd qargs) qmap sym_tab
                           | _ -> raise (Failure ("ERROR: Invalid argument to rz15 gate")))
               | g -> raise (Failure ("NYI: unsupported gate: " ^ g))
             )
           | Some _ -> raise (Failure "ERROR: Not a gate!")
           | None -> raise (Failure "ERROR: Gate not found!")
          ))
     | Meas _ -> print_endline ("NYI: Unsupported op: Measure"); []
     | Reset _ -> print_endline ("NYI: Reset"); [])
  | If _ -> print_endline ("NYI: If"); []
  | Barrier _ -> print_endline ("NYI: Unsupported op: Barrier"); []
  | _ -> []

let parse_decl (s : AST.statement) : (string * int) list =
  match s with
  | Decl d ->
    (match d with
     | QReg (name, size) ->
       List.map (fun i -> (name, i)) (List.init size (fun i -> i))
     | _ -> [])
  | _ -> []

let rec parse_qreg_decls p =
  match p with
  | []      -> []
  | s :: p' ->
    let first = parse_decl s in
    let rest = parse_qreg_decls p' in
    List.append first rest

let rec translate_program p qbit_map sym_tab =
  match p with
  | []      ->  []
  | s :: p' ->  let l = translate_statement s qbit_map sym_tab in
    let m = translate_program p' qbit_map sym_tab in
    List.append l m

let get_gate_list f =
  let ast = OpenQASM.get_ast f in (* dumb parsing *)
  let sym_tab = check ast in (* semantic analysis *)
  let qbit_list = parse_qreg_decls ast in
  let (qbit_map, n) = List.fold_left
      (fun (map, idx) entry -> (QbitMap.add entry idx map, idx+1))
      (QbitMap.empty, 0) qbit_list in
  (translate_program ast qbit_map sym_tab, n)

(** Write SQIR program out as OpenQASM **)

(* Currently too simple! Should convert back to OpenQASM AST and write from there! *)

let sqir_to_qasm_gate oc g =
  match g with
  | E.App1 (E.URzk_H,      n) -> fprintf oc "h q[%d];\n" n
  | E.App1 (E.URzk_X,      n) -> fprintf oc "x q[%d];\n" n
  | E.App1 (E.URzk_Rz(i),  n) ->
     (match i with
      | 8192 ->  fprintf oc "t q[%d];\n" n (* PI/4 *)
      | 16384 -> fprintf oc "s q[%d];\n" n (* PI/2 *)
      | 24576 -> fprintf oc "t q[%d];\ns q[%d];\n" n n (* 3PI/4 *)
      | 32768 -> fprintf oc "z q[%d];\n" n (* PI *)
      | 40960 -> fprintf oc "t q[%d];\nz q[%d];\n" n n (* 5PI/4 *)
      | 49152 -> fprintf oc "sdg q[%d];\n" n (* 3PI/2 *)
      | 57344 -> fprintf oc "tdg q[%d];\n" n (* 7PI/4 *)
      | _ -> fprintf oc "rz15(%d) q[%d];\n" i n)
  | E.App2 (E.URzk_CNOT, m, n) -> fprintf oc "cx q[%d], q[%d];\n" m n
  | _ -> raise (Failure ("ERROR: Failed to write qasm file")) (* badly typed case (e.g. App2 of UPI4_H) *)

let write_qasm_file fname p dim =
  let oc = open_out fname in
  (fprintf oc "OPENQASM 2.0;\ninclude \"qelib1.inc\";\n\n";
   fprintf oc "qreg q[%d];\n" dim;
   fprintf oc "\n";
   ignore(List.map (sqir_to_qasm_gate oc) p);
   close_out oc)
