open OpenQASM
open OpenQASM.AST
open Printf
module StringMap = Map.Make(String)

(* Code for converting between OpenQASM and SQIR programs (gate set independent). *)

(** List of recognized gates **)

let qelib1 = [

  (* standard gates *)
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
  
  (* custom - rotation by a rational multiple of PI *)
  ("rzq", TGate(2,1))
]

let check_stmt symTab stmt =
  match stmt with
  | Include "qelib1.inc" -> List.fold_left
                              (fun map (gate, typ) -> StringMap.add gate typ map)
                              symTab qelib1
  | Include _ -> raise (Failure "ERROR: Unsupported include")
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
     | _ -> raise (Failure "ERROR: Not a qubit register"))
  | Some ci, None ->
    (match StringMap.find tid sym_tab with
     | TQReg tsize ->
       let ctrl_idx = (QbitMap.find (cid, ci) qmap) in
       List.init tsize (fun i -> gate ctrl_idx (QbitMap.find (tid, i) qmap))
     | _ -> raise (Failure "ERROR: Not a qubit register"))
  | None, None -> (* parallel application *)
    (match StringMap.find cid sym_tab, StringMap.find tid sym_tab with
     | TQReg csize, TQReg tsize ->
       if csize != tsize
       then raise (Failure "ERROR: Register sizes do not match")
       else List.init csize (fun i ->
           gate (QbitMap.find (cid, i) qmap) (QbitMap.find (tid, i) qmap))
     | _ -> raise (Failure "ERROR: Not a qubit register"))

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
  | _ -> raise (Failure "ERROR: Not a qubit register")

let apply_gate gate (id, idx) qmap sym_tab =
  match idx with
  | Some i  -> [gate (QbitMap.find (id, i) qmap)]
  | None    ->
    match StringMap.find id sym_tab with
    | TQReg size -> List.init size (fun i -> gate (QbitMap.find (id, i) qmap))
    | _ -> raise (Failure "ERROR: Not a qubit register")

let rec interp_float_exp (e : exp) : float =
  match e with
  | Real r -> r
  | Pi -> Float.pi
  | Nninteger n -> Float.of_int n
  | UnaryOp (UMinus, e1) -> -. (interp_float_exp e1)
  | BinaryOp (Times, e1, e2) -> (interp_float_exp e1) *. (interp_float_exp e2)
  | BinaryOp (Div, e1, e2) -> (interp_float_exp e1) /. (interp_float_exp e2)
  | _ -> raise (Failure "NYI: Invalid float expression")

let rec interp_int_exp (e : exp) : int =
  match e with
  | Nninteger n -> n
  | UnaryOp (UMinus, e1) -> - (interp_int_exp e1)
  | _ -> raise (Failure "NYI: Invalid int expression")

let translate_statement s qmap sym_tab qasm_to_sqir_gate =
  match s with
  | Qop qop ->
    (match qop with
     | Uop uop -> qasm_to_sqir_gate uop qmap sym_tab
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

let rec parse_qreg_decls' p acc =
  match p with
  | []      -> acc
  | s :: p' ->
    let first = parse_decl s in
    parse_qreg_decls' p' (acc @ first)
let parse_qreg_decls p = parse_qreg_decls' p []

let rec translate_program' p qbit_map sym_tab acc qasm_to_sqir_gate =
  match p with
  | []      ->  acc
  | s :: p' ->  
      let l = translate_statement s qbit_map sym_tab qasm_to_sqir_gate in
      translate_program' p' qbit_map sym_tab (acc @ l) qasm_to_sqir_gate
let translate_program p qbit_map sym_tab qasm_to_sqir_gate = 
  translate_program' p qbit_map sym_tab [] qasm_to_sqir_gate

let get_gate_list f qasm_to_sqir_gate =
  let ast = OpenQASM.get_ast f in (* dumb parsing *)
  let sym_tab = check ast in (* semantic analysis *)
  let qbit_list = parse_qreg_decls ast in
  let (qbit_map, n) = List.fold_left
      (fun (map, idx) entry -> (QbitMap.add entry idx map, idx+1))
      (QbitMap.empty, 0) qbit_list in
  (translate_program ast qbit_map sym_tab qasm_to_sqir_gate, n)

(** Write SQIR program out as OpenQASM **)

(* Currently too simple! Should convert back to OpenQASM AST and write from there! *)

let write_qasm_file fname p dim sqir_to_qasm_gate =
  let oc = open_out fname in
  (fprintf oc "OPENQASM 2.0;\ninclude \"qelib1.inc\";\n\n";
   fprintf oc "qreg q[%d];\n" dim;
   fprintf oc "\n";
   ignore(List.map (sqir_to_qasm_gate oc) p);
   close_out oc)
   
