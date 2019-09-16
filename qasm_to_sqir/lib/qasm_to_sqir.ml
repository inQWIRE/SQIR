module S = SqirGates

open OQAST
open OQLexer
open Semant

open Printf
open Lexing

(* Error handling adapted from Real World OCaml *)
let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try OQParser.mainprogram OQLexer.token lexbuf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    []
  | OQParser.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)

(* core parsing routine *)
let parse_file f =
  let lexbuf = Lexing.from_channel (open_in f) in
  parse_with_error lexbuf

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

let apply_gate gate (id, idx) qmap sym_tab =
  match idx with
  | Some i  -> [gate (QbitMap.find (id, i) qmap)]
  | None    ->
    match StringMap.find id sym_tab with
    | TQReg size -> List.init size (fun i -> gate (QbitMap.find (id, i) qmap))
    | _ -> raise (Failure "ERROR: Not a qubit register!")

(* TODO very hacky right now *)
let apply_p_gate gate params (id, idx) qmap sym_tab =
  match idx, params with
  | Some i, [Real lambda] -> [gate lambda (QbitMap.find (id, i) qmap)]
  | None, [Real lambda] ->
    (match StringMap.find id sym_tab with
     | TQReg size -> List.init size (fun i -> gate lambda (QbitMap.find (id, i) qmap))
     | _ -> raise (Failure "ERROR: Not a qubit register!"))
  | _ -> raise (Failure "NYI: parametrized gate")

let apply_meas (id, idx) qmap sym_tab =
  match idx with
  | Some i  -> [S.Meas (QbitMap.find (id, i) qmap, S.Skip, S.Skip)]
  | None    ->
    match StringMap.find id sym_tab with
    | TQReg size -> List.init size (fun i -> S.Meas (QbitMap.find (id, i) qmap,
                                                     S.Skip, S.Skip))
    | _ -> raise (Failure "ERROR: Not a qubit register!")

let apply_reset (id, idx) qmap sym_tab =
  match idx with
  | Some i  -> let n = (QbitMap.find (id, i) qmap) in [S.Meas (n, S.Uc (S.x n), S.Skip)]
  | None    ->
    match StringMap.find id sym_tab with
    | TQReg size -> List.init size (fun i -> let n = (QbitMap.find (id, i) qmap) in
                                     S.Meas (n, S.Uc (S.x n), S.Skip))
    | _ -> raise (Failure "ERROR: Not a qubit register!")

let translate_statement s bmap sym_tab : S.base_Unitary S.com list =
  match s with
  | Qop qop ->
    (match qop with
     | Uop uop -> List.map (fun ucom -> S.Uc ucom) (match uop with
         | CX (ctrl, tgt) -> apply_c_gate S.cNOT ctrl tgt bmap sym_tab
         | U _ -> raise (Failure "NYI: generic Unitary!")
         | Gate (id, params, qargs) ->
           (match StringMap.find_opt id sym_tab with
            | Some TGate _ -> (match id with
                | "cx"  -> apply_c_gate S.cNOT
                             (List.hd qargs) (List.nth qargs 1) bmap sym_tab
                | "x"   -> apply_gate S.x     (List.hd qargs) bmap sym_tab
                | "y"   -> apply_gate S.y     (List.hd qargs) bmap sym_tab
                | "z"   -> apply_gate S.z     (List.hd qargs) bmap sym_tab
                | "h"   -> apply_gate S.h     (List.hd qargs) bmap sym_tab
                | "id"  -> apply_gate S.iD    (List.hd qargs) bmap sym_tab
                | "s"   -> apply_gate S.p     (List.hd qargs) bmap sym_tab (* phase gate *)
                | "sdg" -> apply_gate S.pDAG  (List.hd qargs) bmap sym_tab
                | "t"   -> apply_gate S.t     (List.hd qargs) bmap sym_tab
                | "tdg" -> apply_gate S.tDAG  (List.hd qargs) bmap sym_tab
                | "rz"  -> apply_p_gate S.rz params (List.hd qargs) bmap sym_tab
                (*TODO other parametrized gates*)
                | g -> raise (Failure ("NYI: unsupported gate: " ^ g))
              )
            | Some _ -> raise (Failure "ERROR: Not a gate!")
            | None -> raise (Failure "ERROR: Gate not found!")
           ))
     | Meas (qarg, _) -> apply_meas qarg bmap sym_tab
     | Reset qarg -> apply_reset qarg bmap sym_tab)
  | If _ -> print_endline ("NYI: If"); []
  | Barrier _ -> print_endline ("NYI: Unsupported op: Barrier"); []
  | _ -> []

let parse_decl (s : OQAST.statement) : (bool * string * int) list =
  match s with
  | Decl d ->
    (match d with
     | QReg (name, size) ->
       List.map (fun i -> (true, name, i)) (List.init size (fun i -> i))
     | CReg (name, size) ->
       List.map (fun i -> (false, name, i)) (List.init size (fun i -> i)))
  | _ -> []

let rec parse_reg_decls p =
  match p with
  | []      -> []
  | s :: p' ->
    let first = parse_decl s in
    let rest = parse_reg_decls p' in
    List.append first rest

let rec translate_program p bit_map sym_tab =
  match p with
  | []      ->  []
  | s :: p' ->  let l = translate_statement s bit_map sym_tab in
    let m = translate_program p' bit_map sym_tab in
    List.append l m

let parse f =
  let ast = parse_file f in (* dumb parsing *)
  let sym_tab = check ast in (* semantic analysis *)
  let bit_list = parse_reg_decls ast in
  let qbit_list = List.map (fun (_, id, i) -> (id, i))
      (List.filter (fun (ty, _, _) -> ty) bit_list) in
  let cbit_list = List.map (fun (_, id, i) -> (id, i))
      (List.filter (fun (ty, _, _) -> not ty) bit_list) in
  let (qbit_map, _) = List.fold_left
      (fun (map, idx) entry -> (QbitMap.add entry idx map, idx+1))
      (QbitMap.empty, 0) qbit_list in
  let (bit_map, _) = List.fold_left
      (fun (map, idx) entry -> (QbitMap.add entry idx map, idx+1))
      (qbit_map, 0) cbit_list in
  translate_program ast bit_map sym_tab
