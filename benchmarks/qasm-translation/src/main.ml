module B = BenchmarkGates
module S = SqireGates
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

let _CNOT m n = B.App2 (B.UPI4_CNOT, m, n)
let _X    n = B.App1 (B.UPI4_X,    n)
let _Z    n = B.App1 (B.uPI4_Z,    n)
let _H    n = B.App1 (B.UPI4_H,    n)
let _P    n = B.App1 (B.uPI4_P,    n)
let _PDAG n = B.App1 (B.uPI4_PDAG, n)
let _T    n = B.App1 (B.uPI4_T,    n)
let _TDAG n = B.App1 (B.uPI4_TDAG, n)

(* _bm for benchmarks; TODO: abstract out these two functions *)
let translate_statement_bm s qmap sym_tab =
  match s with
  | Qop qop ->
    (match qop with
     | Uop uop ->
       (match uop with
        | CX (ctrl, tgt) -> apply_c_gate _CNOT ctrl tgt qmap sym_tab
        | U _ -> raise (Failure "NYI: generic Unitary!")
        | Gate (id, _, qargs) ->
          (match StringMap.find_opt id sym_tab with
           | Some TGate _ -> (match id with
               | "cx"  -> apply_c_gate _CNOT
                            (List.hd qargs) (List.nth qargs 1) qmap sym_tab
               | "x"   -> apply_gate _X     (List.hd qargs) qmap sym_tab
               | "z"   -> apply_gate _Z     (List.hd qargs) qmap sym_tab
               | "h"   -> apply_gate _H     (List.hd qargs) qmap sym_tab
               | "s"   -> apply_gate _P     (List.hd qargs) qmap sym_tab (* phase gate *)
               | "sdg" -> apply_gate _PDAG  (List.hd qargs) qmap sym_tab
               | "t"   -> apply_gate _T     (List.hd qargs) qmap sym_tab
               | "tdg" -> apply_gate _TDAG  (List.hd qargs) qmap sym_tab
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

let translate_statement s qmap sym_tab : S.base_Unitary S.com list =
  match s with
  | Qop qop ->
    (match qop with
     | Uop uop -> List.map (fun ucom -> S.Uc ucom) (match uop with
         | CX (ctrl, tgt) -> apply_c_gate S.cNOT ctrl tgt qmap sym_tab
         | U _ -> raise (Failure "NYI: generic Unitary!")
         | Gate (id, params, qargs) ->
           (match StringMap.find_opt id sym_tab with
            | Some TGate _ -> (match id with
                | "cx"  -> apply_c_gate S.cNOT
                             (List.hd qargs) (List.nth qargs 1) qmap sym_tab
                | "x"   -> apply_gate S.x     (List.hd qargs) qmap sym_tab
                | "y"   -> apply_gate S.y     (List.hd qargs) qmap sym_tab
                | "z"   -> apply_gate S.z     (List.hd qargs) qmap sym_tab
                | "h"   -> apply_gate S.h     (List.hd qargs) qmap sym_tab
                | "id"  -> apply_gate S.iD    (List.hd qargs) qmap sym_tab
                | "s"   -> apply_gate S.p     (List.hd qargs) qmap sym_tab (* phase gate *)
                | "sdg" -> apply_gate S.pDAG  (List.hd qargs) qmap sym_tab
                | "t"   -> apply_gate S.t     (List.hd qargs) qmap sym_tab
                | "tdg" -> apply_gate S.tDAG  (List.hd qargs) qmap sym_tab
                | "rz"  -> apply_p_gate S.rz params (List.hd qargs) qmap sym_tab
                (*TODO other parametrized gates*)
                | g -> raise (Failure ("NYI: unsupported gate: " ^ g))
              )
            | Some _ -> raise (Failure "ERROR: Not a gate!")
            | None -> raise (Failure "ERROR: Gate not found!")
           ))
     | Meas (qarg, _) -> apply_meas qarg qmap sym_tab
     | Reset qarg -> apply_reset qarg qmap sym_tab)
  | If _ -> print_endline ("NYI: If"); []
  | Barrier _ -> print_endline ("NYI: Unsupported op: Barrier"); []
  | _ -> []

let parse_decl (s : OQAST.statement) : (string * int) list =
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

let rec translate_program_bm p qbit_map sym_tab =
  match p with
  | []      ->  []
  | s :: p' ->  let l = translate_statement_bm s qbit_map sym_tab in
    let m = translate_program_bm p' qbit_map sym_tab in
    List.append l m

let rec translate_program p qbit_map sym_tab =
  match p with
  | []      ->  []
  | s :: p' ->  let l = translate_statement s qbit_map sym_tab in
    let m = translate_program p' qbit_map sym_tab in
    List.append l m

(* used only for benchmarks *)
let get_gate_list f =
  let ast = parse_file f in (* dumb parsing *)
  let sym_tab = check ast in (* semantic analysis *)
  let qbit_list = parse_qreg_decls ast in
  let (qbit_map, _) = List.fold_left
      (fun (map, idx) entry -> (QbitMap.add entry idx map, idx+1))
      (QbitMap.empty, 0) qbit_list in
  translate_program_bm ast qbit_map sym_tab

(* general parsing *)
let parse f =
  let ast = parse_file f in (* dumb parsing *)
  let sym_tab = check ast in (* semantic analysis *)
  let qbit_list = parse_qreg_decls ast in
  let (qbit_map, _) = List.fold_left
      (fun (map, idx) entry -> (QbitMap.add entry idx map, idx+1))
      (QbitMap.empty, 0) qbit_list in
  translate_program ast qbit_map sym_tab

let nam_benchmark_filenames = [
  "../nam-benchmarks/adder_8.qasm";
  "../nam-benchmarks/barenco_tof_10.qasm";
  "../nam-benchmarks/barenco_tof_3.qasm";
  "../nam-benchmarks/barenco_tof_4.qasm";
  "../nam-benchmarks/barenco_tof_5.qasm";
  "../nam-benchmarks/csla_mux_3.qasm";
  "../nam-benchmarks/csum_mux_9.qasm";
  "../nam-benchmarks/gf2^E10_mult.qasm";
  "../nam-benchmarks/gf2^E16_mult.qasm";
  "../nam-benchmarks/gf2^E32_mult.qasm";
  "../nam-benchmarks/gf2^E4_mult.qasm";
  "../nam-benchmarks/gf2^E5_mult.qasm";
  "../nam-benchmarks/gf2^E64_mult.qasm";
  "../nam-benchmarks/gf2^E6_mult.qasm";
  "../nam-benchmarks/gf2^E7_mult.qasm";
  "../nam-benchmarks/gf2^E8_mult.qasm";
  "../nam-benchmarks/gf2^E9_mult.qasm";
  "../nam-benchmarks/mod5_4.qasm";
  "../nam-benchmarks/mod_mult_55.qasm";
  "../nam-benchmarks/mod_red_21.qasm";
  "../nam-benchmarks/qcla_adder_10.qasm";
  "../nam-benchmarks/qcla_com_7.qasm";
  "../nam-benchmarks/qcla_mod_7.qasm";
  "../nam-benchmarks/rc_adder_6.qasm";
  "../nam-benchmarks/tof_10.qasm";
  "../nam-benchmarks/tof_3.qasm";
  "../nam-benchmarks/tof_4.qasm";
  "../nam-benchmarks/tof_5.qasm";
  "../nam-benchmarks/vbe_adder_3.qasm";
]

let parse_nam_benchmarks () = List.map (fun x -> get_gate_list x) nam_benchmark_filenames

type counts = {h:int; x:int; rz:int; cnot:int; total:int}

let get_counts progs : counts list =
  let tot p = (B.count_H_gates p) + (B.count_X_gates p)
              + (B.count_rotation_gates p) + (B.count_CNOT_gates p) in
  List.map (fun p -> {h=B.count_H_gates p;
                      x=B.count_X_gates p;
                      rz=B.count_rotation_gates p;
                      cnot=B.count_CNOT_gates p;
                      total=tot p})
    progs

(* write the results of running cancel_gates, hadamard_reduction on the Nam benchmarks to file f *)
let run_on_nam_benchmarks f =
  let bs = parse_nam_benchmarks () in
  let _ = printf "Running cancel_gates pass\n%!" in
  let bs1 = List.mapi (fun i p ->
      (printf "Processing %s...\n%!" (List.nth nam_benchmark_filenames i);
       B.cancel_gates p)) bs in
  let _ = printf "Running alternating passes\n%!" in
  let bs2 = List.mapi (fun i p ->
      (printf "Processing %s...\n%!" (List.nth nam_benchmark_filenames i);
       B.cancel_gates (B.hadamard_reduction (B.cancel_gates
                                               (B.hadamard_reduction
                                                  (B.cancel_gates p)))))) bs in
  let counts1 = get_counts bs1 in
  let counts2 = get_counts bs2 in
  let oc = open_out f in
  (ignore(List.mapi (fun i x -> fprintf oc "%s,%d,%d\n"
                        (List.nth nam_benchmark_filenames i)
                        x.total
                        ((fun x -> x.total) (List.nth counts2 i)))
            counts1);
   close_out oc)

let percent_diff l1 l2 = List.mapi (fun i x -> (float (x - (List.nth l2 i))) /. (float x)) l1
let average l = (List.fold_left ( +. ) 0.0 l) /. (float (List.length l))

(* print the results of running cancel_gates, hadamard_reduction on the random benchmarks in directory d *)
let run_on_random_benchmarks d =
  let fs = Array.to_list (Array.map (fun f -> d ^ "/" ^ f) (Sys.readdir d)) in
  let bs = List.map get_gate_list fs in
  let _ = printf "Running cancel_gates pass\n%!" in
  let bs1 = List.mapi (fun i p ->
      (printf "Processing %s...\n%!" (List.nth fs i);
       B.cancel_gates p)) bs in
  let _ = printf "Running alternating passes\n%!" in
  let bs2 = List.mapi (fun i p ->
      (printf "Processing %s...\n%!" (List.nth fs i);
       B.cancel_gates (B.hadamard_reduction (B.cancel_gates
                                               (B.hadamard_reduction
                                                  (B.cancel_gates p)))))) bs in
  let initial = get_counts bs in
  let final1 = get_counts bs1 in
  let h_red1 = percent_diff (List.map (fun x -> x.h) initial) (List.map (fun x -> x.h) final1) in
  let x_red1 = percent_diff (List.map (fun x -> x.x) initial) (List.map (fun x -> x.x) final1) in
  let u1_red1 = percent_diff (List.map (fun x -> x.rz) initial) (List.map (fun x -> x.rz) final1) in
  let cnot_red1 = percent_diff (List.map (fun x -> x.cnot) initial) (List.map (fun x -> x.cnot) final1) in
  let final2 = get_counts bs2 in
  let h_red2 = percent_diff (List.map (fun x -> x.h) initial) (List.map (fun x -> x.h) final2) in
  let x_red2 = percent_diff (List.map (fun x -> x.x) initial) (List.map (fun x -> x.x) final2) in
  let u1_red2 = percent_diff (List.map (fun x -> x.rz) initial) (List.map (fun x -> x.rz) final2) in
  let cnot_red2 = percent_diff (List.map (fun x -> x.cnot) initial) (List.map (fun x -> x.cnot) final2) in
  (printf "cancel_gates results:\n";
   printf "Gate h: average reduction = %f\n" (average h_red1);
   printf "Gate x: average reduction = %f\n" (average x_red1);
   printf "Gate rz: average reduction = %f\n" (average u1_red1);
   printf "Gate cnot: average reduction = %f\n" (average cnot_red1);
   printf "cancel_gates + hadamard_reduction results:\n";
   printf "Gate h: average reduction = %f\n" (average h_red2);
   printf "Gate x: average reduction = %f\n" (average x_red2);
   printf "Gate rz: average reduction = %f\n" (average u1_red2);
   printf "Gate cnot: average reduction = %f\n" (average cnot_red2))
