module B = BenchmarkGates

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

let _CNOT m n = B.App2 (B.UPI4_CNOT, m, n)
let _X    n = B.App1 (B.UPI4_X,    n)
let _Z    n = B.App1 (B.uPI4_Z,    n)
let _H    n = B.App1 (B.UPI4_H,    n)
let _P    n = B.App1 (B.uPI4_P,    n)
let _PDAG n = B.App1 (B.uPI4_PDAG, n)
let _T    n = B.App1 (B.uPI4_T,    n)
let _TDAG n = B.App1 (B.uPI4_TDAG, n)

let translate_statement s qmap sym_tab =
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

let rec translate_program p qbit_map sym_tab =
  match p with
  | []      ->  []
  | s :: p' ->  let l = translate_statement s qbit_map sym_tab in
    let m = translate_program p' qbit_map sym_tab in
    List.append l m

let get_gate_list f =
  let ast = parse_file f in (* dumb parsing *)
  let sym_tab = check ast in (* semantic analysis *)
  let qbit_list = parse_qreg_decls ast in
  let (qbit_map, _) = List.fold_left
      (fun (map, idx) entry -> (QbitMap.add entry idx map, idx+1))
      (QbitMap.empty, 0) qbit_list in
  translate_program ast qbit_map sym_tab

(******************************************************************************)
(* Benchmark specific code                                                    *)
(******************************************************************************)

let nam_benchmark_filenames = [
  "../nam-benchmarks/adder_8.qasm";
  "../nam-benchmarks/barenco_tof_10.qasm";
  "../nam-benchmarks/barenco_tof_3.qasm";
  "../nam-benchmarks/barenco_tof_4.qasm";
  "../nam-benchmarks/barenco_tof_5.qasm";
  "../nam-benchmarks/csla_mux_3.qasm";
  "../nam-benchmarks/csum_mux_9.qasm";
  "../nam-benchmarks/gf2^10_mult.qasm";
  "../nam-benchmarks/gf2^16_mult.qasm";
  "../nam-benchmarks/gf2^32_mult.qasm";
  "../nam-benchmarks/gf2^4_mult.qasm";
  "../nam-benchmarks/gf2^5_mult.qasm";
  (*"../nam-benchmarks/gf2^64_mult.qasm";*)
  "../nam-benchmarks/gf2^6_mult.qasm";
  "../nam-benchmarks/gf2^7_mult.qasm";
  "../nam-benchmarks/gf2^8_mult.qasm";
  "../nam-benchmarks/gf2^9_mult.qasm";
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

let nam_benchmark_dims = [ 24; 19; 5; 7; 9; 15; 30; 30; 48; 96; 12; 15; (*192;*) 18; 21; 24; 27; 5; 9; 11; 36; 24; 26; 14; 19; 5; 7; 9; 10; ]

let parse_nam_benchmarks () = List.map (fun x -> get_gate_list x) nam_benchmark_filenames

(* super simple translation to QASM *)
let sqire_to_qasm_gate oc g =
  match g with
  | B.App1 (B.UPI4_H,     n) -> fprintf oc "h q[%d];\n" n
  | B.App1 (B.UPI4_X,     n) -> fprintf oc "x q[%d];\n" n
  | B.App1 (B.UPI4_PI4(1), n) -> fprintf oc "t q[%d];\n" n
  | B.App1 (B.UPI4_PI4(2), n) -> fprintf oc "s q[%d];\n" n
  | B.App1 (B.UPI4_PI4(3), n) -> fprintf oc "t q[%d];\ns q[%d];\n" n n
  | B.App1 (B.UPI4_PI4(4), n) -> fprintf oc "z q[%d];\n" n
  | B.App1 (B.UPI4_PI4(5), n) -> fprintf oc "t q[%d];\nz q[%d];\n" n n
  | B.App1 (B.UPI4_PI4(6), n) -> fprintf oc "sdg q[%d];\n" n
  | B.App1 (B.UPI4_PI4(7), n) -> fprintf oc "tdg q[%d];\n" n
  | B.App2 (B.UPI4_CNOT, m, n) -> fprintf oc "cx q[%d], q[%d];\n" m n
  | B.App1 (B.UPI4_PI4(x), _) -> (printf "skipping current gate w/ rotation=%d\n%!" x) (* should never happen *)
  | _ -> () (* badly typed case (e.g. App2 of UPI4_H) *)

let write_qasm_file fname p dim =
  let oc = open_out fname in
  (fprintf oc "OPENQASM 2.0;\ninclude \"qelib1.inc\";\n\n";
   fprintf oc "qreg q[%d];\n" dim;
   fprintf oc "\n";
   ignore(List.map (sqire_to_qasm_gate oc) p);
   close_out oc;
   printf "Done.\n")
   
type counts = {h:int; x:int; rz:int; cnot:int; total:int}

let total_count p = (B.count_H_gates p) + (B.count_X_gates p) + (B.count_rotation_gates p) + (B.count_CNOT_gates p)

let get_counts progs : counts list =
  List.map (fun p -> {h=B.count_H_gates p;
                      x=B.count_X_gates p;
                      rz=B.count_rotation_gates p;
                      cnot=B.count_CNOT_gates p;
                      total=total_count p})
    progs

let rec run_alternating_passes num_qbits p prev_c =
  if (B.pI4_list_well_typed_b num_qbits p)  
  then ()
  else printf "Dimension check failed - optimization results are invalid!\n%!";
  let p' = B.merge_rotations num_qbits 
           (B.hadamard_reduction (B.cancel_gates p)) in
  let c = total_count p' in
  if c < prev_c
  then (printf "\tRepeating alternating iteration...\n%!";
      run_alternating_passes num_qbits p' c)
  else p'

(* write the results of running optimizations on the Nam benchmarks to file f *)
let run_on_nam_benchmarks f =
  let bs = parse_nam_benchmarks () in
  let bs' = List.mapi (fun i p ->
      (printf "Processing %s\n%!" (List.nth nam_benchmark_filenames i);
       run_alternating_passes (List.nth nam_benchmark_dims i) p (total_count p))) bs in
  let counts = get_counts bs' in
  let oc = open_out f in
  (ignore(List.mapi (fun i x -> fprintf oc "%s,%d\n"
                        (List.nth nam_benchmark_filenames i)
                        x.total)
            counts);
   close_out oc)
   
(* special function to run limited opts. on gf2^64 *)
let rec run_limited_alternating_passes num_qbits p prev_c =
  if (B.pI4_list_well_typed_b num_qbits p)  
  then ()
  else printf "Dimension check failed - optimization results are invalid!\n%!";
  let p' = B.hadamard_reduction (B.cancel_gates p) in
  let c = total_count p' in
  if c < prev_c
  then (printf "\tRepeating alternating iteration...\n%!";
      run_limited_alternating_passes num_qbits p' c)
  else p'
let run_on_gf2_64 () =
  let p = get_gate_list "../gf2^64_mult.qasm" in
  let p' = run_limited_alternating_passes 192 p (total_count p) in
  printf "Final gate count: %d\n" (total_count p')

let percent_diff l1 l2 = List.mapi (fun i x -> (float (x - (List.nth l2 i))) /. (float x)) l1
let average l = (List.fold_left ( +. ) 0.0 l) /. (float (List.length l))

(* print the results of running optimizations on the random benchmarks in directory d,
   assumes all benchmarks use nq qubits *)
let run_on_random_benchmarks d nq =
  let fs = Array.to_list (Array.map (fun f -> d ^ "/" ^ f) (Sys.readdir d)) in
  let bs = List.map get_gate_list fs in
  let bs' = List.mapi (fun i p ->
      (printf "Processing %s\n%!" (List.nth fs i);
       run_alternating_passes nq p (total_count p))) bs in
  let initial = get_counts bs in
  let final = get_counts bs' in
  let h_red = percent_diff (List.map (fun x -> x.h) initial) (List.map (fun x -> x.h) final) in
  let x_red = percent_diff (List.map (fun x -> x.x) initial) (List.map (fun x -> x.x) final) in
  let u1_red = percent_diff (List.map (fun x -> x.rz) initial) (List.map (fun x -> x.rz) final) in
  let cnot_red = percent_diff (List.map (fun x -> x.cnot) initial) (List.map (fun x -> x.cnot) final) in
  (printf "Results:\n";
   printf "Gate h: average reduction = %f\n" (average h_red);
   printf "Gate x: average reduction = %f\n" (average x_red);
   printf "Gate rz: average reduction = %f\n" (average u1_red);
   printf "Gate cnot: average reduction = %f\n" (average cnot_red))
   