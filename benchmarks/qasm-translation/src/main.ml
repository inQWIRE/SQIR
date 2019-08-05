open Extracted_code
open OQAST
open Printf

let parse_file f =
  let lexbuf = Lexing.from_channel (open_in f) in
  OQParser.mainprogram OQLexer.token lexbuf

module QbitIdx =
struct
  type t = string * int
  let compare (q0, i0) (q1, i1) =
    match Stdlib.compare q0 q1 with
    | 0 -> Stdlib.compare i0 i1
    | c -> c
end

module QbitMap = Map.Make(QbitIdx)

let convert_repr qmap (id, idx) =
  match idx with
  | Some i  -> QbitMap.find (id, i) qmap
  | None    -> QbitMap.find (id, 0) qmap (* assumes q[0] for q instead of the whole register TODO *)

let parse_statement s qmap : gate_app list =
  match s with
  | Decl _ -> []
  | GateDecl _ -> []
  | OpaqueDecl _ -> []
  | Qop qop ->
    (match qop with
     | Uop uop ->
       (match uop with
        | CX (ctrl, tgt)  ->
          [_CNOT (convert_repr qmap ctrl) (convert_repr qmap tgt)]
        | u               -> print_endline ("NYI UOP: " ^ show_uop u); [])
     | _ -> [])
  | If _ -> []
  | Barrier _ -> []

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

let rec parse_program p qbit_map =
  match p with
  | []      ->  []
  | s :: p' ->  let l = parse_statement s qbit_map in
    let m = parse_program p' qbit_map in
    List.append l m

let parse_gate_list f =
  let p = parse_file f in
  let qbit_list = parse_qreg_decls p in
  if (List.length qbit_list) == 0 then print_endline "INFO: No qubits!";
  let (qbit_map, _) = List.fold_left
      (fun (map, idx) entry -> (QbitMap.add entry idx map, idx+1))
      (QbitMap.empty, 0) qbit_list in
  parse_program p qbit_map

let parse f = parse_gate_list f

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

let parse_nam_benchmarks () = List.map (fun x -> parse x) nam_benchmark_filenames

type counts = {h:int; x:int; rz:int; cnot:int; total:int}

let get_counts progs : counts list =
  let tot p = (count_H_gates p) + (count_X_gates p) + (count_rotation_gates p) + (count_CNOT_gates p) in
  List.map (fun p -> {h=count_H_gates p;
                      x=count_X_gates p;
                      rz=count_rotation_gates p;
                      cnot=count_CNOT_gates p;
                      total=tot p})
           progs

(* write the results of running cancel_gates on the Nam benchmarks to file f *)
let run_on_nam_benchmarks f =
  let bs = parse_nam_benchmarks () in
  let bs' = List.mapi (fun i p ->
                       (printf "Processing %s...\n%!" (List.nth nam_benchmark_filenames i);
                        cancel_gates p)) bs in
  let counts = get_counts bs' in
  let oc = open_out f in
  (ignore(List.mapi (fun i x -> fprintf oc "%s,%d\n" (List.nth nam_benchmark_filenames i) x.total) counts);
   close_out oc)

let percent_diff l1 l2 = List.mapi (fun i x -> (float (x - (List.nth l2 i))) /. (float x)) l1
let average l = (List.fold_left ( +. ) 0.0 l) /. (float (List.length l))

(* print the results of running cancel_gates on the random benchmarks in directory d *)
let run_on_random_benchmarks d =
  let fs = Array.to_list (Array.map (fun f -> d ^ "/" ^ f) (Sys.readdir d)) in
  let bs = List.map parse fs in
  let bs' = List.mapi (fun i p ->
                       (printf "Processing %s...\n%!" (List.nth fs i);
                        cancel_gates p)) bs in
  let initial = get_counts bs in
  let final = get_counts bs' in
  let h_red = percent_diff (List.map (fun x -> x.h) initial) (List.map (fun x -> x.h) final) in
  let x_red = percent_diff (List.map (fun x -> x.x) initial) (List.map (fun x -> x.x) final) in
  let u1_red = percent_diff (List.map (fun x -> x.rz) initial) (List.map (fun x -> x.rz) final) in
  let cnot_red = percent_diff (List.map (fun x -> x.cnot) initial) (List.map (fun x -> x.cnot) final) in
  (printf "Gate h: average reduction = %f\n" (average h_red);
   printf "Gate x: average reduction = %f\n" (average x_red);
   printf "Gate rz: average reduction = %f\n" (average u1_red);
   printf "Gate cnot: average reduction = %f\n" (average cnot_red))
