open OQAST
open Extracted_code

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
  | None    -> QbitMap.find (id, 0) qmap

let parse_statement s qmap : benchmark_gate_app list =
  match s with
  | Decl _ -> []
  | GateDecl _ -> []
  | Qop qop ->
    (match qop with
     | Uop uop ->
       (match uop with
        | CX (ctrl, tgt)  ->
          [Bench_CNOT (convert_repr qmap ctrl, convert_repr qmap tgt)]
        | H q             -> [Bench_H (convert_repr qmap q)]
        | X q             -> [Bench_X (convert_repr qmap q)]
        | Z q             -> [Bench_Z (convert_repr qmap q)]
        | u               -> print_endline ("NYI UOP: " ^ show_uop u); [])
     | _ -> [])
  | If _ -> []

let parse_decl (s : OQAST.statement) : (string * int) list =
  match s with
  | Decl d ->
    (match d with
     | Qreg (name, size) ->
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

let parse f =
  let q = parse_gate_list f in
  benchmark_to_list q

let qasm_filenames = [
  "deutsch.qasm";
]

type counts = {h:int; x:int; rz:int; cnot:int; total:int}

let ast_list = List.map (fun f -> parse_file f) qasm_filenames

let benchmarks_list = List.map (fun file -> parse file) qasm_filenames
