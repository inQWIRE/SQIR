open Qasm2sqir
open Printf
    
open Optimize
open GateCount
open SimpleMappingWithLayout
open MappingExamples

(* To compile: 
     In VOQC directory, `dune build mapper.exe`
   To run: 
     In VOQC directory, `dune exec -- ./mapper.exe -i <input file> -o <output file>`  
   *)

(* Some architectures extracted from Coq:
   - LNN: coq_LNN_is_in_graph_b, coq_LNN_get_path
   - LNN ring: coq_LNN_ring_is_in_graph_b, coq_LNN_ring_get_path
   - 2d LNN: grid_is_in_graph_b, grid_get_graph
   - Tenerife (sets pdim = 5): tenerife_is_in_graph_b, tenerife_get_graph
   
   I'll use LNNRing with pdim (number of physical qubits in the architecture)
   equal to ldim (the number of logical qubits in the program).

   We should support arbitrary graphs. 
   Here's one OCaml graph library I was looking at: https://opam.ocaml.org/packages/ocamlgraph/ *)

let print_layout ldim pdim m =
  List.iter (fun x -> match x with | None -> printf "X " | Some n -> printf "%d " n) (layout_to_list ldim pdim m)

let fname = ref ""
let outf = ref ""
let usage = "usage: " ^ Sys.argv.(0) ^ " [-i string] [-o string]"
let speclist = [
    ("-i", Arg.Set_string fname, ": input filename");
    ("-o", Arg.Set_string outf, ": output filename");
  ]
let () =
  Arg.parse
    speclist
    (fun x -> raise (Arg.Bad ("Bad argument : " ^ x)))
    usage;
if !fname = "" then printf "Input filename required.\n%!" else 
if !outf = "" then printf "Output filename required.\n%!" else
let _ = printf "Input file: %s\nOutput file: %s\n%!" !fname !outf in
let (p, ldim) = get_gate_list !fname in
let pdim = ldim in
let origTotal = List.length p in
let origRz = get_rz_count p in
let origH = get_h_count p in
let origX = get_x_count p in
let origCNOT = get_cnot_count p in
let _ = printf "Original:\t Total %d, Rz %d, H %d, X %d, CNOT %d\n%!" 
        origTotal origRz origH origX origCNOT in
let m = trivial_layout ldim pdim in
let _ = (printf "Input layout: "; print_layout ldim pdim m; printf "\n%!") in
let get_path = LNNRing.coq_LNN_ring_get_path pdim in
let is_in_graph_b = LNNRing.coq_LNN_ring_is_in_graph_b pdim in
let p1 = only_map ldim pdim p m get_path is_in_graph_b in
let p2 = optimize_then_map ldim pdim p m get_path is_in_graph_b in
let p3 = map_then_optimize ldim pdim p m get_path is_in_graph_b in
let p4 = optimize_then_map_then_optimize ldim pdim p m get_path is_in_graph_b in
match p1 with
| None -> printf "VOQC failed - Ill-formed input layout or input program"
| Some (p1,m1) ->
    let finalTotal = List.length p1 in
    let finalRz = get_rz_count p1 in
    let finalH = get_h_count p1 in
    let finalX = get_x_count p1 in
    let finalCNOT = get_cnot_count p1 in
    let _ = printf "Final (map):\t Total %d, Rz %d, H %d, X %d, CNOT %d\n%!" 
            finalTotal finalRz finalH finalX finalCNOT in
    let _ = (printf "Final layout: "; print_layout ldim pdim m1; printf "\n%!") in
    write_qasm_file !outf p1 pdim;
    match p2, p3, p4 with
    | Some (p2,_), Some (p3,_), Some (p4,_) ->
        let finalTotal = List.length p2 in
        let finalRz = get_rz_count p2 in
        let finalH = get_h_count p2 in
        let finalX = get_x_count p2 in
        let finalCNOT = get_cnot_count p2 in
        let _ = printf "Final (optimize -> map):\t Total %d, Rz %d, H %d, X %d, CNOT %d\n%!" 
                finalTotal finalRz finalH finalX finalCNOT in
        let finalTotal = List.length p3 in
        let finalRz = get_rz_count p3 in
        let finalH = get_h_count p3 in
        let finalX = get_x_count p3 in
        let finalCNOT = get_cnot_count p3 in
        let _ = printf "Final (map -> optimize):\t Total %d, Rz %d, H %d, X %d, CNOT %d\n%!" 
                finalTotal finalRz finalH finalX finalCNOT in
        let finalTotal = List.length p4 in
        let finalRz = get_rz_count p4 in
        let finalH = get_h_count p4 in
        let finalX = get_x_count p4 in
        let finalCNOT = get_cnot_count p4 in
        let _ = printf "Final (optimize -> map -> optimize):\t Total %d, Rz %d, H %d, X %d, CNOT %d\n%!" 
                finalTotal finalRz finalH finalX finalCNOT in
        ()
    | _, _, _ -> printf "should be unreachable???"

   
