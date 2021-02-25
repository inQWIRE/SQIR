open IBMUtils
open Printf
open Optimize

(* light argument parsing *)
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
let _ = if !outf = "" then outf := !fname ^ "_opt" else () in
let _ = printf "Input file: %s\nOutput file: %s\n%!" !fname !outf in
let (p, dim) = get_gate_list !fname in
let origTotal = List.length p in
let origU1 = get_u1_count p in
let origU2 = get_u2_count p in
let origU3 = get_u3_count p in
let origCNOT = get_cnot_count p in
let _ = printf "Original:\t %d Total, U1 %d, U2 %d, U3 %d, CNOT %d\n%!" 
        origTotal origU1 origU2 origU3 origCNOT in
let p1 = optimize_ibm p in
let finalTotal = List.length p1 in
let finalU1 = get_u1_count p1 in
let finalU2 = get_u2_count p1 in
let finalU3 = get_u3_count p1 in
let finalCNOT = get_cnot_count p1 in
let _ = printf "Final:\t\t %d Total, U1 %d, U2 %d, U3 %d, CNOT %d\n%!" 
        finalTotal finalU1 finalU2 finalU3 finalCNOT in
write_qasm_file !outf p1 dim;
