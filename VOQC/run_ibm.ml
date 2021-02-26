open Printf
open Voqc.IBMUtils
open Voqc.Optimize

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
let t1 = Unix.gettimeofday () in
let (p, dim) = get_gate_list !fname in
let _ = printf "Time to parse: %fs\n" (Unix.gettimeofday () -. t1) in
let t2 = Unix.gettimeofday () in
let origTotal = List.length p in
let origU1 = get_u1_count p in
let origU2 = get_u2_count p in
let origU3 = get_u3_count p in
let origCNOT = get_cnot_count p in
let _ = printf "Original:\t %d Total, U1 %d, U2 %d, U3 %d, CNOT %d\n%!" 
        origTotal origU1 origU2 origU3 origCNOT in
let _ = printf "Time to count orig. gates: %fs\n" (Unix.gettimeofday () -. t2) in
let t3 = Unix.gettimeofday () in
let p1 = optimize_ibm p in
let _ = printf "Time to optimize: %fs\n" (Unix.gettimeofday () -. t3) in
let t4 = Unix.gettimeofday () in
let finalTotal = List.length p1 in
let finalU1 = get_u1_count p1 in
let finalU2 = get_u2_count p1 in
let finalU3 = get_u3_count p1 in
let finalCNOT = get_cnot_count p1 in
let _ = printf "Final:\t\t %d Total, U1 %d, U2 %d, U3 %d, CNOT %d\n%!" 
        finalTotal finalU1 finalU2 finalU3 finalCNOT in
let _ = printf "Time to count final gates: %fs\n" (Unix.gettimeofday () -. t4) in
let t5 = Unix.gettimeofday () in
write_qasm_file !outf p1 dim;
printf "Time to write file: %fs\n" (Unix.gettimeofday () -. t5) 
