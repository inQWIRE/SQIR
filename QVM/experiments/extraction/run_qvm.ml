open Printf

open AltGateSet
open AltPQASM
(*open OracleExample*)

(* find max qubit value used (hacky) *)
let rec get_dim_aux (u : coq_U ucom) acc =
  match u with
  | Coq_useq (u1, u2) -> get_dim_aux u1 (get_dim_aux u2 acc)
  | Coq_uapp (_, _, qs) -> List.fold_left max acc qs
let get_dim u = 1 + get_dim_aux u 0

(* write to qasm file *)
let rec sqir_to_qasm oc (u : coq_U ucom) k =
  match u with
  | Coq_useq (u1, u2) -> sqir_to_qasm oc u1 (fun _ -> sqir_to_qasm oc u2 k)
  | Coq_uapp (1, U_X, [a]) -> (fprintf oc "x q[%d];\n" a ; k ())
  | Coq_uapp (1, U_H, [a]) -> (fprintf oc "h q[%d];\n" a ; k ())
  | Coq_uapp (1, U_U1 (r), [a]) -> (fprintf oc "u1(%f) q[%d];\n" r a ; k ())
  | Coq_uapp (1, U_U2 (r1,r2), [a]) -> (fprintf oc "u2(%f,%f) q[%d];\n" r1 r2 a ; k ())
  | Coq_uapp (1, U_U3 (r1,r2,r3), [a]) -> (fprintf oc "u3(%f,%f,%f) q[%d];\n" r1 r2 r3 a ; k ())
  | Coq_uapp (2, U_CX, [a;b]) -> (fprintf oc "cx q[%d], q[%d];\n" a b ; k ())
  | Coq_uapp (2, U_SWAP, [a;b]) -> (fprintf oc "swap q[%d], q[%d];\n" a b ; k ())
  | Coq_uapp (3, U_CCX, [a;b;c]) -> (fprintf oc "ccx q[%d], q[%d], q[%d];\n" a b c ; k ())
  | Coq_uapp (3, U_CSWAP, [a;b;c]) -> (fprintf oc "cswap q[%d], q[%d], q[%d];\n" a b c ; k ())
  | Coq_uapp (4, U_C3X, [a;b;c;d]) -> (fprintf oc "c3x q[%d], q[%d], q[%d], q[%d];\n" a b c d ; k ())
  | Coq_uapp (5, U_C4X, [a;b;c;d;e]) -> (fprintf oc "c4x q[%d], q[%d], q[%d], q[%d], q[%d];\n" a b c d e ; k ())
  (* badly typed case (e.g. App2 of U_H) or unsupported gate *)
  | _ -> failwith "ERROR: Failed to write qasm file" 

(* insert measurements to get simulation results *)
let rec write_measurements oc dim =
  if dim = 0 then ()
  else (write_measurements oc (dim - 1) ; fprintf oc "measure q[%d] -> c[%d];\n" (dim - 1) (dim - 1))

let write_qasm_file fname (u : coq_U ucom) =
  let dim = get_dim u in
  let oc = open_out fname in
  (fprintf oc "OPENQASM 2.0;\ninclude \"qelib1.inc\";\n\n";
   fprintf oc "qreg q[%d];\n" dim;
   (*fprintf oc "creg c[%d];\n" dim;*)
   fprintf oc "\n";
   ignore(sqir_to_qasm oc u (fun _ -> ()));
   (*ignore(write_measurements oc dim);*)
   ignore(fprintf oc "\n"); (* ddsim is fussy about having a newline at the end *)
   close_out oc)

(* function to count gates *)
let rec count_gates_aux (u : coq_U ucom) acc =
  let (one,two,three,four,five) = acc in
  match u with
  | Coq_useq (u1, u2) -> count_gates_aux u1 (count_gates_aux u2 acc)
  | Coq_uapp (1, _, _) -> (1 + one, two, three, four, five)
  | Coq_uapp (2, _, _) -> (one, 1 + two, three, four, five)
  | Coq_uapp (3, _, _) -> (one, two, 1 + three, four, five)
  | Coq_uapp (4, _, _) -> (one, two, three, 1 + four, five)
  | Coq_uapp (5, _, _) -> (one, two, three, four, 1 + five)
  | _ -> failwith "ERROR: Failed to count gates"
let count_gates u = count_gates_aux u (0,0,0,0,0)

let print_and_write_file circ fname =
  let (c1,c2,c3,c4,c5) = count_gates circ in
  let _ = printf "\t%d qubits, %d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates, %d 4-qubit gates, %d 5-qubit gates\n%!" 
          (get_dim circ) c1 c2 c3 c4 c5 in
  write_qasm_file fname circ

let run_modmult_experiments c cinv m =
  if (c * cinv) mod m <> 1
  then failwith "Invalid inputs to run_modmult_experiments"
  else 
    let n = int_of_float (ceil (log10 (float_of_int (2 * m)) /. log10 2.0)) in (* = log2up m *)
    let fname = string_of_int (int_of_float (ceil (log10 (float_of_int m) /. log10 2.0))) ^ ".qasm" in

    let _ = printf "Generating circuit for ModMult.modmult_rev, inputs c=%d and m=%d...\n%!" c m in
    let _ = print_and_write_file (decompose_CU1_and_C3X (bc2ucom (ModMult.modmult_rev m c cinv n))) ("sqir-mod-mul-" ^ fname) in

    let _ = printf "Generating circuit for RZArith.rz_modmult_full, inputs c=%d and m=%d...\n%!" c m in
    let _ = print_and_write_file (trans_rz_modmult_rev m c cinv n) ("rz-mod-mul-" ^ fname) in

    let _ = printf "Generating circuit for CLArith.modmult_rev, inputs c=%d and m=%d...\n%!" c m in
    let _ = print_and_write_file (trans_modmult_rev m c cinv n) ("cl-mod-mul-" ^ fname) in

    ();;

let run_adders size m =
  let size_of_m = int_of_float (ceil (log10 (float_of_int m) /. log10 2.0)) in
  let fname = (string_of_int size) ^ ".qasm" in
  if size < size_of_m 
  then failwith "Invalid inputs to run_adders"
  else
    let _ = printf "Generating circuit for TOFF-based adder, input size=%d...\n%!" size in
    let _ = print_and_write_file (trans_cl_adder size) ("cl-adder-" ^ fname) in
    
    let _ = printf "Generating circuit for QFT-based constant adder, inputs size=%d M=%d...\n%!" size m in
    let _ = print_and_write_file (trans_rz_const_adder size m) ("rz-const-adder-" ^ fname) in
    
    let _ = printf "Generating circuit for QFT-based adder, input size=%d...\n%!" size in
    let _ = print_and_write_file (trans_rz_adder size) ("rz-adder-" ^ fname) in
    
    ();;

let run_multipliers size m =
  let size_of_m = int_of_float (ceil (log10 (float_of_int m) /. log10 2.0)) in
  let fname = (string_of_int size) ^ ".qasm" in
  if size < size_of_m 
  then failwith "Invalid inputs to run_multipliers"
  else
    let _ = printf "Generating circuit for TOFF-based constant multiplier, inputs size=%d M=%d...\n%!" size m in
    let _ = print_and_write_file (trans_cl_const_mul size m) ("cl-const-mul-" ^ fname) in

    let _ = printf "Generating circuit for TOFF-based multiplier, input size=%d...\n%!" size in
    let _ = print_and_write_file (trans_cl_mul size) ("cl-mul-" ^ fname) in
    
    let _ = printf "Generating circuit for QFT-based constant multiplier, inputs size=%d M=%d...\n%!" size m in
    let _ = print_and_write_file (trans_rz_const_mul size m) ("rz-const-mul-" ^ fname) in
    
    let _ = printf "Generating circuit for QFT-based multiplier, input size=%d...\n%!" size in
    let _ = print_and_write_file (trans_rz_mul size) ("rz-mul-" ^ fname) in
    
    ();;

let run_div_mod size m =
  let size_of_m = int_of_float (ceil (log10 (float_of_int m) /. log10 2.0)) in
  let fname = (string_of_int size) ^ ".qasm" in
  if size < size_of_m 
  then failwith "Invalid inputs to run_multipliers"
  else
    let _ = printf "Generating circuit for TOFF-based constant modder, inputs size=%d M=%d...\n%!" size m in
    let _ = print_and_write_file (trans_cl_mod size m) ("cl-mod-" ^ fname) in

    let _ = printf "Generating circuit for TOFF-based constant divider, inputs size=%d M=%d...\n%!" size m in
    let _ = print_and_write_file (trans_cl_div size m) ("cl-div-" ^ fname) in
    
    let _ = printf "Generating circuit for TOFF-based constant modder/divider, inputs size=%d M=%d...\n%!" size m in
    let _ = print_and_write_file (trans_cl_div_mod size m) ("cl-div-mod-" ^ fname) in
    
    let _ = printf "Generating circuit for QFT-based constant modder, inputs size=%d M=%d...\n%!" size m in
    let _ = print_and_write_file (trans_rz_mod size m) ("rz-mod-" ^ fname) in

    let _ = printf "Generating circuit for QFT-based constant divider, inputs size=%d M=%d...\n%!" size m in
    let _ = print_and_write_file (trans_rz_div size m) ("rz-div-" ^ fname) in
    
    let _ = printf "Generating circuit for QFT-based constant modder/divider, inputs size=%d M=%d...\n%!" size m in
    let _ = print_and_write_file (trans_rz_div_mod size m) ("rz-div-mod-" ^ fname) in
    
    ();;

let run_partial_eval_exp size =
  let fname = (string_of_int size) ^ ".qasm" in
  let _ = printf "Generating circuits for partial eval experiments, input size=%d...\n%!" size in
  match trans_dmc_qft size with 
  | None -> printf "ERROR: trans_dmc_qft returned None\n%!"
  | Some c -> print_and_write_file c ("partial-eval-rz-const-" ^ fname);
  match trans_dmc_cl size with 
  | None -> printf "ERROR: trans_dmc_cl returned None\n%!"
  | Some c -> print_and_write_file c ("partial-eval-cl-const-" ^ fname);
  match trans_dmq_qft size with 
  | None -> printf "ERROR: trans_dmq_qft returned None\n%!"
  | Some c -> print_and_write_file c ("partial-eval-rz-" ^ fname);
  match trans_dmq_cl size with 
  | None -> printf "ERROR: trans_dmq_cl returned None\n%!"
  | Some c -> print_and_write_file c ("partial-eval-cl-" ^ fname);
  ();;

run_modmult_experiments 139 117 173;;
run_adders 16 38168;;
run_multipliers 16 38168;;
run_div_mod 16 38168;;
run_partial_eval_exp 16;;
