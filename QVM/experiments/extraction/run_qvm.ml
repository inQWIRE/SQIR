open Printf

open AltGateSet2
open AltPQASM
open OracleExample

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
  | Coq_uapp (3, U_CCX, [a;b;c]) -> (fprintf oc "ccx q[%d], q[%d], q[%d];\n" a b c ; k ())
  | _ -> failwith "ERROR: Failed to write qasm file" (* badly typed case (e.g. App2 of U_H) *)

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
  let (one,two,three) = acc in
  match u with
  | Coq_useq (u1, u2) -> count_gates_aux u1 (count_gates_aux u2 acc)
  | Coq_uapp (1, _, _) -> (1 + one, two, three)
  | Coq_uapp (2, _, _) -> (one, 1 + two, three)
  | Coq_uapp (3, _, _) -> (one, two, 1 + three)
  | _ -> failwith "ERROR: Failed to count gates"
let count_gates u = count_gates_aux u (0,0,0)

let run_modmult_experiments c cinv m =
  if (c * cinv) mod m <> 1
  then failwith "Invalid inputs to run_modmult_experiments"
  else 
    let n = int_of_float (ceil (log10 (float_of_int (2 * m)) /. log10 2.0)) in (* = log2up m *)
    let fname = string_of_int (int_of_float (ceil (log10 (float_of_int m) /. log10 2.0))) ^ ".qasm" in

    let _ = printf "Generating circuit for ModMult.modmult_rev, inputs c=%d and m=%d...\n%!" c m in
    let sqir_circ = bc2ucom (ModMult.modmult_rev m c cinv n) in
    let (x,y,z) = count_gates sqir_circ in
    let _ = printf "\t%d qubits, %d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates, %d total\n%!" 
              (get_dim sqir_circ) x y z (x+y+z) in
    let _ = write_qasm_file ("sqir-mod-mul-" ^ fname) sqir_circ in

    let _ = printf "Generating circuit for RZArith.rz_modmult_full, inputs c=%d and m=%d...\n%!" c m in
    let rz_circ = fst (fst (trans_rz_modmult_rev m c cinv n)) in
    let (x,y,z) = count_gates rz_circ in
    let _ = printf "\t%d qubits, %d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates, %d total\n%!" 
              (get_dim rz_circ) x y z (x+y+z) in
    let _ = write_qasm_file ("rz-mod-mul-" ^ fname) rz_circ in

    let _ = printf "Generating circuit for CLArith.modmult_rev, inputs c=%d and m=%d...\n%!" c m in
    let cl_circ = fst (fst (trans_modmult_rev m c cinv n)) in
    let (x,y,z) = count_gates cl_circ in
    let _ = printf "\t%d qubits, %d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates, %d total\n%!" 
              (get_dim cl_circ) x y z (x+y+z) in
    let _ = write_qasm_file ("cl-mod-mul-" ^ fname) cl_circ in
    ();;

(*run_modmult_experiments 2 2 3;;
run_modmult_experiments 5 3 7;;
run_modmult_experiments 7 13 15;;
run_modmult_experiments 17 11 31;;
run_modmult_experiments 32 2 63;;*)

(* testing... *)
match QIMP.trans_prog (sin_prog 1) Classic with
  | None -> printf "Failed\n%!"
  | Some _ -> printf "Succeeded\n%!"
;;

(*
(* these both end up being 1-gate (SKIP) programs *)
let c_qfta = prog_to_sqir_real (sin_prog 31) QFTA;;
let (x,y,z) = count_gates c_qfta;;
printf "%d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates\n%!" x y z;;

let c_classic = prog_to_sqir_real (sin_prog 31) Classic;;
let (x,y,z) = count_gates c_classic;;
printf "%d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates\n%!" x y z;;
*)

let run_adders size m =
  let size_of_m = int_of_float (ceil (log10 (float_of_int m) /. log10 2.0)) in
  let fname = (string_of_int size) ^ ".qasm" in
  if size < size_of_m 
  then failwith "Invalid inputs to run_adders"
  else
    let _ = printf "Generating circuit for TOFF-based adder, input size=%d...\n%!" size in
    let cl_adder = fst (fst (trans_cl_adder size)) in
    let (x,y,z) = count_gates cl_adder in
    let _ = printf "\t%d qubits, %d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates\n%!" 
              (get_dim cl_adder) x y z in
    let _ = write_qasm_file ("cl-adder-" ^ fname) cl_adder in
    
    let _ = printf "Generating circuit for QFT-based constant adder, inputs size=%d M=%d...\n%!" size m in
    let rz_const_adder = fst (fst (trans_rz_const_adder size m)) in
    let (x,y,z) = count_gates rz_const_adder in
    let _ = printf "\t%d qubits, %d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates\n%!" 
              (get_dim rz_const_adder) x y z in
    let _ = write_qasm_file ("rz-const-adder-" ^ fname) rz_const_adder in
    
    let _ = printf "Generating circuit for QFT-based adder, input size=%d...\n%!" size in
    let rz_adder = fst (fst (trans_rz_adder size)) in
    let (x,y,z) = count_gates rz_adder in
    let _ = printf "\t%d qubits, %d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates\n%!" 
              (get_dim rz_adder) x y z in
    let _ = write_qasm_file ("rz-adder-" ^ fname) rz_adder in
    ();;

let run_multipliers size m =
  let size_of_m = int_of_float (ceil (log10 (float_of_int m) /. log10 2.0)) in
  let fname = (string_of_int size) ^ ".qasm" in
  if size < size_of_m 
  then failwith "Invalid inputs to run_multipliers"
  else
    let _ = printf "Generating circuit for TOFF-based constant multiplier, input size=%d M=%d...\n%!" size m in
    let cl_const_mul = fst (fst (trans_cl_const_mul size m)) in
    let (x,y,z) = count_gates cl_const_mul in
    let _ = printf "\t%d qubits, %d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates\n%!" 
              (get_dim cl_const_mul) x y z in
    let _ = write_qasm_file ("cl-const-mul-" ^ fname) cl_const_mul in

    let _ = printf "Generating circuit for TOFF-based multiplier, input size=%d...\n%!" size in
    let cl_mul = fst (fst (trans_cl_mul size)) in
    let (x,y,z) = count_gates cl_mul in
    let _ = printf "\t%d qubits, %d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates\n%!" 
              (get_dim cl_mul) x y z in
    let _ = write_qasm_file ("cl-mul-" ^ fname) cl_mul in
    
    let _ = printf "Generating circuit for QFT-based constant multiplier, inputs size=%d M=%d...\n%!" size m in
    let rz_const_mul = fst (fst (trans_rz_const_mul size m)) in
    let (x,y,z) = count_gates rz_const_mul in
    let _ = printf "\t%d qubits, %d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates\n%!" 
              (get_dim rz_const_mul) x y z in
    let _ = write_qasm_file ("rz-const-mul-" ^ fname) rz_const_mul in
    
    let _ = printf "Generating circuit for QFT-based multiplier, input size=%d...\n%!" size in
    let rz_mul = fst (fst (trans_rz_mul size)) in
    let (x,y,z) = count_gates rz_mul in
    let _ = printf "\t%d qubits, %d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates\n%!" 
              (get_dim rz_mul) x y z in
    let _ = write_qasm_file ("rz-mul-" ^ fname) rz_mul in
    ();;

run_adders 32 3647837559;; (* overflows! *)
(*run_adders 8 143;;
run_adders 16 38168;;
run_multipliers 8 143;;
run_multipliers 16 38168;;*)
