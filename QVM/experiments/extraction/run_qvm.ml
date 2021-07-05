open Printf

open AltGateSet2
open AltVSQIR
open OracleExample

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

let write_qasm_file fname (u : coq_U ucom) dim =
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

(* main function *)
let run c cinv m =
  if (c * cinv) mod m <> 1
  then failwith "Invalid inputs to run function"
  else 
    let n = int_of_float (ceil (log10 (float_of_int (2 * m)) /. log10 2.0)) in (* = log2up m *)
    let dim_for_rz = 2 * n + 1 in
    let dim_for_cl = 4 * n + 2 in
    let dim_for_sqir = 4 * n + 11 in
    let fname = string_of_int (int_of_float (ceil (log10 (float_of_int m) /. log10 2.0))) ^ ".qasm" in

    let _ = printf "Generating circuit for ModMult.modmult_rev, inputs c=%d and m=%d...\n%!" c m in
    let sqir_circ = bc2ucom (ModMult.modmult_rev m c cinv n) in
    let (x,y,z) = count_gates sqir_circ in
    let _ = printf "\t%d qubits, %d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates, %d total\n%!" 
              dim_for_sqir x y z (x+y+z) in
    let _ = write_qasm_file ("sqir-mod-mul-" ^ fname) sqir_circ dim_for_sqir in

    let _ = printf "Generating circuit for RZArith.rz_modmult_full, inputs c=%d and m=%d...\n%!" c m in
    let rz_circ = fst (fst (trans_rz_modmult_rev m c cinv n)) in
    let (x,y,z) = count_gates rz_circ in
    let _ = printf "\t%d qubits, %d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates, %d total\n%!" 
              dim_for_rz x y z (x+y+z) in
    let _ = write_qasm_file ("rz-mod-mul-" ^ fname) rz_circ dim_for_rz in

    let _ = printf "Generating circuit for CLArith.modmult_rev, inputs c=%d and m=%d...\n%!" c m in
    let cl_circ = fst (fst (trans_modmult_rev m c cinv n)) in
    let (x,y,z) = count_gates cl_circ in
    let _ = printf "\t%d qubits, %d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates, %d total\n%!" 
              dim_for_cl x y z (x+y+z) in
    let _ = write_qasm_file ("cl-mod-mul-" ^ fname) cl_circ dim_for_cl in
    ();;

(*run 2 2 3;;
run 5 3 7;;
run 7 13 15;;
run 17 11 31;;
run 32 2 63;;*)

let c_qfta = prog_to_sqir_real (sin_prog 31) QFTA;;
let (x,y,z) = count_gates c_qfta;;
printf "%d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates\n%!" x y z;;
write_qasm_file "foo1.qasm" c_qfta 10;;
match (sin_prog 3) with
| (p0, _) ->
  let (p1, _) = p0 in
  let (p2, fl) = p1 in
  let (_, l) = p2 in
  match (MiniQASM.gen_genv l) with
  | None -> printf "FAILED at gen_genv\n%!"
  | Some bv -> 
    (match (MiniQASM.type_funs bv MiniQASM.fenv_empty fl) with
     | None -> printf "FAILED at type_funs\n%!"
     | Some _ -> printf "succeeded\n%!")
;;

let c_classic = prog_to_sqir_real (sin_prog 31) Classic;;
let (x,y,z) = count_gates c_classic;;
printf "%d 1-qubit gates, %d 2-qubit gates, %d 3-qubit gates\n%!" x y z;;
write_qasm_file "foo2.qasm" c_classic 10;;
