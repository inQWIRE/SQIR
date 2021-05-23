open Printf

open AltGateSet

let rec sqir_to_qasm oc (u : coq_U ucom) k =
  match u with
  | Coq_useq (u1, u2) -> sqir_to_qasm oc u1 (fun _ -> sqir_to_qasm oc u2 k)
  | Coq_uapp (1, U_X, [a]) -> (fprintf oc "x q[%d];\n" a ; k ())
  | Coq_uapp (1, U_H, [a]) -> (fprintf oc "h q[%d];\n" a ; k ())
  | Coq_uapp (1, U_U1 (r), [a]) -> (fprintf oc "u1(%f) q[%d];\n" r a ; k ())
  | Coq_uapp (1, U_U2 (r1,r2), [a]) -> (fprintf oc "u2(%f,%f) q[%d];\n" r1 r2 a ; k ())
  | Coq_uapp (1, U_U3 (r1,r2,r3), [a]) -> (fprintf oc "u3(%f,%f,%f) q[%d];\n" r1 r2 r3 a ; k ())
  | Coq_uapp (2, U_CX, [a;b]) -> (fprintf oc "cx q[%d], q[%d];\n" a b ; k ())
  | Coq_uapp (2, U_CU1 (r), [a;b]) -> (fprintf oc "cu1(%f) q[%d], q[%d];\n" r a b ; k ())
  | Coq_uapp (2, U_SWAP, [a;b]) -> (fprintf oc "swap q[%d], q[%d];\n" a b ; k ())
  | Coq_uapp (3, U_CCX, [a;b;c]) -> (fprintf oc "ccx q[%d], q[%d], q[%d];\n" a b c ; k ())
  | Coq_uapp (3, U_CSWAP, [a;b;c]) -> (fprintf oc "cswap q[%d], q[%d], q[%d];\n" a b c ; k ())
  | Coq_uapp (4, U_C3X, [a;b;c;d]) -> (fprintf oc "c3x q[%d], q[%d], q[%d], q[%d];\n" a b c d ; k ())
  | Coq_uapp (5, U_C4X, [a;b;c;d;e]) -> (fprintf oc "c4x q[%d], q[%d], q[%d], q[%d], q[%d];\n" a b c d e ; k ())
  | _ -> raise (Failure ("ERROR: Failed to write qasm file")) (* badly typed case (e.g. App2 of U_H) *)

let rec write_measurements oc dim =
  if dim = 0 then ()
  else (write_measurements oc (dim - 1) ; fprintf oc "measure q[%d] -> c[%d];\n" (dim - 1) (dim - 1))

let write_qasm_file fname (u : coq_U ucom) dim m =
  let oc = open_out fname in
  (fprintf oc "OPENQASM 2.0;\ninclude \"qelib1.inc\";\n\n";
   fprintf oc "qreg q[%d];\n" dim;
   fprintf oc "creg c[%d];\n" m;
   fprintf oc "\n";
   ignore(sqir_to_qasm oc u (fun _ -> ()));
   ignore(write_measurements oc m);
   ignore(fprintf oc "\n"); (* ddsim is fussy about having a newline at the end *)
   close_out oc)

(* slow because it has to do file I/O, start Python, import qiskit, do simulation *)
let run_circuit n k u =
  (* write circuit to shor.qasm *)
  write_qasm_file "shor.qasm" u n k;
  (* simulate circuit using run_circuit.py *)
  let inc = Unix.open_process_in "python run_circuit.py" in
  try 
    let line = input_line inc in
    let x = int_of_string line in
    (close_in inc; printf "Measurement outcome is %d\n" x; x)
  with _ ->
    (close_in_noerr inc;
     failwith "Error occurred while getting measurement results.\n")
 
let run_circuit_cached () =
  (* simulate circuit using run_circuit.py -c *)
  let inc = Unix.open_process_in "python run_circuit.py -c" in
  try 
    let line = input_line inc in
    let x = int_of_string line in
    (close_in inc; printf "Measurement outcome is %d\n" x; x) 
  with _ ->
    (close_in_noerr inc;
     failwith "Error occurred while getting measurement results.\n")