open Printf

open ExtractionGateSet

let rec sqir_to_qasm oc (u : coq_U ucom) k =
  match u with
  | Coq_useq (u1, u2) -> sqir_to_qasm oc u1 (fun _ -> sqir_to_qasm oc u2 k)
  | Coq_uapp (_, U_X, [a]) -> (fprintf oc "x q[%d];\n" (Z.to_int a) ; k ())
  | Coq_uapp (_, U_H, [a]) -> (fprintf oc "h q[%d];\n" (Z.to_int a) ; k ())
  | Coq_uapp (_, U_U1 (r), [a]) -> (fprintf oc "u1(%f) q[%d];\n" r (Z.to_int a) ; k ())
  | Coq_uapp (_, U_U2 (r1,r2), [a]) -> (fprintf oc "u2(%f,%f) q[%d];\n" r1 r2 (Z.to_int a) ; k ())
  | Coq_uapp (_, U_U3 (r1,r2,r3), [a]) -> (fprintf oc "u3(%f,%f,%f) q[%d];\n" r1 r2 r3 (Z.to_int a) ; k ())
  | Coq_uapp (_, U_CX, [a;b]) -> (fprintf oc "cx q[%d], q[%d];\n" (Z.to_int a) (Z.to_int b) ; k ())
  | Coq_uapp (_, U_CU1 (r), [a;b]) -> (fprintf oc "cu1(%f) q[%d], q[%d];\n" r (Z.to_int a) (Z.to_int b) ; k ())
  | Coq_uapp (_, U_CH, [a;b]) -> (fprintf oc "ch q[%d], q[%d];\n" (Z.to_int a) (Z.to_int b) ; k ())
  | Coq_uapp (_, U_SWAP, [a;b]) -> (fprintf oc "swap q[%d], q[%d];\n" (Z.to_int a) (Z.to_int b) ; k ())
  | Coq_uapp (_, U_CCX, [a;b;c]) -> (fprintf oc "ccx q[%d], q[%d], q[%d];\n" (Z.to_int a) (Z.to_int b) (Z.to_int c) ; k ())
  | Coq_uapp (_, U_CCU1 (r), [a;b;c]) -> (fprintf oc "ccu1(%f) q[%d], q[%d], q[%d];\n" r (Z.to_int a) (Z.to_int b) (Z.to_int c) ; k ())
  | Coq_uapp (_, U_CSWAP, [a;b;c]) -> (fprintf oc "cswap q[%d], q[%d], q[%d];\n" (Z.to_int a) (Z.to_int b) (Z.to_int c) ; k ())
  | Coq_uapp (_, U_C3X, [a;b;c;d]) -> (fprintf oc "c3x q[%d], q[%d], q[%d], q[%d];\n" (Z.to_int a) (Z.to_int b) (Z.to_int c) (Z.to_int d) ; k ())
  | Coq_uapp (_, U_C4X, [a;b;c;d;e]) -> (fprintf oc "c4x q[%d], q[%d], q[%d], q[%d], q[%d];\n" (Z.to_int a) (Z.to_int b) (Z.to_int c) (Z.to_int d) (Z.to_int e) ; k ())
  | _ -> raise (Failure ("ERROR: Failed to write qasm file"))

let rec write_measurements oc dim =
  if dim = 0 then ()
  else (write_measurements oc (dim - 1) ; fprintf oc "measure q[%d] -> c[%d];\n" (dim - 1) (dim - 1))

let write_qasm_file fname (u : coq_U ucom) dim =
  let oc = open_out fname in
  (fprintf oc "OPENQASM 2.0;\ninclude \"qelib1.inc\";\n\n";
   fprintf oc "qreg q[%d];\n" dim;
   fprintf oc "creg c[%d];\n" dim;
   fprintf oc "\n";
   ignore(sqir_to_qasm oc u (fun _ -> ()));
   ignore(write_measurements oc dim);
   ignore(fprintf oc "\n"); (* ddsim is fussy about having a newline at the end *)
   close_out oc)

(** val run_circuit : int -> coq_U ucom -> float -> int *)
(* float argument (rnd) is ignored *)
let run_circuit n c _ =
  (* write circuit to shor.qasm *)
  write_qasm_file "shor.qasm" c (Z.to_int n);
  (* simulate circuit using run_circuit.py *)
  let _ = printf "Simulating circuit, this will take a little while...\n%!" in
  let start = Unix.gettimeofday () in
  let inc = Unix.open_process_in "python run_circuit.py shor.qasm" in
  (* read measurement outcome from console *)
  try 
    let line = input_line inc in
    let x = Z.of_string line in
    let stop = Unix.gettimeofday () in
    (close_in inc; 
     printf "\tOutcome of simulation is %d\n%!" (Z.to_int x); 
     printf "\tTime taken: %fs\n%!" (stop -. start); 
     x)
  with _ ->
    (close_in_noerr inc;
     failwith "ERROR: circuit simulation failed.\n")