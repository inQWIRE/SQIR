open Printf

open AltGateSet

let rec sqir_to_qasm oc (u : coq_U ucom) k =
  match u with
  | Coq_useq (u1, u2) -> sqir_to_qasm oc u1 (fun _ -> sqir_to_qasm oc u2 k)
  | Coq_uapp (_, U_X, [a]) -> (fprintf oc "x q[%d];\n" a ; k ())
  | Coq_uapp (_, U_H, [a]) -> (fprintf oc "h q[%d];\n" a ; k ())
  | Coq_uapp (_, U_U1 (r), [a]) -> (fprintf oc "u1(%f) q[%d];\n" r a ; k ())
  | Coq_uapp (_, U_U2 (r1,r2), [a]) -> (fprintf oc "u2(%f,%f) q[%d];\n" r1 r2 a ; k ())
  | Coq_uapp (_, U_U3 (r1,r2,r3), [a]) -> (fprintf oc "u3(%f,%f,%f) q[%d];\n" r1 r2 r3 a ; k ())
  | Coq_uapp (_, U_CX, [a;b]) -> (fprintf oc "cx q[%d], q[%d];\n" a b ; k ())
  | Coq_uapp (_, U_CU1 (r), [a;b]) -> (fprintf oc "cu1(%f) q[%d], q[%d];\n" r a b ; k ())
  | Coq_uapp (_, U_SWAP, [a;b]) -> (fprintf oc "swap q[%d], q[%d];\n" a b ; k ())
  | Coq_uapp (_, U_CCX, [a;b;c]) -> (fprintf oc "ccx q[%d], q[%d], q[%d];\n" a b c ; k ())
  | Coq_uapp (_, U_CSWAP, [a;b;c]) -> (fprintf oc "cswap q[%d], q[%d], q[%d];\n" a b c ; k ())
  | Coq_uapp (_, U_C3X, [a;b;c;d]) -> (fprintf oc "c3x q[%d], q[%d], q[%d], q[%d];\n" a b c d ; k ())
  | Coq_uapp (_, U_C4X, [a;b;c;d;e]) -> (fprintf oc "c4x q[%d], q[%d], q[%d], q[%d], q[%d];\n" a b c d e ; k ())
  | _ -> raise (Failure ("ERROR: Failed to write qasm file"))

let write_qasm_file fname (u : coq_U ucom) dim =
  let oc = open_out fname in
  (fprintf oc "OPENQASM 2.0;\ninclude \"qelib1.inc\";\n\n";
   fprintf oc "qreg q[%d];\n\n" dim;
   ignore(sqir_to_qasm oc u (fun _ -> ()));
   ignore(fprintf oc "\n");
   close_out oc)