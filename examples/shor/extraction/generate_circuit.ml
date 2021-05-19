open Printf

open AltGateSet
open ShorExtr

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
   ignore(fprintf oc "\n"); (* ddsim is fussy about having a newline at the end... *)
   close_out oc)
   
(* function to count gates *)
let rec count_gates_aux (u : coq_U ucom) acc =
  match u with
  | Coq_useq (u1, u2) -> count_gates_aux u1 (count_gates_aux u2 acc)
  | Coq_uapp (_, _, _) -> 1 + acc
let count_gates u = count_gates_aux u 0

(* light argument parsing *)
let n = ref 0
let a = ref 0
let usage = "usage: " ^ Sys.argv.(0) ^ " [-N int] [-a int]"
let speclist = [
    ("-N", Arg.Set_int n, ": number to factor");
    ("-a", Arg.Set_int a, ": coprime value");
  ]
let () =
  Arg.parse
    speclist
    (fun x -> raise (Arg.Bad ("Bad argument : " ^ x)))
    usage;
if (!a <= 0 || !n <= !a) then printf "ERROR: Requires 0 < a < N\n%!" else 
if (Z.gcd (Z.of_int !a) (Z.of_int !n) > Z.one) then printf "ERROR: Requires a, N comprime\n%!" else 
(printf "Generating circuit for N = %d and a = %d...\n%!" !n !a;
 let t1 = Unix.gettimeofday () in
 let ((u, num_qubits), num_cbits) = shor_circuit !a !n in 
 let _ = printf "Time to generate: %fs\n%!" (Unix.gettimeofday () -. t1) in
 let _ = printf "Counting gates...\n%!" in
 let t2 = Unix.gettimeofday () in
 let c = count_gates u in
 let _ = printf "%d qubits and %d gates.\n%!" num_qubits c in
 let _ = printf "Time to count gates: %fs\n" (Unix.gettimeofday () -. t2) in
 let _ = printf("Writing file to shor.qasm...\n%!") in
 let t3 = Unix.gettimeofday () in
 let _ = write_qasm_file "shor.qasm" u num_qubits num_cbits in
 printf "Time to write file: %fs\n%!" (Unix.gettimeofday () -. t3))


