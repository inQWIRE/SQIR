open Printf
open SQIR
open ShorExtr

(* functions to write SQIR data structure to OpenQASM *)
let rec sqir_to_qasm oc (u : base_ucom) k =
  match u with
  | Coq_useq (u1, u2) -> sqir_to_qasm oc u1 (fun _ -> sqir_to_qasm oc u2 k)
  | Coq_uapp1 (U_R (f1,f2,f3), n) -> 
      if f1 = Float.pi /. 2.0 && f2 = 0.0 && f3 = Float.pi
      then (fprintf oc "h q[%d];\n" n ; k ())
      else if f1 = Float.pi && f2 = 0.0 && f3 = Float.pi
      then (fprintf oc "x q[%d];\n" n ; k ())
      else if f1 = 0.0 && f2 = 0.0
      then (fprintf oc "u1(%f) q[%d];\n" f3 n ; k ())
      else (fprintf oc "u3(%f,%f,%f) q[%d];\n" f1 f2 f3 n ; k ())
  | Coq_uapp2 (U_CNOT, m, n) -> fprintf oc "cx q[%d], q[%d];\n" m n ; k ()
  | _ -> raise (Failure ("ERROR: Failed to write qasm file")) (* badly typed case (e.g. App2 of U_R) *)

let rec write_measurements oc dim =
  if dim = 0 then ()
  else (write_measurements oc (dim - 1) ; fprintf oc "measure q[%d] -> c[%d];\n" (dim - 1) (dim - 1))

let write_qasm_file fname (u : base_ucom) dim m =
  let oc = open_out fname in
  (fprintf oc "OPENQASM 2.0;\ninclude \"qelib1.inc\";\n\n";
   fprintf oc "qreg q[%d];\n" dim;
   fprintf oc "creg c[%d];\n" m;
   fprintf oc "\n";
   ignore(sqir_to_qasm oc u (fun _ -> ()));
   ignore(write_measurements oc m);
   close_out oc)
   
(* function to count gates *)
let rec count_gates_aux (u : base_ucom) k =
  match u with
  | Coq_useq (u1, u2) -> 
       let k' (c1, c2) =
         count_gates_aux u2 (fun (c1', c2') -> k (c1 + c1', c2 + c2')) in
       count_gates_aux u1 k'
  | Coq_uapp1 (U_R (_,_,_), _) -> k (1,0)
  | Coq_uapp2 (U_CNOT, _, _) -> k (0,1)
  | _ -> raise (Failure ("ERROR: Failed to count gates")) 
let count_gates u = count_gates_aux u (fun x -> x)

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
 let (c1,c2) = count_gates u in
 let _ = printf "%d qubits, %d 1-qubit gates, and %d 2-qubit gates.\n%!" num_qubits c1 c2 in
 let _ = printf "Time to count gates: %fs\n" (Unix.gettimeofday () -. t2) in
 let _ = printf("Writing file to shor.qasm...\n%!") in
 let t3 = Unix.gettimeofday () in
 let _ = write_qasm_file "shor.qasm" u num_qubits num_cbits in
 printf "Time to write file: %fs\n%!" (Unix.gettimeofday () -. t3))



(* ignore the following -- it's from my attempt at runing VOQC *)

 (* let _ = printf "Converting from SQIR ucom to VOQC gate_list...\n%!" in
 let t2 = Unix.gettimeofday () in
 let l = ucom_to_gate_list u in
 let _ = printf "Time to convert: %fs\n%!" (Unix.gettimeofday () -. t2) in
 let _ = printf "Optimizing resulting gate_list...\n%!" in
 let t3 = Unix.gettimeofday () in
 let l' = optimize_ibm l in
 let _ = printf "Time to optimize: %fs\n" (Unix.gettimeofday () -. t3) in
 let _ = printf "Writing result to shor.qasm...\n%!" in
 let t4 = Unix.gettimeofday () in
 let _ = write_qasm_file "shor.qasm" l' num_qubits in
 let _ = add_measurements "shor.qasm" num_cbits in
 let _ = printf "Time to write: %fs\n\n" (Unix.gettimeofday () -. t4) in
 let origU1 = get_u1_count l in
 let origU2 = get_u2_count l in
 let origU3 = get_u3_count l in
 let origCNOT = get_cnot_count l in
 let _ = printf "Original stats:\t %d qubits, U1 %d, U2 %d, U3 %d, CNOT %d\n%!" 
         num_qubits origU1 origU2 origU3 origCNOT in
 let finalU1 = get_u1_count l' in
 let finalU2 = get_u2_count l' in
 let finalU3 = get_u3_count l' in
 let finalCNOT = get_cnot_count l' in
 let _ = printf "Final stats:\t %d qubits, U1 %d, U2 %d, U3 %d, CNOT %d\n%!" 
         num_qubits finalU1 finalU2 finalU3 finalCNOT in
 ()) *)

