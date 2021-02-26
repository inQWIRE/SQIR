open Printf
open SQIR
open ShorExtr
open Voqc.IBMGateSet
open Voqc.IBMUtils
open Voqc.Optimize

(* tail recursive append *)
let app l1 l2 = List.rev_append (List.rev l1) l2

let rec ucom_to_gate_list (u : base_ucom) : coq_IBM_ucom_l =
  match u with
  | Coq_useq (u1, u2) -> app (ucom_to_gate_list u1) (ucom_to_gate_list u2)
  | Coq_uapp1 (U_R (f1,f2,f3), n) -> [ App1 (UIBM_U3(f1,f2,f3), n) ]
  | Coq_uapp2 (U_CNOT, m, n) -> [ App2 (UIBM_CNOT, m, n) ]
  | _ -> raise (Failure ("ERROR: Failed to convert ucom to gate_list"))

let rec write_measurements oc n =
  if n = 0 then ()
  else (write_measurements oc (n - 1) ; fprintf oc "measure q[%d] -> c[%d];\n" (n - 1) (n - 1))

let add_measurements fname n =
  let oc = open_out_gen [Open_append] 0o666 fname in (* open & append to file *)
  fprintf oc "creg c[%d];\n" n;
  write_measurements oc n;
  close_out oc

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
 let _ = printf "Converting from SQIR ucom to VOQC gate_list...\n%!" in
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
 ())

