open Printf

(* The extracted code is in the file ShorExtr.ml *)
open SQIR
open ShorExtr

(* functions to write SQIR data structure to OpenQASM *)
let rec sqir_to_qasm oc (u : base_ucom) k =
  match u with
  | Coq_useq (u1, u2) -> sqir_to_qasm oc u1 (fun _ -> sqir_to_qasm oc u2 k)
  | Coq_uapp1 (U_R (f1,f2,f3), n) -> fprintf oc "u3(%f,%f,%f) q[%d];\n" f1 f2 f3 n ; k ()
  | Coq_uapp2 (U_CNOT, m, n) -> fprintf oc "cx q[%d], q[%d];\n" m n ; k ()
  | _ -> raise (Failure ("ERROR: Failed to write qasm file")) (* badly typed case (e.g. App2 of U_R) *)

let write_qasm_file fname (u : base_ucom) dim =
  let oc = open_out fname in
  (fprintf oc "OPENQASM 2.0;\ninclude \"qelib1.inc\";\n\n";
   fprintf oc "qreg q[%d];\n" dim;
   fprintf oc "\n";
   ignore(sqir_to_qasm oc u (fun _ -> ()));
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
    ("-a", Arg.Set_int a, ": coprime vaue");
  ]
let () =
  Arg.parse
    speclist
    (fun x -> raise (Arg.Bad ("Bad argument : " ^ x)))
    usage;
if (!a <= 0 || !n <= !a) then printf "ERROR: Requires 0 < a < N\n%!" else 
if (Z.gcd (Z.of_int !a) (Z.of_int !n) > Z.one) then printf "ERROR: Requires a, N comprime\n%!" else 
(printf "Generating circuit for N = %d and a = %d...\n%!" !n !a;
 let (u, num_qubits) = shor_circuit !a !n in
 (* print some stats *)
 let (c1,c2) = count_gates u in
 printf "Produced a circuit with %d qubits, %d 1-qubit gates, and %d 2-qubit gates.\n%!" num_qubits c1 c2;
 (* write OpenQASM file *)
 printf("Writing file...\n%!");
 write_qasm_file "shor.qasm" u num_qubits;
 printf("Done.\n%!"))