open Printf

open ExtractionGateSet
open ExtrShor
open Main
open Run
   
(* function to count gates (sanity check) *)
let rec count_gates_aux (u : coq_U ucom) acc =
  match u with
  | Coq_useq (u1, u2) -> count_gates_aux u1 (count_gates_aux u2 acc)
  | Coq_uapp (_, _, _) -> 1 + acc
let count_gates u = count_gates_aux u 0

let rec get_random_stream' n = 
  if n = 0 then [] else Random.float 1. :: get_random_stream' (n - 1)

let get_random_stream n = Random.self_init (); get_random_stream' n

(* light argument parsing *)
let n = ref 0
let a = ref 0
let niters = ref 1
let usage = "usage: " ^ Sys.argv.(0) ^ " [-N int] [--gen-circuit int] [--niters int]"
let speclist = [
    ("-N", Arg.Set_int n, ": number to factor");
    ("--gen-circuit", Arg.Set_int a, ": generate an OF circuit with coprime value a (don't run full Shor's)");
    ("--niters", Arg.Set_int niters, ": max number of iterations (default is 1)")
  ]
let () =
  Arg.parse
    speclist
    (fun x -> raise (Arg.Bad ("Bad argument : " ^ x)))
    usage;
if (!n <= 1) then printf "ERROR: Requires 1 < N\n%!" else 
(
printf "TODO: add check that N can be written as (p^k * q) for k>0, prime p>2, q>2, and coprime(p^k, q)\n";
if (!a == 0)
then (
  printf "Running Shor's for N = %d\n%!" !n;
  let rnds = get_random_stream !niters in
  let res = end_to_end_shors (Z.of_int !n) rnds in
  match res with
  | Some o -> printf "Non-trivial factor is %d.\n" (Z.to_int o)
  | None -> printf "Failed to find non-trivial factor.\n"
)
else (
  if (!a < 0 || !n <= !a) then printf "ERROR: Requires 0 < a < N\n%!" else 
  if (Z.gcd (Z.of_int !a) (Z.of_int !n) > Z.one) then printf "ERROR: Requires a, N comprime\n%!" else 
  (printf "Generating circuit for N = %d and a = %d\n%!" !n !a;
   let c = shor_circuit (Z.of_int !a) (Z.of_int !n) in
   let nqs = Z.to_int (shor_nqs (Z.of_int !n)) in
   write_qasm_file ("shor_" ^ string_of_int !n ^ "_" ^ string_of_int !a ^ ".qasm") c nqs)
)
)
 