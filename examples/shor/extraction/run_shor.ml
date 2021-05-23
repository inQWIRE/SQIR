open Printf

open AltGateSet
open Main
   
(* function to count gates (sanity check) *)
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
(printf "TODO: add check that N can be written as (p^k * q) for k>0, prime p>2, q>2, and p^k, q coprime\n";

 printf "Running Shor's for N = %d and a = %d...\n%!" !n !a;
 let res = end_to_end_shors !a !n in
 match res with
 | Some o -> printf "Non-trivial factor is %d.\n" o
 | None ->
     let quit = ref false in
     while not !quit do
      print_string "Failed to find non-trivial factor. Try another measurement outcome? (Y/n) ";
      let str = read_line () in
        if str.[0] <> 'Y' then quit := true
        else let x = Run.run_circuit_cached () in
             match factor !a !n (cont_frac_exp !a !n x) with
             | None -> ()
             | Some o -> (printf "Non-trivial factor is %d.\n" o; quit := true)
     done )
 